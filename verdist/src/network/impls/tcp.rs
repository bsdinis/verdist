use std::io::Read;
use std::io::Write;
use std::marker::PhantomData;
use std::net::SocketAddr;
use std::net::TcpStream;
use std::net::ToSocketAddrs;
use std::os::fd::AsRawFd;
use std::time::Duration;

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::network::channel::Connector;
use crate::network::channel::Listener;
use crate::network::channel::RawFdChannel;
use crate::network::channel::RawFdListener;
use crate::network::error::ConnectError;
use crate::network::error::TryListenError;

#[cfg(verus_only)]
use vlib::serde::ExDeserialize;
#[cfg(verus_only)]
use vlib::serde::ExSerialize;

use vstd::prelude::*;

verus! {

/// Timeout for receive
const RECV_TIMEOUT_MILLIS: u64 = 2;

/// Detect if IO errors are timeouts
fn is_recv_timeout(e: &std::io::Error) -> bool {
    e.kind() == std::io::ErrorKind::WouldBlock || e.kind() == std::io::ErrorKind::TimedOut
}

/// Tcp Socket that unmarshals receiving types (R) and marshals sending types (S)
pub struct TypedTcpStream<R, S> {
    inner: TcpStream,
    _marker: PhantomData<(R, S)>,
}

impl<R, S> TypedTcpStream<R, S> where for <'de>R: serde::Deserialize<'de>, S: serde::Serialize {
    pub fn new(stream: TcpStream) -> Self {
        stream.set_nonblocking(false).expect("this should never fail");
        stream.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS))).expect(
            "this should never fail",
        );
        // ABD's protocol messages (get/get_timestamp/write requests, quorum replies) are small;
        // without this, Nagle's algorithm (sender-side) interacting with delayed ACKs
        // (receiver-side) can add tens of milliseconds of latency per hop.
        stream.set_nodelay(true).expect("this should never fail");
        TypedTcpStream { inner: stream, _marker: PhantomData }
    }

    fn deserialize(buf: &[u8]) -> Result<R, std::io::Error> {
        let root = flexbuffers::Reader::get_root(buf).map_err(
            |e|
                {
                    #[cfg(not(verus_only))]
                    { std::io::Error::other(format!("failed to deserialize: {e:?}")) }
                    #[cfg(verus_only)]
                    { std::io::Error::from_raw_os_error(-1) }
                },
        )?;
        let value = R::deserialize(root).map_err(
            |e|
                {
                    #[cfg(not(verus_only))]
                    { std::io::Error::other(format!("failed to deserialize: {e:?}")) }
                    #[cfg(verus_only)]
                    { std::io::Error::from_raw_os_error(-1) }
                },
        )?;
        Ok(value)
    }

    /// Fills `buf` completely, retrying through recv-timeouts by resuming from where the
    /// previous attempt left off (tracked in `filled`) rather than restarting `read_exact` from
    /// `buf[0]`
    ///
    /// If `bail_if_empty` is set, returns `Ok(false)` (without having consumed anything) the
    /// first time a timeout occurs with zero bytes of *this* field read so far
    #[verifier::external_body]
    fn read_exact_or_none(stream: &mut &TcpStream, buf: &mut [u8], bail_if_empty: bool) -> Result<
        bool,
        std::io::Error,
    > {
        let mut filled = 0usize;
        while filled < buf.len() {
            match stream.read(&mut buf[filled..]) {
                Ok(0) => {
                    return Err(
                        std::io::Error::new(
                            std::io::ErrorKind::UnexpectedEof,
                            "peer closed connection mid-message",
                        ),
                    );
                },
                Ok(n) => {
                    filled += n;
                },
                Err(e) if is_recv_timeout(&e) && bail_if_empty && filled == 0 => {
                    return Ok(false);
                },
                Err(e) if is_recv_timeout(&e) => {
                    continue;
                },
                Err(e) => {
                    return Err(e);
                },
            }
        }
        Ok(true)
    }

    #[verifier::external_body]
    pub fn try_recv(&self) -> Result<Option<R>, std::io::Error> {
        // TcpStream implements Read, which takes in a mut ref
        // However, &TcpStream also implements Read, so this is how we get around it
        let mut stream = &self.inner;
        let mut len_bytes = [0u8;4];
        if !Self::read_exact_or_none(&mut stream, &mut len_bytes, true)? {
            return Ok(None);
        }
        let len = u32::from_ne_bytes(len_bytes) as usize;

        let mut buf = vec![0u8; len];
        Self::read_exact_or_none(&mut stream, &mut buf, false)?;
        let res = Self::deserialize(&buf)?;
        Ok(Some(res))
    }

    fn serialize(v: &S) -> Result<flexbuffers::FlexbufferSerializer, std::io::Error> {
        let mut s = flexbuffers::FlexbufferSerializer::new();
        v.serialize(&mut s).map_err(
            |e|
                {
                    #[cfg(not(verus_only))]
                    { std::io::Error::other(format!("failed to serialize: {e:?}")) }
                    #[cfg(verus_only)]
                    { std::io::Error::from_raw_os_error(-1) }
                },
        )?;
        Ok(s)
    }

    #[verifier::external_body]
    pub fn send(&self, v: &S) -> Result<(), std::io::Error> {
        let s = Self::serialize(v)?;
        let len = s.view().len() as u32;
        let len_bytes = len.to_ne_bytes();
        // One `write_vectored` call instead of two separate `write_all`s -- on Linux this maps to
        // a single `writev(2)`, so the common (small-message, no-backpressure) case costs one
        // syscall instead of two, with no extra copy to combine the length prefix and payload
        // into one buffer. This changes nothing about atomicity: TCP already gives no atomicity
        // guarantee across *any* split of bytes into separate `send`/`write` calls, whether we
        // choose the split (the old two-call version) or the kernel does (a `writev` can return a
        // partial count torn anywhere, including exactly at this same prefix/payload boundary). A
        // partial-but-successful write (`Ok(n)` short of everything queued) is not a failure --
        // `advance_slices` just resumes from where it left off, same as `write_all` already does
        // internally for a single buffer. Only a hard error partway through is the same
        // "non-atomic write" case the old code already flagged: some bytes are already
        // irrevocably in the kernel's send buffer but not all, and there is no way to un-send
        // them, so this channel must be treated as broken -- same recovery (log + `Err`) as before.
        // See above (try_recv) for &TcpStream impl Read discussion.
        let mut stream = &self.inner;
        let mut bufs_storage = [std::io::IoSlice::new(&len_bytes), std::io::IoSlice::new(s.view())];
        let mut bufs: &mut [std::io::IoSlice] = &mut bufs_storage;
        while !bufs.is_empty() {
            match stream.write_vectored(bufs) {
                Ok(0) => {
                    vlib::veprintln!("warning: non-atomic write of len + payload failed");
                    return Err(
                        std::io::Error::new(
                            std::io::ErrorKind::WriteZero,
                            "failed to write whole buffer",
                        ),
                    );
                },
                Ok(n) => std::io::IoSlice::advance_slices(&mut bufs, n),
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(e) => {
                    vlib::veprintln!("warning: non-atomic write of len + payload failed");
                    return Err(e);
                },
            }
        }
        Ok(())
    }

    pub fn local_addr(&self) -> SocketAddr {
        self.inner.local_addr().expect("local addr should be set")
    }

    pub fn peer_addr(&self) -> SocketAddr {
        self.inner.peer_addr().expect("peer addr should be set")
    }

    /// The underlying stream's raw fd, for `Server::run_epoll` to register with an `mio::Poll`
    /// instance (see `crate::network::channel::RawFdChannel`).
    pub fn raw_fd(&self) -> i32 {
        self.inner.as_raw_fd()
    }
}

#[verifier::external_body]
pub struct TcpListener {
    listener: std::net::TcpListener,
    id: u64,
}

impl TcpListener {
    #[verifier::external_body]
    pub fn listen<A: ToSocketAddrs>(addr: A, id: u64) -> std::io::Result<Self> {
        let listener = std::net::TcpListener::bind(addr)?;
        listener.set_nonblocking(true).expect("this should never fail");
        Ok(TcpListener { listener, id })
    }
}

#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct TcpConnector<A: ToSocketAddrs> {
    listening_addr: A,
    #[allow(dead_code)]
    server_id: u64,
}

impl<A: ToSocketAddrs> TcpConnector<A> {
    #[verifier::external_body]
    pub fn new(listening_addr: A, server_id: u64) -> std::io::Result<Self> {
        Ok(TcpConnector { listening_addr, server_id })
    }
}

/// Channel TO Client
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct ClientChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    stream: TypedTcpStream<R, S>,
    server_id: u64,
    client_id: u64,
}

/// Channel TO Server
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct ServerChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    stream: TypedTcpStream<R, S>,
    server_id: u64,
    client_id: u64,
}

impl<K, R, S> ClientChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        stream: TypedTcpStream<R, S>,
    ) -> Self {
        ClientChannel { pred, stream, server_id, client_id }
    }
}

impl<K, R, S> ServerChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        stream: TypedTcpStream<R, S>,
    ) -> Self {
        ServerChannel { pred, stream, server_id, client_id }
    }
}

pub struct EmptyChanInv;

impl<Id, R, S> ChannelInvariant<EmptyChanInv, Id, R, S> for EmptyChanInv {
    open spec fn recv_inv(k: Self, id: Id, r: R) -> bool {
        true
    }

    open spec fn send_inv(k: Self, id: Id, s: S) -> bool {
        true
    }
}

impl<K, R, S> Channel for ClientChannel<K, R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    type R = R;

    type S = S;

    type Id = (u64, u64);

    type K = K;

    #[verifier::external_body]
    closed spec fn constant(self) -> Self::K {
        self.pred@
    }

    #[verifier::external_body]
    fn try_recv(&self) -> Result<R, crate::network::error::TryRecvError> {
        match self.stream.try_recv() {
            Ok(Some(x)) => Ok(x),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        self.stream.send(v).map_err(|e| e.into())
    }

    #[verifier::external_body]
    fn id(&self) -> Self::Id {
        (self.server_id, self.client_id)
    }

    #[verifier::external_body]
    closed spec fn spec_id(self) -> Self::Id {
        (self.server_id, self.client_id)
    }
}

// `ClientChannel` is itself `#[verifier::external_body]` (see its definition above), which makes
// every one of its fields opaque to Verus even from its own impl blocks -- exactly like `id()`
// above, this is a mechanical consequence of that pre-existing annotation on the struct, not new
// hidden logic: `raw_fd` is a trivial one-line field delegation, same shape/risk as `id()`.
impl<K, R, S> RawFdChannel for ClientChannel<K, R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    fn raw_fd(&self) -> i32 {
        self.stream.raw_fd()
    }
}

impl<K, R, S> Channel for ServerChannel<K, R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    type R = R;

    type S = S;

    type Id = (u64, u64);

    type K = K;

    #[verifier::external_body]
    closed spec fn constant(self) -> Self::K {
        self.pred@
    }

    #[verifier::external_body]
    fn try_recv(&self) -> Result<R, crate::network::error::TryRecvError> {
        match self.stream.try_recv() {
            Ok(Some(x)) => Ok(x),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        self.stream.send(v).map_err(|e| e.into())
    }

    #[verifier::external_body]
    fn id(&self) -> Self::Id {
        (self.client_id, self.server_id)
    }

    #[verifier::external_body]
    closed spec fn spec_id(self) -> Self::Id {
        (self.client_id, self.server_id)
    }
}

// NOTE: `try_accept` does not itself construct the channel invariant/ghost map -- that already
// exists by this point. The `Service` establishes it once up front from its own state/resources
// (e.g. `abd`'s `ChannelInv::from_state_pred(..)` in `abd/src/server/mod.rs::create_server`,
// which folds in the per-server ghost-location map) and hands it to `Server::new`, which passes
// it down as the `gen_pred` closure threaded through every `try_accept` call (see
// `Listener::try_accept`'s `gen_pred: Ghost<spec_fn(&Self) -> C::K>` in
// `verdist/src/network/channel.rs`, and `Server::poll_accept`'s call site in
// `verdist/src/service/mod.rs`). All `try_accept` does here is capture that already-built
// invariant into the new channel's `pred` field (`Ghost(gen_pred@(self))`) so `constant()` can
// return it later.
//
// `#[verifier::external_body]` on this fn is an intentional, permanent trust boundary: the real
// work here is a blocking accept + client-id handshake over a raw socket, which Verus cannot
// reason about. The postcondition `r.constant() == gen_pred(self)` (declared on the `Listener`
// trait) is therefore assumed rather than checked, but it holds by construction since the body
// does nothing to `pred` other than store the given ghost value verbatim. This pattern is
// identical across all three network impls (tcp, udp, modelled), so none of them is more/less
// complete than the others here.
impl<K, R, S> Listener<ClientChannel<K, R, S>> for TcpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.id
    }

    type Raw = (TcpStream, u64);

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn try_accept_raw(&self) -> Result<(u64, Self::Raw), TryListenError> {
        let (mut stream, addr) = match self.listener.accept() {
            Ok(res) => res,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                return Err(TryListenError::Empty);
            },
            Err(e) => {
                return Err(e.into());
            },
        };

        let mut client_id_buf = [0u8;8];
        stream.set_nonblocking(false).expect("this should never fail");
        stream.read_exact(&mut client_id_buf)?;
        stream.write_all(&self.id.to_ne_bytes())?;
        let client_id = u64::from_ne_bytes(client_id_buf);
        stream.set_nonblocking(true).expect("this should never fail");

        Ok((client_id, (stream, client_id)))
    }

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn wrap_raw(&self, raw: Self::Raw, gen_pred: Ghost<spec_fn(&Self) -> K>) -> (r: Result<
        ClientChannel<K, R, S>,
        TryListenError,
    >) {
        let (stream, client_id) = raw;
        let pred = Ghost(gen_pred@(self));
        let tstream = TypedTcpStream::new(stream);
        let chan = ClientChannel::new(pred, self.id, client_id, tstream);

        vlib::veprintln!("[server|{:>3}]: accepted connection from client {client_id} (channel_id: {:?})", self.id, chan.id());

        Ok(chan)
    }
}

// Same mechanical note as `ClientChannel`'s `RawFdChannel` impl above: `TcpListener` is itself
// `#[verifier::external_body]`, so this trivial field delegation needs the annotation too.
impl<K, R, S> RawFdListener<ClientChannel<K, R, S>> for TcpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    fn raw_fd(&self) -> i32 {
        self.listener.as_raw_fd()
    }
}

impl<K, R, S, A> Connector<ServerChannel<K, R, S>> for TcpConnector<A> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
    A: ToSocketAddrs + Clone,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.server_id
    }

    #[verifier::external_body]
    fn connect<F>(&self, local_id: u64, gen_pred: F) -> (r: Result<
        ServerChannel<K, R, S>,
        ConnectError,
    >) where F: FnOnce(&Self, u64) -> Ghost<K> {
        vlib::veprintln!(
            "[client|{:>3}]: connecting to server", local_id,
        );
        let mut stream = TcpStream::connect(self.listening_addr.clone())?;
        stream.set_nonblocking(false).expect("this should never fail");
        stream.write_all(&local_id.to_ne_bytes())?;
        let mut server_id_buf = [0u8;8];
        stream.read_exact(&mut server_id_buf)?;
        let server_id = u64::from_ne_bytes(server_id_buf);
        stream.set_nonblocking(true).expect("this should never fail");

        let tstream = TypedTcpStream::new(stream);
        let pred = gen_pred(self, local_id);

        let peer_addr = tstream.peer_addr();
        let chan = ServerChannel::new(pred, server_id, local_id, tstream);
        vlib::veprintln!(
            "[client|{:>3}]: connected to server {server_id} (channel_id: {:?}, server addr: {:?})", local_id, chan.id(),
            peer_addr
        );
        Ok(chan)
    }
}

} // verus!
