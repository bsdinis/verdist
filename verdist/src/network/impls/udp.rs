use std::marker::PhantomData;
use std::net::IpAddr;
use std::net::SocketAddr;
use std::net::ToSocketAddrs;
use std::net::UdpSocket;
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

// NOTE(fix_udp): resolved.
//
// This TODO originally asked for a "batteries included" `Server` driven by a `Service` trait
// (`fn handle(conn_id, request) -> response`, with pre/post conditions to be figured out) so
// that server code wouldn't need to know its listener's concrete type or drive explicit
// listen/poll steps.
//
// That abstraction now exists: `verdist::service::{Service, MutService, Server}`
// (`verdist/src/service/mod.rs`). `Service`/`MutService` provide exactly the sketched
// `handle` method, plus `pre`/`post` spec fns and `recv_implies_pre`/`post_implies_send` proof
// obligations tying them to the channel's `ChannelInvariant::recv_inv`/`send_inv` -- that's how
// the open "pre/post conditions" question above got resolved. `Server::run()` spawns its own
// accept + per-shard poll threads, so callers no longer drive an explicit poll loop.
//
// `UdpListener`/`ClientChannel`/`ServerChannel` below already implement the generic
// `Listener`/`Channel` traits `Server` is parameterized over, and `abd-example`/`echo-example`
// already construct a `UdpListener` and hand it straight to `Server` (via
// `abd_example::server::run_server` / `echo_example::server::run_server`, which call
// `Server::new(..).run()`) -- see `abd-example/src/server.rs` and `abd/src/server/mod.rs`.
// The one remaining explicit step is `UdpListener::listen(addr, id)` at the call site, which is
// inherent to picking a concrete network binding (parsing/binding a UDP-specific address) and is
// mirrored by TCP/modelled; it is not the "server doesn't know its listener type" problem this
// TODO was about.

#[cfg(verus_only)]
use vlib::serde::ExDeserialize;
#[cfg(verus_only)]
use vlib::serde::ExSerialize;

use vstd::prelude::*;

verus! {

/// How long a `recv`/`recv_from` call is allowed to block before giving up and reporting "no
/// data yet" (`WouldBlock`/`TimedOut`), same as the old non-blocking + spin design would report
/// immediately. Mirrors `network::impls::tcp::RECV_TIMEOUT_MILLIS`.
const RECV_TIMEOUT_MILLIS: u64 = 2;

/// Read timeouts surface as `WouldBlock` on some platforms and `TimedOut` on others; both mean
/// "no data within `RECV_TIMEOUT`", same as the non-blocking design's `WouldBlock`.
fn is_recv_timeout(e: &std::io::Error) -> bool {
    e.kind() == std::io::ErrorKind::WouldBlock || e.kind() == std::io::ErrorKind::TimedOut
}

const BUF_SIZE: usize = 1 << 12;

/// How many datagrams one `recvmmsg` call asks the kernel for at once (see `try_recv`'s doc
/// comment). Generous relative to any burst this workload produces; `recvmmsg` never blocks
/// waiting to fill this many -- it returns as soon as no more are *immediately* available, so an
/// idle/single-message socket costs exactly the same one syscall as the old `recv`-based version.
const RECV_BATCH: usize = 32;

/// Buffers datagrams already pulled off the socket by `recvmmsg` but not yet handed to the
/// caller, plus the (reused, allocated once) raw scratch buffers `recvmmsg` writes into.
struct RecvBatch<R> {
    pending: std::collections::VecDeque<R>,
    bufs: Vec<[u8; BUF_SIZE]>,
}

impl<R> RecvBatch<R> {
    fn new() -> Self {
        RecvBatch {
            pending: std::collections::VecDeque::new(),
            bufs: vec![[0u8; BUF_SIZE]; RECV_BATCH],
        }
    }
}

/// Udp Socket that unmarshals receiving types (R) and marshals sending types (S)
// `#[verifier::external_body]`: needed once `recv_batch` (a `std::cell::UnsafeCell`, which Verus
// has no spec surface for) became a field -- same reasoning as `ClientChannel`/`ServerChannel`
// just below in this file. This makes every field opaque to Verus even from this type's own impl
// block, so every method touching a field directly (`new`, `refill`, `local_addr`, `peer_addr`,
// `raw_fd`, in addition to the already-external_body `try_recv`/`send`/`send_to`) needs the
// annotation too -- mechanical, not new hidden logic.
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct TypedUdpSocket<R, S> {
    inner: UdpSocket,
    // See `try_recv`'s doc comment. `UnsafeCell`, not a lock, for the same reason as
    // `network::impls::tcp::TypedTcpStream::read_ahead`: exclusivity here is a documented caller
    // invariant (only the single thread that owns this channel's connection ever calls
    // `send`/`try_recv` on it), not something the type system enforces -- `Channel::send`/
    // `try_recv` already take `&self`, not `&mut self`, so nothing before this prevented a caller
    // from racing two calls on one instance either.
    recv_batch: std::cell::UnsafeCell<RecvBatch<R>>,
    _marker: PhantomData<(R, S)>,
}

impl<R, S> TypedUdpSocket<R, S> where for <'de>R: serde::Deserialize<'de>, S: serde::Serialize {
    #[verifier::external_body]
    pub fn new(socket: UdpSocket) -> Self {
        socket.set_nonblocking(false).expect("this should never fail");
        socket.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS))).expect(
            "this should never fail",
        );
        TypedUdpSocket {
            inner: socket,
            recv_batch: std::cell::UnsafeCell::new(RecvBatch::new()),
            _marker: PhantomData,
        }
    }

    /// Pulls up to `RECV_BATCH` already-queued datagrams off this (`connect`ed, single-peer)
    /// socket into `recv_batch`'s reused buffers via one `recvmmsg` call, deserializing each into
    /// `recv_batch.pending`. Returns how many were received (0 if none were, matching `try_recv`'s
    /// old `Ok(None)` case).
    ///
    /// Two calls, not one -- found by direct measurement, not assumed: a *blocking* `recvmmsg`
    /// (relying on the socket's own `SO_RCVTIMEO`, `timeout: null`) does **not** return as soon as
    /// one datagram is available the way `recv` does -- it waits for the full timeout regardless
    /// (confirmed directly: a pre-queued datagram still took ~2.7ms to come back, matching the
    /// nothing-queued case almost exactly). So batching only works as a *non-blocking* check
    /// (`MSG_DONTWAIT`, confirmed elsewhere to return in single-digit microseconds whether 0, 1 or
    /// several datagrams are queued): try that first, and only if it finds nothing at all fall
    /// back to the exact original single-`recv` call (same `SO_RCVTIMEO`-based wait as before this
    /// change), so idle-socket pacing/liveness is unchanged from the old code.
    #[verifier::external_body]
    fn refill(&self) -> Result<usize, std::io::Error> {
        let mut iovecs: [libc::iovec; RECV_BATCH] = unsafe { std::mem::zeroed() };
        let mut msgs: [libc::mmsghdr; RECV_BATCH] = unsafe { std::mem::zeroed() };
        {
            // SAFETY: single-owner-thread invariant, see `recv_batch`'s field doc. This borrow
            // ends before any further `recv_batch` access (the `deserialize`/`push_back` loop
            // below re-borrows fresh), so it never overlaps with another live `&mut` into the
            // same cell.
            let rb = unsafe { &mut *self.recv_batch.get() };
            for i in 0..RECV_BATCH {
                iovecs[i] = libc::iovec {
                    iov_base: rb.bufs[i].as_mut_ptr() as *mut libc::c_void,
                    iov_len: BUF_SIZE,
                };
                msgs[i].msg_hdr.msg_iov = &mut iovecs[i] as *mut libc::iovec;
                msgs[i].msg_hdr.msg_iovlen = 1;
            }
        }
        let fd = self.inner.as_raw_fd();
        let n = unsafe {
            libc::recvmmsg(
                fd,
                msgs.as_mut_ptr(),
                RECV_BATCH as u32,
                libc::MSG_DONTWAIT,
                std::ptr::null_mut(),
            )
        };
        if n < 0 {
            let e = std::io::Error::last_os_error();
            if !is_recv_timeout(&e) {
                return Err(e);
            }
            // Nothing was immediately queued -- fall back to the original single blocking `recv`
            // (still governed by `SO_RCVTIMEO`) so a genuinely idle connection waits/paces exactly
            // as it did before this change, rather than busy-spinning on repeated `MSG_DONTWAIT`
            // misses.

            let mut buf = [0u8;BUF_SIZE];
            return match self.inner.recv(&mut buf) {
                Ok(r) => {
                    if r == BUF_SIZE {
                        vlib::veprintln!("[udp:{:?}]: warning: receiving {:x} bytes from {:?} may have exhausted the buffer, message may have been truncated",
                            self.local_addr(), BUF_SIZE, self.peer_addr());
                    }
                    let v = Self::deserialize(&buf[..r])?;
                    let rb = unsafe { &mut *self.recv_batch.get() };
                    rb.pending.push_back(v);
                    Ok(1)
                },
                Err(e) if is_recv_timeout(&e) => Ok(0),
                Err(e) => Err(e),
            };
        }
        let n = n as usize;
        let rb = unsafe { &mut *self.recv_batch.get() };
        for (i, msg) in msgs.iter().enumerate().take(n) {
            let len = msg.msg_len as usize;
            if len == BUF_SIZE {
                vlib::veprintln!("[udp:{:?}]: warning: receiving {:x} bytes from {:?} may have exhausted the buffer, message may have been truncated",
                    self.local_addr(), BUF_SIZE, self.peer_addr());
            }
            let v = Self::deserialize(&rb.bufs[i][..len])?;
            rb.pending.push_back(v);
        }
        Ok(n)
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

    /// Reads one message, serving it straight out of `recv_batch.pending` (zero syscalls) if a
    /// previous `refill` already queued it -- common under any pipelining/backlog, since a burst
    /// of datagrams already sitting in this (`connect`ed) socket's receive buffer all come back
    /// in one `recvmmsg` call the first time any of them is asked for. Otherwise calls `refill`
    /// once and serves from whatever it just fetched. Same `Ok(None)`-on-timeout contract as the
    /// old single-`recv` version.
    #[verifier::external_body]
    pub fn try_recv(&self) -> Result<Option<R>, std::io::Error> {
        // SAFETY: single-owner-thread invariant, see `recv_batch`'s field doc. Not held across
        // the `self.refill()` call below, so it never overlaps with `refill`'s own borrow.
        if let Some(v) = unsafe { &mut *self.recv_batch.get() }.pending.pop_front() {
            return Ok(Some(v));
        }
        self.refill()?;
        // SAFETY: same as above -- a fresh, independent borrow.
        Ok(unsafe { &mut *self.recv_batch.get() }.pending.pop_front())
    }

    #[verifier::external_body]
    pub fn try_recv_from(&self) -> Result<Option<(R, SocketAddr)>, std::io::Error> {
        let mut buf = [0;BUF_SIZE];
        let (r, addr) = match self.inner.recv_from(&mut buf) {
            Ok(x) => x,
            Err(e) if is_recv_timeout(&e) => {
                return Ok(None);
            },
            Err(e) => {
                return Err(e);
            },
        };
        if r == BUF_SIZE {
            vlib::veprintln!("[udp:{:?}]: warning: receiving {:x} bytes from {:?} may have exhausted the buffer, message may have been truncated",
                self.local_addr(), BUF_SIZE, self.peer_addr());
        }
        let v = Self::deserialize(&buf[..r])?;
        Ok(Some((v, addr)))
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
        let sent_len = self.inner.send(s.view())?;
        if sent_len != s.view().len() {
            vlib::veprintln!("warning: partial write (only 0x{:x}B / 0x{:x}B sent). partial writes should be impossible for sizes <= 0x{:x}",
            sent_len, s.view().len(), i32::MAX);
        }
        Ok(())
    }

    #[verifier::external_body]
    pub fn send_to<A: ToSocketAddrs>(&self, v: &S, addr: A) -> Result<(), std::io::Error> {
        let s = Self::serialize(v)?;
        let sent_len = self.inner.send_to(s.view(), addr)?;
        if sent_len != s.view().len() {
            vlib::veprintln!("warning: partial write (only 0x{:x}B / 0x{:x}B sent). partial writes should be impossible for sizes <= 0x{:x}",
            sent_len, s.view().len(), i32::MAX);
        }
        Ok(())
    }

    #[verifier::external_body]
    pub fn local_addr(&self) -> SocketAddr {
        self.inner.local_addr().expect("local addr should be set")
    }

    #[verifier::external_body]
    pub fn peer_addr(&self) -> SocketAddr {
        self.inner.peer_addr().expect("peer addr should be set")
    }

    /// The underlying socket's raw fd, for `Server::run_epoll` to register with an `mio::Poll`
    /// instance (see `crate::network::channel::RawFdChannel`).
    #[verifier::external_body]
    pub fn raw_fd(&self) -> i32 {
        self.inner.as_raw_fd()
    }
}

#[verifier::external_body]
pub struct UdpListener {
    listening_socket: TypedUdpSocket<(u64, SocketAddr), (u64, SocketAddr)>,
    id: u64,
}

impl UdpListener {
    #[verifier::external_body]
    pub fn listen<A: ToSocketAddrs>(addr: A, id: u64) -> std::io::Result<Self> {
        let listening_socket = TypedUdpSocket::new(UdpSocket::bind(addr)?);
        Ok(UdpListener { listening_socket, id })
    }
}

#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct UdpConnector<A: ToSocketAddrs> {
    listening_addr: A,
    local_ip: IpAddr,
    #[allow(dead_code)]
    server_id: u64,
}

impl<A: ToSocketAddrs> UdpConnector<A> {
    #[verifier::external_body]
    pub fn new(listening_addr: A, local_ip: IpAddr, server_id: u64) -> std::io::Result<Self> {
        Ok(UdpConnector { listening_addr, local_ip, server_id })
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
    socket: TypedUdpSocket<R, S>,
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
    socket: TypedUdpSocket<R, S>,
    server_id: u64,
    client_id: u64,
}

impl<K, R, S> ClientChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        socket: TypedUdpSocket<R, S>,
    ) -> Self {
        ClientChannel { pred, socket, server_id, client_id }
    }
}

impl<K, R, S> ServerChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        socket: TypedUdpSocket<R, S>,
    ) -> Self {
        ServerChannel { pred, socket, server_id, client_id }
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
        match self.socket.try_recv() {
            Ok(Some(x)) => Ok(x),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        self.socket.send(v).map_err(|e| e.into())
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
        self.socket.raw_fd()
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
        match self.socket.try_recv() {
            Ok(Some(x)) => Ok(x),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        self.socket.send(v).map_err(|e| e.into())
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
// work here is a blocking recv-from + rendezvous handshake (binding a fresh socket, exchanging
// addresses/ids) over UDP, which Verus cannot reason about. The postcondition
// `r.constant() == gen_pred(self)` (declared on the `Listener` trait) is therefore assumed
// rather than checked, but it holds by construction since the body does nothing to `pred` other
// than store the given ghost value verbatim. This pattern is identical across all three network
// impls (tcp, udp, modelled), so none of them is more/less complete than the others here.
impl<K, R, S> Listener<ClientChannel<K, R, S>> for UdpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.id
    }

    type Raw = (UdpSocket, u64);

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn try_accept_raw(&self) -> Result<(u64, Self::Raw), TryListenError> {
        let ((client_id, connect_addr), addr) = match self.listening_socket.try_recv_from() {
            Ok(Some(x)) => { x },
            Ok(None) => {
                return Err(TryListenError::Empty);
            },
            Err(e) => {
                return Err(e.into());
            },
        };

        let local_ip = self.listening_socket.local_addr().ip();
        let socket = UdpSocket::bind((local_ip, 0))?;

        vlib::veprintln!(
            "[server|{:>3}]: accepting a connection from client {} id={client_id}, local addr is {:?}", self.id, &addr, socket.local_addr().unwrap()
        );

        self.listening_socket.send_to(&(self.id, socket.local_addr().unwrap()), addr)?;

        socket.connect(connect_addr)?;

        Ok((client_id, (socket, client_id)))
    }

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn wrap_raw(&self, raw: Self::Raw, gen_pred: Ghost<spec_fn(&Self) -> K>) -> (r: Result<
        ClientChannel<K, R, S>,
        TryListenError,
    >) {
        let (socket, client_id) = raw;
        let pred = Ghost(gen_pred@(self));
        let tsocket = TypedUdpSocket::new(socket);

        let chan = ClientChannel::new(pred, self.id, client_id, tsocket);

        vlib::veprintln!("[server|{:>3}]: accepted connection from client {client_id} (channel_id: {:?})", self.id, chan.id());

        Ok(chan)
    }
}

// Same mechanical note as `ClientChannel`'s `RawFdChannel` impl above: `UdpListener` is itself
// `#[verifier::external_body]`, so this trivial field delegation needs the annotation too.
impl<K, R, S> RawFdListener<ClientChannel<K, R, S>> for UdpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    fn raw_fd(&self) -> i32 {
        self.listening_socket.raw_fd()
    }
}

impl<K, R, S, A> Connector<ServerChannel<K, R, S>> for UdpConnector<A> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
    A: ToSocketAddrs,
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
        let addr = SocketAddr::new(self.local_ip, 0);
        let connect_socket = UdpSocket::bind(addr)?;
        let channel_socket = UdpSocket::bind(addr)?;
        connect_socket.connect(&self.listening_addr)?;
        let connect_tsocket = TypedUdpSocket::<(u64, SocketAddr), (u64, SocketAddr)>::new(
            connect_socket,
        );

        connect_tsocket.send(&(local_id, channel_socket.local_addr().unwrap()))?;
        loop {
            if let Ok(Some((server_id, addr))) = connect_tsocket.try_recv() {
                channel_socket.connect(addr)?;
                let tsocket = TypedUdpSocket::new(channel_socket);
                let pred = gen_pred(self, local_id);

                let chan = ServerChannel::new(pred, server_id, local_id, tsocket);
                vlib::veprintln!(
                        "[client|{:>3}]: connected to server {server_id} (channel_id: {:?}, server addr: {addr:?})", local_id, chan.id()
                    );
                return Ok(chan);
            }
        }
    }
}

} // verus!
// Unlike `TypedTcpStream` (see tcp.rs), `TypedUdpSocket` genuinely needs `Sync`: UDP is
// connectionless, so `UdpListener` embeds a `TypedUdpSocket` directly as its listening socket
// (see `UdpListener::listening_socket`), and `Server::poll_shard`/`poll_shard_epoll` call
// `self.listener.wrap_raw`/`spec_id` from every shard's worker thread concurrently -- real,
// structural shared access, not the vestigial bound removed from `Channel`'s `C` (see
// `Server::_marker`'s `ChannelTypeMarker` doc). Per-connection `TypedUdpSocket`s (inside
// `ClientChannel`/`ServerChannel`) never actually need this -- they're single-owner exactly like
// TCP's -- but it's one nominal type serving both roles, so the stronger bound applies to all of
// it. Splitting the listener-socket role from the per-connection-channel role into two distinct
// types would let the latter drop this, but that's a separate, larger change than the Sync-bound
// cleanup this belongs to.
// SAFETY: see `TypedUdpSocket::recv_batch`'s field doc -- exclusivity for the per-connection role
// is the caller's responsibility, not proven by this type (`verus!` disallows `unsafe impl`
// inside its own block, hence this living out here, same as `vlib::reclaim::Slot`'s identical
// pattern). `R: Send` is required because (unlike TCP's phantom-only `R`/`S`) `RecvBatch<R>`
// genuinely stores `R` values that may be handed to a different thread across later calls.
unsafe impl<R: Send, S> Sync for TypedUdpSocket<R, S> {}
