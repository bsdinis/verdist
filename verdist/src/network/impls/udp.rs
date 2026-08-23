use std::marker::PhantomData;
use std::net::IpAddr;
use std::net::SocketAddr;
use std::net::ToSocketAddrs;
use std::net::UdpSocket;
use std::time::Duration;

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::network::channel::Connector;
use crate::network::channel::Listener;
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

/// Udp Socket that unmarshals receiving types (R) and marshals sending types (S)
pub struct TypedUdpSocket<R, S> {
    inner: UdpSocket,
    _marker: PhantomData<(R, S)>,
}

impl<R, S> TypedUdpSocket<R, S> where for <'de>R: serde::Deserialize<'de>, S: serde::Serialize {
    pub fn new(socket: UdpSocket) -> Self {
        socket.set_nonblocking(false).expect("this should never fail");
        socket.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS))).expect(
            "this should never fail",
        );
        TypedUdpSocket { inner: socket, _marker: PhantomData }
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

    #[verifier::external_body]
    pub fn try_recv(&self) -> Result<Option<R>, std::io::Error> {
        let mut buf = [0;BUF_SIZE];
        let res = self.inner.recv(&mut buf);
        let r = match res {
            Ok(r) => r,
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
        let res = Self::deserialize(&buf[..r])?;
        Ok(Some(res))
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

    pub fn local_addr(&self) -> SocketAddr {
        self.inner.local_addr().expect("local addr should be set")
    }

    pub fn peer_addr(&self) -> SocketAddr {
        self.inner.peer_addr().expect("peer addr should be set")
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

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn try_accept(&self, gen_pred: Ghost<spec_fn(&Self) -> K>) -> (r: Result<
        ClientChannel<K, R, S>,
        TryListenError,
    >) {
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

        let pred = Ghost(gen_pred@(self));
        socket.connect(connect_addr)?;
        let tsocket = TypedUdpSocket::new(socket);

        let chan = ClientChannel::new(pred, self.id, client_id, tsocket);

        vlib::veprintln!("[server|{:>3}]: accepted connection from client {client_id} (channel_id: {:?})", self.id, chan.id());

        Ok(chan)
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
