//! A UDP backend that treats UDP as truly connectionless: no rendezvous handshake, no
//! per-connection socket. See `udp.rs` for the handshake-based backend this sits alongside
//! (additive, not a replacement -- both remain selectable at the CLI).
//!
//! Design (see the planning session that produced this file for the full investigation):
//!
//! - The server binds `num_router_threads` UDP sockets to the same address (`num_router_threads
//!   == 1` needs no special socket option; `> 1` sets `SO_REUSEPORT` before `bind()` via the
//!   `socket2` crate, so the kernel fans inbound datagrams out across the sockets by a
//!   deterministic hash of the packet's 4-tuple -- the same client's traffic always lands on the
//!   same socket for as long as the reuseport group's membership stays fixed, which this code
//!   guarantees by binding every socket once up front and never adding/removing one afterward).
//! - Each socket gets its own dedicated background "router" thread that owns, exclusively: that
//!   socket, and a private `HashMap<SocketAddr, Sender<R>>` demux table -- never touched by any
//!   other thread, so no lock of any kind is needed (same soundness argument this crate's
//!   `thread_local!` `SEND_BUF` pattern already relies on: sound because exactly one thread ever
//!   touches this state, not because of any synchronization primitive).
//! - A datagram from a KNOWN peer is forwarded straight into that peer's private inbox (a
//!   `crossbeam_channel`) -- no new connection reported.
//! - A datagram from an UNKNOWN peer *is* the implicit accept: the router thread creates a new
//!   inbox right there, forwards the first datagram's payload into it so nothing already-received
//!   is lost, and reports the new (client_id, raw material) tuple on a single, shared
//!   `crossbeam_channel` that every router thread feeds and that `MuxedListener::try_accept_raw`
//!   (called by `verdist::service::Server`'s one dedicated accept thread, same as every other
//!   backend) simply drains from. This is what lets `Server`/the `Listener` trait stay completely
//!   unchanged: from `Server`'s point of view this looks exactly like any other listener that
//!   sometimes has a new connection ready and sometimes doesn't, regardless of how many real
//!   sockets or router threads are working underneath.
//! - Client -> server traffic is wrapped in a small `MuxedEnvelope { client_id, body }` so the
//!   server can learn the peer's declared client id from its very first datagram (needed because
//!   nothing else identifies a fresh peer). Server -> client traffic needs no envelope: the server
//!   already knows which peer to `send_to` (it's a property of which channel is doing the
//!   sending), so responses go out as plain `S`.
//! - `Connector::connect` is close to a true no-op on the wire: `UdpSocket::connect()` for a UDP
//!   socket is a purely local kernel call (it just records a default peer address for `send`/
//!   `recv`), so establishing a client's channel sends *nothing* -- the client's very first real
//!   request is also the first datagram the server ever sees from it.
//!
//! Known, deliberate limitations (see the planning session for why these are follow-ups rather
//! than blockers):
//! - No `RawFdChannel`/`RawFdListener` impl, so `--epoll`/`Server::run_epoll` is not available for
//!   this backend yet -- only `Server::run`'s busy-backoff driver works. A muxed channel has no
//!   private fd (the fd belongs to its router thread's shared socket), so naively implementing
//!   `raw_fd()` to return that shared fd would make `mio` register the same fd from every shard,
//!   defeating `scan_ready`'s whole point (it would then treat *every* channel as ready whenever
//!   the shared socket has anything ready). Resolving this needs shard threads to wait on their
//!   per-channel `crossbeam_channel::Receiver` instead of per-fd epoll readiness -- flagged as a
//!   follow-up, not attempted here.
//! - No idle-peer eviction: a shared, unconnected socket cannot surface an async "peer
//!   unreachable" signal the way a connected per-client socket could (see `udp.rs`'s
//!   `ClientChannel`, whose dedicated socket can at least in principle observe that), so a peer
//!   that vanishes leaves its demux-table entry and its shard's `connected` entry alive forever.
//!   This is a real behavior change from the handshake-based backend, not merely an implementation
//!   detail -- flagged for a follow-up eviction-policy decision, not silently addressed here.

use std::collections::HashMap;
use std::marker::PhantomData;
use std::net::IpAddr;
use std::net::SocketAddr;
use std::net::ToSocketAddrs;
use std::net::UdpSocket;
use std::sync::Arc;
use std::time::Duration;

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::network::channel::Connector;
use crate::network::channel::Listener;
use crate::network::error::ConnectError;
use crate::network::error::TryListenError;

#[cfg(verus_only)]
use vlib::serde::ExDeserialize;
#[cfg(verus_only)]
use vlib::serde::ExSerialize;

use vstd::prelude::*;

thread_local! {
    // Same reuse discipline and soundness argument as `udp.rs`'s `SEND_BUF`: each `send`/`send_to`
    // call is made from the one thread that owns the channel doing the sending (worker threads
    // never share a `C`, per `verdist::service::Server`'s ownership-transfer design), so reusing a
    // thread-local scratch buffer across calls is sound without any lock.
    static SEND_BUF: std::cell::RefCell<Vec<u8>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Wire envelope for client -> server traffic only -- see this module's top doc for why only this
/// direction needs one. Plain data, carries no ghost/proof content, so this is deliberately kept
/// *outside* the `verus! {}` block below (unlike almost everything else in this file): a
/// `#[derive(serde::Serialize, serde::Deserialize)]` on a type generic over `R` crashes Verus's
/// erasure pass with an internal-error panic ("VerusErasureCtxt has not been initialized") when
/// declared inside `verus! {}` -- consistent with why this codebase's other wire-format structs
/// (e.g. `abd/src/proto/get.rs`'s `GetRequest`/`GetResponse`) hand-roll their `Serialize`/
/// `Deserialize` impls instead of deriving them. Since `MuxedEnvelope` is only ever touched from
/// inside functions that are already `#[verifier::external_body]` (this module's (de)serialize
/// helpers), Verus never needing to see it at all is strictly simpler than either hand-rolling the
/// impls or fighting the derive-macro crash, and changes nothing about what's trusted vs. checked.
#[derive(serde::Serialize, serde::Deserialize)]
struct MuxedEnvelope<R> {
    client_id: u64,
    body: R,
}

/// Kept outside `verus! {}` alongside `MuxedEnvelope` itself, for the same reason: a signature
/// merely *mentioning* `MuxedEnvelope<R>` (return type here) is rejected inside the macro even
/// though the function's body would be fully trusted (`#[verifier::external_body]`) regardless --
/// Verus checks a function's signature independently of whether its body is trusted. Called only
/// from `router_thread_body`, which is itself `#[verifier::external_body]` and declared inside
/// `verus! {}` alongside every other real backend's accept-path logic in this crate.
fn deserialize_envelope<R>(buf: &[u8]) -> Result<MuxedEnvelope<R>, std::io::Error> where
    for <'de>R: serde::Deserialize<'de>,
 {
    postcard::from_bytes::<MuxedEnvelope<R>>(buf).map_err(
        |e| std::io::Error::other(format!("failed to deserialize envelope: {e:?}")),
    )
}

verus! {

/// Same real ceiling as `udp.rs::BUF_SIZE` -- see that constant's doc for why this is not a
/// tunable choice.
const BUF_SIZE: usize = 65_507;

/// Same rationale as `udp.rs::RECV_TIMEOUT_MILLIS`: a bounded blocking recv so a router thread (or
/// a client's blocking `recv`) can be polled cooperatively rather than either spinning at 100% or
/// blocking forever with no way to notice anything else.
const RECV_TIMEOUT_MILLIS: u64 = 2;

fn is_recv_timeout(e: &std::io::Error) -> bool {
    e.kind() == std::io::ErrorKind::WouldBlock || e.kind() == std::io::ErrorKind::TimedOut
}

#[verifier::external_body]
fn deserialize_plain<T>(buf: &[u8]) -> Result<T, std::io::Error> where for <'de>T: serde::Deserialize<'de> {
    postcard::from_bytes::<T>(buf).map_err(
        |e|
            {
                #[cfg(not(verus_only))]
                { std::io::Error::other(format!("failed to deserialize: {e:?}")) }
                #[cfg(verus_only)]
                { std::io::Error::from_raw_os_error(-1) }
            },
    )
}

/// Serializes `v` into the thread-local scratch buffer and returns the encoded byte range,
/// mirroring `udp.rs::TypedUdpSocket::send`'s reuse discipline exactly (see `SEND_BUF`'s doc).
#[verifier::external_body]
fn serialize_with<T: serde::Serialize, F: FnOnce(&[u8]) -> std::io::Result<()>>(
    v: &T,
    send: F,
) -> std::io::Result<()> {
    SEND_BUF.with(|cell| {
        let mut buf = cell.borrow_mut();
        let mut taken = std::mem::take(&mut *buf);
        taken.clear();
        let taken = postcard::to_extend(v, taken).map_err(
            |e|
                {
                    #[cfg(not(verus_only))]
                    { std::io::Error::other(format!("failed to serialize: {e:?}")) }
                    #[cfg(verus_only)]
                    { std::io::Error::from_raw_os_error(-1) }
                },
        )?;
        *buf = taken;
        let r = send(buf.as_slice());
        r
    })
}

/// Raw material handed from a router thread to `MuxedListener::wrap_raw` (via the accept thread
/// that calls `try_accept_raw`) -- carries no ghost/invariant-relevant content (see
/// `Listener::Raw`'s doc on the trait), only what's needed to build a working channel: the peer's
/// declared id, its already-demultiplexed private inbox, the shared socket its traffic arrived on
/// (also used to `send_to` it), and its address.
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct MuxedRaw<R> {
    client_id: u64,
    inbox: crossbeam_channel::Receiver<R>,
    socket: Arc<UdpSocket>,
    peer_addr: SocketAddr,
}

/// A UDP listener with no rendezvous handshake -- see this module's top doc. Owns nothing directly
/// except the aggregator `Receiver` every router thread's newly-accepted connections are reported
/// on; the router threads themselves (and the sockets/demux tables they own) are detached
/// background threads spawned by `listen`/`listen_reuseport`, never reachable through `&self`.
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct MuxedListener<R, S> {
    id: u64,
    new_conns: crossbeam_channel::Receiver<(u64, MuxedRaw<R>)>,
    _marker: PhantomData<S>,
}

/// Body of one router thread: owns exactly one socket and one private (non-shared, unlocked) demux
/// table for its whole lifetime. Spawned once per socket by `MuxedListener::listen`/
/// `listen_reuseport`; never joined (mirrors every other long-running thread in this codebase --
/// `verdist::service::Server::run`'s accept/worker threads are likewise never joined, this process
/// is expected to run until killed).
#[verifier::external_body]
fn router_thread_body<R>(
    socket: Arc<UdpSocket>,
    new_conns_tx: crossbeam_channel::Sender<(u64, MuxedRaw<R>)>,
) where for <'de>R: serde::Deserialize<'de> {
    let mut demux: HashMap<SocketAddr, crossbeam_channel::Sender<R>> = HashMap::new();
    let mut buf = vec![0u8; BUF_SIZE];
    loop {
        let (n, addr) = match socket.recv_from(&mut buf) {
            Ok(x) => x,
            Err(e) if is_recv_timeout(&e) => {
                continue;
            },
            Err(e) => {
                vlib::veprintln!("[udp_muxed]: router thread recv error: {e:?}");
                continue;
            },
        };
        let envelope: MuxedEnvelope<R> = match deserialize_envelope(&buf[..n]) {
            Ok(env) => env,
            Err(e) => {
                vlib::veprintln!("[udp_muxed]: warning: failed to decode datagram from {addr}: {e:?}");
                continue;
            },
        };
        if let Some(tx) = demux.get(&addr) {
            // Known peer: forward straight to its inbox. If the receiving worker thread has
            // already dropped this channel (send fails), there is nothing left to route to --
            // drop the datagram and leave the stale demux entry in place (see this module's top
            // doc: idle-peer eviction is a deliberately unaddressed follow-up, not attempted here).
            let _ = tx.send(envelope.body);
            continue;
        }
        // Unknown peer: this *is* the implicit accept, with zero prior network round trips.
        let (tx, rx) = crossbeam_channel::unbounded();
        let _ = tx.send(envelope.body);
        demux.insert(addr, tx);
        let raw = MuxedRaw { client_id: envelope.client_id, inbox: rx, socket: socket.clone(), peer_addr: addr };
        if new_conns_tx.send((envelope.client_id, raw)).is_err() {
            // The `MuxedListener` (and its `new_conns` receiver) was dropped -- nothing left to
            // report new connections to, so this router thread has no further purpose.
            return;
        }
    }
}

impl<R, S> MuxedListener<R, S> where for <'de>R: serde::Deserialize<'de>, R: Send + 'static {
    /// Binds one socket, no `SO_REUSEPORT` -- the `num_router_threads == 1` case of
    /// `listen_reuseport`, kept as its own entry point since it needs no `libc`/`socket2` setsockopt
    /// call at all (`std::net::UdpSocket::bind` alone is sufficient), matching every other
    /// backend's plain `listen(addr, id)` shape.
    #[verifier::external_body]
    pub fn listen<A: ToSocketAddrs>(addr: A, id: u64) -> std::io::Result<Self> {
        let socket = Arc::new(UdpSocket::bind(addr)?);
        socket.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS))).expect(
            "this should never fail",
        );
        let (tx, rx) = crossbeam_channel::unbounded();
        std::thread::spawn(move || router_thread_body::<R>(socket, tx));
        Ok(MuxedListener { id, new_conns: rx, _marker: PhantomData })
    }

    /// Binds `num_router_threads` sockets to the same address, each with `SO_REUSEPORT` set before
    /// `bind()` (via `socket2` -- see this module's top doc for why `socket2` over hand-rolled
    /// `libc` `sockaddr` packing) so the kernel fans traffic out across them by a per-flow hash,
    /// then spawns one independent router thread per socket. `num_router_threads == 1` behaves
    /// identically to `listen` except for the (harmless) `SO_REUSEPORT` socket option.
    #[verifier::external_body]
    pub fn listen_reuseport<A: ToSocketAddrs>(
        addr: A,
        id: u64,
        num_router_threads: usize,
    ) -> std::io::Result<Self> {
        assert!(num_router_threads > 0, "num_router_threads must be at least 1");
        let addr: SocketAddr = addr
            .to_socket_addrs()?
            .next()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidInput, "no address"))?;
        let (tx, rx) = crossbeam_channel::unbounded();
        for _ in 0..num_router_threads {
            let socket = Arc::new(bind_reuseport(addr)?);
            socket.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS))).expect(
                "this should never fail",
            );
            let tx = tx.clone();
            std::thread::spawn(move || router_thread_body::<R>(socket, tx));
        }
        Ok(MuxedListener { id, new_conns: rx, _marker: PhantomData })
    }
}

/// Binds a UDP socket with `SO_REUSEPORT` set before `bind()` -- `std::net::UdpSocket::bind` binds
/// and creates the socket in one step with no opportunity to set a socket option in between, so
/// this goes through `socket2::Socket` instead (which exposes `set_reuse_port`/`bind`/`bind_device`
/// as separate steps) and converts to a plain `std::net::UdpSocket` at the end via `Socket::into()`
/// -- every other method on the resulting socket is then the same standard-library API the rest of
/// this file already uses. Chose `socket2` over hand-rolling `libc::socket`/`setsockopt`/`bind`
/// directly: constructing a correct `sockaddr_in`/`sockaddr_in6` by hand is exactly the kind of
/// unsafe, pointer-casting code most likely to hide a subtle bug (wrong struct size, wrong
/// endianness, wrong address family) for very little benefit over a small, widely-used, purpose-
/// built crate whose only job is this exact "set a socket option before bind" pattern.
/// `#[verifier::external_body]`: same trust-boundary shape as every other real-socket-touching
/// function in this file, just via a different (still foreign, still unverified either way) crate.
#[verifier::external_body]
fn bind_reuseport(addr: SocketAddr) -> std::io::Result<UdpSocket> {
    let domain = if addr.is_ipv4() { socket2::Domain::IPV4 } else { socket2::Domain::IPV6 };
    let socket = socket2::Socket::new(domain, socket2::Type::DGRAM, Some(socket2::Protocol::UDP))?;
    socket.set_reuse_port(true)?;
    socket.set_nonblocking(false)?;
    socket.bind(&addr.into())?;
    Ok(socket.into())
}

#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct MuxedConnector<A: ToSocketAddrs> {
    listening_addr: A,
    local_ip: IpAddr,
    server_id: u64,
}

impl<A: ToSocketAddrs> MuxedConnector<A> {
    #[verifier::external_body]
    pub fn new(listening_addr: A, local_ip: IpAddr, server_id: u64) -> std::io::Result<Self> {
        Ok(MuxedConnector { listening_addr, local_ip, server_id })
    }
}

/// Server's channel to one client, produced by `MuxedListener::wrap_raw`. Unlike `udp.rs`'s
/// `ClientChannel`, this holds a `peer_addr` + a *shared* socket (owned jointly with its router
/// thread and every sibling channel that arrived on the same socket) rather than a private
/// connected socket -- `send` therefore uses `send_to`, not `send`.
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct MuxedClientChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    server_id: u64,
    client_id: u64,
    socket: Arc<UdpSocket>,
    peer_addr: SocketAddr,
    inbox: crossbeam_channel::Receiver<R>,
    _marker: PhantomData<S>,
}

/// Client's channel to the server, produced by `MuxedConnector::connect`. Unlike `udp.rs`'s
/// `ServerChannel`, `send` wraps the outgoing value in a `MuxedEnvelope` (see this module's top
/// doc) so the server's router thread can learn this client's declared id from its very first
/// datagram, with no separate handshake exchange.
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct MuxedServerChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    server_id: u64,
    client_id: u64,
    socket: UdpSocket,
    _marker: PhantomData<(R, S)>,
}

impl<K, R, S> MuxedClientChannel<K, R, S> {
    #[verifier::external_body]
    fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        socket: Arc<UdpSocket>,
        peer_addr: SocketAddr,
        inbox: crossbeam_channel::Receiver<R>,
    ) -> Self {
        MuxedClientChannel { pred, server_id, client_id, socket, peer_addr, inbox, _marker: PhantomData }
    }
}

impl<K, R, S> MuxedServerChannel<K, R, S> {
    #[verifier::external_body]
    fn new(pred: Ghost<K>, server_id: u64, client_id: u64, socket: UdpSocket) -> Self {
        MuxedServerChannel { pred, server_id, client_id, socket, _marker: PhantomData }
    }
}

impl<K, R, S> Channel for MuxedClientChannel<K, R, S> where
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

    /// No socket syscall at all in the common case: the demultiplexing already happened on the
    /// router thread, so this is just draining an already-populated, per-peer queue.
    #[verifier::external_body]
    fn try_recv(&self) -> Result<R, crate::network::error::TryRecvError> {
        match self.inbox.try_recv() {
            Ok(v) => Ok(v),
            Err(crossbeam_channel::TryRecvError::Empty) => {
                Err(crate::network::error::TryRecvError::Empty)
            },
            Err(crossbeam_channel::TryRecvError::Disconnected) => {
                Err(crate::network::error::TryRecvError::Disconnected)
            },
        }
    }

    /// Plain `S`, no envelope: the server already knows which peer this is (it's a property of
    /// which channel is sending), so there's nothing left to tag.
    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        let peer_addr = self.peer_addr;
        let socket = &self.socket;
        serialize_with(v, |bytes| {
            let sent_len = socket.send_to(bytes, peer_addr)?;
            if sent_len != bytes.len() {
                vlib::veprintln!(
                    "[udp_muxed]: warning: partial write (only 0x{:x}B / 0x{:x}B sent)",
                    sent_len, bytes.len(),
                );
            }
            Ok(())
        }).map_err(|e| e.into())
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

impl<K, R, S> Channel for MuxedServerChannel<K, R, S> where
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
        let mut buf = [0;BUF_SIZE];
        let n = match self.socket.recv(&mut buf) {
            Ok(n) => n,
            Err(e) if is_recv_timeout(&e) => {
                return Err(crate::network::error::TryRecvError::Empty);
            },
            Err(e) => {
                return Err(e.into());
            },
        };
        if n == BUF_SIZE {
            vlib::veprintln!(
                "[udp_muxed]: warning: receiving {:x} bytes may have exhausted the buffer, message may have been truncated",
                BUF_SIZE
            );
        }
        deserialize_plain::<R>(&buf[..n]).map_err(|e| e.into())
    }

    /// Wraps `v` in a `MuxedEnvelope` tagging it with this client's declared id -- see this
    /// module's top doc for why: it is the only thing that lets the server's router thread learn
    /// a new peer's id from its very first datagram, with no separate handshake round trip.
    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        let envelope = MuxedEnvelope { client_id: self.client_id, body: v.clone() };
        let socket = &self.socket;
        serialize_with(&envelope, |bytes| {
            let sent_len = socket.send(bytes)?;
            if sent_len != bytes.len() {
                vlib::veprintln!(
                    "[udp_muxed]: warning: partial write (only 0x{:x}B / 0x{:x}B sent)",
                    sent_len, bytes.len(),
                );
            }
            Ok(())
        }).map_err(|e| e.into())
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

// Same permanent-trust-boundary rationale as `udp.rs`'s identical comment on `UdpListener`'s
// `Listener` impl: the real work here (draining an already-populated aggregator channel that
// background router threads feed) is not something Verus can reason about, so the postcondition
// `r.constant() == gen_pred(self)` is assumed rather than checked -- it holds by construction,
// since `wrap_raw`'s body does nothing to `pred` other than store the given ghost value verbatim.
impl<K, R, S> Listener<MuxedClientChannel<K, R, S>> for MuxedListener<R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    R: Send,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.id
    }

    type Raw = MuxedRaw<R>;

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn try_accept_raw(&self) -> Result<(u64, Self::Raw), TryListenError> {
        match self.new_conns.try_recv() {
            Ok((client_id, raw)) => Ok((client_id, raw)),
            Err(crossbeam_channel::TryRecvError::Empty) => Err(TryListenError::Empty),
            Err(crossbeam_channel::TryRecvError::Disconnected) => Err(TryListenError::Disconnected),
        }
    }

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn wrap_raw(&self, raw: Self::Raw, gen_pred: Ghost<spec_fn(&Self) -> K>) -> (r: Result<
        MuxedClientChannel<K, R, S>,
        TryListenError,
    >) {
        let pred = Ghost(gen_pred@(self));
        let chan = MuxedClientChannel::new(pred, self.id, raw.client_id, raw.socket, raw.peer_addr, raw.inbox);
        vlib::veprintln!(
            "[server|{:>3}]: accepted connection from client {} (channel_id: {:?}, no handshake)",
            self.id, chan.client_id, chan.id()
        );
        Ok(chan)
    }
}

// Same permanent-trust-boundary rationale as `udp.rs`'s `UdpConnector` impl.
impl<K, R, S, A> Connector<MuxedServerChannel<K, R, S>> for MuxedConnector<A> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
    A: ToSocketAddrs,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.server_id
    }

    /// Almost a true no-op on the wire: `UdpSocket::connect()` on a UDP socket is a purely local
    /// kernel call (it records a default peer for `send`/`recv`, it does not transmit anything),
    /// so this function sends zero bytes -- the client's very first real request (via
    /// `Channel::send`) is also the very first datagram the server ever sees from this peer.
    #[verifier::external_body]
    fn connect<F>(&self, local_id: u64, gen_pred: F) -> (r: Result<
        MuxedServerChannel<K, R, S>,
        ConnectError,
    >) where F: FnOnce(&Self, u64) -> Ghost<K> {
        vlib::veprintln!(
            "[client|{:>3}]: connecting to server (udp_muxed: no handshake, purely local)", local_id,
        );
        let addr = SocketAddr::new(self.local_ip, 0);
        let socket = UdpSocket::bind(addr)?;
        socket.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS))).expect(
            "this should never fail",
        );
        socket.connect(&self.listening_addr)?;
        let pred = gen_pred(self, local_id);
        let chan = MuxedServerChannel::new(pred, self.server_id, local_id, socket);
        vlib::veprintln!(
            "[client|{:>3}]: connected to server {} (channel_id: {:?})", local_id, self.server_id, chan.id()
        );
        Ok(chan)
    }
}

} // verus!
