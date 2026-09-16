//! An alternative, even simpler server-side driver for the `udp_muxed` wire protocol: no
//! persistent per-client `Channel` object survives between one datagram and the next at all.
//!
//! `udp_muxed.rs`/`io_uring_udp_muxed.rs` still keep a `MuxedClientChannel` (private inbox, demux
//! table entry) alive for a client's whole session, going through `verdist::service::Server`'s
//! full accept/shard/dispatch machinery -- built for transports where a "connection" genuinely
//! needs multi-message state (buffered out-of-order data, a stream's byte offset, TCP's socket
//! itself). This file's `run_ephemeral` recognizes that the muxed *server* side never actually
//! needs any of that, and collapses the whole thing to: recv one datagram -> synchronously handle
//! it -> reply -> forget everything about that client immediately.
//!
//! # Why this is sound
//!
//! Investigated (not assumed) before writing any of this:
//!
//! 1. **The server side never wraps a channel in `BufChannel`** (`verdist::network::channel`'s
//!    out-of-order-tag buffer) -- grep confirms `BufChannel::new` is called only by
//!    `echo`/`echo-example`/`abd-example`'s *client*-side `connect()` helpers, never by anything
//!    on the server path (`verdist::service::Server::scan_full`/`scan_ready` call
//!    `channel.try_recv()` directly). So there is no cross-message transport-level state to lose
//!    by not persisting a channel object.
//! 2. **`ChannelInvariant::recv_inv`/`send_inv` are pure, memoryless predicates** over
//!    `(channel_inv, channel_id, value)` (`verdist::network::channel::ChannelInvariant`, both
//!    plain `spec fn`s with no `self`/no reference to any other call) -- `channel_inv` (`K`) is a
//!    build-time constant obtained once from `Service::channel_inv()`, not ghost state that
//!    accumulates across a channel instance's lifetime. Nothing in the trait's contract lets a
//!    later call depend on an earlier one via the channel object's identity.
//! 3. **All actual protocol state lives in the `Service` itself**, addressed by the
//!    `(server_id, client_id)` value pair, never by the channel object: `Service::handle` takes
//!    `&self` (one instance, shared/called concurrently by every shard *today* already) and a
//!    plain `channel_id: (u64, u64)` -- it has no way to observe "is this the same `Channel`
//!    object as last time," only "which id is this." Whatever per-client bookkeeping a service
//!    needs (e.g. a future register backend's per-client committed-write map) is the service's own
//!    data structure, unaffected by whether a transport-level channel persists.
//!
//! Given 1-3, a channel materialized fresh for exactly one datagram and dropped immediately after
//! satisfies the exact same `Channel` trait contract a long-lived one does -- nothing observably
//! changes about what any proof obligation requires or a service can depend on.
//!
//! # What changes structurally
//!
//! There is no accept thread, no shard dispatch, no `connected: Vec<C>`, no demux table, and (the
//! `udp_muxed.rs` limitation this directly resolves) no idle-peer-eviction question -- nothing
//! survives a single request/response round trip to need evicting. `--num-router-threads`-many
//! threads each run their own `recv_from -> handle -> send_to` loop directly, with zero
//! coordination between them (not even `SO_REUSEPORT` flow stickiness matters here: since no
//! per-peer state persists across messages, it is fine for two consecutive datagrams from the same
//! client to be handled by two *different* threads -- contrast with `udp_muxed.rs`'s router
//! threads, where stickiness is load-bearing precisely because a persistent per-peer inbox exists).
//!
//! This also means `--num-threads` (the shard/worker-thread count) has no meaning for this mode --
//! request-handling parallelism is entirely `--num-router-threads` now, since there is no separate
//! worker-thread pool at all. Callers pass `num_router_threads` directly as this driver's only
//! concurrency knob; `Service::handle`'s `shard_idx` parameter is simply each router thread's own
//! fixed, never-shared index (`0..num_router_threads`) -- satisfying the same "stable per-thread
//! index, never used concurrently by two threads" contract `abd`'s lock-free register backend
//! needs from `shard_idx`, just sized off a different knob than today's shard count.
//!
//! One genuine trade-off, not a soundness issue: today's design lets the accept thread keep
//! accepting brand-new connections while a separate pool of worker threads is busy handling
//! existing traffic (and, within a shard, a slow `handle()` call already blocks that shard's
//! *other* connections in the same poll batch -- this is not a new coupling). Here, a slow
//! `handle()` call blocks *that router thread's own* receiving until it returns, with no separate
//! accept/dispatch stage to insulate new traffic. For services whose `handle()` is fast/local (as
//! `echo`'s and a register server's normally are -- the *client* side is what does any
//! multi-server quorum coordination, not a single server's own `handle()`), this is not expected
//! to matter in practice, but it is a real, disclosed structural difference from the persistent-
//! channel drivers, not a hidden one.

use std::net::SocketAddr;
use std::net::ToSocketAddrs;
use std::net::UdpSocket;
use std::sync::Arc;

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::network::impls::udp_muxed::bind_reuseport;
use crate::network::impls::udp_muxed::deserialize_envelope;
use crate::network::impls::udp_muxed::is_recv_timeout;
use crate::network::impls::udp_muxed::MuxedClientChannel;
use crate::network::impls::udp_muxed::BUF_SIZE;
use crate::service::Service;

use vstd::prelude::*;

verus! {

/// Captures `service.channel_inv()` (a `spec fn`, so only callable from spec/ghost context, i.e.
/// only from inside this `verus! {}` block) into a plain `Ghost<K>` value that
/// `ephemeral_router_thread_body` -- outside `verus! {}` entirely, since it does real socket I/O
/// with no Verus spec -- can then carry across that boundary like any other value.
#[allow(unused_variables)]
fn service_channel_inv<S, K, R, Resp>(service: &S) -> (r: Ghost<K>) where
    S: Service<Request = R, Response = Resp, ChanInv = K>,

    ensures
        r@ == service.channel_inv(),
{
    Ghost(service.channel_inv())
}

/// Builds a one-shot `MuxedClientChannel` whose inbox already contains exactly `body` (the one
/// request this whole channel instance will ever be asked for) -- see this module's top doc for
/// why constructing a *real* `MuxedClientChannel` (rather than inventing a new channel type) is
/// what lets this reuse `Channel::try_recv`/`send`'s *existing* `recv_inv`/`send_inv` contracts
/// verbatim, with no new trust surface for the request/response values themselves.
///
/// `#[verifier::external_body]`, declaring exactly the two facts `handle_one_ephemeral` (below)
/// needs and nothing about the request value's `recv_inv` (that comes from `try_recv()`, called
/// separately, same as every other backend) -- same shape/size of trust boundary as
/// `Listener::wrap_raw`'s existing `r.constant() == gen_pred(self)` postcondition, just moved into
/// a purpose-built helper since this driver has no `Listener` at all.
#[verifier::external_body]
fn build_ephemeral_channel<K, R, S>(
    channel_inv: Ghost<K>,
    server_id: u64,
    client_id: u64,
    socket: Arc<UdpSocket>,
    peer_addr: SocketAddr,
    body: R,
) -> (r: MuxedClientChannel<K, R, S>) where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,

    ensures
        r.constant() == channel_inv@,
        r.spec_id() == (server_id, client_id),
{
    let (tx, rx) = crossbeam_channel::bounded(1);
    let _ = tx.send(body);
    MuxedClientChannel::new(channel_inv, server_id, client_id, socket, peer_addr, rx)
}

/// The verified core: exactly `verdist::service::Server::scan_full`'s per-message inner body
/// (`try_recv` -> `recv_implies_pre` -> `handle` -> `post_implies_send` -> `send`), minus the
/// batch/cursor/drop-tracking machinery `scan_full` needs for a *persistent* connection list --
/// there is no list here, just the one channel this call was given. Not `external_body`: this
/// composition (passing the right values to the right proof obligations in the right order) is
/// exactly the part of `Server::scan_full` that *is* checked today, and staying checked here is
/// the entire point of reusing the real `Channel`/`Service` trait methods rather of inventing a
/// shortcut.
fn handle_one_ephemeral<S, K, R, Resp>(service: &S, shard_idx: usize, channel: MuxedClientChannel<K, R, Resp>)
    where
        S: Service<Request = R, Response = Resp, ChanInv = K>,
        K: ChannelInvariant<K, (u64, u64), R, Resp>,
        for <'de>R: serde::Deserialize<'de>,
        Resp: Clone + serde::Serialize,
    requires
        channel.constant() == service.channel_inv(),
        channel.spec_id().0 == service.spec_id(),
{
    match channel.try_recv() {
        Ok(req) => {
            assert(K::recv_inv(channel.constant(), channel.spec_id(), req));
            proof {
                service.recv_implies_pre(channel.spec_id(), req);
            }
            let response = service.handle(shard_idx, channel.id(), req);
            proof {
                service.post_implies_send(channel.spec_id(), req, response);
            }
            assert(K::send_inv(channel.constant(), channel.spec_id(), response));
            let _ = channel.send(&response);
        },
        // Can't happen in practice (the inbox was just filled with exactly one message, see
        // `build_ephemeral_channel`), but `try_recv`'s contract allows it -- nothing to do.
        Err(_) => {},
    }
}

} // verus!

/// One router thread's whole life: recv one datagram, build a one-shot channel for it, hand it to
/// `handle_one_ephemeral`, repeat forever. `#[verifier::external_body]`-equivalent (kept outside
/// `verus! {}` entirely, like `Server::run`/`run_epoll`'s own thread bodies) for the same
/// structural reason: real socket I/O (`recv_from`) has no Verus spec, and per this crate's
/// existing convention (`network::impls::udp_muxed::router_thread_body`,
/// `network::impls::io_uring_udp_muxed::router_thread_body_io_uring`), that I/O lives in a small,
/// explicitly-trusted outer shell around the actually-checked inner logic
/// (`handle_one_ephemeral`), not folded into it.
fn ephemeral_router_thread_body<S, K, R, Resp>(socket: Arc<UdpSocket>, service: &S, shard_idx: usize)
where
    S: Service<Request = R, Response = Resp, ChanInv = K> + Sync,
    K: ChannelInvariant<K, (u64, u64), R, Resp>,
    for<'de> R: serde::Deserialize<'de>,
    Resp: Clone + serde::Serialize,
{
    let mut buf = vec![0u8; BUF_SIZE];
    loop {
        let (n, addr) = match socket.recv_from(&mut buf) {
            Ok(x) => x,
            Err(e) if is_recv_timeout(&e) => continue,
            Err(e) => {
                vlib::veprintln!("[udp_ephemeral]: router thread recv error: {e:?}");
                continue;
            },
        };
        let envelope = match deserialize_envelope::<R>(&buf[..n]) {
            Ok(env) => env,
            Err(e) => {
                vlib::veprintln!("[udp_ephemeral]: warning: failed to decode datagram from {addr}: {e:?}");
                continue;
            },
        };
        let channel_inv = service_channel_inv(service);
        let channel = build_ephemeral_channel(
            channel_inv,
            service.id(),
            envelope.client_id,
            socket.clone(),
            addr,
            envelope.body,
        );
        handle_one_ephemeral(service, shard_idx, channel);
    }
}

/// Entry point: binds `num_router_threads` sockets (identical `SO_REUSEPORT` story as
/// `udp_muxed::MuxedListener::listen_reuseport` -- `1` needs no special socket option, `> 1` sets
/// it via `socket2` before `bind()`) and runs one `ephemeral_router_thread_body` per socket,
/// blocking until the process is killed (same as `Server::run`/`run_epoll`'s own top-level
/// drivers). Unlike every other network backend in this crate, this takes the `Service` directly
/// rather than a `Listener` -- there is no `Listener`/`Connector`/persistent `Channel` at all in
/// this mode (see this module's top doc), so `verdist::service::Server` is never constructed.
///
/// Same unverifiable-for-structural-reasons category as `Server::run`/`run_epoll` (scoped threads).
pub fn run_ephemeral<A, S, K, R, Resp>(
    addr: A,
    service: S,
    num_router_threads: usize,
) -> std::io::Result<()>
where
    A: ToSocketAddrs,
    S: Service<Request = R, Response = Resp, ChanInv = K> + Sync,
    K: ChannelInvariant<K, (u64, u64), R, Resp>,
    for<'de> R: serde::Deserialize<'de>,
    Resp: Clone + serde::Serialize,
{
    assert!(num_router_threads > 0, "num_router_threads must be at least 1");
    let addr: SocketAddr = addr
        .to_socket_addrs()?
        .next()
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidInput, "no address"))?;
    let sockets: Vec<Arc<UdpSocket>> = (0..num_router_threads)
        .map(|_| {
            let socket = if num_router_threads == 1 {
                UdpSocket::bind(addr)?
            } else {
                bind_reuseport(addr)?
            };
            Ok(Arc::new(socket))
        })
        .collect::<std::io::Result<_>>()?;
    let service = &service;
    std::thread::scope(|scope| {
        for (shard_idx, socket) in sockets.into_iter().enumerate() {
            scope.spawn(move || ephemeral_router_thread_body(socket, service, shard_idx));
        }
    });
    Ok(())
}
