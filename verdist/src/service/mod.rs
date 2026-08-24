use std::collections::HashSet;
use std::time::Duration;

use vstd::atomic_ghost::atomic_with_ghost;
use vstd::prelude::*;
use vstd::rwlock::RwLock;
#[cfg(verus_only)]
use vstd::rwlock::RwLockPredicate;
#[cfg(verus_only)]
use vstd::std_specs::iter::IteratorSpec;

use crate::network::channel::{Channel, ChannelInvariant, Listener, RawFdChannel, RawFdListener};

verus! {

/// Service that requires exclusive access
pub trait MutService {
    type Request;

    type Response;

    type Inv;

    /// Channel invariant this service's requests/responses are carried under
    /// Server can derive `pre`/`post` from the channel's `recv_inv`/`send_inv`
    type ChanInv: ChannelInvariant<Self::ChanInv, (u64, u64), Self::Request, Self::Response>;

    spec fn constant(self) -> Self::Inv;

    spec fn spec_id(self) -> u64;

    spec fn channel_inv(self) -> Self::ChanInv;

    spec fn pre(self, channel_id: (u64, u64), request: Self::Request) -> bool;

    spec fn post(
        self,
        channel_id: (u64, u64),
        request: Self::Request,
        response: Self::Response,
    ) -> bool;

    proof fn recv_implies_pre(tracked &self, channel_id: (u64, u64), request: Self::Request)
        requires
            Self::ChanInv::recv_inv(self.channel_inv(), channel_id, request),
        ensures
            self.pre(channel_id, request),
    ;

    proof fn post_implies_send(
        tracked &self,
        channel_id: (u64, u64),
        request: Self::Request,
        response: Self::Response,
    )
        requires
            self.spec_id() == channel_id.0,
            Self::ChanInv::recv_inv(self.channel_inv(), channel_id, request),
            self.post(channel_id, request, response),
        ensures
            Self::ChanInv::send_inv(self.channel_inv(), channel_id, response),
    ;

    fn handle(&mut self, channel_id: (u64, u64), request: Self::Request) -> (r: Self::Response)
        requires
            old(self).spec_id() == channel_id.0,
            old(self).pre(channel_id, request),
        ensures
            final(self).spec_id() == old(self).spec_id(),
            final(self).constant() == old(self).constant(),
            final(self).post(channel_id, request, r),
    ;

    fn id(&self) -> (r: u64)
        ensures
            self.spec_id() == r,
    ;
}

/// Service that only requires shared access
pub trait Service {
    type Request;

    type Response;

    /// Channel invariant this service's requests/responses are carried under
    /// Server can derive `pre`/`post` from the channel's `recv_inv`/`send_inv`
    type ChanInv: ChannelInvariant<Self::ChanInv, (u64, u64), Self::Request, Self::Response>;

    spec fn spec_id(self) -> u64;

    spec fn channel_inv(self) -> Self::ChanInv;

    spec fn pre(self, channel_id: (u64, u64), request: Self::Request) -> bool;

    spec fn post(
        self,
        channel_id: (u64, u64),
        request: Self::Request,
        response: Self::Response,
    ) -> bool;

    proof fn recv_implies_pre(tracked &self, channel_id: (u64, u64), request: Self::Request)
        requires
            Self::ChanInv::recv_inv(self.channel_inv(), channel_id, request),
        ensures
            self.pre(channel_id, request),
    ;

    proof fn post_implies_send(
        tracked &self,
        channel_id: (u64, u64),
        request: Self::Request,
        response: Self::Response,
    )
        requires
            self.spec_id() == channel_id.0,
            Self::ChanInv::recv_inv(self.channel_inv(), channel_id, request),
            self.post(channel_id, request, response),
        ensures
            Self::ChanInv::send_inv(self.channel_inv(), channel_id, response),
    ;

    fn handle(&self, channel_id: (u64, u64), request: Self::Request) -> (r: Self::Response)
        requires
            self.spec_id() == channel_id.0,
            self.pre(channel_id, request),
        ensures
            self.post(channel_id, request, r),
    ;

    fn id(&self) -> (r: u64)
        ensures
            self.spec_id() == r,
    ;
}

/// Upper bound on how many connections `Server::poll_shard` scans in a single call -- see
/// `PollCursor`.
const MAX_POLL_BATCH: usize = 64;

/// Upper bound on how many connections `Server::sync_shard_registrations` (re-)registers with
/// epoll in a single call -- same bounded-batch mitigation as `MAX_POLL_BATCH`/`PollCursor`
/// above (§3 of Performance.md), applied to the registration-sync scan the mio/epoll rewrite
/// introduced: without this, a very large shard would pay an O(shard-size) registration pass on
/// every accept. A connection not covered by this call's batch still gets picked up within a
/// bounded number of subsequent accept-thread iterations (round-robin, same as `PollCursor`), or
/// -- worst case -- once `poll_shard_epoll`'s own fallback timeout elapses and it falls back to
/// `poll_shard`'s direct scan regardless of epoll registration state.
const MAX_SYNC_BATCH: usize = 64;

/// How long an idle worker thread sleeps in `poll_shard` when its shard currently has zero
/// connections (see §10 of Performance.md) -- a shard's `try_recv` timeout (§1) never fires in
/// this case since there is nothing to call it on, so without this the worker would otherwise
/// spin at full rate acquiring the (momentarily empty) read lock over and over.
const EMPTY_SHARD_BACKOFF_MILLIS: u64 = 2;

/// How long the accept thread sleeps in `poll_accept` when a call accepted nothing at all (see
/// §9 of Performance.md) -- `std::net::TcpListener` has no accept-timeout equivalent to §1's
/// per-socket read timeout, so without this the accept thread's `while self.poll_accept() {}`
/// would spin at full rate regardless of whether any client is trying to connect.
const ACCEPT_BACKOFF_MILLIS: u64 = 2;

/// How long `poll_shard_epoll`/`poll_accept_epoll` block in `mio::Poll::poll` before giving up
/// and re-scanning anyway -- a safety net against a missed registration/race, not the primary
/// wake mechanism: real work wakes instantly via epoll readiness (registering a new fd with a
/// `Poll` instance another thread is already blocked in `poll()` on wakes that thread promptly
/// if the fd is/becomes ready, standard kernel behavior). Deliberately much larger than
/// §1/§9/§10's busy-backoff constants above, since a correctly-registered fd set means this
/// thread is genuinely idle for the whole interval, not repeatedly re-checking.
const EPOLL_FALLBACK_MILLIS: u64 = 100;

/// Trivial invariant for `PollCursor`'s backing atomic: the value is a pure scheduling hint, not
/// part of any correctness invariant, so there is no ghost state (`G = ()`) and nothing to relate
/// it to (`atomic_inv` is unconditionally `true`).
struct PollCursorPred;

impl vstd::atomic_ghost::AtomicInvariantPredicate<(), usize, ()> for PollCursorPred {
    closed spec fn atomic_inv(k: (), v: usize, g: ()) -> bool {
        true
    }
}

/// Round-robins which slice of a shard's connections `poll_shard` actually touches on a given
/// call, instead of scanning every connection every call (see §3 of Performance.md). Backed by
/// `vstd::atomic_ghost::AtomicUsize`, a fully verified sequentially-consistent atomic, so no
/// `external_body`/`assume` is needed even though it's shared (via `&self`) across the accept
/// thread and every per-shard worker thread (see `Server::run`) -- in practice only the single
/// worker thread owning a given shard ever calls `advance` on that shard's cursor, but nothing
/// here relies on that for soundness.
pub struct PollCursor {
    next: vstd::atomic_ghost::AtomicUsize<(), (), PollCursorPred>,
}

impl Default for PollCursor {
    fn default() -> Self {
        Self::new()
    }
}

impl PollCursor {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        self.next.well_formed()
    }

    pub fn new() -> (r: Self) {
        let next = vstd::atomic_ghost::AtomicUsize::new(Ghost(()), 0, Tracked(()));
        let result = PollCursor { next };
        assert(result.inv());
        result
    }

    /// Returns the start index of the next batch of size `min(batch, len)` (mod `len`), and
    /// advances internal state so a subsequent call continues where this one left off.
    pub fn advance(&self, len: usize, batch: usize) -> usize {
        proof {
            use_type_invariant(self);
        }
        if len == 0 {
            return 0;
        }
        let cur = atomic_with_ghost!(&self.next => load(); ghost g => {});
        let start = cur % len;
        // wrapping_add: `start`/`batch` are just scheduling state, not part of any correctness
        // invariant, so on the (practically unreachable) usize wraparound the resulting `next` is
        // still a harmless in-bounds index -- no need to prove `start + batch` doesn't overflow.
        let next = (start.wrapping_add(batch)) % len;
        atomic_with_ghost!(&self.next => store(next); ghost g => {});
        start
    }
}

/// Trivial invariant for the `mio::Poll` handles backing `Server::run_epoll` (see §9/§10 of
/// Performance.md). A `Poll` handle is pure scheduling state, not part of any correctness
/// invariant -- there is nothing to state about it beyond "some `mio::Poll` value lives here" --
/// so this exists only to get verified interior mutability for `mio::Poll::poll`'s `&mut self`
/// requirement through `Server`'s `&self` methods, the same role `RwLock` already plays for
/// `connected`.
pub struct TrivialPollInv;

impl vstd::rwlock::RwLockPredicate<mio::Poll> for TrivialPollInv {
    open spec fn inv(self, v: mio::Poll) -> bool {
        true
    }
}

pub struct ConnectionsInv<K> {
    pub channel_inv: K,
    pub server_id: u64,
}

impl<C> vstd::rwlock::RwLockPredicate<Vec<C>> for ConnectionsInv<C::K> where
    C: Channel<Id = (u64, u64)>,
 {
    open spec fn inv(self, v: Vec<C>) -> bool {
        forall|idx: int|
            0 <= idx < v@.len() ==> {
                let chan = #[trigger] v@[idx];
                &&& self.channel_inv == chan.constant()
                &&& self.server_id == chan.spec_id().0
            }
    }
}

pub struct Server<S, L, C> where
    S: Service<Request = C::R, Response = C::S, ChanInv = C::K>,
    L: Listener<C>,
    C: Channel<Id = (u64, u64)>,
 {
    /// Service being served
    service: S,
    /// Listener channel
    listener: L,
    /// Connected clients, sharded across independent locks so that `connected.len()` worker
    /// threads can each poll their own shard without contending on the others.
    connected: Vec<RwLock<Vec<C>, ConnectionsInv<C::K>>>,
    /// One round-robin cursor per shard (see `PollCursor`), same length as `connected`.
    cursors: Vec<PollCursor>,
    /// Poll handle for the listener socket -- used by `run_epoll`'s accept thread to block on
    /// real fd readiness instead of spinning/backing off (see §9 of Performance.md). Unused by
    /// the plain `run` driver.
    accept_poll: RwLock<mio::Poll, TrivialPollInv>,
    /// Registry clone for `accept_poll`, kept separately since `Registry`'s methods only need
    /// `&self` -- registering the listener fd never contends with the accept thread's blocking
    /// `poll()` call the way sharing `accept_poll`'s lock would.
    accept_registry: mio::Registry,
    /// One Poll handle per shard (same length as `connected`), used by `run_epoll`'s worker
    /// threads.
    shard_polls: Vec<RwLock<mio::Poll, TrivialPollInv>>,
    /// One Registry clone per shard, same length as `connected`.
    shard_registries: Vec<mio::Registry>,
    /// One round-robin cursor per shard (same length as `connected`), bounding
    /// `sync_shard_registrations`'s per-call scan the same way `cursors` bounds `poll_shard`'s
    /// (see §3 of Performance.md) -- separate from `cursors` since the two scans track
    /// independent progress through `connected[shard]` and must not interfere with each other.
    sync_cursors: Vec<PollCursor>,
}

impl<S, L, C> Server<S, L, C> where
    S: Service<Request = C::R, Response = C::S, ChanInv = C::K>,
    L: Listener<C>,
    C: Channel<Id = (u64, u64)>,
 {
    pub closed spec fn spec_server_id(self) -> u64 {
        self.service.spec_id()
    }

    #[allow(unused)]
    pub fn new(service: S, listener: L, channel_inv: Ghost<C::K>, num_shards: usize) -> (r: Self)
        requires
            channel_inv@ == service.channel_inv(),
            listener.spec_id() == service.spec_id(),
            num_shards > 0,
        ensures
            r.spec_server_id() == service.spec_id(),
    {
        let id = service.id();
        let ghost connected_inv = ConnectionsInv { channel_inv: channel_inv@, server_id: id };
        let mut connected: Vec<RwLock<Vec<C>, ConnectionsInv<C::K>>> = Vec::new();
        let mut cursors: Vec<PollCursor> = Vec::new();
        let mut shard_polls: Vec<RwLock<mio::Poll, TrivialPollInv>> = Vec::new();
        let mut shard_registries: Vec<mio::Registry> = Vec::new();
        let mut sync_cursors: Vec<PollCursor> = Vec::new();
        let mut i = 0;
        while i < num_shards
            invariant
                connected.len() == i,
                cursors.len() == i,
                shard_polls.len() == i,
                shard_registries.len() == i,
                sync_cursors.len() == i,
                forall|j: int|
                    0 <= j < connected@.len() ==> #[trigger] connected@[j].pred() == connected_inv,
            decreases num_shards - i,
        {
            let empty: Vec<C> = Vec::new();
            assert(connected_inv.inv(empty));
            connected.push(RwLock::new(empty, Ghost(connected_inv)));
            cursors.push(PollCursor::new());
            let poll = mio::Poll::new().expect("mio::Poll::new should not fail");
            let registry = poll.registry().try_clone().expect(
                "mio::Registry::try_clone should not fail",
            );
            shard_polls.push(RwLock::new(poll, Ghost(TrivialPollInv)));
            shard_registries.push(registry);
            sync_cursors.push(PollCursor::new());
            i += 1;
        }
        let accept_poll_raw = mio::Poll::new().expect("mio::Poll::new should not fail");
        let accept_registry = accept_poll_raw.registry().try_clone().expect(
            "mio::Registry::try_clone should not fail",
        );
        let accept_poll = RwLock::new(accept_poll_raw, Ghost(TrivialPollInv));
        Server {
            service,
            listener,
            connected,
            cursors,
            accept_poll,
            accept_registry,
            shard_polls,
            shard_registries,
            sync_cursors,
        }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.connected.len() > 0
        &&& self.cursors.len() == self.connected.len()
        &&& self.shard_polls.len() == self.connected.len()
        &&& self.shard_registries.len() == self.connected.len()
        &&& self.sync_cursors.len() == self.connected.len()
        &&& self.listener.spec_id() == self.service.spec_id()
        &&& forall|i: int|
            0 <= i < self.connected.len() ==> {
                &&& #[trigger] self.connected[i].pred().server_id == self.service.spec_id()
                &&& self.connected[i].pred().channel_inv == self.service.channel_inv()
            }
    }

    /// Number of independent shards `connected` is split across -- exposed so public
    /// requires/ensures clauses don't have to reach into the (module-private) `connected` field.
    pub closed spec fn spec_num_shards(self) -> int {
        self.connected.len() as int
    }

    /// Number of independent shards `connected` is split across -- also the number of
    /// request-processing worker threads the (unverified) `run()` driver spawns.
    pub fn num_shards(&self) -> (r: usize)
        ensures
            r as int == self.spec_num_shards(),
    {
        proof {
            use_type_invariant(self);
        }
        self.connected.len()
    }

    pub fn server_id(&self) -> (r: u64)
        ensures
            r == self.spec_server_id(),
    {
        proof {
            use_type_invariant(self);
        }
        self.service.id()
    }

    fn accept(&self, channel: C)
        requires
            channel.constant() == self.service.channel_inv(),
            channel.spec_id().0 == self.service.spec_id(),
    {
        proof {
            use_type_invariant(self);
        }
        // Which shard a connection lands in is a pure load-balancing choice -- every shard
        // shares the same `ConnectionsInv`, so any in-bounds index is equally valid here.
        let shard = (channel.id().1 as usize) % self.connected.len();
        assert(self.connected[shard as int].pred().server_id == self.service.spec_id());
        assert(self.connected[shard as int].pred().channel_inv == self.service.channel_inv());
        let (mut guard, handle) = self.connected[shard].acquire_write();
        guard.push(channel);
        assert(ConnectionsInv::inv(self.connected[shard as int].pred(), guard));
        handle.release_write(guard);
    }

    /// Drains up to 10 pending `try_accept`s from the listener into the shards. Meant to be
    /// driven by a single, dedicated accept thread -- see `run()`.
    pub fn poll_accept(&self) -> bool {
        proof {
            use_type_invariant(self);
        }
        // verus does not support unbounded loops + streams probably don't/can't have specs
        // so we do this up to 10 times every time
        let mut i = 10;
        while i > 0
            decreases i,
        {
            use crate::network::error::TryListenError;
            match self.listener.try_accept(Ghost(|l| self.service.channel_inv())) {
                Ok(channel) => {
                    assert(channel.constant() == self.service.channel_inv());
                    proof {
                        use_type_invariant(self);
                    }
                    assert(channel.spec_id().0 == self.service.spec_id());
                    self.accept(channel)
                },
                Err(TryListenError::Empty) => {
                    if i == 10 {
                        // Nothing was accepted this call -- back off instead of immediately
                        // re-looping (see §9 of Performance.md; `std::net::TcpListener` has no
                        // accept-timeout API, so this is the cheap poll-and-sleep mitigation
                        // rather than a true blocking accept).
                        std::thread::sleep(Duration::from_millis(ACCEPT_BACKOFF_MILLIS));
                    }
                    break;
                },
                Err(TryListenError::Disconnected | TryListenError::NoFreePorts) => {
                    return false;
                },
                Err(TryListenError::Io(io)) => {
                    match io.kind() {
                        std::io::ErrorKind::ConnectionRefused
                        | std::io::ErrorKind::ConnectionReset
                        | std::io::ErrorKind::HostUnreachable
                        | std::io::ErrorKind::NetworkUnreachable
                        | std::io::ErrorKind::ConnectionAborted
                        | std::io::ErrorKind::NotConnected
                        | std::io::ErrorKind::AddrNotAvailable
                        | std::io::ErrorKind::NetworkDown => { return false },
                        _ => {
                            break;
                        },
                    }
                },
            }

            i -= 1;
        }

        true
    }

    /// Polls, handles, and drops dead connections within a single shard. Meant to be driven by
    /// one dedicated worker thread per shard -- see `run()`.
    ///
    /// Only holds a *read* lock while scanning/handling connections (every op here --
    /// `try_recv`/`Service::handle`/`send` -- only needs `&self`/`&C`), so the accept thread can
    /// still register new connections in this shard, and nothing else in the shard is blocked by
    /// a slow handler. The write lock is only taken afterwards, and only for the `retain()` that
    /// drops dead connections.
    ///
    /// Only scans up to `MAX_POLL_BATCH` connections per call (round-robin across calls via
    /// `self.cursors[shard]`) instead of every connection in the shard every time (see §3 of
    /// Performance.md) -- cost per call is bounded regardless of how many idle long-lived
    /// connections have accumulated in the shard; full coverage is still reached, just spread
    /// out over multiple calls.
    pub fn poll_shard(&self, shard: usize, drop_scratch: &mut HashSet<C::Id>) -> bool
        requires
            (shard as int) < self.spec_num_shards(),
    {
        proof {
            use_type_invariant(self);
            broadcast use vstd::seq_lib::group_filter_ensures;

        }
        drop_scratch.clear();
        let read_handle = self.connected[shard].acquire_read();

        let ghost connected_pred = self.connected[shard as int].pred();
        assert(connected_pred.server_id == self.service.spec_id());
        assert(connected_pred.channel_inv == self.service.channel_inv());
        let connected = read_handle.borrow();
        assert(connected_pred.inv(*connected));

        let len = connected.len();
        if len == 0 {
            read_handle.release_read();
            std::thread::sleep(Duration::from_millis(EMPTY_SHARD_BACKOFF_MILLIS));
            return true;
        }
        let batch = if len < MAX_POLL_BATCH {
            len
        } else {
            MAX_POLL_BATCH
        };
        let start = self.cursors[shard].advance(len, batch);

        let mut i = 0usize;
        while i < batch
            invariant
                connected_pred == self.connected[shard as int].pred(),
                connected_pred.server_id == self.service.spec_id(),
                connected_pred.channel_inv == self.service.channel_inv(),
                connected_pred.inv(*connected),
                connected@.len() == len,
                batch <= len,
            decreases batch - i,
        {
            use crate::network::error::TryRecvError;
            assume(start + i < usize::MAX);  // XXX: overflow, mirrors poll_accept's `idx`
            let idx = (start + i) % len;
            assert(0 <= idx < connected@.len()) by {
                assert(len > 0);
            };
            let channel = &connected[idx];
            assert(*channel == connected@[idx as int]);  // TRIGGER
            assert(connected_pred.inv(*connected));
            assert({
                let chan = connected@[idx as int];
                &&& connected_pred.channel_inv == chan.constant()
                &&& connected_pred.server_id == chan.spec_id().0
            });
            match channel.try_recv() {
                Ok(req) => {
                    assert(self.service.channel_inv() == channel.constant());
                    assert(C::K::recv_inv(channel.constant(), channel.spec_id(), req));
                    proof {
                        self.service.recv_implies_pre(channel.spec_id(), req);
                    }
                    let response = self.service.handle(channel.id(), req);
                    proof {
                        self.service.post_implies_send(channel.spec_id(), req, response);
                    }
                    assert(C::K::send_inv(channel.constant(), channel.spec_id(), response));
                    if channel.send(&response).is_err() {
                        drop_scratch.insert(channel.id());
                    }
                },
                Err(TryRecvError::Empty) => {},
                Err(e) => {
                    vlib::veprintln!("[server|{:>3}]: dropping channel: {e:?}", self.service.id());
                    drop_scratch.insert(channel.id());
                },
            }
            i += 1;
        }
        read_handle.release_read();

        if drop_scratch.is_empty() {
            return true;
        }
        let (mut connected, handle) = self.connected[shard].acquire_write();
        let ghost old_c = connected@;
        let filter_fn = |c: &C| !drop_scratch.contains(&c.id());
        connected.retain(filter_fn);
        proof {
            let ghost server_inv = self.connected[shard as int].pred();
            assert forall|idx| 0 <= idx < connected@.len() implies {
                let chan = #[trigger] connected@[idx];
                &&& server_inv.channel_inv == chan.constant()
                &&& server_inv.server_id == chan.spec_id().0
            } by {
                let chan = #[trigger] connected@[idx];
                old_c.lemma_filter_contains_rev(|c| filter_fn.ensures((&c,), true), chan);
            }
        }
        handle.release_write(connected);

        true
    }
}

/// `run_epoll`'s verified per-iteration methods -- see §9/§10 of Performance.md. Separate from
/// the fully-generic impl block above (bounded by `Channel`/`Listener`) because these need real
/// fds: `C: RawFdChannel`, `L: RawFdListener<C>`. Not implemented by the in-process `modelled`
/// network, which has no real fd and keeps using `run`/`poll_shard`/`poll_accept` unmodified.
impl<S, L, C> Server<S, L, C> where
    S: Service<Request = C::R, Response = C::S, ChanInv = C::K>,
    L: RawFdListener<C>,
    C: RawFdChannel<Id = (u64, u64)>,
 {
    /// Registers up to `MAX_SYNC_BATCH` connections from `shard`'s list (round-robin across
    /// calls via `sync_cursors[shard]`, same bounded-batch mitigation as `poll_shard`'s scan --
    /// see `MAX_SYNC_BATCH`) with that shard's `mio::Poll` registry, tolerating an
    /// already-registered fd as a no-op. Self-correcting: recomputes from `connected[shard]`'s
    /// current ground truth every call rather than tracking exact accept/drop transitions -- and
    /// there is nothing to do on the drop side at all, since closing a socket (which
    /// `poll_shard`'s `retain` already does for dropped connections) automatically removes it
    /// from any `Poll`'s interest list, standard kernel behavior.
    fn sync_shard_registrations(&self, shard: usize)
        requires
            (shard as int) < self.spec_num_shards(),
    {
        proof {
            use_type_invariant(self);
        }
        assert(shard < self.shard_registries.len());
        let read_handle = self.connected[shard].acquire_read();
        let connected = read_handle.borrow();
        let len = connected.len();
        if len == 0 {
            read_handle.release_read();
            return;
        }
        let batch = if len < MAX_SYNC_BATCH {
            len
        } else {
            MAX_SYNC_BATCH
        };
        let start = self.sync_cursors[shard].advance(len, batch);

        let mut i = 0usize;
        while i < batch
            invariant
                i <= batch,
                batch <= len,
                len == connected@.len(),
                shard < self.shard_registries.len(),
            decreases batch - i,
        {
            assume(start + i < usize::MAX);  // XXX: overflow, mirrors poll_shard's `idx`
            let idx = (start + i) % len;
            assert(0 <= idx < connected@.len()) by {
                assert(len > 0);
            };
            let fd = connected[idx].raw_fd();
            match vlib::mio::mio_register_readable(&self.shard_registries[shard], fd, fd as usize) {
                Ok(()) => {},
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {},
                Err(e) => {
                    vlib::veprintln!(
                        "[server|{:>3}]: warning: failed to register fd {fd} with epoll: {e:?}",
                        self.service.id(),
                    );
                },
            }
            i += 1;
        }
        read_handle.release_read();
    }

    /// Like `poll_shard`, but only calls `try_recv()` on connections whose fd is in `ready` --
    /// every other connection in the shard is skipped with no syscall at all, avoiding the
    /// up-to-`RECV_TIMEOUT_MILLIS` blocking cost `try_recv()` pays on a connection with nothing
    /// to read. `poll_shard_epoll` only calls this once epoll has reported specific fds as
    /// readable, so every connection it does call `try_recv()` on is expected to return data
    /// immediately, not block. See `claude-files/UdpReadRegression.md` for the regression this
    /// addresses: without this, every idle connection a shard has ever accepted (UDP never
    /// signals a connection as dead) cost a real blocking timeout on every single poll.
    fn poll_shard_ready(
        &self,
        shard: usize,
        ready: &std::collections::HashSet<i32>,
        drop_scratch: &mut HashSet<C::Id>,
    ) -> bool
        requires
            (shard as int) < self.spec_num_shards(),
    {
        proof {
            use_type_invariant(self);
        }
        drop_scratch.clear();
        let read_handle = self.connected[shard].acquire_read();

        let ghost connected_pred = self.connected[shard as int].pred();
        assert(connected_pred.server_id == self.service.spec_id());
        assert(connected_pred.channel_inv == self.service.channel_inv());
        let connected = read_handle.borrow();
        assert(connected_pred.inv(*connected));

        let len = connected.len();
        if len == 0 {
            read_handle.release_read();
            return true;
        }
        let mut i = 0usize;
        while i < len
            invariant
                connected_pred == self.connected[shard as int].pred(),
                connected_pred.server_id == self.service.spec_id(),
                connected_pred.channel_inv == self.service.channel_inv(),
                connected_pred.inv(*connected),
                connected@.len() == len,
            decreases len - i,
        {
            use crate::network::error::TryRecvError;
            let channel = &connected[i];
            assert(*channel == connected@[i as int]);  // TRIGGER
            assert(connected_pred.inv(*connected));
            assert({
                let chan = connected@[i as int];
                &&& connected_pred.channel_inv == chan.constant()
                &&& connected_pred.server_id == chan.spec_id().0
            });
            if ready.contains(&channel.raw_fd()) {
                match channel.try_recv() {
                    Ok(req) => {
                        assert(self.service.channel_inv() == channel.constant());
                        assert(C::K::recv_inv(channel.constant(), channel.spec_id(), req));
                        proof {
                            self.service.recv_implies_pre(channel.spec_id(), req);
                        }
                        let response = self.service.handle(channel.id(), req);
                        proof {
                            self.service.post_implies_send(channel.spec_id(), req, response);
                        }
                        assert(C::K::send_inv(channel.constant(), channel.spec_id(), response));
                        if channel.send(&response).is_err() {
                            drop_scratch.insert(channel.id());
                        }
                    },
                    Err(TryRecvError::Empty) => {},
                    Err(e) => {
                        vlib::veprintln!("[server|{:>3}]: dropping channel: {e:?}", self.service.id());
                        drop_scratch.insert(channel.id());
                    },
                }
            }
            i += 1;
        }
        read_handle.release_read();

        if drop_scratch.is_empty() {
            return true;
        }
        let (mut connected, handle) = self.connected[shard].acquire_write();
        let ghost old_c = connected@;
        let filter_fn = |c: &C| !drop_scratch.contains(&c.id());
        connected.retain(filter_fn);
        proof {
            let ghost server_inv = self.connected[shard as int].pred();
            assert forall|idx| 0 <= idx < connected@.len() implies {
                let chan = #[trigger] connected@[idx];
                &&& server_inv.channel_inv == chan.constant()
                &&& server_inv.server_id == chan.spec_id().0
            } by {
                let chan = #[trigger] connected@[idx];
                old_c.lemma_filter_contains_rev(|c| filter_fn.ensures((&c,), true), chan);
            }
        }
        handle.release_write(connected);

        true
    }

    /// Blocks (via real epoll/kqueue readiness, with `EPOLL_FALLBACK_MILLIS` as a safety-net
    /// timeout) until `shard` likely has work, then dispatches only to the connections epoll
    /// reported as ready (`poll_shard_ready`), falling back to a full `poll_shard` scan only when
    /// epoll reported nothing at all (see `poll_shard_ready`'s doc and
    /// `claude-files/UdpReadRegression.md`). Meant to be driven by `run_epoll`'s per-shard worker
    /// thread in place of `poll_shard` alone.
    pub fn poll_shard_epoll(
        &self,
        shard: usize,
        ready_scratch: &mut std::collections::HashSet<i32>,
        drop_scratch: &mut HashSet<C::Id>,
    ) -> bool
        requires
            (shard as int) < self.spec_num_shards(),
    {
        proof {
            use_type_invariant(self);
        }
        let (mut poll, poll_handle) = self.shard_polls[shard].acquire_write();
        let mut events = mio::Events::with_capacity(MAX_POLL_BATCH);
        let _ = poll.poll(&mut events, Some(Duration::from_millis(EPOLL_FALLBACK_MILLIS)));
        vlib::mio::mio_fill_ready_fds(&events, ready_scratch);
        poll_handle.release_write(poll);
        if ready_scratch.is_empty() {
            // Nothing reported ready before the fallback timeout elapsed -- either the shard is
            // genuinely idle, or some connection hasn't been registered with epoll yet (a race
            // with `sync_shard_registrations`, itself bounded/round-robin). Fall back to the
            // full blind scan so such stragglers are still eventually reached. This is now the
            // *only* place the O(shard size) * RECV_TIMEOUT_MILLIS blind scan runs, and it only
            // runs when nothing else was pending anyway -- see `claude-files/UdpReadRegression.md`
            // for why the previous unconditional-every-call version of this was the regression.
            return self.poll_shard(shard, drop_scratch);
        }
        self.poll_shard_ready(shard, ready_scratch, drop_scratch)
    }

    /// Blocks (via real epoll/kqueue readiness on the listener fd, with the same fallback
    /// timeout) until a connection is likely pending, then runs the existing, unmodified
    /// `poll_accept`, then syncs every shard's fd registrations so any newly-accepted
    /// connections are registered promptly (see `sync_shard_registrations`) -- registering the
    /// listener fd itself is idempotent (tolerates already-registered) so no separate one-time
    /// setup is needed. Meant to be driven by `run_epoll`'s accept thread in place of
    /// `poll_accept` alone.
    pub fn poll_accept_epoll(&self) -> bool
        requires
            self.spec_num_shards() > 0,
    {
        proof {
            use_type_invariant(self);
        }
        let listener_fd = self.listener.raw_fd();
        match vlib::mio::mio_register_readable(
            &self.accept_registry,
            listener_fd,
            listener_fd as usize,
        ) {
            Ok(()) => {},
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {},
            Err(e) => {
                vlib::veprintln!(
                    "[server|{:>3}]: warning: failed to register listener fd {listener_fd} with epoll: {e:?}",
                    self.service.id(),
                );
            },
        }
        let (mut poll, poll_handle) = self.accept_poll.acquire_write();
        let mut events = mio::Events::with_capacity(1);
        let _ = poll.poll(&mut events, Some(Duration::from_millis(EPOLL_FALLBACK_MILLIS)));
        poll_handle.release_write(poll);
        let result = self.poll_accept();
        let num_shards = self.num_shards();
        let mut shard = 0usize;
        while shard < num_shards
            invariant
                num_shards == self.spec_num_shards(),
            decreases num_shards - shard,
        {
            self.sync_shard_registrations(shard);
            shard += 1;
        }
        result
    }
}

} // verus!
// Why is this unverified:
// - major: verus does not support scoped threads (`vstd::thread::spawn` only wraps
//   `std::thread::spawn`'s `'static`, owned case) -- this mirrors the pattern every
//   example/bench binary already used to drive the single-worker-thread `poll()`.
impl<S, L, C> Server<S, L, C>
where
    S: Service<Request = C::R, Response = C::S, ChanInv = C::K> + Sync,
    L: Listener<C> + Sync,
    C: Channel<Id = (u64, u64)> + Send + Sync,
{
    /// Spawns one dedicated accept thread plus one dedicated worker thread per shard, and
    /// blocks until they all exit. The accept thread stops on a fatal listener error; each
    /// worker thread polls its own shard forever -- a dead listener no longer takes down
    /// already-connected clients, unlike the single-loop `poll()` this replaces.
    pub fn run(&self) {
        std::thread::scope(|s| {
            s.spawn(|| while self.poll_accept() {});
            for shard in 0..self.num_shards() {
                s.spawn(move || {
                    // Owned by this shard's single dedicated worker thread and reused across
                    // every `poll_shard` call instead of allocating a fresh `HashSet` each time
                    // (the overwhelmingly common case is nothing to drop) -- see
                    // claude-files/UdpConcurrencyBottleneck.md's allocation-cleanup follow-up.
                    let mut drop_scratch = std::collections::HashSet::new();
                    loop {
                        self.poll_shard(shard, &mut drop_scratch);
                    }
                });
            }
        });
    }
}

// Same unverifiable-for-structural-reasons category as `run` above (scoped threads), not a new
// exception -- `run_epoll` differs from `run` only in which per-iteration method each thread
// calls (`poll_accept_epoll`/`poll_shard_epoll`, see the verified impl block above, instead of
// `poll_accept`/`poll_shard`), never in the threading shell itself.
impl<S, L, C> Server<S, L, C>
where
    S: Service<Request = C::R, Response = C::S, ChanInv = C::K> + Sync,
    L: RawFdListener<C> + Sync,
    C: RawFdChannel<Id = (u64, u64)> + Send + Sync,
{
    /// Same thread topology as `run` (one accept thread, one worker thread per shard), but each
    /// thread blocks on real fd readiness (via `mio`/epoll, see `poll_accept_epoll`/
    /// `poll_shard_epoll`) instead of `run`'s busy-backoff, structurally resolving §9/§10 of
    /// Performance.md instead of just mitigating them. Only usable when both `L` and `C` have a
    /// real OS fd (TCP/UDP) -- the in-process `modelled` network keeps using `run`.
    pub fn run_epoll(&self) {
        std::thread::scope(|s| {
            s.spawn(|| while self.poll_accept_epoll() {});
            for shard in 0..self.num_shards() {
                s.spawn(move || {
                    // Same rationale as `run`'s `drop_scratch` -- owned by this shard's single
                    // worker thread, reused across calls instead of allocating fresh every poll.
                    let mut ready_scratch = std::collections::HashSet::new();
                    let mut drop_scratch = std::collections::HashSet::new();
                    loop {
                        self.poll_shard_epoll(shard, &mut ready_scratch, &mut drop_scratch);
                    }
                });
            }
        });
    }
}
