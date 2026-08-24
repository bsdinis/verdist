use std::collections::HashSet;
use std::marker::PhantomData;
use std::time::Duration;

use vstd::atomic_ghost::atomic_with_ghost;
use vstd::prelude::*;
use vstd::rwlock::RwLock;
#[cfg(verus_only)]
use vstd::rwlock::RwLockPredicate;

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

/// Upper bound on how many connections a shard's scan (`Server::poll_shard`'s inner scan,
/// `poll_shard_ready`) touches in a single call, and how many raw handoffs `drain_raw`/
/// `drain_raw_epoll` drain from a shard's channel per call. Round-robin bookkeeping (`cursor`)
/// bounds the scan the same way it always has; the channel drain is bounded for the same
/// Verus-requires-a-`decreases`-measure reason `poll_accept`'s accept loop already was.
const MAX_POLL_BATCH: usize = 64;

/// Upper bound on how many raw connections `drain_raw`/`drain_raw_epoll` pull off a shard's
/// handoff channel in a single call -- same bounded-batch rationale as `MAX_POLL_BATCH`. A raw
/// connection not covered by this call's batch simply remains queued and is picked up on a
/// subsequent call; nothing is lost, just possibly delayed by one extra poll cycle.
const MAX_DRAIN_BATCH: usize = 64;

/// How long an idle worker thread sleeps in `poll_shard` when its shard currently has zero
/// connections (see §10 of Performance.md) -- a shard's `try_recv` timeout (§1) never fires in
/// this case since there is nothing to call it on, so without this the worker would otherwise
/// spin at full rate scanning an (momentarily empty) connection list over and over.
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

/// How many connections `Server::choose_shard` fills an already-active shard with before it
/// starts routing new connections to the next shard, instead of the old policy's immediate
/// modulo-hash spread across every shard from the very first connection. See
/// claude-files/PerfProfiling/syscall_frequency_findings.txt: with too few connections per
/// shard, each `epoll_wait` call finds essentially exactly one ready fd (no batching), so
/// concentrating load onto fewer shards first -- until each is comfortably batching -- cuts
/// total `epoll_wait` call volume and improves throughput for workloads with fewer clients than
/// shards. Chosen to comfortably exceed the ~1.02 ready-fds-per-call the unbatched case measured,
/// without being so large that a genuinely low-concurrency deployment never uses more than one
/// shard at all.
const MIN_CONNS_PER_SHARD_BEFORE_SPREADING: usize = 4;

/// Trivial invariant for `ShardLoad`'s backing atomic: the value is a pure load-balancing hint
/// (how many connections a shard currently owns), not part of any correctness invariant, so
/// there is no ghost state (`G = ()`) and nothing to relate it to (`atomic_inv` is
/// unconditionally `true`) -- same rationale as the (now-deleted) `PollCursorPred`.
struct ShardLoadPred;

impl vstd::atomic_ghost::AtomicInvariantPredicate<(), usize, ()> for ShardLoadPred {
    closed spec fn atomic_inv(k: (), v: usize, g: ()) -> bool {
        true
    }
}

/// A shard's current connection count, incremented by the (single) accept thread when
/// `Server::dispatch_raw` routes a new connection there (via `choose_shard`), decremented by
/// that shard's own worker thread whenever `scan_full`/`scan_ready` drops dead connections.
/// Unlike every other piece of per-shard state in this file, this one really is touched by two
/// different threads -- but only at connection accept/drop time, not per-request, so it stays
/// orders of magnitude rarer than the per-request contention the ownership-transfer redesign
/// removed (see claude-files/ServerOwnershipTransferPlan.md). Backed by
/// `vstd::atomic_ghost::AtomicUsize`, a fully verified sequentially-consistent atomic, so this
/// adds no new trust surface.
pub struct ShardLoad {
    count: vstd::atomic_ghost::AtomicUsize<(), (), ShardLoadPred>,
}

impl Default for ShardLoad {
    fn default() -> Self {
        Self::new()
    }
}

impl ShardLoad {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        self.count.well_formed()
    }

    pub fn new() -> (r: Self) {
        let count = vstd::atomic_ghost::AtomicUsize::new(Ghost(()), 0, Tracked(()));
        let result = ShardLoad { count };
        assert(result.inv());
        result
    }

    pub fn load(&self) -> usize {
        proof {
            use_type_invariant(self);
        }
        atomic_with_ghost!(&self.count => load(); ghost g => {})
    }

    /// Called by the accept thread each time `choose_shard` routes a new connection here.
    pub fn increment(&self) {
        proof {
            use_type_invariant(self);
        }
        // wrapping: this is a load-balancing hint, not part of any correctness invariant, so on
        // the (practically unreachable) usize wraparound the resulting count is still a harmless
        // hint -- no need to prove `count + 1` doesn't overflow (same rationale as
        // `PollCursor::advance`'s wrapping arithmetic).
        let _ = atomic_with_ghost!(&self.count => fetch_add_wrapping(1); ghost g => {});
    }

    /// Called by this shard's own worker thread whenever a scan's `retain` step drops `n` dead
    /// connections.
    pub fn decrement_by(&self, n: usize) {
        proof {
            use_type_invariant(self);
        }
        let _ = atomic_with_ghost!(&self.count => fetch_sub_wrapping(n); ghost g => {});
    }
}

/// Trivial invariant for the `mio::Poll` handle backing the accept thread's blocking wait in
/// `Server::run_epoll` (see §9/§10 of Performance.md). A `Poll` handle is pure scheduling state,
/// not part of any correctness invariant -- there is nothing to state about it beyond "some
/// `mio::Poll` value lives here" -- so this exists only to get verified interior mutability for
/// `mio::Poll::poll`'s `&mut self` requirement through `Server`'s `&self` methods. The accept
/// thread is the only thread that ever touches `accept_poll` (there is exactly one of it), so
/// this remains an `RwLock` purely for that interior-mutability reason, not because of any real
/// cross-thread contention -- unlike the per-shard `mio::Poll`/`Registry` handles, which are now
/// owned directly by each worker thread's local state (see `run_epoll`) since ownership-transfer
/// removed the need to reach them through `&self` at all.
pub struct TrivialPollInv;

impl vstd::rwlock::RwLockPredicate<mio::Poll> for TrivialPollInv {
    open spec fn inv(self, v: mio::Poll) -> bool {
        true
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
    /// One handoff channel sender per shard: the accept thread sends newly-accepted raw
    /// connections here; the shard's own worker thread owns the paired `Receiver` (returned
    /// alongside `Self` by `new`, not stored as a `Server` field -- see that field's absence and
    /// `new`'s doc) and is the only thread that ever wraps a raw payload into a `C` or touches
    /// its shard's connection list. This is the core of the ownership-transfer redesign: no
    /// `RwLock`/lock predicate over connections exists anymore, because no two threads ever share
    /// a shard's connection state at all (see claude-files/ServerOwnershipTransferPlan.md).
    raw_senders: Vec<crossbeam_channel::Sender<L::Raw>>,
    /// One load-balancing hint counter per shard, indexed the same way as `raw_senders` -- see
    /// `ShardLoad`'s doc and `choose_shard`, which is the only reason this exists.
    shard_loads: Vec<ShardLoad>,
    /// Poll handle for the listener socket -- used by `run_epoll`'s accept thread to block on
    /// real fd readiness instead of spinning/backing off (see §9 of Performance.md). Unused by
    /// the plain `run` driver. The only thread that ever touches this is the (single) accept
    /// thread, so -- like the per-shard `Poll`s used to be -- this is an `RwLock` purely for
    /// interior mutability, never real contention.
    accept_poll: RwLock<mio::Poll, TrivialPollInv>,
    /// Registry clone for `accept_poll`, kept separately since `Registry`'s methods only need
    /// `&self` -- registering the listener fd never contends with the accept thread's blocking
    /// `poll()` call the way sharing `accept_poll`'s lock would.
    accept_registry: mio::Registry,
    /// `C` no longer appears in any field (connections are never `Server` state -- see
    /// `raw_senders`'s doc), but `Server<S, L, C>` is still meaningfully parameterized by it (via
    /// the `Listener<C>`/`Channel` bounds), so it needs an explicit marker to stay a valid type
    /// parameter.
    _marker: PhantomData<C>,
}

impl<S, L, C> Server<S, L, C> where
    S: Service<Request = C::R, Response = C::S, ChanInv = C::K>,
    L: Listener<C>,
    C: Channel<Id = (u64, u64)>,
 {
    pub closed spec fn spec_server_id(self) -> u64 {
        self.service.spec_id()
    }

    /// Per-element invariant every shard's locally-owned `connected: Vec<C>` must satisfy: every
    /// channel in it was produced by (directly or via `retain`, which only removes elements)
    /// `Listener::wrap_raw` under this server's own `channel_inv`/`spec_id`. Threaded explicitly
    /// via `requires`/`ensures` on `drain_raw`/`poll_shard`/etc. instead of being carried by an
    /// `RwLock`'s lock predicate, since there is no lock anymore -- the invariant now holds by
    /// ordinary sequential Hoare-style reasoning within the single thread that owns a shard's
    /// `connected`, re-established call after call.
    pub closed spec fn shard_inv(self, connected: Seq<C>) -> bool {
        forall|idx: int|
            0 <= idx < connected.len() ==> {
                let chan = #[trigger] connected[idx];
                &&& self.service.channel_inv() == chan.constant()
                &&& self.service.spec_id() == chan.spec_id().0
            }
    }

    /// Constructs the server and returns, alongside it, one handoff-channel `Receiver` per
    /// shard. The receivers are deliberately *not* a `Server` field: keeping them out of `&self`
    /// entirely is what guarantees each one is only ever owned by a single worker thread (see
    /// `raw_senders`'s doc) -- a `Vec<Receiver<..>>` field reachable via `&self` would invite
    /// accidentally sharing one across more than one thread, silently reintroducing the
    /// cross-thread contention this redesign removes. Callers (`run`/`run_epoll`) move one
    /// receiver into each spawned worker closure.
    #[allow(unused)]
    pub fn new(service: S, listener: L, channel_inv: Ghost<C::K>, num_shards: usize) -> (r: (
        Self,
        Vec<crossbeam_channel::Receiver<L::Raw>>,
    ))
        requires
            channel_inv@ == service.channel_inv(),
            listener.spec_id() == service.spec_id(),
            num_shards > 0,
        ensures
            r.0.spec_server_id() == service.spec_id(),
            r.0.spec_num_shards() == num_shards as int,
            r.1.len() == num_shards,
    {
        let mut raw_senders: Vec<crossbeam_channel::Sender<L::Raw>> = Vec::new();
        let mut raw_receivers: Vec<crossbeam_channel::Receiver<L::Raw>> = Vec::new();
        let mut shard_loads: Vec<ShardLoad> = Vec::new();
        let mut i = 0;
        while i < num_shards
            invariant
                i <= num_shards,
                raw_senders.len() == i,
                raw_receivers.len() == i,
                shard_loads.len() == i,
            decreases num_shards - i,
        {
            let (tx, rx) = crossbeam_channel::unbounded();
            raw_senders.push(tx);
            raw_receivers.push(rx);
            shard_loads.push(ShardLoad::new());
            i += 1;
        }
        assert(raw_senders.len() == num_shards);
        assert(raw_receivers.len() == num_shards);
        assert(shard_loads.len() == num_shards);
        let accept_poll_raw = mio::Poll::new().expect("mio::Poll::new should not fail");
        let accept_registry = accept_poll_raw.registry().try_clone().expect(
            "mio::Registry::try_clone should not fail",
        );
        let accept_poll = RwLock::new(accept_poll_raw, Ghost(TrivialPollInv));
        let server = Server {
            service,
            listener,
            raw_senders,
            shard_loads,
            accept_poll,
            accept_registry,
            _marker: PhantomData,
        };
        assert(server.spec_num_shards() == num_shards as int);
        (server, raw_receivers)
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.raw_senders.len() > 0
        &&& self.listener.spec_id() == self.service.spec_id()
        &&& self.shard_loads.len() == self.raw_senders.len()
    }

    /// Number of independent shards connections are split across -- exposed so public
    /// requires/ensures clauses don't have to reach into the (module-private) `raw_senders`
    /// field.
    pub closed spec fn spec_num_shards(self) -> int {
        self.raw_senders.len() as int
    }

    /// Number of independent shards connections are split across -- also the number of
    /// request-processing worker threads the (unverified) `run()` driver spawns.
    pub fn num_shards(&self) -> (r: usize)
        ensures
            r as int == self.spec_num_shards(),
    {
        proof {
            use_type_invariant(self);
        }
        self.raw_senders.len()
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

    /// Picks which shard a newly-accepted connection should be routed to: fills already-active
    /// shards up to `MIN_CONNS_PER_SHARD_BEFORE_SPREADING` connections each, in shard-index
    /// order, before spreading further connections onto later shards, falling back to a plain
    /// modulo-hash spread of `shard_key` only once every shard is at or above the threshold. See
    /// `MIN_CONNS_PER_SHARD_BEFORE_SPREADING`'s doc for why this policy exists.
    fn choose_shard(&self, shard_key: u64) -> (shard: usize)
        requires
            self.spec_num_shards() > 0,
        ensures
            shard < self.spec_num_shards(),
    {
        proof {
            use_type_invariant(self);
        }
        let num_shards = self.raw_senders.len();
        let mut i = 0usize;
        while i < num_shards
            invariant
                i <= num_shards,
                num_shards == self.raw_senders.len(),
                self.shard_loads.len() == num_shards,
            decreases num_shards - i,
        {
            if self.shard_loads[i].load() < MIN_CONNS_PER_SHARD_BEFORE_SPREADING {
                return i;
            }
            i += 1;
        }
        (shard_key as usize) % num_shards
    }

    /// Sends a just-accepted raw connection to whichever shard's handoff channel owns it (chosen
    /// by `choose_shard`), and records the routing decision in that shard's `ShardLoad` counter.
    /// Unlike the old `accept`, this never touches anything invariant-relevant -- `L::Raw`
    /// carries no spec-relevant content at all (see `Listener::Raw`'s doc), so there is nothing
    /// to prove about the value being sent, only that a shard index is picked in bounds.
    fn dispatch_raw(&self, shard_key: u64, raw: L::Raw)
        requires
            self.spec_num_shards() > 0,
    {
        proof {
            use_type_invariant(self);
        }
        let shard = self.choose_shard(shard_key);
        self.shard_loads[shard].increment();
        let _ = self.raw_senders[shard].send(raw);
    }

    /// Drains up to 10 pending `try_accept_raw`s from the listener, dispatching each to its
    /// shard's handoff channel. Meant to be driven by a single, dedicated accept thread -- see
    /// `run()`. Carries no invariant-relevant proof obligations at all anymore: `try_accept_raw`
    /// makes no invariant-carrying claim about its `Raw` payload, and `dispatch_raw` doesn't
    /// either, so establishing the channel invariant is now entirely `wrap_raw`'s job, done by
    /// the receiving worker thread (see `drain_raw`).
    pub fn poll_accept(&self) -> bool {
        proof {
            use_type_invariant(self);
        }
        // verus does not support unbounded loops + streams probably don't/can't have specs
        // so we do this up to 10 times every time
        let mut i = 10;
        while i > 0
            invariant
                self.spec_num_shards() > 0,
            decreases i,
        {
            use crate::network::error::TryListenError;
            match self.listener.try_accept_raw() {
                Ok((client_id, raw)) => {
                    self.dispatch_raw(client_id, raw);
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

    /// Drains up to `MAX_DRAIN_BATCH` raw connections handed off by the accept thread into
    /// `connected`, wrapping each via `Listener::wrap_raw` right at drain time -- on the worker
    /// thread that will own the resulting channel, which is exactly what lets `wrap_raw`'s
    /// invariant-carrying postcondition get established without needing to prove anything about
    /// the (ghost-inert) raw payload surviving the channel handoff. Bounded (not
    /// drain-until-empty) because Verus requires a `decreases` measure and there's no way to give
    /// one to an unbounded "while channel non-empty" loop -- a raw connection not covered by this
    /// call's batch simply remains queued for the next call.
    fn drain_raw(&self, raw_rx: &crossbeam_channel::Receiver<L::Raw>, connected: &mut Vec<C>)
        requires
            self.shard_inv(old(connected)@),
        ensures
            self.shard_inv(final(connected)@),
    {
        proof {
            use_type_invariant(self);
        }
        let mut i = 0usize;
        while i < MAX_DRAIN_BATCH
            invariant
                self.shard_inv(connected@),
                self.listener.spec_id() == self.service.spec_id(),
            decreases MAX_DRAIN_BATCH - i,
        {
            match raw_rx.try_recv() {
                Ok(raw) => {
                    if let Ok(chan) = self.listener.wrap_raw(
                        raw,
                        Ghost(|l| self.service.channel_inv()),
                    ) {
                        assert(chan.constant() == self.service.channel_inv());
                        assert(chan.spec_id().0 == self.listener.spec_id());
                        assert(chan.spec_id().0 == self.service.spec_id());
                        connected.push(chan);
                        assert(self.shard_inv(connected@));
                    }
                },
                Err(_) => {
                    break;
                },
            }
            i += 1;
        }
    }

    /// Round-robins which slice of `connected` `scan_full` actually touches on a given call
    /// (bounded by `MAX_POLL_BATCH`) instead of scanning every connection every call (see §3 of
    /// Performance.md). `cursor` is a plain, ordinary local `usize` owned by the single worker
    /// thread that also owns `connected` -- unlike the old `PollCursor`, it needs no atomic or
    /// verified-interior-mutability machinery at all, because it is never reachable from any
    /// other thread even in principle (not just "conventionally" single-owner, as the old
    /// `PollCursor`'s own doc comment had to caveat).
    fn advance_cursor(cursor: &mut usize, len: usize, batch: usize) -> usize {
        if len == 0 {
            return 0;
        }
        if batch == len {
            // Every index gets visited by the caller's `(start + i) % len` loop for `i in
            // 0..batch` regardless of `start` once a single batch already covers all of
            // `connected` -- skip advancing `cursor` at all in that case, same rationale as the
            // old `PollCursor::advance`.
            return 0;
        }
        let start = *cursor % len;
        *cursor = (start.wrapping_add(batch)) % len;
        start
    }

    /// The scan-batch/handle-request/drop-dead-connections core shared by `poll_shard` (which
    /// drains new connections into `connected` first, see `drain_raw`) and `poll_shard_epoll`'s
    /// fallback path (which has already drained via `drain_raw_epoll` by the time it calls this,
    /// so doesn't drain again here). No lock of any kind: `connected`/`cursor` are owned outright
    /// by the calling thread.
    fn scan_full(
        &self,
        connected: &mut Vec<C>,
        cursor: &mut usize,
        drop_scratch: &mut HashSet<C::Id>,
        shard_load: &ShardLoad,
    )
        requires
            self.shard_inv(old(connected)@),
        ensures
            self.shard_inv(final(connected)@),
    {
        proof {
            use_type_invariant(self);
            broadcast use vstd::seq_lib::group_filter_ensures;

        }
        drop_scratch.clear();
        let len = connected.len();
        if len == 0 {
            std::thread::sleep(Duration::from_millis(EMPTY_SHARD_BACKOFF_MILLIS));
            return;
        }
        let batch = if len < MAX_POLL_BATCH {
            len
        } else {
            MAX_POLL_BATCH
        };
        let start = Self::advance_cursor(cursor, len, batch);

        let mut i = 0usize;
        while i < batch
            invariant
                self.shard_inv(connected@),
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
            assert({
                let chan = connected@[idx as int];
                &&& self.service.channel_inv() == chan.constant()
                &&& self.service.spec_id() == chan.spec_id().0
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

        if drop_scratch.is_empty() {
            return;
        }
        let ghost old_c = connected@;
        let filter_fn = |c: &C| !drop_scratch.contains(&c.id());
        connected.retain(filter_fn);
        assert(connected@.len() <= len);
        let dropped = len - connected.len();
        shard_load.decrement_by(dropped);
        proof {
            assert forall|idx| 0 <= idx < connected@.len() implies {
                let chan = #[trigger] connected@[idx];
                &&& self.service.channel_inv() == chan.constant()
                &&& self.service.spec_id() == chan.spec_id().0
            } by {
                let chan = #[trigger] connected@[idx];
                old_c.lemma_filter_contains_rev(|c| filter_fn.ensures((&c,), true), chan);
            }
        }
    }

    /// Polls, handles, and drops dead connections within a single shard. Meant to be driven by
    /// one dedicated worker thread per shard -- see `run()`. First drains any newly-handed-off
    /// connections (`drain_raw`), then scans/handles/drops via `scan_full`. No lock of any kind:
    /// `connected`/`cursor` are owned outright by the calling thread (see `Server::raw_senders`'s
    /// doc for why this is sound).
    pub fn poll_shard(
        &self,
        raw_rx: &crossbeam_channel::Receiver<L::Raw>,
        connected: &mut Vec<C>,
        cursor: &mut usize,
        drop_scratch: &mut HashSet<C::Id>,
        shard_load: &ShardLoad,
    )
        requires
            self.shard_inv(old(connected)@),
        ensures
            self.shard_inv(final(connected)@),
    {
        proof {
            use_type_invariant(self);
        }
        self.drain_raw(raw_rx, connected);
        self.scan_full(connected, cursor, drop_scratch, shard_load);
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
    /// Same as `drain_raw`, but also registers each newly-wrapped connection's fd with `registry`
    /// right when it's wrapped -- exactly once, by the same (single, owning) worker thread that
    /// creates the connection, rather than needing a separate, repeatedly-re-scanning
    /// `sync_shard_registrations` pass from a different thread (as the old RwLock-based design
    /// needed, since only the accept thread could see a connection immediately after `accept()`).
    /// Ownership transfer makes that whole self-correcting/round-robin registration-sync
    /// machinery unnecessary: there is no race to guard against anymore, since drain and register
    /// happen atomically in program order on one thread.
    fn drain_raw_epoll(
        &self,
        raw_rx: &crossbeam_channel::Receiver<L::Raw>,
        connected: &mut Vec<C>,
        registry: &mio::Registry,
    )
        requires
            self.shard_inv(old(connected)@),
        ensures
            self.shard_inv(final(connected)@),
    {
        proof {
            use_type_invariant(self);
        }
        let mut i = 0usize;
        while i < MAX_DRAIN_BATCH
            invariant
                self.shard_inv(connected@),
                self.listener.spec_id() == self.service.spec_id(),
            decreases MAX_DRAIN_BATCH - i,
        {
            match raw_rx.try_recv() {
                Ok(raw) => {
                    if let Ok(chan) = self.listener.wrap_raw(
                        raw,
                        Ghost(|l| self.service.channel_inv()),
                    ) {
                        assert(chan.constant() == self.service.channel_inv());
                        assert(chan.spec_id().0 == self.listener.spec_id());
                        assert(chan.spec_id().0 == self.service.spec_id());
                        let fd = chan.raw_fd();
                        match vlib::mio::mio_register_readable(registry, fd, fd as usize) {
                            Ok(()) => {},
                            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {},
                            Err(e) => {
                                vlib::veprintln!(
                                    "[server|{:>3}]: warning: failed to register fd {fd} with epoll: {e:?}",
                                    self.service.id(),
                                );
                            },
                        }
                        connected.push(chan);
                        assert(self.shard_inv(connected@));
                    }
                },
                Err(_) => {
                    break;
                },
            }
            i += 1;
        }
    }

    /// Like `scan_full`, but only calls `try_recv()` on connections whose fd is in `ready` --
    /// every other connection in the shard is skipped with no syscall at all, avoiding the
    /// up-to-`RECV_TIMEOUT_MILLIS` blocking cost `try_recv()` pays on a connection with nothing
    /// to read. `poll_shard_epoll` only calls this once epoll has reported specific fds as
    /// readable, so every connection it does call `try_recv()` on is expected to return data
    /// immediately, not block. See `claude-files/UdpReadRegression.md` for the regression this
    /// addresses: without this, every idle connection a shard has ever accepted (UDP never
    /// signals a connection as dead) cost a real blocking timeout on every single poll.
    fn scan_ready(
        &self,
        connected: &mut Vec<C>,
        ready: &std::collections::HashSet<i32>,
        drop_scratch: &mut HashSet<C::Id>,
        shard_load: &ShardLoad,
    )
        requires
            self.shard_inv(old(connected)@),
        ensures
            self.shard_inv(final(connected)@),
    {
        proof {
            use_type_invariant(self);
            broadcast use vstd::seq_lib::group_filter_ensures;

        }
        drop_scratch.clear();
        let len = connected.len();
        if len == 0 {
            return;
        }
        let mut i = 0usize;
        while i < len
            invariant
                self.shard_inv(connected@),
                connected@.len() == len,
            decreases len - i,
        {
            use crate::network::error::TryRecvError;
            let channel = &connected[i];
            assert(*channel == connected@[i as int]);  // TRIGGER
            assert({
                let chan = connected@[i as int];
                &&& self.service.channel_inv() == chan.constant()
                &&& self.service.spec_id() == chan.spec_id().0
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

        if drop_scratch.is_empty() {
            return;
        }
        let ghost old_c = connected@;
        let filter_fn = |c: &C| !drop_scratch.contains(&c.id());
        connected.retain(filter_fn);
        assert(connected@.len() <= len);
        let dropped = len - connected.len();
        shard_load.decrement_by(dropped);
        proof {
            assert forall|idx| 0 <= idx < connected@.len() implies {
                let chan = #[trigger] connected@[idx];
                &&& self.service.channel_inv() == chan.constant()
                &&& self.service.spec_id() == chan.spec_id().0
            } by {
                let chan = #[trigger] connected@[idx];
                old_c.lemma_filter_contains_rev(|c| filter_fn.ensures((&c,), true), chan);
            }
        }
    }

    /// Blocks (via real epoll/kqueue readiness, with `EPOLL_FALLBACK_MILLIS` as a safety-net
    /// timeout) until `shard` likely has work, drains+registers any newly-handed-off connections
    /// (`drain_raw_epoll`), then dispatches only to the connections epoll reported as ready
    /// (`scan_ready`), falling back to a full `scan_full` scan only when epoll reported nothing
    /// at all (see `scan_ready`'s doc and `claude-files/UdpReadRegression.md`). Meant to be driven
    /// by `run_epoll`'s per-shard worker thread in place of `poll_shard` alone. No lock of any
    /// kind: `connected`/`cursor`/`registry`/`poll` are all owned outright by the calling thread.
    #[allow(clippy::too_many_arguments)]
    pub fn poll_shard_epoll(
        &self,
        raw_rx: &crossbeam_channel::Receiver<L::Raw>,
        connected: &mut Vec<C>,
        cursor: &mut usize,
        registry: &mio::Registry,
        poll: &mut mio::Poll,
        events_scratch: &mut mio::Events,
        ready_scratch: &mut std::collections::HashSet<i32>,
        drop_scratch: &mut HashSet<C::Id>,
        shard_load: &ShardLoad,
    )
        requires
            self.shard_inv(old(connected)@),
        ensures
            self.shard_inv(final(connected)@),
    {
        proof {
            use_type_invariant(self);
        }
        let _ = poll.poll(events_scratch, Some(Duration::from_millis(EPOLL_FALLBACK_MILLIS)));
        vlib::mio::mio_fill_ready_fds(events_scratch, ready_scratch);
        self.drain_raw_epoll(raw_rx, connected, registry);
        if ready_scratch.is_empty() {
            // Nothing reported ready before the fallback timeout elapsed -- either the shard is
            // genuinely idle, or a just-drained connection hasn't been picked up by a subsequent
            // `Poll::poll` yet. Fall back to the full blind scan so such stragglers are still
            // eventually reached. This is the only place the O(shard size) * RECV_TIMEOUT_MILLIS
            // blind scan runs, and it only runs when nothing else was pending anyway -- see
            // `claude-files/UdpReadRegression.md` for why the previous unconditional-every-call
            // version of this was the regression.
            self.scan_full(connected, cursor, drop_scratch, shard_load);
            return;
        }
        self.scan_ready(connected, ready_scratch, drop_scratch, shard_load)
    }

    /// Blocks (via real epoll/kqueue readiness on the listener fd, with the same fallback
    /// timeout) until a connection is likely pending, then runs the existing, unmodified
    /// `poll_accept` -- registering the listener fd itself is idempotent (tolerates
    /// already-registered) so no separate one-time setup is needed. Meant to be driven by
    /// `run_epoll`'s accept thread in place of `poll_accept` alone. No longer needs to sync any
    /// per-shard epoll registrations after accepting (contrast with the old RwLock-based design's
    /// `sync_shard_registrations` loop here): registration now happens inline in each worker
    /// thread's own `drain_raw_epoll`, exactly once per connection, so the accept thread has
    /// nothing shard-related left to do after accepting.
    pub fn poll_accept_epoll(&self, events_scratch: &mut mio::Events) -> bool
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
        let _ = poll.poll(events_scratch, Some(Duration::from_millis(EPOLL_FALLBACK_MILLIS)));
        poll_handle.release_write(poll);
        self.poll_accept()
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
    ///
    /// `raw_receivers` must be exactly the `Vec` returned alongside `self` by `Server::new` --
    /// one receiver is moved into each spawned worker closure, which then owns it (and its
    /// shard's `connected: Vec<C>`) for the lifetime of the thread; no other thread ever touches
    /// either again.
    pub fn run(&self, raw_receivers: Vec<crossbeam_channel::Receiver<L::Raw>>) {
        std::thread::scope(|s| {
            s.spawn(|| while self.poll_accept() {});
            for (shard, raw_rx) in raw_receivers.into_iter().enumerate() {
                s.spawn(move || {
                    let mut connected: Vec<C> = Vec::new();
                    let mut cursor: usize = 0;
                    // Owned by this shard's single dedicated worker thread and reused across
                    // every `poll_shard` call instead of allocating a fresh `HashSet` each time
                    // (the overwhelmingly common case is nothing to drop) -- see
                    // claude-files/UdpConcurrencyBottleneck.md's allocation-cleanup follow-up.
                    let mut drop_scratch = std::collections::HashSet::new();
                    let shard_load = &self.shard_loads[shard];
                    loop {
                        self.poll_shard(
                            &raw_rx,
                            &mut connected,
                            &mut cursor,
                            &mut drop_scratch,
                            shard_load,
                        );
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
    ///
    /// Same `raw_receivers` contract as `run`. Each worker thread now also owns its own
    /// `mio::Poll`/`Registry` pair as plain local state -- unlike the old RwLock-wrapped
    /// `shard_polls`/`shard_registries` `Server` fields these replace, nothing else ever needs to
    /// reach them, so there is no reason for them to be anything but ordinary locals anymore.
    pub fn run_epoll(&self, raw_receivers: Vec<crossbeam_channel::Receiver<L::Raw>>) {
        std::thread::scope(|s| {
            s.spawn(|| {
                // Owned by the accept thread and reused across calls instead of allocating a
                // fresh `mio::Events` every poll -- same rationale as `ready_scratch`/
                // `drop_scratch` below (mio's own docs recommend exactly this: "a single
                // `Events` instance is created ... and reused on each call to `Poll::poll`").
                let mut events_scratch = mio::Events::with_capacity(1);
                while self.poll_accept_epoll(&mut events_scratch) {}
            });
            for (shard, raw_rx) in raw_receivers.into_iter().enumerate() {
                s.spawn(move || {
                    let mut connected: Vec<C> = Vec::new();
                    let mut cursor: usize = 0;
                    let poll = mio::Poll::new().expect("mio::Poll::new should not fail");
                    let registry = poll
                        .registry()
                        .try_clone()
                        .expect("mio::Registry::try_clone should not fail");
                    let mut poll = poll;
                    // Same rationale as `run`'s `drop_scratch` -- owned by this shard's single
                    // worker thread, reused across calls instead of allocating fresh every poll.
                    let mut events_scratch = mio::Events::with_capacity(MAX_POLL_BATCH);
                    let mut ready_scratch = std::collections::HashSet::new();
                    let mut drop_scratch = std::collections::HashSet::new();
                    let shard_load = &self.shard_loads[shard];
                    loop {
                        self.poll_shard_epoll(
                            &raw_rx,
                            &mut connected,
                            &mut cursor,
                            &registry,
                            &mut poll,
                            &mut events_scratch,
                            &mut ready_scratch,
                            &mut drop_scratch,
                            shard_load,
                        );
                    }
                });
            }
        });
    }
}
