use std::collections::HashSet;

use vstd::prelude::*;
use vstd::rwlock::RwLock;
#[cfg(verus_only)]
use vstd::rwlock::RwLockPredicate;
#[cfg(verus_only)]
use vstd::std_specs::iter::IteratorSpec;

use crate::network::channel::{Channel, ChannelInvariant, Listener};

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
        let mut i = 0;
        while i < num_shards
            invariant
                connected.len() == i,
                forall|j: int|
                    0 <= j < connected@.len() ==> #[trigger] connected@[j].pred() == connected_inv,
            decreases num_shards - i,
        {
            let empty: Vec<C> = Vec::new();
            assert(connected_inv.inv(empty));
            connected.push(RwLock::new(empty, Ghost(connected_inv)));
            i += 1;
        }
        Server { service, listener, connected }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.connected.len() > 0
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
    /// still register new connections in this shard, and (once other shards stop sharing this
    /// lock -- N/A here, locks are per-shard) nothing else in the shard is blocked by a slow
    /// handler. The write lock is only taken afterwards, and only for the `retain()` that drops
    /// dead connections.
    pub fn poll_shard(&self, shard: usize) -> bool
        requires
            (shard as int) < self.spec_num_shards(),
    {
        proof {
            use_type_invariant(self);
            broadcast use vstd::seq_lib::group_filter_ensures;

        }
        let mut drop = HashSet::new();
        let read_handle = self.connected[shard].acquire_read();

        let ghost connected_pred = self.connected[shard as int].pred();
        assert(connected_pred.server_id == self.service.spec_id());
        assert(connected_pred.channel_inv == self.service.channel_inv());
        let connected = read_handle.borrow();
        let iterator = connected.iter();
        #[allow(unused_variables)]
        let mut idx = 0usize;
        #[allow(unused_assignments, clippy::explicit_counter_loop)]
        for channel in it: iterator
            invariant
                self.connected[shard as int].pred() == connected_pred,
                connected_pred.server_id == self.service.spec_id(),
                connected_pred.channel_inv == self.service.channel_inv(),
                idx == it.index,
                forall|idx|
                    0 <= idx < connected@.len() ==> {
                        let chan = #[trigger] connected@[idx];
                        &&& it.snapshot@.remaining()[idx] == chan
                        &&& connected_pred.channel_inv == chan.constant()
                        &&& connected_pred.server_id == chan.spec_id().0
                    },
        {
            if idx < connected.len() {
                use crate::network::error::TryRecvError;
                assert(channel == connected@[it.index@]);  // TRIGGER
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
                            drop.insert(channel.id());
                        }
                    },
                    Err(TryRecvError::Empty) => {},
                    Err(e) => {
                        vlib::veprintln!("[server|{:>3}]: dropping channel: {e:?}", self.service.id());
                        drop.insert(channel.id());
                    },
                }
            }
            assume(idx < usize::MAX);  // XXX: overflow
            idx += 1;
        }
        read_handle.release_read();

        if drop.is_empty() {
            return true;
        }

        let (mut connected, handle) = self.connected[shard].acquire_write();
        let ghost old_c = connected@;
        let filter_fn = |c: &C| !drop.contains(&c.id());
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
                s.spawn(move || loop {
                    self.poll_shard(shard);
                });
            }
        });
    }
}
