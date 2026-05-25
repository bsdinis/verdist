use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants;
use crate::invariants::StateInvariant;
use crate::proto::EchoRequest;
use crate::proto::EchoResponse;
use crate::proto::Request;
use crate::proto::RequestInner;
use crate::proto::Response;
use crate::proto::ResponseInner;

use verdist::network::channel::Channel;
#[cfg(verus_only)]
use verdist::network::channel::ChannelInvariant;
use verdist::network::channel::Listener;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;

use std::collections::HashSet;
use std::sync::Arc;

#[cfg(verus_only)]
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;
use vstd::rwlock::RwLock;
#[cfg(verus_only)]
use vstd::rwlock::RwLockPredicate;

verus! {

pub struct ServerInv {
    pub channel_inv: ChannelInv,
    pub server_id: u64,
}

impl<C> vstd::rwlock::RwLockPredicate<Vec<C>> for ServerInv where
    C: Channel<Id = (u64, u64), R = Request, S = Response, K = ChannelInv>,
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

#[verifier::reject_recursive_types(C)]
pub struct EchoServer<L, C> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
 {
    /// ID of the server
    id: u64,
    /// Listener channel
    listener: L,
    /// Connected clients
    connected: RwLock<Vec<C>, ServerInv>,
}

impl<L, C> EchoServer<L, C> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
 {
    #[allow(unused)]
    pub fn new(listener: L, id: u64, state_inv: Tracked<Arc<StateInvariant>>) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
        ensures
            r.spec_server_id() == id,
    {
        let empty = Vec::new();
        let ghost channel_inv = ChannelInv::from_state_pred(state_inv@.constant());
        let ghost server_inv = ServerInv { channel_inv, server_id: id };
        assert(server_inv.inv(empty));
        EchoServer { id, connected: RwLock::new(empty, Ghost(server_inv)), listener }
    }

    pub closed spec fn spec_server_id(self) -> u64 {
        self.id
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.connected.pred().server_id == self.id
    }

    pub fn server_id(&self) -> (r: u64)
        ensures
            r == self.spec_server_id(),
    {
        self.id
    }

    fn accept(&self, channel: C)
        requires
            channel.constant() == self.connected.pred().channel_inv,
    {
        proof {
            use_type_invariant(self);
        }
        let (mut guard, handle) = self.connected.acquire_write();
        assume(channel.spec_id().0 == self.id);  // TODO(connector)
        guard.push(channel);
        assert(ServerInv::inv(self.connected.pred(), guard));
        handle.release_write(guard);
    }

    fn handle_echo(&self, req: EchoRequest) -> (r: ResponseInner)
        ensures
            r is Echo,
            ({
                let resp = r->Echo_0;
                &&& resp.spec_message() == req.spec_message()
            }),
    {
        proof {
            use_type_invariant(self);
        }
        ResponseInner::Echo(EchoResponse::new(req.message()))
    }

    fn handle(
        &self,
        request: Request,
        #[allow(unused_variables)]
        client_id: u64,
    ) -> (r: Response)
        requires
            request.request_key() == (client_id, request.spec_tag()),
        ensures
            r.spec_tag() == request.spec_tag(),
            r.request_id() == request.request_id(),
            r.request_key() == request.request_key(),
            r.request().spec_eq(request.request()),
            request.req_type() == r.req_type(),
            r.req_type() is Echo ==> ({
                let echo_req = request.echo();
                let resp = r.echo();
                &&& echo_req.spec_message() == resp.spec_message()
            }),
    {
        vlib::veprintln!("[server|{:>3}]: received req: {:?}", self.id, request);
        let (request_id, request_inner, request_proof) = request.destruct();
        let resp_inner = match request_inner {
            RequestInner::Echo(req) => self.handle_echo(req),
        };

        proof {
            if request_inner is Echo {
                let echo_req = request_inner->Echo_0;
                let proof_echo_req = request_proof@.value()->Echo_0;
                EchoRequest::lemma_spec_eq(proof_echo_req, echo_req);
            }
        }

        let r = Response::new(request_id, resp_inner, request_proof);
        proof {
            RequestInner::spec_eq_refl(r.request());
        }
        vlib::veprintln!("[server|{:>3}]: sending resp: {:?}", self.id, r);
        r
    }

    pub fn poll(&self) -> bool {
        proof {
            use_type_invariant(self);
            broadcast use vstd::seq_lib::group_filter_ensures;

        }
        // verus does not support unbounded loops + streams probably don't/can't have specs
        // so we do this up to 10 times every time
        let mut i = 10;
        while i > 0
            decreases i,
        {
            use verdist::network::error::TryListenError;
            match self.listener.try_accept(Ghost(|l| self.connected.pred().channel_inv)) {
                Ok(channel) => {
                    assert(channel.constant() == self.connected.pred().channel_inv);
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

        let mut drop = HashSet::new();
        let (mut connected, handle) = self.connected.acquire_write();

        let ghost connected_pred = self.connected.pred();
        let iterator = connected.iter();
        #[allow(unused_variables)]
        let mut idx = 0usize;
        #[allow(unused_assignments)]
        for channel in it: iterator
            invariant
                self.connected.pred() == connected_pred,
                connected_pred.server_id == self.id,
                idx == it.index,
                forall|idx|
                    0 <= idx < connected@.len() ==> {
                        let chan = #[trigger] connected@[idx];
                        &&& connected_pred.channel_inv == chan.constant()
                        &&& connected_pred.server_id == chan.spec_id().0
                    },
        {
            use verdist::network::error::TryRecvError;
            match channel.try_recv() {
                Ok(req) => {
                    assert(C::K::recv_inv(channel.constant(), channel.spec_id(), req));
                    let response = self.handle(req, channel.id().1);
                    assert(C::K::send_inv(channel.constant(), channel.spec_id(), response));
                    if channel.send(&response).is_err() {
                        drop.insert(channel.id());
                    }
                },
                Err(TryRecvError::Empty) => {},
                Err(_) => {
                    drop.insert(channel.id());
                },
            }
            assume(idx < usize::MAX);  // XXX: overflow
            idx += 1;
        }

        let ghost old_c = connected@;
        let filter_fn = |c: &C| !drop.contains(&c.id());
        connected.retain(filter_fn);
        proof {
            let ghost server_inv = self.connected.pred();
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

pub fn create_server<L, C>(server_id: u64, listener: L) -> EchoServer<L, C> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
 {
    let tracked state_inv;
    proof {
        state_inv = invariants::get_system_state();
    }
    EchoServer::new(listener, server_id, Tracked(state_inv))
}

} // verus!
