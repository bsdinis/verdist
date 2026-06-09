use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants;
#[cfg(verus_only)]
use crate::invariants::committed_to::WriteCommitment;
#[cfg(verus_only)]
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::StateInvariant;
use crate::proto::GetRequest;
use crate::proto::GetTimestampRequest;
use crate::proto::Request;
use crate::proto::RequestInner;
use crate::proto::Response;
use crate::proto::ResponseInner;
use crate::proto::WriteRequest;
#[cfg(verus_only)]
use crate::proto::WriteResponse;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::server::register::MonotonicRegister;
#[cfg(verus_only)]
use crate::server::register::MonotonicRegisterInner;
#[cfg(verus_only)]
use crate::timestamp::Timestamp;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use verdist::network::channel::Channel;
#[cfg(verus_only)]
use verdist::network::channel::ChannelInvariant;
use verdist::network::channel::Listener;
#[cfg(verus_only)]
use verdist::network::modelled::ModelledListener;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;

use std::collections::HashSet;
use std::sync::Arc;

#[cfg(verus_only)]
use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::RwLock;
use vstd::rwlock::RwLockPredicate;
#[cfg(verus_only)]
use vstd::std_specs::iter::IteratorSpec;

pub mod register;

verus! {

#[allow(dead_code)]
struct LowerBoundPredicate {
    #[allow(dead_code)]
    loc: Loc,
}

impl RwLockPredicate<Tracked<MonotonicTimestampResource>> for LowerBoundPredicate {
    closed spec fn inv(self, lb: Tracked<MonotonicTimestampResource>) -> bool {
        &&& lb@@ is LowerBound
        &&& lb@.loc() == self.loc
    }
}

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
pub struct RegisterServer<L, C, ML, RL> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    /// ID of the server
    id: u64,
    /// Listener channel
    listener: L,
    /// Connected clients
    connected: RwLock<Vec<C>, ServerInv>,
    /// Register state
    register: MonotonicRegister<ML, RL>,
}

impl<L, C, ML, RL> RegisterServer<L, C, ML, RL> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(listener: L, id: u64, state_inv: Tracked<Arc<StateInvariant<ML, RL>>>) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
            state_inv@.constant().server_locs.contains_key(id),
    {
        let empty = Vec::new();
        let ghost channel_inv = ChannelInv::from_state_pred(state_inv@.constant());
        let ghost server_inv = ServerInv { channel_inv, server_id: id };
        assert(server_inv.inv(empty));
        RegisterServer {
            id,
            register: MonotonicRegister::new(id, state_inv),
            connected: RwLock::new(empty, Ghost(server_inv)),
            listener,
        }
    }

    pub closed spec fn spec_server_id(self) -> u64 {
        self.id
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.register.id() == self.id
        &&& self.register.commitment_id() == self.commitment_id()
        &&& self.register.server_token_id() == self.server_token_id()
        &&& self.connected.pred().server_id == self.id
        &&& self.server_locs().contains_key(self.id)
        &&& self.server_locs()[self.id] == self.register.resource_loc()
    }

    pub fn server_id(&self) -> (r: u64)
        ensures
            r == self.spec_server_id(),
    {
        self.id
    }

    closed spec fn commitment_id(self) -> Loc {
        self.connected.pred().channel_inv.commitment_id
    }

    closed spec fn server_token_id(self) -> Loc {
        self.connected.pred().channel_inv.server_tokens_id
    }

    closed spec fn server_locs(self) -> Map<u64, Loc> {
        self.connected.pred().channel_inv.server_locs
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

    fn handle_get(&self, req: GetRequest) -> (r: ResponseInner)
        requires
            req.servers().locs() == self.server_locs(),
        ensures
            r is Get,
            ({
                let resp = r->Get_0;
                &&& resp.server_id() == self.id
                &&& resp.spec_commitment().id() == self.commitment_id()
                &&& resp.server_token_id() == self.server_token_id()
                &&& self.server_locs().contains_key(resp.server_id())
                &&& self.server_locs()[resp.server_id()] == resp.loc()
                &&& req.servers().contains_key(resp.server_id())
                &&& req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
            }),
    {
        proof {
            use_type_invariant(self);
        }
        ResponseInner::Get(self.register.read(req))
    }

    fn handle_get_timestamp(&self, req: GetTimestampRequest) -> (r: ResponseInner)
        requires
            req.servers().locs() == self.server_locs(),
        ensures
            r is GetTimestamp,
            ({
                let resp = r->GetTimestamp_0;
                &&& resp.server_id() == self.id
                &&& resp.server_token_id() == self.server_token_id()
                &&& self.server_locs().contains_key(resp.server_id())
                &&& self.server_locs()[resp.server_id()] == resp.loc()
                &&& req.servers().contains_key(resp.server_id())
                &&& req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
            }),
    {
        proof {
            use_type_invariant(self);
        }
        ResponseInner::GetTimestamp(self.register.read_timestamp(req))
    }

    fn handle_write(&self, req: WriteRequest) -> (r: ResponseInner)
        requires
            req.servers().locs() == self.server_locs(),
            req.commitment_id() == self.commitment_id(),
        ensures
            r is Write,
            ({
                let resp = r->Write_0;
                &&& resp.server_id() == self.id
                &&& resp.server_token_id() == self.server_token_id()
                &&& self.server_locs().contains_key(resp.server_id())
                &&& self.server_locs()[resp.server_id()] == resp.loc()
                &&& req.servers().contains_key(resp.server_id())
                &&& req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
                &&& req.spec_timestamp() <= resp.spec_timestamp()
            }),
    {
        proof {
            use_type_invariant(self);
        }
        ResponseInner::Write(self.register.write(req))
    }

    fn handle(
        &self,
        request: Request,
        #[allow(unused_variables)]
        client_id: u64,
    ) -> (r: Response)
        requires
            request.request_key() == (client_id, request.spec_tag()),
            request.req_type() is Get ==> {
                let get_req = request.get();
                &&& get_req.servers().locs() == self.server_locs()
            },
            request.req_type() is GetTimestamp ==> {
                let get_ts_req = request.get_timestamp();
                &&& get_ts_req.servers().locs() == self.server_locs()
            },
            request.req_type() is Write ==> {
                let write_req = request.write();
                &&& write_req.servers().locs() == self.server_locs()
                &&& write_req.commitment_id() == self.commitment_id()
            },
        ensures
            r.spec_tag() == request.spec_tag(),
            r.request_id() == request.request_id(),
            r.request_key() == request.request_key(),
            r.request().spec_eq(request.request()),
            r.server_id() == self.id,
            request.req_type() == r.req_type(),
            r.req_type() is Get ==> ({
                let get_req = request.get();
                let resp = r.get();
                &&& resp.spec_commitment().id() == self.commitment_id()
                &&& resp.server_token_id() == self.server_token_id()
                &&& self.server_locs().contains_key(resp.server_id())
                &&& self.server_locs()[resp.server_id()] == resp.loc()
                &&& get_req.servers().contains_key(resp.server_id())
                &&& get_req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
            }),
            r.req_type() is GetTimestamp ==> ({
                let get_ts_req = request.get_timestamp();
                let resp = r.get_timestamp();
                &&& resp.server_token_id() == self.server_token_id()
                &&& self.server_locs().contains_key(resp.server_id())
                &&& self.server_locs()[resp.server_id()] == resp.loc()
                &&& get_ts_req.servers().contains_key(resp.server_id())
                &&& get_ts_req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
            }),
            r.req_type() is Write ==> ({
                let write_req = request.write();
                let resp = r.write();
                &&& resp.server_token_id() == self.server_token_id()
                &&& self.server_locs().contains_key(resp.server_id())
                &&& self.server_locs()[resp.server_id()] == resp.loc()
                &&& write_req.servers().contains_key(resp.server_id())
                &&& write_req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
            }),
    {
        // vlib::veprintln!("[server|{:>3}]: received req: {:?}", self.id, request);
        let (request_id, request_inner, request_proof) = request.destruct();
        let resp_inner = match request_inner {
            RequestInner::Get(req) => self.handle_get(req),
            RequestInner::GetTimestamp(req) => self.handle_get_timestamp(req),
            RequestInner::Write(req) => self.handle_write(req),
        };

        proof {
            if request_inner is Get {
                let get_req = request_inner->Get_0;
                let proof_get_req = request_proof@.get();
                assume(proof_get_req.servers().inv());  // TODO(verus): type invariants on spec items
                assume(get_req.servers().inv());  // TODO(verus): type invariants on spec items
                GetRequest::lemma_spec_eq(proof_get_req, get_req);
                ServerUniverse::lemma_eq(proof_get_req.servers(), get_req.servers());
                proof_get_req.servers().lemma_locs();
            }
            if request_inner is GetTimestamp {
                let get_ts_req = request_inner->GetTimestamp_0;
                let proof_get_ts_req = request_proof@.get_timestamp();
                assume(proof_get_ts_req.servers().inv());  // TODO(verus): type invariants on spec items
                assume(get_ts_req.servers().inv());  // TODO(verus): type invariants on spec items
                GetTimestampRequest::lemma_spec_eq(proof_get_ts_req, get_ts_req);
                ServerUniverse::lemma_eq(proof_get_ts_req.servers(), get_ts_req.servers());
                proof_get_ts_req.servers().lemma_locs();
            }
            if request_inner is Write {
                let write_req = request_inner->Write_0;
                let proof_write_req = request_proof@.write();
                assume(proof_write_req.servers().inv());  // TODO(verus): type invariants on spec items
                assume(write_req.servers().inv());  // TODO(verus): type invariants on spec items
                WriteRequest::lemma_spec_eq(proof_write_req, write_req);
                ServerUniverse::lemma_eq(proof_write_req.servers(), write_req.servers());
                proof_write_req.servers().lemma_locs();
            }
        }

        let r = Response::new(request_id, resp_inner, request_proof);
        proof {
            RequestInner::spec_eq_refl(r.request());
        }
        // vlib::veprintln!("[server|{:>3}]: sending resp: {:?}", self.id, r);
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
                        &&& it.snapshot@.remaining()[idx] == chan
                        &&& connected_pred.channel_inv == chan.constant()
                        &&& connected_pred.server_id == chan.spec_id().0
                    },
        {
            if idx < connected.len() {
                use verdist::network::error::TryRecvError;
                assert(channel == connected@[it.index@]);  // TRIGGER
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

#[allow(unused_variables)]
pub fn create_server<L, C, ML, RL>(
    server_ids: &HashSet<u64>,
    my_server_id: u64,
    listener: L,
) -> RegisterServer<L, C, ML, RL> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    requires
        server_ids@.contains(my_server_id),
{
    let tracked state_inv;
    proof {
        let tracked (s, v) = invariants::get_system_state::<ML, RL>(server_ids@);
        state_inv = s;
    }
    RegisterServer::new(listener, my_server_id, Tracked(state_inv))
}

} // verus!
