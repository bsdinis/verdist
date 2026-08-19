use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants;
#[cfg(verus_only)]
use crate::invariants::quorum::ServerUniverseLb;
use crate::proto::GetRequest;
use crate::proto::GetTimestampRequest;
use crate::proto::Request;
use crate::proto::RequestInner;
use crate::proto::Response;
use crate::proto::ResponseInner;
use crate::proto::WriteRequest;
#[cfg(verus_only)]
use crate::proto::WriteResponse;
use crate::server::register::MonotonicRegister;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use verdist::network::channel::Channel;
use verdist::network::channel::Listener;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;
use verdist::service::Server;
use verdist::service::Service;

use std::collections::HashSet;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

pub mod register;

verus! {

#[verifier::reject_recursive_types(ML)]
#[verifier::reject_recursive_types(RL)]
pub struct RegisterService<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    /// ID of the server
    id: u64,
    /// Register state
    register: MonotonicRegister<ML, RL>,
    /// Channel invariant this server's connections are held under
    #[allow(dead_code)]
    channel_inv: Ghost<ChannelInv>,
}

impl<ML, RL> RegisterService<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(id: u64, register: MonotonicRegister<ML, RL>, channel_inv: Ghost<ChannelInv>) -> (r:
        Self)
        requires
            register.id() == id,
            channel_inv@.commitment_id == register.commitment_id(),
            channel_inv@.server_tokens_id == register.server_token_id(),
            channel_inv@.server_locs.contains_key(id),
            channel_inv@.server_locs[id] == register.resource_loc(),
        ensures
            r.spec_id() == id,
            r.channel_inv() == channel_inv@,
    {
        RegisterService { id, register, channel_inv }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.register.id() == self.id
        &&& self.channel_inv@.commitment_id == self.register.commitment_id()
        &&& self.channel_inv@.server_tokens_id == self.register.server_token_id()
        &&& self.channel_inv@.server_locs.contains_key(self.id)
        &&& self.channel_inv@.server_locs[self.id] == self.register.resource_loc()
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.register.commitment_id()
    }

    pub closed spec fn server_token_id(self) -> Loc {
        self.register.server_token_id()
    }

    pub closed spec fn server_locs(self) -> Map<u64, Loc> {
        self.channel_inv@.server_locs
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
}

impl<ML, RL> Service for RegisterService<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    type Request = Request;

    type Response = Response;

    type ChanInv = ChannelInv;

    closed spec fn spec_id(self) -> u64 {
        self.id
    }

    closed spec fn channel_inv(self) -> ChannelInv {
        self.channel_inv@
    }

    open spec fn pre(self, channel_id: (u64, u64), request: Request) -> bool {
        &&& request.request_key() == (channel_id.1, request.spec_tag())
        &&& request.req_type() is Get ==> {
            let get_req = request.get();
            &&& get_req.servers().locs() == self.server_locs()
        }
        &&& request.req_type() is GetTimestamp ==> {
            let get_ts_req = request.get_timestamp();
            &&& get_ts_req.servers().locs() == self.server_locs()
        }
        &&& request.req_type() is Write ==> {
            let write_req = request.write();
            &&& write_req.servers().locs() == self.server_locs()
            &&& write_req.commitment_id() == self.commitment_id()
        }
    }

    open spec fn post(self, channel_id: (u64, u64), request: Request, response: Response) -> bool {
        &&& response.spec_tag() == request.spec_tag()
        &&& response.request_id() == request.request_id()
        &&& response.request_key() == request.request_key()
        &&& response.request().spec_eq(request.request())
        &&& response.server_id() == self.spec_id()
        &&& request.req_type() == response.req_type()
        &&& (response.req_type() is Get ==> {
            let get_req = request.get();
            let resp = response.get();
            &&& resp.spec_commitment().id() == self.commitment_id()
            &&& resp.server_token_id() == self.server_token_id()
            &&& self.server_locs().contains_key(resp.server_id())
            &&& self.server_locs()[resp.server_id()] == resp.loc()
            &&& get_req.servers().contains_key(resp.server_id())
            &&& get_req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
        })
        &&& (response.req_type() is GetTimestamp ==> {
            let get_ts_req = request.get_timestamp();
            let resp = response.get_timestamp();
            &&& resp.server_token_id() == self.server_token_id()
            &&& self.server_locs().contains_key(resp.server_id())
            &&& self.server_locs()[resp.server_id()] == resp.loc()
            &&& get_ts_req.servers().contains_key(resp.server_id())
            &&& get_ts_req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
        })
        &&& (response.req_type() is Write ==> {
            let write_req = request.write();
            let resp = response.write();
            &&& resp.server_token_id() == self.server_token_id()
            &&& self.server_locs().contains_key(resp.server_id())
            &&& self.server_locs()[resp.server_id()] == resp.loc()
            &&& write_req.servers().contains_key(resp.server_id())
            &&& write_req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
        })
    }

    proof fn recv_implies_pre(tracked &self, channel_id: (u64, u64), request: Request) {
        use_type_invariant(self);
        assert(crate::channel::chan_request_inv(
            self.channel_inv(),
            channel_id.1,
            channel_id.0,
            request,
        ));
        if request.req_type() is Get {
            assert(request.get().servers().locs() == self.server_locs());
        }
        if request.req_type() is GetTimestamp {
            assert(request.get_timestamp().servers().locs() == self.server_locs());
        }
        if request.req_type() is Write {
            assert(request.write().servers().locs() == self.server_locs());
            assert(request.write().commitment_id() == self.commitment_id());
        }
    }

    proof fn post_implies_send(
        tracked &self,
        channel_id: (u64, u64),
        request: Request,
        response: Response,
    ) {
        use_type_invariant(self);
        assert(crate::channel::chan_request_inv(
            self.channel_inv(),
            channel_id.1,
            channel_id.0,
            request,
        ));
        assert(crate::channel::chan_response_inv(
            self.channel_inv(),
            channel_id.1,
            channel_id.0,
            response,
        ));
    }

    fn handle(
        &self,
        #[allow(unused_variables)]
        channel_id: (u64, u64),
        request: Request,
    ) -> (r: Response) {
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
                request_proof.borrow().lemma_get_inv();
                GetRequest::lemma_spec_eq(proof_get_req, get_req);
                get_req.servers().lemma_eq_preserves_inv(proof_get_req.servers());
                ServerUniverseLb::lemma_eq(proof_get_req.servers(), get_req.servers());
                proof_get_req.servers().lemma_locs();
                get_req.servers().lemma_locs();
                proof_get_req.servers().lemma_dom();
                get_req.servers().lemma_dom();
            }
            if request_inner is GetTimestamp {
                let get_ts_req = request_inner->GetTimestamp_0;
                let proof_get_ts_req = request_proof@.get_timestamp();
                request_proof.borrow().lemma_get_timestamp_inv();
                GetTimestampRequest::lemma_spec_eq(proof_get_ts_req, get_ts_req);
                get_ts_req.servers().lemma_eq_preserves_inv(proof_get_ts_req.servers());
                ServerUniverseLb::lemma_eq(proof_get_ts_req.servers(), get_ts_req.servers());
                proof_get_ts_req.servers().lemma_locs();
                get_ts_req.servers().lemma_locs();
                proof_get_ts_req.servers().lemma_dom();
                get_ts_req.servers().lemma_dom();
            }
            if request_inner is Write {
                let write_req = request_inner->Write_0;
                let proof_write_req = request_proof@.write();
                request_proof.borrow().lemma_write_inv();
                WriteRequest::lemma_spec_eq(proof_write_req, write_req);
                write_req.servers().lemma_eq_preserves_inv(proof_write_req.servers());
                ServerUniverseLb::lemma_eq(proof_write_req.servers(), write_req.servers());
                proof_write_req.servers().lemma_locs();
                write_req.servers().lemma_locs();
                proof_write_req.servers().lemma_dom();
                write_req.servers().lemma_dom();
            }
        }

        let r = Response::new(request_id, resp_inner, request_proof);
        proof {
            RequestInner::spec_eq_refl(r.request());
        }
        // vlib::veprintln!("[server|{:>3}]: sending resp: {:?}", self.id, r);
        r
    }

    fn id(&self) -> (r: u64) {
        self.id
    }
}

pub type RegisterServer<L, C, ML, RL> = Server<RegisterService<ML, RL>, L, C>;

#[allow(unused_variables)]
pub fn create_server<L, C, ML, RL>(
    server_ids: &HashSet<u64>,
    my_server_id: u64,
    listener: L,
    num_threads: usize,
) -> RegisterServer<L, C, ML, RL> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    requires
        server_ids@.contains(my_server_id),
        num_threads > 0,
{
    let tracked state_inv;
    proof {
        let tracked (s, v) = invariants::get_system_state::<ML, RL>(server_ids@);
        state_inv = s;
    }
    let state_inv = Tracked(state_inv);
    let ghost channel_inv = ChannelInv::from_state_pred(state_inv@.constant());
    let register = MonotonicRegister::new(my_server_id, state_inv);
    let service = RegisterService::new(my_server_id, register, Ghost(channel_inv));
    Server::new(service, listener, Ghost(channel_inv), num_threads)
}

} // verus!
