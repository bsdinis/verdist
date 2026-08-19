#[cfg(verus_only)]
use crate::invariants;
use crate::proto::EchoRequest;
use crate::proto::EchoResponse;
use crate::proto::Request;
use crate::proto::RequestInner;
use crate::proto::Response;
use crate::proto::ResponseInner;

use crate::channel::ChannelInv;

use verdist::network::channel::Channel;
#[cfg(verus_only)]
use verdist::network::channel::ChannelInvariant;
use verdist::network::channel::Listener;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;
use verdist::service::Server;
use verdist::service::Service;

use vstd::prelude::*;

verus! {

pub struct EchoService {
    /// ID of the server
    id: u64,
    /// Channel invariant this server's connections are held under
    #[allow(dead_code)]
    channel_inv: Ghost<ChannelInv>,
}

impl EchoService {
    #[allow(unused)]
    pub fn new(id: u64, channel_inv: Ghost<ChannelInv>) -> (r: Self)
        ensures
            r.spec_id() == id,
            r.channel_inv() == channel_inv@,
    {
        EchoService { id, channel_inv }
    }

    fn handle_echo(&self, req: EchoRequest) -> (r: ResponseInner)
        ensures
            r is Echo,
            ({
                let resp = r->Echo_0;
                &&& resp.spec_message() == req.spec_message()
            }),
    {
        ResponseInner::Echo(EchoResponse::new(req.message()))
    }
}

impl Service for EchoService {
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
        request.request_key() == (channel_id.1, request.spec_tag())
    }

    open spec fn post(self, channel_id: (u64, u64), request: Request, response: Response) -> bool {
        &&& response.spec_tag() == request.spec_tag()
        &&& response.request_id() == request.request_id()
        &&& response.request_key() == request.request_key()
        &&& response.request().spec_eq(request.request())
        &&& request.req_type() == response.req_type()
        &&& (response.req_type() is Echo ==> {
            let echo_req = request.echo();
            let resp = response.echo();
            &&& echo_req.spec_message() == resp.spec_message()
        })
    }

    proof fn recv_implies_pre(tracked &self, channel_id: (u64, u64), request: Request) {
    }

    proof fn post_implies_send(
        tracked &self,
        channel_id: (u64, u64),
        request: Request,
        response: Response,
    ) {
    }

    fn handle(
        &self,
        #[allow(unused_variables)]
        channel_id: (u64, u64),
        request: Request,
    ) -> (r: Response) {
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

    fn id(&self) -> (r: u64) {
        self.id
    }
}

pub type EchoServer<L, C> = Server<EchoService, L, C>;

pub fn create_server<L, C>(server_id: u64, listener: L, num_threads: usize) -> EchoServer<
    L,
    C,
> where L: Listener<C>, C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>
    requires
        num_threads > 0,
{
    let tracked state_inv;
    proof {
        state_inv = invariants::get_system_state();
    }
    #[allow(unused_variables)]
    let state_inv = Tracked(state_inv);
    let ghost channel_inv = ChannelInv::from_state_pred(state_inv@.constant());
    let service = EchoService::new(server_id, Ghost(channel_inv));
    Server::new(service, listener, Ghost(channel_inv), num_threads)
}

} // verus!
