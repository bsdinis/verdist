use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants;
#[cfg(verus_only)]
use crate::invariants::quorum::ServerUniverseLb;
use crate::proto::GetRequest;
use crate::proto::GetResponse;
use crate::proto::GetTimestampRequest;
use crate::proto::GetTimestampResponse;
use crate::proto::Request;
use crate::proto::RequestInner;
use crate::proto::Response;
use crate::proto::ResponseInner;
use crate::proto::WriteRequest;
use crate::proto::WriteResponse;
use crate::server::lockfree::EpochMonotonicRegister;
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

pub mod lockfree;
pub mod register;

verus! {

/// Which `RegisterStore` variant `create_server` should build (design doc section 5.5). Plain
/// runtime data with no spec meaning of its own -- CLI/config wiring (`abd-example`/`abd-bench`)
/// is a later phase; this is just what `create_server` needs to pick a backend today.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegisterBackend {
    Locked,
    Lockfree,
}

/// Runtime switch between the two register backends (design doc section 5.5): same identity
/// (`resource_loc`/`commitment_id`/`server_token_id`/`id`) and (`shard_idx`-taking)
/// `read`/`read_timestamp`/`write` contracts as `MonotonicRegister` itself (`register.rs`), so
/// `RegisterService` below can hold either without any change to its own contracts. `shard_idx`
/// only ever selects an `EpochMonotonicRegister` reader slot (see `lockfree.rs`'s module docs) --
/// the `Locked` arm has no reader slots to pick between and simply ignores it.
pub enum RegisterStore<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    Locked(MonotonicRegister<ML, RL>),
    Lockfree(EpochMonotonicRegister<ML, RL>),
}

impl<ML, RL> RegisterStore<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub closed spec fn resource_loc(self) -> Loc {
        match self {
            RegisterStore::Locked(r) => r.resource_loc(),
            RegisterStore::Lockfree(r) => r.resource_loc(),
        }
    }

    pub closed spec fn commitment_id(self) -> Loc {
        match self {
            RegisterStore::Locked(r) => r.commitment_id(),
            RegisterStore::Lockfree(r) => r.commitment_id(),
        }
    }

    pub closed spec fn server_token_id(self) -> Loc {
        match self {
            RegisterStore::Locked(r) => r.server_token_id(),
            RegisterStore::Lockfree(r) => r.server_token_id(),
        }
    }

    pub closed spec fn id(self) -> u64 {
        match self {
            RegisterStore::Locked(r) => r.id(),
            RegisterStore::Lockfree(r) => r.id(),
        }
    }

    /// Exactly `MonotonicRegister::read`'s contract (`register.rs`), plus a leading `shard_idx`
    /// forwarded to `EpochMonotonicRegister::read` and ignored by `Locked`.
    pub fn read(&self, shard_idx: usize, req: GetRequest) -> (r: GetResponse)
        requires
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
        ensures
            r.loc() == self.resource_loc(),
            r.server_id() == self.id(),
            r.spec_commitment().id() == self.commitment_id(),
            r.server_token_id() == self.server_token_id(),
            req.servers().contains_key(r.server_id()),
            req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp(),
    {
        match self {
            RegisterStore::Locked(r) => r.read(req),
            RegisterStore::Lockfree(r) => r.read(shard_idx, req),
        }
    }

    /// Exactly `MonotonicRegister::read_timestamp`'s contract (`register.rs`), plus a leading
    /// `shard_idx` forwarded to `EpochMonotonicRegister::read_timestamp` and ignored by `Locked`.
    pub fn read_timestamp(&self, shard_idx: usize, req: GetTimestampRequest) -> (r:
        GetTimestampResponse)
        requires
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
        ensures
            r.loc() == self.resource_loc(),
            r.server_id() == self.id(),
            r.server_token_id() == self.server_token_id(),
            req.servers().contains_key(r.server_id()),
            req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp(),
    {
        match self {
            RegisterStore::Locked(r) => r.read_timestamp(req),
            RegisterStore::Lockfree(r) => r.read_timestamp(shard_idx, req),
        }
    }

    /// Exactly `MonotonicRegister::write`'s contract (`register.rs`), plus a leading `shard_idx`
    /// forwarded to `EpochMonotonicRegister::write` and ignored by `Locked`.
    pub fn write(&self, shard_idx: usize, req: WriteRequest) -> (r: WriteResponse)
        requires
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
            req.commitment_id() == self.commitment_id(),
        ensures
            r.loc() == self.resource_loc(),
            r.server_id() == self.id(),
            r.server_token_id() == self.server_token_id(),
            req.servers().contains_key(r.server_id()),
            req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp(),
            req.spec_timestamp() <= r.spec_timestamp(),
    {
        match self {
            RegisterStore::Locked(r) => r.write(req),
            RegisterStore::Lockfree(r) => r.write(shard_idx, req),
        }
    }

    /// Background-maintenance hook (`Service::background_tick`, via `RegisterService`): a no-op
    /// on `Locked` (its `RwLock` needs no reclaim), forwarded to
    /// `EpochMonotonicRegister::reclaim_pass` on `Lockfree`. Plain exec, not part of any spec --
    /// see `reclaim_pass`'s own doc there.
    pub fn reclaim_pass(&self) {
        match self {
            RegisterStore::Locked(_) => (),
            RegisterStore::Lockfree(r) => r.reclaim_pass(),
        }
    }
}

#[verifier::reject_recursive_types(ML)]
#[verifier::reject_recursive_types(RL)]
pub struct RegisterService<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    /// ID of the server
    id: u64,
    /// Register state -- either backend (design doc section 5.5)
    register: RegisterStore<ML, RL>,
    /// Channel invariant this server's connections are held under
    #[allow(dead_code)]
    channel_inv: Ghost<ChannelInv>,
}

impl<ML, RL> RegisterService<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(id: u64, register: RegisterStore<ML, RL>, channel_inv: Ghost<ChannelInv>) -> (r:
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

    fn handle_get(&self, shard_idx: usize, req: GetRequest) -> (r: ResponseInner)
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
        ResponseInner::Get(self.register.read(shard_idx, req))
    }

    fn handle_get_timestamp(&self, shard_idx: usize, req: GetTimestampRequest) -> (r: ResponseInner)
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
        ResponseInner::GetTimestamp(self.register.read_timestamp(shard_idx, req))
    }

    fn handle_write(&self, shard_idx: usize, req: WriteRequest) -> (r: ResponseInner)
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
        ResponseInner::Write(self.register.write(shard_idx, req))
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
        // Forwarded to `RegisterStore`'s `read`/`read_timestamp`/`write` below: the lock-free
        // backend needs it as its `EpochAtomicPtr::pin` reader identity (design doc section 5.5).
        // The RwLock backend ignores it.
        shard_idx: usize,
        #[allow(unused_variables)]
        channel_id: (u64, u64),
        request: Request,
    ) -> (r: Response) {
        // vlib::veprintln!("[server|{:>3}]: received req: {:?}", self.id, request);
        let (request_id, request_inner, request_proof) = request.destruct();
        let resp_inner = match request_inner {
            RequestInner::Get(req) => self.handle_get(shard_idx, req),
            RequestInner::GetTimestamp(req) => self.handle_get_timestamp(shard_idx, req),
            RequestInner::Write(req) => self.handle_write(shard_idx, req),
        };

        proof {
            if request_inner is Get {
                let get_req = request_inner->Get_0;
                let proof_get_req = request_proof@.get();
                GetRequest::lemma_spec_eq(proof_get_req, get_req);
                proof_get_req.servers().lemma_dom_correspondence();
                get_req.servers().lemma_dom_correspondence();
                ServerUniverseLb::lemma_eq(proof_get_req.servers(), get_req.servers());
            }
            if request_inner is GetTimestamp {
                let get_ts_req = request_inner->GetTimestamp_0;
                let proof_get_ts_req = request_proof@.get_timestamp();
                GetTimestampRequest::lemma_spec_eq(proof_get_ts_req, get_ts_req);
                proof_get_ts_req.servers().lemma_dom_correspondence();
                get_ts_req.servers().lemma_dom_correspondence();
                ServerUniverseLb::lemma_eq(proof_get_ts_req.servers(), get_ts_req.servers());
            }
            if request_inner is Write {
                let write_req = request_inner->Write_0;
                let proof_write_req = request_proof@.write();
                WriteRequest::lemma_spec_eq(proof_write_req, write_req);
                proof_write_req.servers().lemma_dom_correspondence();
                write_req.servers().lemma_dom_correspondence();
                ServerUniverseLb::lemma_eq(proof_write_req.servers(), write_req.servers());
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

    // Only the `Lockfree` backend has anything to do here -- `Locked`'s `RwLock` needs no
    // background maintenance, so `Server::run`/`run_epoll` spawn no extra thread at all in that
    // case (see `Service::has_background_work`'s doc).
    fn has_background_work(&self) -> bool {
        matches!(self.register, RegisterStore::Lockfree(_))
    }

    fn background_tick(&self) {
        self.register.reclaim_pass();
    }
}

pub type RegisterServer<L, C, ML, RL> = Server<RegisterService<ML, RL>, L, C>;

#[allow(unused_variables)]
#[allow(clippy::type_complexity)]
pub fn create_server<L, C, ML, RL>(
    server_ids: &HashSet<u64>,
    my_server_id: u64,
    listener: L,
    num_threads: usize,
    backend: RegisterBackend,
) -> (RegisterServer<L, C, ML, RL>, Vec<crossbeam_channel::Receiver<L::Raw>>) where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    requires
        server_ids@.contains(my_server_id),
        num_threads > 0,
        // Only load-bearing for the `Lockfree` branch below (`num_slots = num_threads + 2` must
        // fit `EpochAtomicPtr`'s `INDEX_SPACE`, design doc section 6's sizing rule) -- required
        // unconditionally since `backend` is a runtime value `requires` cannot branch on.
        num_threads + 2 <= vlib::reclaim::atomic_ptr::INDEX_SPACE,
        listener.spec_id() == my_server_id,
{
    let tracked state_inv;
    proof {
        let tracked (s, v) = invariants::get_system_state::<ML, RL>(server_ids@);
        state_inv = s;
    }
    let state_inv = Tracked(state_inv);
    let ghost channel_inv = ChannelInv::from_state_pred(state_inv@.constant());
    // Sizing per design doc section 6: `num_readers = num_threads` (one reader slot per polling
    // thread -- see `EpochMonotonicRegister::read`'s `shard_idx % self.num_readers`),
    // `num_slots = num_threads + 2` (writers are already serialized by the gate, so one spare
    // slot beyond the readers is generous headroom for a reader pinned across a publish).
    let register = match backend {
        RegisterBackend::Locked => RegisterStore::Locked(
            MonotonicRegister::new(my_server_id, state_inv),
        ),
        RegisterBackend::Lockfree => RegisterStore::Lockfree(
            EpochMonotonicRegister::new(my_server_id, state_inv, num_threads, num_threads + 2),
        ),
    };
    let service = RegisterService::new(my_server_id, register, Ghost(channel_inv));
    Server::new(service, listener, Ghost(channel_inv), num_threads)
}

} // verus!
