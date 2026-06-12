use std::collections::BTreeSet;

use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::requests::RequestProof;
#[cfg(verus_only)]
use crate::invariants::StatePredicate;
use crate::proto::Response;
#[cfg(verus_only)]
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

use verdist::network::channel::Channel;
#[cfg(verus_only)]
use verdist::network::channel::ChannelInvariant;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;
use verdist::rpc::replies::ReplyAccumulator;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::Loc;
#[cfg(verus_only)]
use vstd::std_specs::btree::increasing_seq;

verus! {

#[allow(unused_variables, dead_code)]
pub ghost struct WritePred<C: Channel<K = ChannelInv>> {
    pub server_locs: Map<u64, Loc>,
    pub orig_servers: ServerUniverse,
    pub commitment_id: Loc,
    pub request_map_id: Loc,
    pub server_tokens_id: Loc,
    pub channels: Map<C::Id, C>,
    pub timestamp: Timestamp,
    pub client_id: u64,
    pub request_id: u64,
}

impl<C: Channel<K = ChannelInv>> WritePred<C> {
    pub open spec fn new(
        state: StatePredicate,
        channels: Map<C::Id, C>,
        client_id: u64,
        request: RequestProof,
    ) -> WritePred<C> {
        WritePred {
            server_locs: state.server_locs,
            orig_servers: request.write().servers(),
            commitment_id: state.commitments_ids.commitment_id,
            request_map_id: state.request_map_ids.request_auth_id,
            server_tokens_id: state.server_tokens_id,
            channels,
            timestamp: request.write().spec_timestamp(),
            client_id,
            request_id: request.key().1,
        }
    }
    // TODO: type invariant here relating the channels.dom() to the server_locs.dom()

}

#[allow(dead_code)]
pub struct WriteAccumulator<C: Channel<K = ChannelInv, Id = (u64, u64)>> {
    // EXEC state
    /// Received replies
    replies: BTreeSet<C::Id>,
    // Spec state
    /// Constructed view over the server map
    /// The target is to show that there is a unanimous quorum >= request...timestamp()
    servers: Tracked<ServerUniverse>,
    /// Lower bound for the server tokens
    server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
    /// channels of the pool this accumulator is working with
    channels: Ghost<Map<C::Id, C>>,
    /// write request proof
    request: Tracked<RequestProof>,
}

impl<C> InvariantPredicate<WritePred<C>, WriteAccumulator<C>> for WritePred<C> where
    C: Channel<K = ChannelInv, Id = (u64, u64)>,
 {
    open spec fn inv(pred: WritePred<C>, v: WriteAccumulator<C>) -> bool {
        pred == v.constant()
    }
}

pub open spec fn request_inv<C: Channel<K = ChannelInv>>(
    request: RequestProof,
    pred: WritePred<C>,
) -> bool {
    &&& request.id() == pred.request_map_id
    &&& request.key().0 == pred.client_id
    &&& request.key().1 == pred.request_id
    &&& request.req_type() is Write
    &&& request.write().commitment_id() == pred.commitment_id
    &&& request.write().spec_timestamp() == pred.timestamp
    &&& server_inv(request.write().servers())
}

pub open spec fn server_inv(s: ServerUniverse) -> bool {
    &&& s.inv()
    &&& s.is_lb()
}

pub open spec fn channel_inv<C: Channel<K = ChannelInv, Id = (u64, u64)>>(
    c_inv: ChannelInv,
    pred: WritePred<C>,
) -> bool {
    &&& c_inv.request_map_id == pred.request_map_id
    &&& c_inv.commitment_id == pred.commitment_id
    &&& c_inv.server_tokens_id == pred.server_tokens_id
    &&& c_inv.server_locs == pred.server_locs
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> WriteAccumulator<C> {
    pub fn new(
        servers: Tracked<ServerUniverse>,
        server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
        request: Tracked<RequestProof>,
        #[allow(unused_variables)]
        pred: Ghost<WritePred<C>>,
    ) -> (r: Self)
        requires
            pred@.server_locs == servers@.locs(),
            pred@.server_tokens_id == server_tokens@.id(),
            server_tokens@@ <= servers@.locs(),
            server_inv(servers@),
            request_inv(request@, pred@),
            request@.write().servers().eq_timestamp(servers@),
            request@.write().servers() == pred@.orig_servers,
            forall|c_id| #[trigger]
                pred@.channels.contains_key(c_id) ==> {
                    let c = pred@.channels[c_id];
                    &&& c_id.0 == request@.key().0
                    &&& channel_inv(c.constant(), pred@)
                },
        ensures
            r.constant() == pred@,
            r.replies().is_empty(),
            r.spec_timestamp() == request@.write().spec_timestamp(),
            r.server_locs() == servers@.locs(),
            r.server_tokens_id() == server_tokens@.id(),
    {
        WriteAccumulator {
            replies: BTreeSet::new(),
            servers,
            server_tokens,
            channels: Ghost(pred@.channels),
            request,
        }
    }

    closed spec fn server_invs(
        servers: ServerUniverse,
        req_servers: ServerUniverse,
        server_tokens: Map<u64, Loc>,
    ) -> bool {
        &&& server_inv(servers)
        &&& server_inv(req_servers)
        &&& req_servers.leq(servers)
        &&& server_tokens <= servers.locs()
    }

    closed spec fn channel_inv(channels: Map<C::Id, C>, k: WritePred<C>) -> bool {
        forall|c_id| #[trigger]
            channels.contains_key(c_id) ==> {
                let c = channels[c_id];
                &&& c_id.0 == k.client_id
                &&& channel_inv(c.constant(), k)
            }
    }

    closed spec fn replies_inv(
        replies: Set<C::Id>,
        servers: ServerUniverse,
        timestamp: Timestamp,
        client_id: u64,
    ) -> bool {
        &&& forall|cid| #[trigger]
            replies.contains(cid) ==> {
                &&& cid.0 == client_id
                &&& servers.contains_key(cid.1)
                &&& servers[cid.1]@@.timestamp() >= timestamp
            }
    }

    closed spec fn unchanged_inv(
        servers: ServerUniverse,
        req_servers: ServerUniverse,
        replies: Set<C::Id>,
        client_id: u64,
    ) -> bool {
        forall|cid|
            {
                &&& !#[trigger] replies.contains(cid)
                &&& servers.contains_key(cid.1)
                &&& cid.0 == client_id
            } ==> { servers[cid.1]@@.timestamp() == req_servers[cid.1]@@.timestamp() }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& Self::server_invs(self.servers(), self.orig_servers(), self.server_tokens@@)
        &&& Self::channel_inv(self.channels@, self.constant())
        &&& Self::replies_inv(self.replies@, self.servers@, self.spec_timestamp(), self.client_id())
        &&& Self::unchanged_inv(
            self.servers(),
            self.orig_servers(),
            self.replies@,
            self.client_id(),
        )
        &&& self.request@.req_type() is Write
    }

    // SPEC
    pub open spec fn constant(self) -> WritePred<C> {
        WritePred {
            server_locs: self.server_locs(),
            orig_servers: self.orig_servers(),
            commitment_id: self.commitment_id(),
            request_map_id: self.request_map_id(),
            server_tokens_id: self.server_tokens_id(),
            channels: self.spec_channels(),
            timestamp: self.spec_timestamp(),
            client_id: self.client_id(),
            request_id: self.request_id(),
        }
    }

    pub closed spec fn client_id(self) -> u64 {
        self.request@.key().0
    }

    pub closed spec fn request_id(self) -> u64 {
        self.request@.key().1
    }

    pub closed spec fn orig_servers(self) -> ServerUniverse {
        self.request@.write().servers()
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub open spec fn server_locs(self) -> Map<u64, Loc> {
        self.servers().locs()
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.request@.write().commitment_id()
    }

    pub closed spec fn request_map_id(self) -> Loc {
        self.request@.id()
    }

    pub closed spec fn server_tokens_id(self) -> Loc {
        self.server_tokens@.id()
    }

    pub closed spec fn spec_channels(self) -> Map<C::Id, C> {
        self.channels@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.request@.write().spec_timestamp()
    }

    pub open spec fn quorum(self) -> Quorum {
        self.replies().map(|id: (u64, u64)| id.1)
    }

    pub closed spec fn replies(self) -> Set<C::Id> {
        self.replies@
    }

    // PROOF
    pub fn lemma_quorum(&self)
        ensures
            self.quorum().len() == self.replies().len(),
            self.quorum() <= self.server_locs().dom(),
    {
        proof {
            use_type_invariant(self);
            let q = self.replies().map(|id: (u64, u64)| id.1);
            vstd::set_lib::lemma_map_size(self.replies(), q, |id: (u64, u64)| id.1);
        }
    }

    pub fn lemma_timestamp(&self)
        requires
            !self.replies().is_empty(),
        ensures
            self.servers().inv(),
            self.servers().valid_quorum(self.quorum()) ==> {
                self.servers().unanimous_quorum(self.quorum(), self.spec_timestamp())
            },
    {
        proof {
            use_type_invariant(self);
        }
    }

    proof fn update_servers(
        tracked servers: &mut ServerUniverse,
        req_servers: ServerUniverse,
        server_id: u64,
        tracked lb: MonotonicTimestampResource,
    )
        requires
            Self::server_invs(*old(servers), req_servers, old(servers).locs()),
            old(servers).contains_key(server_id),
            old(servers)[server_id]@.loc() == lb.loc(),
            lb@ is LowerBound,
        ensures
            Self::server_invs(*final(servers), req_servers, final(servers).locs()),
            final(servers).dom() == old(servers).dom(),
            final(servers).locs() == old(servers).locs(),
            old(servers).leq(*final(servers)),
            forall|id| #[trigger]
                final(servers).contains_key(id) ==> {
                    &&& id != server_id ==> final(servers)[id]@@.timestamp() == old(
                        servers,
                    )[id]@@.timestamp()
                    &&& id == server_id ==> final(servers)[id]@@.timestamp() >= lb@.timestamp()
                },
            final(servers)[server_id]@@.timestamp() >= lb@.timestamp(),
    {
        let ghost old_servers = *old(servers);
        if servers[server_id]@@.timestamp() < lb@.timestamp() {
            servers.tracked_update_lb(server_id, lb);
        }
        assert(servers[server_id]@@.timestamp() >= lb@.timestamp());
        ServerUniverse::lemma_leq_trans(req_servers, old_servers, *servers);
    }

    // EXEC
    pub fn n_replies(&self) -> (r: usize)
        ensures
            r@ == self.replies().len(),
    {
        proof {
            use_type_invariant(self);
        }
        self.replies.len()
    }

    pub fn write_replies(&self) -> (r: BTreeSet<C::Id>)
        ensures
            r@ == self.replies(),
    {
        proof {
            use_type_invariant(self);
        }
        self.replies.clone()
    }

    pub fn servers_lb(&self) -> (r: Tracked<ServerUniverse>)
        requires
            !self.replies().is_empty(),
        ensures
            self.server_locs() == r@.locs(),
            self.servers().leq(r@),
            self.servers().inv(),
            r@.leq(self.servers()),
            r@.inv(),
            r@.is_lb(),
            r@.valid_quorum(self.quorum()) ==> r@.unanimous_quorum(
                self.quorum(),
                self.spec_timestamp(),
            ),
            self.servers().eq_timestamp(r@),
    {
        self.lemma_timestamp();
        let tracked lbs;
        proof {
            use_type_invariant(self);
            lbs = self.servers.borrow().extract_lbs();
            lbs.lemma_locs();
            lbs.lemma_eq(self.servers());
        }
        Tracked(lbs)
    }

    fn insert_aux(
        replies: &mut BTreeSet<C::Id>,
        #[allow(unused_variables)]
        servers: &mut Tracked<ServerUniverse>,
        server_tokens: &mut Tracked<GhostPersistentSubmap<u64, Loc>>,
        #[allow(unused_variables)]
        request: &Tracked<RequestProof>,
        id: (u64, u64),
        resp: Response,
    )
        requires
            resp.server_id() == id.1,
            resp.req_type() is Write,
            resp.request() == request@@,
            resp.write().server_token_id() == old(server_tokens)@.id(),
            resp.write().loc() == old(servers)@.locs()[resp.server_id()],
            old(servers)@.locs().contains_key(id.1),
            request@.req_type() is Write,
            request@.key().0 == id.0,
            Self::server_invs(old(servers)@, request@.write().servers(), old(server_tokens)@@),
            Self::replies_inv(
                old(replies)@,
                old(servers)@,
                request@.write().spec_timestamp(),
                id.0,
            ),
            Self::unchanged_inv(old(servers)@, request@.write().servers(), old(replies)@, id.0),
        ensures
            final(servers)@.locs() == old(servers)@.locs(),
            final(server_tokens)@.id() == old(server_tokens)@.id(),
            final(replies)@ == old(replies)@.insert(id),
            Self::server_invs(final(servers)@, request@.write().servers(), final(server_tokens)@@),
            Self::replies_inv(
                final(replies)@,
                final(servers)@,
                request@.write().spec_timestamp(),
                id.0,
            ),
            Self::unchanged_inv(final(servers)@, request@.write().servers(), final(replies)@, id.0),
        no_unwind
    {
        if replies.contains(&id) {
            return;
        }
        let r = resp.destruct_write();

        r.lemma_write_response();
        r.lemma_token_agree(server_tokens);
        assert(r.lb()@ is LowerBound);
        let Tracked(lb) = r.duplicate_lb();
        assert(lb@ is LowerBound);

        proof {
            Self::update_servers(servers.borrow_mut(), request@.write().servers(), id.1, lb);
        }

        replies.insert(id);
    }

    fn insert_write(&mut self, id: (u64, u64), resp: Response)
        requires
            WritePred::inv(old(self).constant(), *old(self)),
            old(self).client_id() == id.0,
            resp.req_type() is Write,
            resp.write().server_id() == id.1,
            resp.request() == old(self).request@@,
            old(self).constant().server_tokens_id == resp.write().server_token_id(),
            old(self).constant().server_locs.contains_key(resp.server_id()),
            old(self).constant().server_locs[resp.server_id()] == resp.write().loc(),
        ensures
            WritePred::inv(final(self).constant(), *final(self)),
            final(self).constant() == old(self).constant(),
            final(self).replies() == old(self).replies().insert(id),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }

        Self::insert_aux(
            &mut self.replies,
            &mut self.servers,
            &mut self.server_tokens,
            &self.request,
            id,
            resp,
        );
    }
}

impl<C> ReplyAccumulator<C, WritePred<C>> for WriteAccumulator<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    #[allow(unused_variables)]
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(&mut self, pred: Ghost<WritePred<C>>, id: (u64, u64), reply: Response)
        ensures
            final(self).channels() == old(self).channels(),
    {
        proof {
            use_type_invariant(&*self);

            assume(C::K::recv_inv(self.channels()[id].constant(), id, reply));  // TODO(verus): this is a verus problem
        }
        reply.agree_request(&mut self.request);
        reply.lemma_inv();

        self.insert_write(id, reply);
    }

    open spec fn request_tag(self) -> u64 {
        self.request_id()
    }

    open spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.replies()
    }

    fn handled_replies(&self) -> BTreeSet<C::Id> {
        self.write_replies()
    }

    open spec fn channels(self) -> Map<C::Id, C> {
        self.spec_channels()
    }
}

} // verus!
