use std::collections::BTreeSet;

use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::requests::RequestProof;
#[cfg(verus_only)]
use crate::invariants::StatePredicate;
use crate::proto::GetTimestampResponse;
use crate::proto::Response;
#[cfg(verus_only)]
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
#[cfg(verus_only)]
use crate::timestamp::Timestamp;

use verdist::network::channel::Channel;
#[cfg(verus_only)]
use verdist::network::channel::ChannelInvariant;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;
use verdist::rpc::replies::ReplyAccumulator;

use vstd::invariant::InvariantPredicate;
#[cfg(verus_only)]
use vstd::map_lib::lemma_values_finite;
use vstd::prelude::*;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::Loc;

verus! {

#[allow(unused_variables, dead_code)]
pub ghost struct GetTimestampPred<C: Channel<K = ChannelInv>> {
    pub server_locs: Map<u64, Loc>,
    pub orig_servers: ServerUniverse,
    pub request_map_id: Loc,
    pub server_tokens_id: Loc,
    pub channels: Map<C::Id, C>,
    pub client_id: u64,
    pub request_id: u64,
}

impl<C: Channel<K = ChannelInv>> GetTimestampPred<C> {
    pub open spec fn new(
        state: StatePredicate,
        channels: Map<C::Id, C>,
        client_id: u64,
        request: RequestProof,
    ) -> GetTimestampPred<C> {
        GetTimestampPred {
            server_locs: state.server_locs,
            orig_servers: request.get_timestamp().servers(),
            request_map_id: state.request_map_ids.request_auth_id,
            server_tokens_id: state.server_tokens_id,
            channels,
            client_id,
            request_id: request.key().1,
        }
    }
}

#[allow(dead_code)]
pub struct GetTimestampAccumulator<C: Channel<K = ChannelInv, Id = (u64, u64)>> {
    // EXEC state
    /// The max response seen
    /// This is the value that will ultimately be returned
    max_resp: Option<GetTimestampResponse>,
    /// The set of servers that we know are >= max_resp.timestamp()
    agree_with_max: BTreeSet<u64>,
    /// Received replies
    replies: BTreeSet<C::Id>,
    // Spec state
    /// Constructed view over the server map
    ///
    /// In the beginning, we only know that every quorum is bounded bellow by the watermark
    servers: Tracked<ServerUniverse>,
    /// Lower bound for the server tokens
    server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
    /// channels of the pool this accumulator is working with
    channels: Ghost<Map<C::Id, C>>,
    /// get timestamp request proof
    request: Tracked<RequestProof>,
}

impl<C> InvariantPredicate<GetTimestampPred<C>, GetTimestampAccumulator<C>> for GetTimestampPred<
    C,
> where C: Channel<K = ChannelInv, Id = (u64, u64)> {
    open spec fn inv(pred: GetTimestampPred<C>, v: GetTimestampAccumulator<C>) -> bool {
        pred == v.constant()
    }
}

pub open spec fn request_inv(
    request: RequestProof,
    request_map_id: Loc,
    client_id: u64,
    request_id: u64,
) -> bool {
    &&& request.id() == request_map_id
    &&& request.key().0 == client_id
    &&& request.key().1 == request_id
    &&& request.req_type() is GetTimestamp
    &&& server_inv(request.get_timestamp().servers())
}

pub open spec fn server_inv(s: ServerUniverse) -> bool {
    &&& s.inv()
    &&& s.is_lb()
}

pub open spec fn channel_inv<C: Channel<K = ChannelInv, Id = (u64, u64)>>(
    c_inv: ChannelInv,
    pred: GetTimestampPred<C>,
) -> bool {
    &&& c_inv.request_map_id == pred.request_map_id
    &&& c_inv.server_tokens_id == pred.server_tokens_id
    &&& c_inv.server_locs == pred.server_locs
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> GetTimestampAccumulator<C> {
    pub fn new(
        servers: Tracked<ServerUniverse>,
        server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
        request: Tracked<RequestProof>,
        #[allow(unused_variables)]
        pred: Ghost<GetTimestampPred<C>>,
    ) -> (r: Self)
        requires
            pred@.server_locs == servers@.locs(),
            pred@.server_tokens_id == server_tokens@.id(),
            server_tokens@@ <= servers@.locs(),
            server_inv(servers@),
            request_inv(request@, pred@.request_map_id, pred@.client_id, pred@.request_id),
            request@.get_timestamp().servers().eq_timestamp(servers@),
            request@.get_timestamp().servers() == pred@.orig_servers,
            forall|c_id| #[trigger]
                pred@.channels.contains_key(c_id) ==> {
                    let c = pred@.channels[c_id];
                    &&& c_id.0 == request@.key().0
                    &&& channel_inv(c.constant(), pred@)
                },
        ensures
            r.constant() == pred@,
            r.replies().is_empty(),
            r.server_locs() == servers@.locs(),
            r.server_tokens_id() == server_tokens@.id(),
    {
        GetTimestampAccumulator {
            max_resp: None,
            agree_with_max: BTreeSet::new(),
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

    closed spec fn channel_inv(channels: Map<C::Id, C>, k: GetTimestampPred<C>) -> bool {
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
        client_id: u64,
    ) -> bool {
        &&& replies.finite()
        &&& forall|cid| #[trigger] replies.contains(cid) ==> cid.0 == client_id
        &&& replies.map(|id: (u64, u64)| id.1) <= servers.dom()
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

    closed spec fn agree_with_max_aux_inv(
        agree_with_max: Set<u64>,
        replies: Set<C::Id>,
        max_resp: Option<GetTimestampResponse>,
    ) -> bool {
        &&& agree_with_max.finite()
        &&& agree_with_max.is_empty() <==> replies.is_empty()
        &&& max_resp is None <==> agree_with_max.is_empty()
        &&& agree_with_max <= replies.map(|id: (u64, u64)| id.1)
    }

    closed spec fn agree_with_max_inv(
        agree_with_max: Set<u64>,
        replies: Set<C::Id>,
        servers: ServerUniverse,
        max_resp: Option<GetTimestampResponse>,
    ) -> bool {
        &&& Self::agree_with_max_aux_inv(agree_with_max, replies, max_resp)
        &&& agree_with_max <= servers.dom()
    }

    closed spec fn max_resp_inv(
        max_resp: GetTimestampResponse,
        servers: ServerUniverse,
        agree_with_max: Set<u64>,
        replies: Set<C::Id>,
        server_tokens_id: Loc,
    ) -> bool {
        &&& forall|id| #[trigger]
            agree_with_max.contains(id) ==> { servers[id]@@.timestamp() == max_resp.spec_timestamp()
            }
        &&& forall|id| #[trigger]
            replies.contains(id) ==> { servers[id.1]@@.timestamp() <= max_resp.spec_timestamp() }
        &&& max_resp.server_token_id() == server_tokens_id
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& Self::server_invs(self.servers(), self.orig_servers(), self.server_tokens@@)
        &&& Self::channel_inv(self.channels@, self.constant())
        &&& Self::replies_inv(self.replies@, self.servers@, self.client_id())
        &&& Self::unchanged_inv(
            self.servers(),
            self.orig_servers(),
            self.replies@,
            self.client_id(),
        )
        &&& Self::agree_with_max_inv(
            self.agree_with_max@,
            self.replies@,
            self.servers(),
            self.max_resp@,
        )
        &&& self.max_resp is Some ==> {
            Self::max_resp_inv(
                self.max_resp->Some_0,
                self.servers(),
                self.agree_with_max@,
                self.replies@,
                self.server_tokens@.id(),
            )
        }
        &&& self.request@.req_type() is GetTimestamp
    }

    // SPEC
    pub open spec fn constant(self) -> GetTimestampPred<C> {
        GetTimestampPred {
            server_locs: self.server_locs(),
            orig_servers: self.orig_servers(),
            request_map_id: self.request_map_id(),
            server_tokens_id: self.server_tokens_id(),
            channels: self.spec_channels(),
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
        self.request@.get_timestamp().servers()
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub open spec fn server_locs(self) -> Map<u64, Loc> {
        self.servers().locs()
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

    pub open spec fn quorum(self) -> Quorum {
        self.replies().map(|id: (u64, u64)| id.1)
    }

    pub closed spec fn spec_max_resp(&self) -> GetTimestampResponse
        recommends
            !self.replies().is_empty(),
    {
        self.max_resp->Some_0
    }

    pub open spec fn spec_max_timestamp(&self) -> Timestamp
        recommends
            !self.replies().is_empty(),
    {
        self.spec_max_resp().spec_timestamp()
    }

    pub closed spec fn replies(self) -> Set<C::Id> {
        self.replies@
    }

    // PROOF
    pub fn lemma_quorum(&self)
        ensures
            self.quorum().len() == self.replies().len(),
            self.quorum().finite(),
            self.quorum() <= self.server_locs().dom(),
    {
        proof {
            use_type_invariant(self);
            let q = self.replies().map(|id: (u64, u64)| id.1);
            vstd::set_lib::lemma_map_size(self.replies(), q, |id: (u64, u64)| id.1);
        }
    }

    pub fn lemma_max_timestamp(&self)
        requires
            !self.replies().is_empty(),
        ensures
            self.servers().inv(),
            self.servers().valid_quorum(self.quorum()) ==> {
                self.servers().quorum_timestamp(self.quorum()) == self.spec_max_timestamp()
            },
    {
        proof {
            use_type_invariant(self);
            if self.servers().valid_quorum(self.quorum()) {
                let max = self.spec_max_timestamp();
                let quorum_map = self.servers().map.restrict(self.quorum());
                assert(quorum_map.dom() == self.quorum());  // XXX: load bearing
                lemma_values_finite(quorum_map);
                quorum_map.values().lemma_map_finite(
                    |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
                );
                let quorum_vals = self.servers().quorum_vals(self.quorum());
                assume(quorum_vals.len() > 0);  // TODO(verus): this needs a verus lemma
                quorum_vals.find_unique_maximal_ensures(ServerUniverse::ts_leq());

                // triggers
                let witness = choose|id| #[trigger]
                    quorum_map.contains_key(id) && self.servers()[id]@@.timestamp() == max;
                assert(quorum_map.values().contains(self.servers()[witness]));
                assert(vstd::relations::is_maximal(ServerUniverse::ts_leq(), max, quorum_vals));
            }
        }
    }

    proof fn update_servers(
        tracked servers: &mut ServerUniverse,
        req_servers: ServerUniverse,
        agree_with_max: Set<u64>,
        max_resp: &Option<GetTimestampResponse>,
        server_id: u64,
        tracked lb: MonotonicTimestampResource,
    )
        requires
            Self::server_invs(*old(servers), req_servers, old(servers).locs()),
            old(servers).contains_key(server_id),
            old(servers)[server_id]@.loc() == lb.loc(),
            old(servers)[server_id]@@.timestamp() <= lb@.timestamp(),
            agree_with_max <= old(servers).dom(),
            max_resp is Some ==> forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    old(servers)[id]@@.timestamp() == max_resp->Some_0.spec_timestamp()
                },
            lb@ is LowerBound,
            !agree_with_max.contains(server_id),
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
                    &&& id == server_id ==> final(servers)[id]@@.timestamp() == lb@.timestamp()
                },
            final(servers)[server_id]@@.timestamp() == lb@.timestamp(),
            max_resp is Some ==> forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    final(servers)[id]@@.timestamp() >= max_resp->Some_0.spec_timestamp()
                },
    {
        let ghost old_servers = *old(servers);
        servers.tracked_update_lb(server_id, lb);
        if max_resp is Some {
            assert forall|id| #[trigger]
                agree_with_max.contains(id) implies servers[id]@@.timestamp()
                == max_resp->Some_0.spec_timestamp() by {
                assert(servers.contains_key(id));  // XXX: trigger
            }
        }
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

    pub fn get_ts_replies(&self) -> (r: BTreeSet<C::Id>)
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
            r@.inv(),
            r@.is_lb(),
            r@.valid_quorum(self.quorum()) ==> r@.quorum_timestamp(self.quorum())
                == self.spec_max_timestamp(),
            self.servers().eq_timestamp(r@),
            self.orig_servers().leq(r@),
    {
        self.lemma_max_timestamp();
        let tracked lbs;
        proof {
            use_type_invariant(self);
            lbs = self.servers.borrow().extract_lbs();
            lbs.lemma_locs();
            lbs.lemma_eq(self.servers());
            ServerUniverse::lemma_leq_trans(self.orig_servers(), self.servers(), lbs);
        }
        Tracked(lbs)
    }

    pub fn max_resp(&self) -> (r: &GetTimestampResponse)
        requires
            !self.replies().is_empty(),
        ensures
            r == self.spec_max_resp(),
            r.spec_timestamp() == self.spec_max_timestamp(),
    {
        proof {
            use_type_invariant(self);
        }
        self.max_resp.as_ref().unwrap()
    }

    fn update_max_resp_and_quorum(
        max_resp: &mut Option<GetTimestampResponse>,
        agree_with_max: &mut BTreeSet<u64>,
        replies: &mut BTreeSet<C::Id>,
        #[allow(unused_variables)]
        servers: &Tracked<ServerUniverse>,
        resp: GetTimestampResponse,
        id: (u64, u64),
    )
        requires
            !old(replies)@.contains(id),
            !old(agree_with_max)@.contains(id.1),
            Self::replies_inv(old(replies)@, servers@, id.0),
            Self::agree_with_max_aux_inv(old(agree_with_max)@, old(replies)@, *old(max_resp)),
            servers@.contains_key(id.1),
        ensures
            *final(max_resp) is Some,
            !final(agree_with_max)@.is_empty(),
            final(replies)@ == old(replies)@.insert(id),
            Self::replies_inv(final(replies)@, servers@, id.0),
            Self::agree_with_max_aux_inv(final(agree_with_max)@, final(replies)@, *final(max_resp)),
            *old(max_resp) is Some ==> {
                let old_max_ts = old(max_resp)->Some_0.spec_timestamp();
                let new_max_ts = final(max_resp)->Some_0.spec_timestamp();
                &&& resp.spec_timestamp() > old_max_ts ==> {
                    &&& *final(max_resp) == Some(resp)
                    &&& final(agree_with_max)@ == set![id.1]
                }
                &&& resp.spec_timestamp() == old_max_ts ==> {
                    &&& *final(max_resp) == *old(max_resp)
                    &&& final(agree_with_max)@ == old(agree_with_max)@.insert(id.1)
                }
                &&& resp.spec_timestamp() < old_max_ts ==> {
                    &&& *final(max_resp) == *old(max_resp)
                    &&& final(agree_with_max)@ == old(agree_with_max)@
                }
                &&& new_max_ts >= old_max_ts
            },
            *old(max_resp) is None ==> {
                &&& *final(max_resp) == Some(resp)
                &&& final(agree_with_max)@ == set![id.1]
            },
        no_unwind
    {
        let mut new_val = None;
        if let Some(max_resp) = max_resp.as_ref() {
            if resp.timestamp() > max_resp.timestamp() {
                new_val = Some(resp);
            } else if resp.timestamp() == max_resp.timestamp() {
                agree_with_max.insert(id.1);
            }
        } else {
            new_val = Some(resp);
        }

        if new_val.is_some() {
            *max_resp = new_val;
            agree_with_max.clear();
            agree_with_max.insert(id.1);
        }
        replies.insert(id);

        assert(forall|server_id| #[trigger]
            agree_with_max@.contains(server_id) ==> replies@.contains((id.0, server_id)));
    }

    fn insert_aux(
        max_resp: &mut Option<GetTimestampResponse>,
        agree_with_max: &mut BTreeSet<u64>,
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
            resp.req_type() is GetTimestamp,
            resp.request() == request@@,
            resp.get_timestamp().server_token_id() == old(server_tokens)@.id(),
            resp.get_timestamp().loc() == old(servers)@.locs()[resp.server_id()],
            old(servers)@.locs().contains_key(id.1),
            request@.req_type() is GetTimestamp,
            request@.key().0 == id.0,
            Self::server_invs(
                old(servers)@,
                request@.get_timestamp().servers(),
                old(server_tokens)@@,
            ),
            Self::replies_inv(old(replies)@, old(servers)@, id.0),
            Self::agree_with_max_inv(
                old(agree_with_max)@,
                old(replies)@,
                old(servers)@,
                *old(max_resp),
            ),
            Self::unchanged_inv(
                old(servers)@,
                request@.get_timestamp().servers(),
                old(replies)@,
                id.0,
            ),
            *old(max_resp) is Some ==> {
                Self::max_resp_inv(
                    old(max_resp)->Some_0,
                    old(servers)@,
                    old(agree_with_max)@,
                    old(replies)@,
                    old(server_tokens)@.id(),
                )
            },
        ensures
            final(servers)@.locs() == old(servers)@.locs(),
            final(server_tokens)@.id() == old(server_tokens)@.id(),
            final(replies)@ == old(replies)@.insert(id),
            Self::server_invs(
                final(servers)@,
                request@.get_timestamp().servers(),
                final(server_tokens)@@,
            ),
            Self::replies_inv(final(replies)@, final(servers)@, id.0),
            Self::agree_with_max_inv(
                final(agree_with_max)@,
                final(replies)@,
                final(servers)@,
                *final(max_resp),
            ),
            Self::unchanged_inv(
                final(servers)@,
                request@.get_timestamp().servers(),
                final(replies)@,
                id.0,
            ),
            *final(max_resp) is Some ==> {
                Self::max_resp_inv(
                    final(max_resp)->Some_0,
                    final(servers)@,
                    final(agree_with_max)@,
                    final(replies)@,
                    final(server_tokens)@.id(),
                )
            },
        no_unwind
    {
        if replies.contains(&id) {
            return;
        }
        let r = resp.destruct_get_timestamp();

        r.lemma_get_timestamp_response();
        r.lemma_token_agree(server_tokens);
        assert(r.lb()@ is LowerBound);
        let Tracked(lb) = r.duplicate_lb();
        assert(lb@ is LowerBound);

        proof {
            Self::update_servers(
                servers.borrow_mut(),
                request@.get_timestamp().servers(),
                agree_with_max@,
                &*max_resp,
                id.1,
                lb,
            );

            assert forall|cid|
                {
                    &&& !#[trigger] replies@.insert(id).contains(cid)
                    &&& servers@.contains_key(cid.1)
                    &&& cid.0 == request@.key().0
                } implies servers@[cid.1]@@.timestamp()
                == request@.get_timestamp().servers()[cid.1]@@.timestamp() by {
                if cid.1 == id.1 {
                    assert(replies@.insert(id).contains(cid));
                } else {
                    assert(servers@[cid.1]@@.timestamp()
                        == request@.get_timestamp().servers()[cid.1]@@.timestamp());
                }
            }

            if *max_resp is Some {
                assert forall|cid| #[trigger]
                    replies@.contains(cid) implies servers@[cid.1]@@.timestamp()
                    <= max_resp->Some_0.spec_timestamp() by {
                    if cid.1 != id.1 {
                        assert(servers@.contains_key(cid.1));  // trigger
                    }
                }
            }
        }

        Self::update_max_resp_and_quorum(max_resp, agree_with_max, replies, &*servers, r, id);
    }

    fn insert_get_timestamp(&mut self, id: (u64, u64), resp: Response)
        requires
            GetTimestampPred::inv(old(self).constant(), *old(self)),
            old(self).client_id() == id.0,
            resp.req_type() is GetTimestamp,
            resp.get_timestamp().server_id() == id.1,
            resp.request() == old(self).request@@,
            old(self).constant().server_tokens_id == resp.get_timestamp().server_token_id(),
            old(self).constant().server_locs.contains_key(resp.server_id()),
            old(self).constant().server_locs[resp.server_id()] == resp.get_timestamp().loc(),
        ensures
            GetTimestampPred::inv(final(self).constant(), *final(self)),
            final(self).constant() == old(self).constant(),
            final(self).replies() == old(self).replies().insert(id),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }

        Self::insert_aux(
            &mut self.max_resp,
            &mut self.agree_with_max,
            &mut self.replies,
            &mut self.servers,
            &mut self.server_tokens,
            &self.request,
            id,
            resp,
        );
    }
}

impl<C> ReplyAccumulator<C, GetTimestampPred<C>> for GetTimestampAccumulator<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    #[allow(unused_variables)]
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(&mut self, pred: Ghost<GetTimestampPred<C>>, id: (u64, u64), reply: Response)
        ensures
            final(self).channels() == old(self).channels(),
    {
        proof {
            use_type_invariant(&*self);

            assume(C::K::recv_inv(self.channels()[id].constant(), id, reply));  // TODO(verus): this is a verus problem
        }

        reply.agree_request(&mut self.request);
        reply.lemma_inv();

        self.insert_get_timestamp(id, reply);
    }

    open spec fn request_tag(self) -> u64 {
        self.request_id()
    }

    open spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.replies()
    }

    fn handled_replies(&self) -> BTreeSet<C::Id> {
        self.get_ts_replies()
    }

    open spec fn channels(self) -> Map<C::Id, C> {
        self.spec_channels()
    }
}

} // verus!
