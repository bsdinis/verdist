use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants;
use crate::invariants::committed_to::ClientCtrToken;
#[cfg(verus_only)]
use crate::invariants::lin_queue::InsertError;
#[cfg(verus_only)]
use crate::invariants::lin_queue::LinWriteToken;
#[cfg(verus_only)]
use crate::invariants::lin_queue::MaybeWriteLinearized;
#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
#[cfg(verus_only)]
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::requests::RequestCtrToken;
#[cfg(verus_only)]
use crate::invariants::RegisterView;
use crate::invariants::StateInvariant;
use crate::proto::Request;
use crate::proto::RequestInner;
use crate::proto::Response;
use crate::timestamp::Timestamp;

use specs::register::LinRegisterClient;
#[cfg(verus_only)]
use specs::register::RegisterError;
use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use verdist::network::channel::Channel;
use verdist::pool::BroadcastPool;
use verdist::pool::ConnectionPool;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;
use verdist::rpc::replies::ReplyAccumulator;

pub mod error;
mod net_invs;

use net_invs::*;

use vstd::atomic::PAtomicU64;
#[cfg(verus_only)]
use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::proph::Prophecy;
#[cfg(verus_only)]
use vstd::resource::ghost_var::GhostVarAuth;
use vstd::resource::Loc;

use std::hash::Hash;
use std::sync::Arc;

verus! {

#[allow(dead_code)]
pub struct AbdPool<Pool, ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pool: Pool,
    id: u64,
    register_id: Ghost<Loc>,
    state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
    client_ctr_token: Tracked<ClientCtrToken>,
    client_ctr: PAtomicU64,
    request_ctr_token: Tracked<RequestCtrToken>,
    request_ctr: PAtomicU64,
}

impl<Pool, C, ML, RL> AbdPool<Pool, ML, RL> where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Response, S = Request, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(
        pool: Pool,
        id: u64,
        client_ctr: PAtomicU64,
        client_ctr_token: Tracked<ClientCtrToken>,
        request_ctr: PAtomicU64,
        request_ctr_token: Tracked<RequestCtrToken>,
        state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
    ) -> (r: Self)
        requires
            pool.spec_len() > 0,
            forall|cid: (u64, u64)| #[trigger]
                pool.spec_channels().contains_key(cid) ==> {
                    let c = pool.spec_channels()[cid];
                    &&& cid == c.spec_id()
                    &&& cid.0 == id
                    &&& state_inv@.constant().server_locs.contains_key(cid.1)
                    &&& state_inv@.constant().request_map_ids.request_auth_id
                        == c.constant().request_map_id
                    &&& state_inv@.constant().commitments_ids.commitment_id
                        == c.constant().commitment_id
                    &&& state_inv@.constant().server_tokens_id == c.constant().server_tokens_id
                    &&& state_inv@.constant().server_locs == c.constant().server_locs
                },
            state_inv@.namespace() == invariants::state_inv_id(),
            state_inv@.constant().commitments_ids.client_ctr_id == client_ctr_token@.id(),
            state_inv@.constant().request_map_ids.request_ctr_id == request_ctr_token@.id(),
            state_inv@.constant().server_locs.len() == pool.spec_len(),
            client_ctr_token@.key() == id,
            client_ctr_token@.value().0 == 0,
            client_ctr_token@.value().1 == client_ctr.id(),
            request_ctr_token@.key() == id,
            request_ctr_token@.value().0 == 0,
            request_ctr_token@.value().1 == request_ctr.id(),
        ensures
            r._inv(),
            r.register_loc() == state_inv@.constant().register_id,
    {
        AbdPool {
            pool,
            id,
            state_inv,
            register_id: Ghost(state_inv@.constant().register_id),
            client_ctr_token,
            client_ctr,
            request_ctr_token,
            request_ctr,
        }
    }

    closed spec fn spec_len(self) -> nat {
        self.pool.spec_len()
    }

    closed spec fn id(self) -> u64 {
        self.id
    }

    pub closed spec fn _inv(self) -> bool {
        &&& self.pool.spec_len() > 0
        &&& self.state_inv@.namespace() == invariants::state_inv_id()
        &&& self.state_inv@.constant().register_id == self.register_id
        &&& self.state_inv@.constant().commitments_ids.client_ctr_id == self.client_ctr_token@.id()
        &&& self.state_inv@.constant().request_map_ids.request_ctr_id
            == self.request_ctr_token@.id()
        &&& self.client_ctr_token@.key() == self.id()
        &&& self.client_ctr_token@.value().1 == self.client_ctr.id()
        &&& self.request_ctr_token@.key() == self.id()
        &&& self.request_ctr_token@.value().1 == self.request_ctr.id()
        &&& self.pool.spec_len() == self.state_inv@.constant().server_locs.len()
        &&& forall|c_id| #[trigger]
            self.pool.spec_channels().contains_key(c_id) ==> {
                let c = self.pool.spec_channels()[c_id];
                &&& c_id == c.spec_id()
                &&& c_id.0 == self.id
                &&& self.state_inv@.constant().request_map_ids.request_auth_id
                    == c.constant().request_map_id
                &&& self.state_inv@.constant().commitments_ids.commitment_id
                    == c.constant().commitment_id
                &&& self.state_inv@.constant().server_tokens_id == c.constant().server_tokens_id
                &&& self.state_inv@.constant().server_locs == c.constant().server_locs
                &&& self.state_inv@.constant().server_locs.contains_key(c_id.1)
            }
    }

    pub fn quorum_size(&self) -> (r: usize)
        ensures
            r == self.spec_quorum_size(),
    {
        self.pool.len() / 2 + 1
    }

    pub closed spec fn spec_quorum_size(self) -> nat {
        self.spec_len() / 2 + 1
    }

    proof fn lemma_quorum_nonzero(self)
        requires
            self.spec_len() > 0,
        ensures
            self.spec_quorum_size() > 0,
    {
    }

    closed spec fn client_id(self) -> u64 {
        self.id()
    }
}

impl<Pool, C, ML, RL> LinRegisterClient<C, ML, RL> for AbdPool<Pool, ML, RL> where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Response, S = Request, Id = (u64, u64), K = ChannelInv>,
    C::Id: Eq + Hash,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    type ReadErr = error::ReadError<RL, RL::Completion>;

    type WriteErr = error::WriteError<ML, ML::Completion>;

    type Timestamp = Timestamp;

    open spec fn read_lin_requires(lin: RL) -> bool {
        &&& !lin.namespaces().contains(invariants::state_inv_id())
        &&& lin.namespaces().finite()
    }

    open spec fn write_lin_requires(lin: ML) -> bool {
        &&& !lin.namespaces().contains(invariants::state_inv_id())
        &&& lin.namespaces().finite()
    }

    closed spec fn register_loc(self) -> Loc {
        self.register_id@
    }

    closed spec fn inv(self) -> bool {
        self._inv()
    }

    fn read(&mut self, Tracked(lin): Tracked<RL>) -> (r: Result<
        (Option<u64>, Timestamp, Tracked<RL::Completion>),
        error::ReadError<RL, RL::Completion>,
    >) {
        let tracked op = RegisterRead { id: Ghost(self.register_loc()) };
        // NOTE: IMPORTANT: We need to add the linearizer to the queue at this point -- see
        // discussion on `write`
        let proph_val = Prophecy::<Option<u64>>::new();
        let tracked token;
        let tracked server_lbs;
        let tracked server_tokens_lb;
        let ghost state_constant = self.state_inv@.constant();
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                broadcast use vstd::map_lib::lemma_submap_of_trans;
                server_lbs = state.servers.extract_lbs();
                server_tokens_lb = state.server_tokens.lower_bound();
                assert(server_tokens_lb@ == state.server_tokens@);
                state.servers.lemma_leq_quorums(server_lbs, state.linearization_queue.watermark());
                token = state.linearization_queue.insert_read_linearizer(lin, op, proph_val@, &state.register);

                assert(forall|q: Quorum|  #[trigger] server_lbs.valid_quorum(q) ==> {
                    token.value().min_ts@.timestamp() <= server_lbs.quorum_timestamp(q)
                });
            }
            // XXX: debug assert
            assert(state.inv());
        });

        let req_inner = RequestInner::new_get(Tracked(server_lbs.extract_lbs()));
        let tracked request_proof;
        let request_id;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            let ghost old_dom = state.request_map.request_ctr_map().dom();
            let tracked mut perm;
            proof {
                perm = state.request_map.take_permission(self.request_ctr_token.borrow());
            }
            assume(perm.value() < u64::MAX); // XXX: integer overflow
            request_id = self.request_ctr.fetch_add(Tracked(&mut perm), 1);
            proof {
                request_proof = state.request_map.issue_request_proof(
                    self.request_ctr_token.borrow_mut(),
                    request_id,
                    req_inner, perm
                );
                assert(state.request_map.request_ctr_map().dom() == old_dom);
            }
            // XXX: debug assert
            assert(state.inv());
        });

        let req = Request::new(self.id, request_id, req_inner, Tracked(request_proof.duplicate()));

        let ghost qsize = self.spec_quorum_size();
        let bpool = BroadcastPool::new(&self.pool);
        let read_pred = Ghost(
            ReadPred::new(
                state_constant,
                bpool.spec_channels(),
                token.value().min_ts,
                self.id,
                request_proof,
            ),
        );
        let tracked server_lbs_cpy;
        proof {
            server_lbs_cpy = server_lbs.extract_lbs();
            ServerUniverse::lemma_eq_timestamp_trans(
                request_proof.get().servers(),
                server_lbs,
                server_lbs_cpy,
            );
            server_lbs.lemma_leq_quorums(server_lbs_cpy, read_pred@.min_timestamp);
        }
        #[allow(unused_parens)]
        let accum = ReadAccumGetPhase::new(
            Tracked(server_lbs_cpy),
            Tracked(server_tokens_lb),
            Tracked(request_proof),
            read_pred,
        );
        let quorum_res = bpool.broadcast(req, read_pred, accum).wait_for(
            |s| -> (r: bool)
                ensures
                    r ==> s.spec_len() >= qsize,
                { s.len() >= self.quorum_size() },
        );

        let replies = match quorum_res {
            Ok(replies) => replies.into_accumulator().destruct(),
            Err(e) => {
                let tracked lincomp;
                vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                    proof {
                        lincomp = state.linearization_queue.remove_read_lin(token);
                    }
                    // XXX: debug assert
                    assert(state.inv());
                });
                return Err(
                    error::ReadError::FailedFirstQuorum {
                        obtained: e.into_accumulator().handled_replies().len(),
                        required: self.quorum_size(),
                        lincomp: Tracked(lincomp),
                    },
                );
            },
        };

        assert(replies.constant() == read_pred@);
        let agree_with_max = replies.agree_with_max().clone();
        let max_resp = replies.max_resp();
        let max_ts = max_resp.timestamp();
        let value = max_resp.value().clone();
        let Tracked(commitment) = max_resp.commitment();
        proph_val.resolve(&value);

        replies.lemma_first_quorum();
        // check the size of the servers
        {
            let Tracked(replies_servers) = replies.servers_lb();  // needed to have an owned instance
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                proof {
                    state.servers.lemma_locs();
                    replies_servers.lemma_locs();

                    // NOTE: this is an annoying thing from the way that equality works for
                    // ServerUniverse. Even though replies_server does not change, it is not `==`
                    let ghost old_replies_servers = replies_servers;
                    replies_servers.lemma_lb(&state.servers);
                    old_replies_servers.lemma_eq(replies_servers);
                    assert(old_replies_servers.valid_quorum(replies.first_quorum()));
                    replies_servers.lemma_leq_implies_validity(state.servers, replies.first_quorum());
                }
            });
        }
        replies.lemma_max_min();
        assert(replies.spec_min_timestamp() <= replies.spec_max_timestamp());
        vlib::veprintln!("\n[client|{:>3}]: got first round reads quorum_size: {} agree_with_max: {:?}\n", self.id, self.quorum_size(), replies.agree_with_max());
        // check early return
        if replies.agree_with_max().len() >= self.quorum_size() {
            vlib::veprintln!("[client|{:>3}]: first round is unanimous", self.id);
            replies.lemma_quorum();
            replies.lemma_max_timestamp();
            let Tracked(replies_servers) = replies.servers_lb();  // needed to have an owned instance
            let tracked comp;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                proof {
                    let ghost old_known = state.linearization_queue.known_timestamps();
                    state.servers.lemma_locs();
                    replies_servers.lemma_locs();

                    state.commitments.agree_commitment(&commitment);
                    // NOTE: this is an annoying thing from the way that equality works for
                    // ServerUniverse. Even though replies_server does not change, it is not `==`
                    let ghost old_replies_servers = replies_servers;
                    replies_servers.lemma_lb(&state.servers);
                    old_replies_servers.lemma_eq(replies_servers);
                    assert(old_replies_servers.valid_quorum(replies.quorum()));
                    replies_servers.lemma_leq_implies_validity(state.servers, replies.quorum());
                    replies_servers.lemma_leq_retains_unanimity(state.servers, replies.quorum(), max_ts);
                    state.servers.lemma_quorum_lb(replies.quorum(), max_ts);

                    let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                    let tracked watermark = state.linearization_queue.apply_linearizers_up_to(
                            &mut state.register,
                            max_ts,
                    );

                    comp = state.linearization_queue.extract_read_completion(
                        token,
                        max_ts,
                        watermark,
                        commitment.duplicate(),
                    );

                    // XXX: load bearing
                    assert(state.linearization_queue.known_timestamps() == old_known);
                }

                // XXX: debug assert
                assert(state.inv());
            });
            return Ok((value, max_ts, Tracked(comp)));
        }
        // non-unanimous read: write-back

        let req_inner = RequestInner::new_write(
            value,
            max_ts,
            Tracked(commitment.duplicate()),
            Tracked(server_lbs),
        );
        let tracked request_proof;
        let request_id;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            let ghost old_dom = state.request_map.request_ctr_map().dom();
            let tracked mut perm;
            proof {
                perm = state.request_map.take_permission(self.request_ctr_token.borrow());
            }
            assume(perm.value() < u64::MAX); // XXX: integer overflow
            request_id = self.request_ctr.fetch_add(Tracked(&mut perm), 1);
            proof {
                request_proof = state.request_map.issue_request_proof(
                    self.request_ctr_token.borrow_mut(),
                    request_id,
                    req_inner,
                    perm
                );
                assert(state.request_map.request_ctr_map().dom() == old_dom);
            }
            // XXX: debug assert
            assert(state.inv());
        });

        let req = Request::new(self.id, request_id, req_inner, Tracked(request_proof.duplicate()));
        let read_wb_pred = Ghost(
            ReadWbPred {
                read_pred: ReadPred { wb_request_id: Some(request_proof.key().1), ..read_pred@ },
                max_resp: *max_resp,
            },
        );
        let ghost qsize = self.spec_quorum_size();
        let bpool = BroadcastPool::new(&self.pool);
        let accum = ReadAccumWbPhase::new(replies, Tracked(request_proof));
        #[allow(unused_parens)]
        let replies_result = bpool.broadcast_filter(
            req,
            read_wb_pred,
            accum,
            |id: (u64, u64)| !agree_with_max.contains(&id.1),
        ).wait_for(
            (|s| -> (r: bool)
                ensures
                    r ==> s.spec_accumulator().spec_agree_with_max().len() >= qsize,
                { s.accumulator().agree_with_max().len() >= self.quorum_size() }),
        );

        let wb_replies = match replies_result {
            Ok(r) => r.into_accumulator().destruct(),
            Err(replies) => {
                let tracked lincomp;
                vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                    proof {
                        lincomp = state.linearization_queue.remove_read_lin(token);
                    }
                    // XXX: debug assert
                    assert(state.inv());
                });
                let accum = replies.into_accumulator().destruct();
                return Err(
                    error::ReadError::FailedSecondQuorum {
                        obtained: accum.wb_replies().len(),
                        required: self.quorum_size().saturating_sub(accum.agree_with_max().len()),
                        lincomp: Tracked(lincomp),
                    },
                );
            },
        };

        vlib::veprintln!("\n[client|{:>3}]: got read writeback round quorum_size: {} agree_with_max: {:?}\n", self.id, self.quorum_size(), wb_replies.agree_with_max());

        let tracked comp;
        wb_replies.lemma_quorum();
        wb_replies.lemma_max_timestamp();
        let Tracked(replies_servers) = wb_replies.servers_lb();  // needed to have an owned instance
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                let ghost old_known = state.linearization_queue.known_timestamps();
                state.servers.lemma_locs();
                replies_servers.lemma_locs();

                state.commitments.agree_commitment(&commitment);
                // NOTE: this is an annoying thing from the way that equality works for
                // ServerUniverse. Even though replies_server does not change, it is not `==`
                let ghost old_replies_servers = replies_servers;
                replies_servers.lemma_lb(&state.servers);
                old_replies_servers.lemma_eq(replies_servers);
                assert(old_replies_servers.valid_quorum(wb_replies.quorum()));
                replies_servers.lemma_leq_implies_validity(state.servers, wb_replies.quorum());
                replies_servers.lemma_leq_retains_unanimity(state.servers, wb_replies.quorum(), max_ts);
                assert(state.servers.unanimous_quorum(wb_replies.quorum(), max_ts));
                state.servers.lemma_quorum_lb(wb_replies.quorum(), max_ts);

                let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                let tracked watermark = state.linearization_queue.apply_linearizers_up_to(
                        &mut state.register,
                        max_ts,
                );

                comp = state.linearization_queue.extract_read_completion(
                    token,
                    max_ts,
                    watermark,
                    commitment.duplicate(),
                );

                // XXX: load bearing
                assert(state.linearization_queue.known_timestamps() == old_known);
            }

            // XXX: debug assert
            assert(state.inv());
        });
        return Ok((value, max_ts, Tracked(comp)));
    }

    fn write(&mut self, value: Option<u64>, Tracked(lin): Tracked<ML>) -> (r: Result<
        Tracked<ML::Completion>,
        error::WriteError<ML, ML::Completion>,
    >) {
        let tracked op = RegisterWrite { id: Ghost(self.register_loc()), new_value: value };
        // NOTE: IMPORTANT: We need to add the linearizer to the queue at this point
        //
        // Imagine if we added this after the read quorum is achieved
        // and we know which timestamp we are writing to.
        //
        // A concurrent write can read the same timestamp but write to a posterior one
        // (by having a greater client id)
        //
        // This means that secondary write can actually go ahead and finish before the first phase
        // of our write finishes
        //
        // Consequently, when they apply all the linearizers up to their watermark, our linearizer
        // is not there. This breaks the invariant on the linearization queue: all possible
        // linearizers refering to timestamps not greater than the watermark (increased when the
        // linearizers are applied) have been applied
        //
        // The way we go about this is by prophecizing the timestamp a write will get and put it in
        // the queue immediately. Once we figure out the timestamp, we resolve the prophecy
        // variable.
        let proph_seqno = Prophecy::<u64>::new();
        let tracked token_res;
        let client_ctr;
        let tracked server_lbs;
        let tracked server_tokens_lb;
        let ghost state_constant = self.state_inv@.constant();
        let ghost old_watermark;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            let ghost old_dom = state.commitments.client_map().dom();
            let tracked mut perm;
            proof {
                perm = state.commitments.take_permission(self.client_ctr_token.borrow());
            }

            assume(perm.value() < u64::MAX); // XXX: integer overflow
            client_ctr = self.client_ctr.fetch_add(Tracked(&mut perm), 1);
            let ghost proph_ts = Timestamp { seqno: proph_seqno@, client_id: self.client_id(), client_ctr };

            proof {
                broadcast use vstd::map_lib::lemma_submap_of_trans;
                server_lbs = state.servers.extract_lbs();
                server_tokens_lb = state.server_tokens.lower_bound();
                assert(server_tokens_lb@ == state.server_tokens@);
                state.servers.lemma_leq_quorums(server_lbs, state.linearization_queue.watermark());
                let ghost old_known = state.linearization_queue.known_timestamps();

                let tracked allocation_opt = if proph_ts > state.linearization_queue.watermark() {
                    let tracked mut allocation = state.commitments.alloc_value(self.client_ctr_token.borrow_mut(), proph_ts, op.new_value, perm);
                    state.commitments.agree_allocation(&allocation);

                    // XXX: load bearing
                    assert(!state.linearization_queue.known_timestamps().contains(proph_ts));
                    state.linearization_queue.lemma_known_timestamps();

                    Some(allocation)
                } else {
                    state.commitments.return_permission(self.client_ctr_token.borrow_mut(), perm);
                    None
                };
                assert(state.commitments.client_map().dom() == old_dom);

                token_res = state.linearization_queue.insert_write_linearizer(lin, op, proph_ts, allocation_opt);

                old_watermark = state.linearization_queue.watermark();

                // XXX: load bearing
                assert(token_res is Ok ==> state.linearization_queue.known_timestamps() == old_known.insert(proph_ts));
            }
            // XXX: debug assert
            assert(state.inv());
        });
        let ghost proph_ts = Timestamp {
            seqno: proph_seqno@,
            client_id: self.client_id(),
            client_ctr,
        };

        let req_inner = RequestInner::new_get_timestamp(Tracked(server_lbs.extract_lbs()));
        let tracked request_proof;
        let request_id;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            let ghost old_dom = state.request_map.request_ctr_map().dom();
            let tracked mut perm;
            proof {
                perm = state.request_map.take_permission(self.request_ctr_token.borrow());
            }
            assume(perm.value() < u64::MAX); // XXX: integer overflow
            request_id = self.request_ctr.fetch_add(Tracked(&mut perm), 1);
            proof {
                request_proof = state.request_map.issue_request_proof(
                    self.request_ctr_token.borrow_mut(),
                    request_id,
                    req_inner,
                    perm
                );
                request_proof.get_timestamp().servers().lemma_eq(server_lbs);
                assert(state.request_map.request_ctr_map().dom() == old_dom);
            }
            // XXX: debug assert
            assert(state.inv());
        });

        let req = Request::new(self.id, request_id, req_inner, Tracked(request_proof.duplicate()));

        let bpool = BroadcastPool::new(&self.pool);
        let get_ts_pred = Ghost(
            GetTimestampPred::new(state_constant, bpool.spec_channels(), self.id, request_proof),
        );
        let get_ts_replies = {
            let ghost qsize = self.spec_quorum_size();
            let accum = GetTimestampAccumulator::new(
                Tracked(server_lbs),
                Tracked(server_tokens_lb),
                Tracked(request_proof),
                get_ts_pred,
            );
            #[allow(unused_parens)]
            let quorum_res = bpool.broadcast(req, get_ts_pred, accum).wait_for(
                (|s| -> (r: bool)
                    ensures
                        r ==> s.spec_len() >= qsize,
                    { s.len() >= self.quorum_size() }),
            );

            match quorum_res {
                Ok(q) => q.into_accumulator(),
                Err(e) => {
                    let tracked lincomp;
                    vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                        let ghost old_dom = state.commitments.client_map().dom();
                        proof {
                            if &token_res is Ok {
                                let tracked token = token_res.tracked_unwrap();

                                let tracked (lc, allocation_opt) = state.linearization_queue.remove_write_lin(token);

                                // if this write had not been committed we need to remove it from
                                // the commitment map
                                if &allocation_opt is Some {
                                    let tracked allocation = allocation_opt.tracked_unwrap();
                                    state.commitments.remove_allocation(allocation, self.client_ctr_token.borrow());
                                    // XXX: load bearing
                                    assert(state.commitments.client_map().dom() == old_dom);
                                    assert(state.linearization_queue.known_timestamps() == state.commitments.allocated().dom());
                                }
                                lincomp = lc;
                            } else {
                                let tracked err = token_res.tracked_unwrap_err();
                                let tracked err_lin = err.tracked_write_destruct();
                                lincomp = MaybeWriteLinearized::linearizer(err_lin, op, proph_ts);
                            }
                        }
                        // XXX: debug assert
                        assert(state.inv());
                    });

                    return Err(
                        error::WriteError::FailedFirstQuorum {
                            obtained: e.into_accumulator().n_replies(),
                            required: self.quorum_size(),
                            lincomp: Tracked(lincomp),
                        },
                    );
                },
            }
        };

        vlib::veprintln!("\n[client|{:>3}]: got write get timestamp round quorum_size: {} quorum: {:?} max_timestamp: {:?}\n", self.id, self.quorum_size()
            , get_ts_replies.get_ts_replies(), get_ts_replies.max_resp().timestamp() );

        assert(get_ts_replies.constant() == get_ts_pred@);
        let max_resp = get_ts_replies.max_resp();
        let max_ts = max_resp.timestamp();
        get_ts_replies.lemma_quorum();
        get_ts_replies.lemma_max_timestamp();

        // XXX: timestamp recycling would be interesting
        assume(max_ts.seqno < u64::MAX - 1);  // XXX: integer overflow
        let exec_seqno = max_ts.seqno + 1;
        let exec_ts = Timestamp { seqno: exec_seqno, client_id: self.id, client_ctr };
        proph_seqno.resolve(&exec_seqno);
        assert(proph_ts == exec_ts);

        let tracked token;
        let tracked mut commitment;
        {
            let Tracked(replies_servers) = get_ts_replies.servers_lb();  // needed to have an owned instance
            let ghost replies_orig_servers = get_ts_replies.orig_servers();
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                proof {
                    state.servers.lemma_locs();
                    replies_servers.lemma_locs();

                    // NOTE: this is an annoying thing from the way that equality works for
                    // ServerUniverse. Even though replies_server does not change, it is not `==`
                    let ghost old_replies_servers = replies_servers;
                    let ghost quorum = get_ts_replies.quorum();
                    old_replies_servers.lemma_eq(replies_servers);
                    assert(old_replies_servers.valid_quorum(quorum));

                    ServerUniverse::lemma_leq_trans(replies_orig_servers, old_replies_servers, replies_servers);
                    replies_orig_servers.lemma_leq_implies_validity(replies_servers, quorum);

                    let tracked mut tk = lemma_watermark_contradiction(
                        token_res,
                        proph_ts,
                        old_watermark,
                        lin,
                        op,
                        replies_orig_servers,
                        replies_servers,
                        state.linearization_queue.write_token_id(),
                        quorum
                    );

                    commitment = state.linearization_queue.commit_value(&mut tk);
                    token = tk;
                }

                // XXX: debug assert
                assert(state.inv());
            });
        }

        let tracked server_lbs;
        let tracked server_tokens_lb;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                server_lbs = state.servers.extract_lbs();
                server_tokens_lb = state.server_tokens.lower_bound();
            }
        });

        {
            let req_inner = RequestInner::new_write(
                value,
                exec_ts,
                Tracked(commitment.duplicate()),
                Tracked(server_lbs.extract_lbs()),
            );
            let tracked request_proof;
            let request_id;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                let ghost old_dom = state.request_map.request_ctr_map().dom();
                let tracked mut perm;
                proof {
                    perm = state.request_map.take_permission(self.request_ctr_token.borrow());
                }
                assume(perm.value() < u64::MAX); // XXX: integer overflow
                request_id = self.request_ctr.fetch_add(Tracked(&mut perm), 1);
                proof {
                    request_proof = state.request_map.issue_request_proof(
                        self.request_ctr_token.borrow_mut(),
                        request_id,
                        req_inner,
                        perm
                    );
                    assert(state.request_map.request_ctr_map().dom() == old_dom);
                }
                // XXX: debug assert
                assert(state.inv());
            });

            let req = Request::new(
                self.id,
                request_id,
                req_inner,
                Tracked(request_proof.duplicate()),
            );

            let bpool = BroadcastPool::new(&self.pool);
            let write_pred = Ghost(
                WritePred::new(state_constant, bpool.spec_channels(), self.id, request_proof),
            );
            let tracked server_lbs_cpy;
            proof {
                server_lbs_cpy = server_lbs.extract_lbs();
                ServerUniverse::lemma_eq_timestamp_trans(
                    request_proof.write().servers(),
                    server_lbs,
                    server_lbs_cpy,
                );
            }
            let accum = WriteAccumulator::new(
                Tracked(server_lbs_cpy),
                Tracked(server_tokens_lb),
                Tracked(request_proof),
                write_pred,
            );
            let ghost qsize = self.spec_quorum_size();
            #[allow(unused_parens)]
            let quorum_res = bpool.broadcast(req, write_pred, accum).wait_for(
                (|s| -> (r: bool)
                    ensures
                        r ==> s.spec_len() >= qsize,
                    { s.len() >= self.quorum_size() }),
            );

            let write_replies = match quorum_res {
                Ok(q) => q.into_accumulator(),
                Err(e) => {
                    return Err(
                        error::WriteError::FailedSecondQuorum {
                            obtained: e.into_accumulator().n_replies(),
                            required: self.quorum_size(),
                            timestamp: exec_ts,
                            token: Tracked(token),
                            commitment: Tracked(commitment),
                        },
                    );
                },
            };

            vlib::veprintln!("\n[client|{:>3}]: got write quorum quorum_size: {} quorum: {:?}\n", self.id, self.quorum_size() , write_replies.write_replies());

            let exec_comp;
            write_replies.lemma_quorum();
            write_replies.lemma_timestamp();
            let Tracked(replies_servers) = write_replies.servers_lb();  // needed to have an owned instance
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                let tracked comp;
                proof {
                    let ghost old_known = state.linearization_queue.known_timestamps();
                    let ghost old_watermark = state.linearization_queue.watermark();

                    state.servers.lemma_locs();
                    replies_servers.lemma_locs();

                    // NOTE: this is an annoying thing from the way that equality works for
                    // ServerUniverse. Even though replies_server does not change, it is not `==`
                    let ghost old_replies_servers = replies_servers;
                    let ghost quorum = write_replies.quorum();
                    replies_servers.lemma_lb(&state.servers);
                    old_replies_servers.lemma_eq(replies_servers);
                    assert(old_replies_servers.valid_quorum(quorum));

                    replies_servers.lemma_leq_retains_unanimity(state.servers, quorum, exec_ts);
                    state.linearization_queue.lemma_write_token(&token);
                    state.commitments.agree_commitment(&commitment);

                    let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                    let tracked resource = state.linearization_queue.apply_linearizers_up_to(&mut state.register, exec_ts);

                    if exec_ts > old_watermark {
                        state.servers.lemma_quorum_lb(quorum, exec_ts);
                        assert(state.linearization_queue.watermark() == exec_ts);
                    } else {
                        assert(old_watermark == state.linearization_queue.watermark());
                    }

                    comp = state.linearization_queue.extract_write_completion(token, resource);

                    // XXX: load bearing
                    assert(state.linearization_queue.known_timestamps() == old_known);
                }

                exec_comp = Tracked(comp);

                // XXX: debug assert
                assert(state.inv());
            });

            Ok(exec_comp)
        }
    }
}

pub proof fn lemma_inv<Pool, C, ML, RL>(c: AbdPool<Pool, ML, RL>) where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Response, S = Request, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    ensures
        c._inv() <==> c.inv(),
{
}

pub proof fn lemma_watermark_contradiction<ML, RL>(
    tracked token_res: Result<LinWriteToken<ML>, InsertError<ML, RL>>,
    timestamp: Timestamp,
    old_watermark: Timestamp,
    lin: ML,
    op: RegisterWrite,
    orig_servers: ServerUniverse,
    servers: ServerUniverse,
    write_token_id: Loc,
    quorum: Quorum,
) -> (tracked tok: LinWriteToken<ML>) where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    requires
        orig_servers.inv(),
        orig_servers.is_lb(),
        servers.inv(),
        servers.is_lb(),
        servers.valid_quorum(quorum),
        orig_servers.leq(servers),
        orig_servers.valid_quorum(quorum),
        servers.valid_quorum(quorum),
        old_watermark <= orig_servers.quorum_timestamp(quorum),
        servers.quorum_timestamp(quorum) < timestamp,
        token_res is Ok ==> {
            let tok = token_res->Ok_0;
            &&& tok.key() == timestamp
            &&& tok.value().lin == lin
            &&& tok.value().op == op
            &&& tok.id() == write_token_id
        },
        token_res is Err ==> ({
            let err = token_res->Err_0;
            let watermark_lb = token_res->Err_0->w_watermark_lb;
            &&& err is WriteWatermarkContradiction
            &&& timestamp <= watermark_lb@.timestamp()
            &&& watermark_lb@ is LowerBound
            &&& watermark_lb@.timestamp() == old_watermark
        }),
    ensures
        tok == token_res->Ok_0,
        tok.key() == timestamp,
        tok.value().lin == lin,
        tok.value().op == op,
        tok.id() == write_token_id,
        token_res is Ok,
{
    if &token_res is Err {
        let tracked err = token_res.tracked_unwrap_err();
        assert(err is WriteWatermarkContradiction);
        let tracked mut watermark_lb = err.lower_bound();

        // derive the contradiction
        //
        // proph_ts <= watermark_old
        assert(timestamp <= watermark_lb@.timestamp());
        assert(watermark_lb@.timestamp() == old_watermark);
        // old_watermark <= quorum.timestamp() (forall valid quorums in orig_servers)
        assert(old_watermark <= orig_servers.quorum_timestamp(quorum));
        // orig_servers <= servers ==> orig_servers.quorum_timestamp(quorum) <= server.quorum_timestamp(quorum)
        orig_servers.lemma_leq_quorum_timestamp(servers, quorum);
        assert(orig_servers.quorum_timestamp(quorum) <= servers.quorum_timestamp(quorum));
        // quorum.timestamp() < proph_ts (by construction)
        assert(servers.quorum_timestamp(quorum) < timestamp);
        // CONTRADICTION
        assert(timestamp < timestamp);
        proof_from_false()
    } else {
        let tracked token = token_res.tracked_unwrap();
        token
    }
}

} // verus!
