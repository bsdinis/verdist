#[cfg(verus_only)]
use crate::invariants;
use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::ServerToken;
use crate::invariants::StateInvariant;
use crate::proto::GetRequest;
use crate::proto::GetTimestampRequest;
use crate::proto::WriteRequest;
use crate::proto::WriteResponse;
use crate::proto::{GetResponse, GetTimestampResponse};
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use std::sync::Arc;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::RwLock;

verus! {

#[allow(dead_code)]
pub struct RegisterIds {
    pub resource_loc: Loc,
    pub commitment_id: Loc,
    pub server_token_id: Loc,
    pub state_inv_id: int,
    pub id: u64,
}

#[allow(dead_code)]
pub struct MonotonicRegisterInner<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub id: u64,
    pub value: Option<u64>,
    pub timestamp: Timestamp,
    pub commitment: Tracked<WriteCommitment>,
    pub resource: Tracked<MonotonicTimestampResource>,
    pub state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
    pub server_token: Tracked<ServerToken>,
}

impl<ML, RL> MonotonicRegisterInner<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(
        #[allow(unused_variables)]
        server_id: u64,
        state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
    ) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
            state_inv@.constant().server_locs.contains_key(server_id),
        ensures
            r.id == server_id,
            r.value is None,
            r.timestamp == Timestamp::spec_default(),
            r.resource@@ is HalfRightToAdvance,
            r.id() == server_id,
            r.commitment_id() == state_inv@.constant().commitments_ids.commitment_id,
            r.server_token_id() == state_inv@.constant().server_tokens_id,
            r.resource_loc() == state_inv@.constant().server_locs[server_id],
            r.inv(),
    {
        let tracked zero_commitment;
        let tracked resource;
        let tracked server_token;
        vstd::open_atomic_invariant!(&state_inv.borrow() => state => {
            proof {
                zero_commitment = state.commitments.zero_commitment();

                let ghost old_servers = state.servers;
                let ghost old_unclaimed = state.unclaimed_servers();
                let ghost old_tokens = state.server_tokens@;

                assert(old_tokens <= old_servers.locs());
                assume(state.unclaimed_servers().contains(server_id)); // XXX: server login
                old_servers.lemma_dom();
                assert(old_servers.dom().contains(server_id));
                assert(old_servers.contains_key(server_id));
                resource = state.servers.split_auth(server_id);
                server_token = state.server_tokens.insert(server_id, resource.loc());
                state.servers.lemma_dom();
                assert forall |id| #[trigger] state.unclaimed_servers().contains(id) implies state.servers[id]@@ is FullRightToAdvance by {
                    assert(state.servers.dom().contains(id));
                    assert(old_servers.dom().contains(id));
                    assert(old_servers.contains_key(id)); // TRIGGER
                    // TRIGGER case search (?)
                    if old_unclaimed.contains(id) {
                    } else {
                    }
                }

                state.servers.lemma_dom();
                assert(state.servers.dom().contains(server_id));
                assert(state.servers.contains_key(server_id));
                state.servers.lemma_index_loc(server_id);
                assert(resource.loc() == state.servers.locs()[server_id]);
                assert(state.server_tokens@ <= state.servers.locs());
                state.servers.lemma_locs();
                assert(state.servers.locs().dom() == state.servers.dom());
                assert forall |id| #[trigger] state.server_tokens@.contains_key(id) implies state.servers[id]@@ is HalfRightToAdvance by {
                    assert(state.servers.dom().contains(id));
                    assert(old_servers.dom().contains(id));
                    assert(old_servers.contains_key(id)); // TRIGGER
                }

                old_servers.lemma_leq_quorums(state.servers, state.linearization_queue.watermark());
            }
            // XXX: debug assert
            assert(state.inv());
        });
        MonotonicRegisterInner {
            id: server_id,
            value: None,
            timestamp: Timestamp::default(),
            resource: Tracked(resource),
            commitment: Tracked(zero_commitment),
            server_token: Tracked(server_token),
            state_inv,
        }
    }

    pub open spec fn ids(self) -> RegisterIds {
        RegisterIds {
            resource_loc: self.resource_loc(),
            state_inv_id: self.state_inv_id(),
            commitment_id: self.commitment_id(),
            server_token_id: self.server_token_id(),
            id: self.id(),
        }
    }

    pub closed spec fn resource_loc(self) -> Loc {
        self.resource@.loc()
    }

    pub closed spec fn state_inv_id(self) -> int {
        self.state_inv@.namespace()
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.commitment@.id()
    }

    pub closed spec fn server_token_id(self) -> Loc {
        self.server_token@.id()
    }

    pub closed spec fn id(self) -> u64 {
        self.server_token@.key()
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.id == self.id()
        &&& self.timestamp == self.resource@@.timestamp()
        &&& self.timestamp == self.commitment@.key()
        &&& self.value == self.commitment@.value()
        &&& self.state_inv@.namespace() == invariants::state_inv_id()
        &&& self.server_token@.value() == self.resource@.loc()
        &&& self.server_token@.id() == self.state_inv@.constant().server_tokens_id
        &&& self.commitment_id() == self.state_inv@.constant().commitments_ids.commitment_id
    }

    #[allow(unused_variables)]
    pub fn read(&self, mut req: GetRequest) -> (r: GetResponse)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
        ensures
            r.spec_value() == self.value,
            r.spec_timestamp() == self.timestamp,
            r.spec_commitment().id() == self.commitment_id(),
            r.server_token_id() == self.server_token_id(),
            r.loc() == self.resource_loc(),
            r.server_id() == self.id(),
            req.servers().contains_key(r.server_id()),
            req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp(),
    {
        proof {
            req.servers().lemma_locs();
            req.servers().lemma_dom();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
        }
        let lb = req.server_lower_bound(Ghost(self.id()));
        proof {
            req.servers().lemma_locs();
            req.servers().lemma_dom();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
            req.servers().lemma_index_loc(self.id());
        }

        let tracked r = self.resource.borrow();

        let tracked commitment;
        let tracked new_lb;
        let tracked server_token;
        proof {
            let tracked Tracked(mut lb) = lb;
            lb.lemma_lower_bound(r);

            new_lb = r.extract_lower_bound();
            commitment = self.commitment.borrow().duplicate();
            server_token = self.server_token.borrow().duplicate();

            assert(new_lb@.timestamp() >= lb@.timestamp());
            assert(new_lb@.timestamp() == self.timestamp);
            assert(new_lb@.timestamp() == commitment.key());
            assert(commitment.value() == self.value);
        }

        assert(req.servers()[self.id()]@@.timestamp() == lb@@.timestamp());
        assert(req.servers()[self.id()]@@.timestamp() <= r@.timestamp());
        assert(req.servers()[self.id()]@@.timestamp() <= new_lb@.timestamp());
        GetResponse::new(
            self.value,
            self.timestamp,
            Tracked(new_lb),
            Tracked(commitment),
            Tracked(server_token),
        )
    }

    #[allow(unused_variables)]
    pub fn read_timestamp(&self, mut req: GetTimestampRequest) -> (r: GetTimestampResponse)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
        ensures
            r.spec_timestamp() == self.timestamp,
            r.server_token_id() == self.server_token_id(),
            r.loc() == self.resource_loc(),
            r.server_id() == self.id(),
            req.servers().contains_key(r.server_id()),
            req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp(),
    {
        proof {
            req.servers().lemma_locs();
            req.servers().lemma_dom();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
        }
        let lb = req.server_lower_bound(Ghost(self.id()));
        proof {
            req.servers().lemma_locs();
            req.servers().lemma_dom();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
            req.servers().lemma_index_loc(self.id());
        }

        let tracked r = self.resource.borrow();

        let tracked new_lb;
        let tracked server_token;
        proof {
            let tracked Tracked(mut lb) = lb;
            lb.lemma_lower_bound(r);

            new_lb = r.extract_lower_bound();
            server_token = self.server_token.borrow().duplicate();

            assert(new_lb@.timestamp() >= lb@.timestamp());
            assert(new_lb@.timestamp() == self.timestamp);
        }

        assert(req.servers()[self.id()]@@.timestamp() == lb@@.timestamp());
        assert(req.servers()[self.id()]@@.timestamp() <= r@.timestamp());
        assert(req.servers()[self.id()]@@.timestamp() <= new_lb@.timestamp());
        GetTimestampResponse::new(self.timestamp, Tracked(new_lb), Tracked(server_token))
    }

    pub fn write(self, req: WriteRequest) -> (r: Self)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
            req.commitment_id() == self.commitment_id(),
        ensures
            r.inv(),
            r.ids() == self.ids(),
            r.resource@@ is HalfRightToAdvance,
            req.spec_timestamp() > self.timestamp ==> r.timestamp == req.spec_timestamp() && r.value
                == req.spec_value(),
            req.spec_timestamp() <= self.timestamp ==> self == r,
            req.spec_timestamp() <= r.timestamp,
            req.servers().contains_key(r.id()),
            req.servers()[r.id()]@@.timestamp() <= r.timestamp,
            req.spec_timestamp() <= r.timestamp,
    {
        proof {
            req.servers().lemma_locs();
            req.servers().lemma_dom();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
            req.servers().lemma_index_loc(self.id());
        }
        #[allow(unused_variables)]
        let (value, timestamp, commitment, lb) = req.destruct(self.id);
        let ret = if timestamp > self.timestamp {
            let tracked mut r = self.resource.get();
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                proof {
                    let ghost old_servers = state.servers;
                    old_servers.lemma_locs();
                    old_servers.lemma_dom();
                    assert(state.server_tokens@ <= old_servers.locs());
                    assert(old_servers.locs().dom() == old_servers.dom());

                    state.server_tokens.lemma_lb_points_to(self.server_token.borrow());
                    let ghost server_id = self.server_token@.key();
                    assert(old_servers.locs().contains_key(server_id));
                    assert(state.servers.locs().contains_key(server_id));
                    assert(old_servers.dom().contains(server_id));
                    assert(old_servers.contains_key(server_id));
                    old_servers.lemma_index_loc(server_id);
                    assert(old_servers[server_id]@.loc() == old_servers.locs()[server_id]);
                    assert(r.loc() == old_servers.locs()[server_id]);

                    let tracked mut other_half = state.servers.tracked_remove_auth(server_id);
                    let ghost unchanged_servers = state.servers;
                    unchanged_servers.lemma_dom();
                    assert(!unchanged_servers.dom().contains(server_id));
                    r.lemma_halves_agree(&other_half);
                    r.advance_halves(&mut other_half, timestamp);
                    state.servers.tracked_insert_auth(server_id, other_half);
                    state.servers.lemma_dom();

                    assert(old_servers.leq(state.servers)) by {
                        assert(old_servers.locs() == state.servers.locs());
                        assert forall |id| #[trigger] old_servers.contains_key(id)
                            implies state.servers[id]@@.timestamp() >= old_servers[id]@@.timestamp() by {
                            if id != server_id {
                                assert(old_servers.dom().contains(id));
                                assert(unchanged_servers.dom().contains(id));
                                assert(unchanged_servers.contains_key(id)); // TRIGGER
                                assert(state.servers.dom().contains(id));
                            }
                        }
                    }
                    assert forall |id: u64| #[trigger] state.unclaimed_servers().contains(id) implies state.servers[id]@@ is FullRightToAdvance by {
                        assert(state.servers.dom().contains(id));
                        if id != server_id {
                            assert(unchanged_servers.dom().contains(id));
                            assert(unchanged_servers.contains_key(id));
                        }
                    }
                    assert forall |id: u64| #[trigger] state.server_tokens@.contains_key(id) implies state.servers[id]@@ is HalfRightToAdvance by {
                        assert(old_servers.locs().contains_key(id));
                        assert(old_servers.dom().contains(id));
                        assert(state.servers.dom().contains(id));
                        if id != server_id {
                            assert(unchanged_servers.dom().contains(id));
                            assert(unchanged_servers.contains_key(id));
                        }
                    }
                    old_servers.lemma_leq_quorums(state.servers, state.linearization_queue.watermark());
                }
                // XXX: debug assert
                assert(state.inv());
            });

            MonotonicRegisterInner {
                id: self.id,
                value,
                timestamp,
                resource: Tracked(r),
                commitment,
                server_token: self.server_token,
                state_inv: self.state_inv,
            }
        } else {
            self
        };

        let Tracked(mut lb) = lb;
        proof {
            lb.lemma_lower_bound(ret.resource.borrow());
        }
        ret
    }
}

#[allow(dead_code)]
pub struct MonotonicRegisterInv {
    pub ids: RegisterIds,
}

impl<ML, RL> vstd::rwlock::RwLockPredicate<
    MonotonicRegisterInner<ML, RL>,
> for MonotonicRegisterInv where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    open spec fn inv(self, v: MonotonicRegisterInner<ML, RL>) -> bool {
        &&& v.inv()
        &&& v.ids() == self.ids
        &&& v.resource@@ is HalfRightToAdvance
    }
}

pub struct MonotonicRegister<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    inner: RwLock<MonotonicRegisterInner<ML, RL>, MonotonicRegisterInv>,
}

impl<ML, RL> MonotonicRegister<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(server_id: u64, state_inv: Tracked<Arc<StateInvariant<ML, RL>>>) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
            state_inv@.constant().server_locs.contains_key(server_id),
        ensures
            r.id() == server_id,
            r.commitment_id() == state_inv@.constant().commitments_ids.commitment_id,
            r.server_token_id() == state_inv@.constant().server_tokens_id,
            r.resource_loc() == state_inv@.constant().server_locs[server_id],
    {
        let inner_reg = MonotonicRegisterInner::new(server_id, state_inv);

        let pred = Ghost(MonotonicRegisterInv { ids: inner_reg.ids() });
        assert(<MonotonicRegisterInv as vstd::rwlock::RwLockPredicate<_>>::inv(pred@, inner_reg));
        let inner = RwLock::new(inner_reg, pred);

        MonotonicRegister { inner }
    }

    pub closed spec fn resource_loc(self) -> Loc {
        self.inner.pred().ids.resource_loc
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.inner.pred().ids.commitment_id
    }

    pub closed spec fn server_token_id(self) -> Loc {
        self.inner.pred().ids.server_token_id
    }

    pub closed spec fn id(self) -> u64 {
        self.inner.pred().ids.id
    }

    pub fn read(&self, req: GetRequest) -> (r: GetResponse)
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
        let handle = self.inner.acquire_read();
        let inner = handle.borrow();
        let res = inner.read(req);
        handle.release_read();

        res
    }

    pub fn read_timestamp(&self, req: GetTimestampRequest) -> (r: GetTimestampResponse)
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
        let handle = self.inner.acquire_read();
        let inner = handle.borrow();
        let res = inner.read_timestamp(req);
        handle.release_read();

        res
    }

    pub fn write(&self, req: WriteRequest) -> (r: WriteResponse)
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
        let (guard, handle) = self.inner.acquire_write();

        let new_value = guard.write(req);
        let tracked r = new_value.resource.borrow();
        let tracked lower_bound = r.extract_lower_bound();
        let tracked server_token;

        proof {
            lower_bound.lemma_lower_bound(r);
            server_token = new_value.server_token.borrow().duplicate();
        }

        handle.release_write(new_value);

        WriteResponse::new(Tracked(lower_bound), Tracked(server_token))
    }
}

} // verus!
