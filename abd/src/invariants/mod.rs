use vlib::monotonic::map::GhostMonotonicMap;

#[cfg(verus_only)]
use vstd::atomic::PermissionU64;
use vstd::invariant::AtomicInvariant;
use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::resource::ghost_var::GhostVar;
use vstd::resource::ghost_var::GhostVarAuth;
#[cfg(verus_only)]
use vstd::resource::map::GhostMapAuth;
use vstd::resource::map::GhostPersistentPointsTo;
#[cfg(verus_only)]
use vstd::resource::map::GhostPointsTo;
use vstd::resource::Loc;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

#[allow(unused_imports)]
use crate::timestamp::Timestamp;

#[allow(unused_imports)]
use std::sync::Arc;

pub mod committed_to;
pub mod lin_queue;
pub mod quorum;
pub mod requests;

use committed_to::*;
use lin_queue::*;
use quorum::*;
use requests::*;

use vstd::prelude::*;

verus! {

// XXX: how to number invariants
//
// Right now we are giving them sequential numbers. This is very error prone.
//
// Alternative:
//  - define a pub uninterp spec fn invariant_X_id()
//
// spec fns are deterministic so the value would be the same
//
// Question: how to handle collisions?
pub open spec fn state_inv_id() -> int {
    1int
}

pub type ServerToken = GhostPersistentPointsTo<u64, Loc>;

pub struct StatePredicate {
    pub lin_queue_ids: LinQueueIds,
    pub register_id: Loc,
    pub server_locs: Map<u64, Loc>,
    pub commitments_ids: CommitmentIds,
    pub request_map_ids: RequestMapIds,
    pub server_tokens_id: Loc,
}

pub struct State<ML, RL> where ML: MutLinearizer<RegisterWrite>, RL: ReadLinearizer<RegisterRead> {
    pub tracked register: GhostVarAuth<Option<u64>>,
    pub tracked linearization_queue: LinearizationQueue<ML, RL>,
    pub tracked servers: ServerUniverseAuth,
    pub tracked server_tokens: GhostMonotonicMap<u64, Loc>,
    pub tracked commitments: Commitments,
    pub tracked request_map: RequestMap,
}

impl<ML, RL> State<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub open spec fn unclaimed_servers(self) -> Set<u64> {
        self.servers.dom().difference(self.server_tokens@.dom())
    }

    pub open spec fn inv(self) -> bool {
        // member invariants
        &&& self.linearization_queue.inv()
        &&& self.servers.inv()
        &&& self.commitments.is_full()
        &&& self.request_map.is_full()
        // client ids
        &&& self.commitments.client_map().dom() == self.request_map.request_ctr_map().dom().insert(
            0,
        )
        // server claims
        &&& self.server_tokens@ <= self.servers.locs()
        &&& self.unclaimed_servers() <= self.servers.dom()
        &&& forall|id: u64| #[trigger]
            self.unclaimed_servers().contains(id) ==> self.servers[id]@@ is FullRightToAdvance
        &&& forall|id: u64| #[trigger]
            self.server_tokens@.contains_key(id)
                ==> self.servers[id]@@ is HalfRightToAdvance
            // id concordance
        &&& self.linearization_queue.register_id() == self.register.id()
        &&& self.linearization_queue.committed_to_id()
            == self.commitments.commitment_id()
        // matching state
        &&& self.linearization_queue.current_value() == self.register@
        &&& self.linearization_queue.known_timestamps() == self.commitments.allocated().dom()
        &&& forall|q: Quorum| #[trigger]
            self.servers.valid_quorum(q) ==> {
                self.linearization_queue.watermark() <= self.servers.quorum_timestamp(q)
            }
    }
}

impl<ML, RL> InvariantPredicate<StatePredicate, State<ML, RL>> for StatePredicate where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    open spec fn inv(p: StatePredicate, state: State<ML, RL>) -> bool {
        &&& p.register_id == state.register.id()
        &&& p.lin_queue_ids == state.linearization_queue.ids()
        &&& p.server_locs == state.servers.locs()
        &&& p.commitments_ids == state.commitments.ids()
        &&& p.request_map_ids == state.request_map.ids()
        &&& p.server_tokens_id == state.server_tokens.id()
        &&& state.inv()
    }
}

pub type StateInvariant<ML, RL> = AtomicInvariant<StatePredicate, State<ML, RL>, StatePredicate>;

pub type RegisterView = GhostVar<Option<u64>>;

pub proof fn initialize_system_state<ML, RL>(tracked zero_perm: PermissionU64) -> (tracked r: (
    Arc<StateInvariant<ML, RL>>,
    RegisterView,
)) where ML: MutLinearizer<RegisterWrite>, RL: ReadLinearizer<RegisterRead>
    requires
        zero_perm.value() == 1,
    ensures
        r.0.namespace() == state_inv_id(),
        r.0.constant().register_id == r.1.id(),
{
    let tracked (register, view) = GhostVarAuth::<Option<u64>>::new(None);
    let tracked servers = ServerUniverseAuth::dummy();
    let tracked commitments = Commitments::new(zero_perm);
    let tracked request_map = RequestMap::new();
    let tracked zero_commitment = commitments.zero_commitment();
    let tracked mut linearization_queue = LinearizationQueue::new(register.id(), zero_commitment);
    let tracked server_tokens = GhostMonotonicMap::empty();

    commitments.agree_commitment_submap(linearization_queue.tracked_committed_values());
    // XXX: load bearing
    assert(linearization_queue.known_timestamps() == set![Timestamp::spec_default()]);

    let pred = StatePredicate {
        lin_queue_ids: linearization_queue.ids(),
        register_id: register.id(),
        server_locs: servers.locs(),
        commitments_ids: commitments.ids(),
        request_map_ids: request_map.ids(),
        server_tokens_id: server_tokens.id(),
    };

    let tracked state = State {
        register,
        linearization_queue,
        servers,
        commitments,
        request_map,
        server_tokens,
    };
    state.servers.lemma_dom();
    assert forall|id| #[trigger]
        state.unclaimed_servers().contains(
            id,
        ) implies state.servers[id]@@ is FullRightToAdvance by {
        assert(state.servers.dom().contains(id));
        assert(state.servers.contains_key(id));
    }

    assert(<StatePredicate as InvariantPredicate<_, _>>::inv(pred, state));
    let tracked state_inv = AtomicInvariant::new(pred, state, state_inv_id());

    (Arc::new(state_inv), view)
}

pub axiom fn get_system_state<ML, RL>(server_ids: Set<u64>) -> (tracked r: (
    Arc<StateInvariant<ML, RL>>,
    RegisterView,
)) where ML: MutLinearizer<RegisterWrite>, RL: ReadLinearizer<RegisterRead>
    ensures
        r.0.namespace() == state_inv_id(),
        r.0.constant().register_id == r.1.id(),
        r.0.constant().server_locs.dom() == server_ids,
;

} // verus!
