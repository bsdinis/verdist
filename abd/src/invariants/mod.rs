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

#[cfg(verus_only)]
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;

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

/// Claim `server_id`'s slot in the server universe: split off a fresh `HalfRightToAdvance` for
/// it, mint its `ServerToken`, and hand back a duplicate of the zero commitment -- exactly the
/// ghost sequence both register backends need at construction time (`MonotonicRegisterInner::new`
/// in `server/register.rs` and `EpochMonotonicRegister::new` in `server/lockfree.rs`). Factored
/// out so that sequence -- and the one `assume` inside it -- exists exactly once in the codebase
/// instead of once per backend (see `claude-files/backend_switch_questions.md` Q1).
///
/// Re-establishes `state.inv()` itself: callers only need to open the state invariant, call this,
/// and use the returned triple -- no bookkeeping of their own is required to close the invariant
/// back up.
pub proof fn claim_server<ML, RL>(tracked state: &mut State<ML, RL>, server_id: u64) -> (tracked r:
    (MonotonicTimestampResource, ServerToken, WriteCommitment)) where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    requires
        old(state).inv(),
        old(state).servers.locs().contains_key(server_id),
    ensures
        final(state).inv(),
        final(state).register.id() == old(state).register.id(),
        final(state).linearization_queue.ids() == old(state).linearization_queue.ids(),
        final(state).servers.locs() == old(state).servers.locs(),
        final(state).commitments.ids() == old(state).commitments.ids(),
        final(state).request_map.ids() == old(state).request_map.ids(),
        final(state).server_tokens.id() == old(state).server_tokens.id(),
        // r.0 = the freshly split `HalfRightToAdvance` for `server_id`
        r.0@ is HalfRightToAdvance,
        r.0@.timestamp() == Timestamp::spec_default(),
        r.0.loc() == old(state).servers.locs()[server_id],
        // r.1 = server_id's freshly minted token
        r.1.id() == final(state).server_tokens.id(),
        r.1.key() == server_id,
        r.1.value() == r.0.loc(),
        // r.2 = a duplicate of the zero commitment
        r.2.id() == final(state).commitments.commitment_id(),
        r.2.key() == Timestamp::spec_default(),
        r.2.value() == None::<u64>,
{
    let tracked zero_commitment = state.commitments.zero_commitment();

    let ghost old_servers = state.servers;
    let ghost old_unclaimed = state.unclaimed_servers();
    let ghost old_tokens = state.server_tokens@;

    assert(old_tokens <= old_servers.locs());
    // XXX: server login -- the single hole in this file. There is no ghost "server login"
    // protocol anywhere in this codebase establishing that `server_id` is currently unclaimed
    // (only that it is *in* `server_locs`, via this function's own `requires`); a real login
    // handshake would produce that fact honestly and this `assume` would be replaced by it, here
    // and only here -- both register backends claim a server exclusively by calling
    // `claim_server`, so this is the one and only copy of this trust hole in `abd`.
    assume(state.unclaimed_servers().contains(server_id));
    state.servers.lemma_inv();
    assert(old_servers.dom().contains(server_id));
    assert(old_servers.contains_key(server_id));
    let tracked resource = state.servers.split_auth(server_id);
    let tracked server_token = state.server_tokens.insert(server_id, resource.loc());
    state.servers.lemma_inv();
    assert forall|id| #[trigger]
        state.unclaimed_servers().contains(
            id,
        ) implies state.servers[id]@@ is FullRightToAdvance by {
        assert(state.servers.dom().contains(id));
        assert(old_servers.dom().contains(id));
        assert(old_servers.contains_key(id));  // TRIGGER
        // TRIGGER case search (?)
        if old_unclaimed.contains(id) {
        } else {
        }
    }

    assert(state.servers.dom().contains(server_id));
    assert(state.servers.contains_key(server_id));
    assert(resource.loc() == state.servers.locs()[server_id]);
    assert(state.server_tokens@ <= state.servers.locs());
    state.servers.lemma_inv();
    assert(state.servers.locs().dom() == state.servers.dom());
    assert forall|id| #[trigger]
        state.server_tokens@.contains_key(id) implies state.servers[id]@@ is HalfRightToAdvance by {
        assert(state.servers.dom().contains(id));
        assert(old_servers.dom().contains(id));
        assert(old_servers.contains_key(id));  // TRIGGER
    }

    old_servers.lemma_leq_quorums(state.servers, state.linearization_queue.watermark());

    // XXX: debug assert
    assert(state.inv());
    (resource, server_token, zero_commitment)
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
    state.servers.lemma_inv();
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
