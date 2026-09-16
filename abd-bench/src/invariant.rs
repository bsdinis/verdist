use std::sync::Arc;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use abd::invariants::committed_to::ClientCtrToken;
use abd::invariants::requests::RequestCtrToken;
use abd::invariants::RegisterView;
use abd::invariants::StateInvariant;

verus! {

#[allow(unused, clippy::type_complexity)]
pub fn get_invariant_state<const N: usize, ML, RL>() -> (
    Tracked<ClientCtrToken>,
    Tracked<RequestCtrToken>,
    Tracked<Arc<StateInvariant<N, ML, RL>>>,
    Tracked<RegisterView<N>>,
) where ML: MutLinearizer<RegisterWrite<N>>, RL: ReadLinearizer<RegisterRead<N>> {
    (
        Tracked(proof_from_false()),
        Tracked(proof_from_false()),
        Tracked(proof_from_false()),
        Tracked(proof_from_false()),
    )
}

pub fn fake_tracked<T>() -> Tracked<T> {
    Tracked(proof_from_false())
}

pub fn fake_ghost<T>() -> Ghost<T> {
    Ghost(arbitrary())
}

} // verus!
