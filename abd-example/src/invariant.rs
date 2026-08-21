use std::sync::Arc;

use vstd::atomic::PermissionU64;
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
pub fn get_invariant_state<ML, RL>(
    server_ids: &Ghost<Set<u64>>,
    client_id: u64,
    client_perm: Tracked<PermissionU64>,
    request_perm: Tracked<PermissionU64>,
) -> (r: (
    Tracked<ClientCtrToken>,
    Tracked<RequestCtrToken>,
    Tracked<Arc<StateInvariant<ML, RL>>>,
    Tracked<RegisterView>,
)) where ML: MutLinearizer<RegisterWrite>, RL: ReadLinearizer<RegisterRead>
    requires
        client_perm@.value() == 0,
        request_perm@.value() == 0,
    ensures
        r.0@.key() == client_id,
        r.0@.value().0 == 0,
        r.0@.value().1 == client_perm@.id(),
        r.0@.id() == r.2@.constant().commitments_ids.client_ctr_id,
        r.1@.key() == client_id,
        r.1@.value().0 == 0,
        r.1@.value().1 == request_perm@.id(),
        r.1@.id() == r.2@.constant().request_map_ids.request_ctr_id,
        r.2@.namespace() == abd::invariants::state_inv_id(),
        r.2@.constant().register_id == r.3@.id(),
        server_ids@ == r.2@.constant().server_locs.dom(),
{
    let tracked state_inv;
    let tracked view;
    proof {
        let tracked (s, v) = abd::invariants::get_system_state::<ML, RL>(server_ids@);
        state_inv = s;
        view = v;
    }

    let tracked mut client_ctr_token;
    let tracked mut request_ctr_token;
    vstd::open_atomic_invariant!(&state_inv => state => {
        proof {
            // XXX(assume/client_disjoint): client_id uniqueness: could be resolved by a client id service
            assume(!state.commitments.client_map().contains_key(client_id));

            let tracked Tracked(client_p) = client_perm;
            client_ctr_token = state.commitments.login(client_id, client_p);
            state.commitments.agree_client_token(&client_ctr_token);

            let tracked Tracked(request_p) = request_perm;
            request_ctr_token = state.request_map.login(client_id, request_p);
            state.request_map.agree_client_token(&request_ctr_token);

            assert(state.commitments.client_map().dom() == state.request_map.request_ctr_map().dom().insert(0));
        }

        // XXX: not load bearing but good for debugging
        assert(<abd::invariants::StatePredicate as vstd::invariant::InvariantPredicate<_, _>>::inv(state_inv.constant(), state));
    });

    (Tracked(client_ctr_token), Tracked(request_ctr_token), Tracked(state_inv), Tracked(view))
}

} // verus!
