//! Infrastructure of committed to values by clients
//!
//! In general, the way this happens is:
//! - Clients get access to their entire timestamp range
//! - When the timestamp is known, the client can commit to a value by persisting the kv-pair
use vstd::atomic::PermissionU64;
use vstd::resource::map::GhostMapAuth;
use vstd::resource::map::GhostPersistentPointsTo;
#[cfg(verus_only)]
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::map::GhostPointsTo;
use vstd::resource::Loc;

use crate::timestamp::Timestamp;

use vstd::prelude::*;

verus! {

pub type WriteCommitment<const N: usize> = GhostPersistentPointsTo<Timestamp, Option<[u8; N]>>;

pub type WriteAllocation<const N: usize> = GhostPointsTo<Timestamp, Option<[u8; N]>>;

pub type CommitmentAuthMap<const N: usize> = GhostMapAuth<Timestamp, Option<[u8; N]>>;

pub type ClientCtrToken = GhostPointsTo<u64, (u64, int)>;

#[allow(dead_code)]
#[verifier::reject_recursive_types(N)]
pub tracked struct Commitments<const N: usize> {
    commitment_auth: GhostMapAuth<Timestamp, Option<[u8; N]>>,
    zero_commitment: WriteCommitment<N>,
    client_ctr_auth: GhostMapAuth<u64, (u64, int)>,
    client_perm: Map<u64, PermissionU64>,
    zero_client: ClientCtrToken,
    missing_perm: Ghost<Option<(u64, int)>>,
}

pub struct CommitmentIds {
    pub commitment_id: Loc,
    pub client_ctr_id: Loc,
}

impl<const N: usize> Commitments<N> {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.commitment_auth@.contains_pair(Timestamp::spec_default(), None)
        &&& self.zero_commitment.id() == self.commitment_auth.id()
        &&& self.zero_commitment.key() == Timestamp::spec_default()
        &&& self.zero_commitment.value() == None::<[u8; N]>
        &&& *self.missing_perm is None ==> { self.client_ctr_auth@.dom() == self.client_perm.dom() }
        &&& *self.missing_perm is Some ==> {
            let missing_client = self.missing_perm->Some_0.0;
            self.client_ctr_auth@.dom() == self.client_perm.dom().insert(missing_client)
        }
        &&& forall|client_id: u64|
            {
                &&& #[trigger] self.client_ctr_auth@.contains_key(client_id)
                &&& #[trigger] self.client_perm.contains_key(client_id)
            } ==> {
                &&& self.client_ctr_auth@[client_id].0 == self.client_perm[client_id].value()
                &&& self.client_ctr_auth@[client_id].1 == self.client_perm[client_id].id()
            }
        &&& forall|ts: Timestamp| #[trigger]
            self.commitment_auth@.contains_key(ts) ==> {
                &&& self.client_ctr_auth@.contains_key(ts.client_id)
                &&& ts.client_ctr < self.client_ctr_auth@[ts.client_id].0
            }
            // client 0 is reserved for the original write -- it never writes anything else
        &&& self.zero_client.id() == self.client_map_id()
        &&& self.zero_client.key() == 0
        &&& self.zero_client.value().0 == 1
        &&& self.client_perm.contains_key(0)  // 0 cannot be missing

    }

    pub open spec fn ids(self) -> CommitmentIds {
        CommitmentIds { commitment_id: self.commitment_id(), client_ctr_id: self.client_map_id() }
    }

    pub closed spec fn is_full(self) -> bool {
        *self.missing_perm is None
    }

    pub closed spec fn missing_perm(self) -> (u64, int)
        recommends
            !self.is_full(),
    {
        self.missing_perm->Some_0
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.commitment_auth.id()
    }

    pub closed spec fn client_map_id(self) -> Loc {
        self.client_ctr_auth.id()
    }

    pub closed spec fn allocated(self) -> Map<Timestamp, Option<[u8; N]>> {
        self.commitment_auth.view()
    }

    pub closed spec fn client_map(self) -> Map<u64, (u64, int)> {
        self.client_ctr_auth@
    }

    pub closed spec fn client_perm(self) -> Map<u64, PermissionU64> {
        self.client_perm
    }

    pub proof fn new(tracked zero_perm: PermissionU64) -> (tracked r: Commitments<N>)
        requires
            zero_perm.value() == 1,
        ensures
            r.is_full(),
            r.allocated() == map![Timestamp::spec_default() => None::<[u8; N]>],
            r.client_map() == map![0u64 => (1u64, zero_perm.id())],
            r.client_perm() == map![0u64 => zero_perm],
    {
        let tracked (commitment_auth, zero_submap) = GhostMapAuth::new(
            map![Timestamp::spec_default() => None],
        );
        let tracked mut zero_commitment = zero_submap.points_to();
        zero_commitment.agree(&commitment_auth);

        let tracked (client_ctr_auth, zero_client_submap) = GhostMapAuth::new(
            map![0 => (1, zero_perm.id())],
        );
        let tracked mut zero_client = zero_client_submap.points_to();
        zero_client.agree(&client_ctr_auth);

        let tracked mut client_perm = Map::tracked_empty();
        client_perm.tracked_insert(0u64, zero_perm);

        let tracked commitments = Commitments::<N> {
            commitment_auth,
            zero_commitment: zero_commitment.persist(),
            client_ctr_auth,
            client_perm,
            zero_client,
            missing_perm: Ghost(None),
        };
        commitments
    }

    pub proof fn zero_commitment(tracked &self) -> (tracked r: WriteCommitment<N>)
        ensures
            r.id() == self.commitment_id(),
            r.key() == Timestamp::spec_default(),
            r.value() == None::<[u8; N]>,
    {
        use_type_invariant(self);
        self.zero_commitment.duplicate()
    }

    pub proof fn login(
        tracked &mut self,
        client_id: u64,
        tracked client_perm: PermissionU64,
    ) -> (tracked r: ClientCtrToken)
        requires
            old(self).is_full(),
            !old(self).client_map().contains_key(client_id),
            client_perm.value() == 0,
        ensures
            final(self).is_full(),
            final(self).ids() == old(self).ids(),
            final(self).allocated() == old(self).allocated(),
            final(self).client_map() == old(self).client_map().insert(
                client_id,
                (0, client_perm.id()),
            ),
            final(self).client_perm() == old(self).client_perm().insert(client_id, client_perm),
            r.id() == final(self).client_map_id(),
            r.key() == client_id,
            r.value().0 == 0,
            r.value().1 == client_perm.id(),
    {
        use_type_invariant(&*self);
        Self::perm_ctr_insert(
            &mut self.client_perm,
            &mut self.client_ctr_auth,
            client_id,
            client_perm,
        )
    }

    proof fn perm_ctr_insert(
        tracked perm_map: &mut Map<u64, PermissionU64>,
        tracked ctr_auth: &mut GhostMapAuth<u64, (u64, int)>,
        client_id: u64,
        tracked client_perm: PermissionU64,
    ) -> (tracked r: ClientCtrToken)
        requires
            forall|client_id: u64|
                {
                    &&& #[trigger] old(ctr_auth)@.contains_key(client_id)
                    &&& #[trigger] old(perm_map).contains_key(client_id)
                } ==> {
                    &&& old(ctr_auth)@[client_id].0 == old(perm_map)[client_id].value()
                    &&& old(ctr_auth)@[client_id].1 == old(perm_map)[client_id].id()
                },
            !old(ctr_auth)@.contains_key(client_id),
            client_perm.value() == 0,
        ensures
            final(ctr_auth).id() == old(ctr_auth).id(),
            forall|client_id: u64|
                {
                    &&& #[trigger] final(ctr_auth)@.contains_key(client_id)
                    &&& #[trigger] final(perm_map).contains_key(client_id)
                } ==> {
                    &&& final(ctr_auth)@[client_id].0 == final(perm_map)[client_id].value()
                    &&& final(ctr_auth)@[client_id].1 == final(perm_map)[client_id].id()
                },
            r.id() == final(ctr_auth).id(),
            r.key() == client_id,
            r.value().0 == 0,
            r.value().1 == client_perm.id(),
            *final(perm_map) == old(perm_map).insert(client_id, client_perm),
            final(ctr_auth)@ == old(ctr_auth)@.insert(client_id, (0, client_perm.id())),
    {
        let ghost client_perm_id = client_perm.id();
        perm_map.tracked_insert(client_id, client_perm);
        ctr_auth.insert(client_id, (0, client_perm_id))
    }

    pub proof fn take_permission(
        tracked &mut self,
        tracked client_token: &ClientCtrToken,
    ) -> (tracked r: PermissionU64)
        requires
            old(self).is_full(),
            client_token.id() == old(self).client_map_id(),
        ensures
            !final(self).is_full(),
            final(self).ids() == old(self).ids(),
            final(self).missing_perm() == (client_token.key(), r.id()),
            final(self).allocated() == old(self).allocated(),
            final(self).client_map() == old(self).client_map(),
            old(self).client_map().contains_key(client_token.key()),
            final(self).client_perm() == old(self).client_perm().remove(client_token.key()),
            r == old(self).client_perm()[client_token.key()],
            r.id() == client_token.value().1,
            r.value() == client_token.value().0,
    {
        use_type_invariant(&*self);
        assert(client_token.id() == self.client_map_id());
        assert(self.zero_client.id() == self.client_map_id());
        client_token.agree(&self.client_ctr_auth);
        self.zero_client.disjoint(client_token);
        Self::remove_permission(&mut self.client_perm, &mut self.missing_perm, client_token)
    }

    proof fn remove_permission(
        tracked perm_map: &mut Map<u64, PermissionU64>,
        tracked missing_perm: &mut Ghost<Option<(u64, int)>>,
        tracked client_token: &ClientCtrToken,
    ) -> (tracked r: PermissionU64)
        requires
            **old(missing_perm) is None,
            old(perm_map).contains_key(client_token.key()),
            old(perm_map)[client_token.key()].id() == client_token.value().1,
            old(perm_map)[client_token.key()].value() == client_token.value().0,
        ensures
            **final(missing_perm) == Some(
                (client_token.key(), old(perm_map)[client_token.key()].id()),
            ),
            *final(perm_map) == old(perm_map).remove(client_token.key()),
            r == old(perm_map)[client_token.key()],
            r.id() == client_token.value().1,
            r.value() == client_token.value().0,
    {
        let tracked r = perm_map.tracked_remove(client_token.key());
        *missing_perm = Ghost(Some((client_token.key(), r.id())));
        r
    }

    pub proof fn alloc_value(
        tracked &mut self,
        tracked client_token: &mut ClientCtrToken,
        timestamp: Timestamp,
        value: Option<[u8; N]>,
        tracked client_perm: PermissionU64,
    ) -> (tracked r: WriteAllocation<N>)
        requires
            !old(self).is_full(),
            old(client_token).id() == old(self).client_map_id(),
            old(self).missing_perm() == (old(client_token).key(), client_perm.id()),
            timestamp.client_id == old(client_token).key(),
            timestamp.client_ctr == old(client_token).value().0,
            timestamp.client_ctr < client_perm.value(),
            client_perm.id() == old(client_token).value().1,
        ensures
            final(self).is_full(),
            final(self).ids() == old(self).ids(),
            !old(self).allocated().contains_key(timestamp),
            final(self).allocated() == old(self).allocated().insert(timestamp, value),
            old(self).client_map().contains_key(final(client_token).key()),
            final(self).client_map() == old(self).client_map().insert(
                timestamp.client_id,
                (client_perm.value(), client_perm.id()),
            ),
            final(self).client_perm() == old(self).client_perm().insert(
                timestamp.client_id,
                client_perm,
            ),
            final(client_token).id() == old(client_token).id(),
            final(client_token).key() == old(client_token).key(),
            final(client_token).value().0 == client_perm.value(),
            final(client_token).value().1 == client_perm.id(),
            r.key() == timestamp,
            r.value() == value,
            r.id() == final(self).commitment_id(),
    {
        use_type_invariant(&*self);
        Self::alloc(
            &mut self.client_perm,
            &mut self.client_ctr_auth,
            &mut self.missing_perm,
            &mut self.commitment_auth,
            &self.zero_client,
            client_token,
            timestamp,
            value,
            client_perm,
        )
    }

    proof fn alloc(
        tracked perm_map: &mut Map<u64, PermissionU64>,
        tracked ctr_auth: &mut GhostMapAuth<u64, (u64, int)>,
        tracked missing_perm: &mut Ghost<Option<(u64, int)>>,
        tracked commitment_auth: &mut GhostMapAuth<Timestamp, Option<[u8; N]>>,
        tracked zero_client: &ClientCtrToken,
        tracked client_token: &mut ClientCtrToken,
        timestamp: Timestamp,
        value: Option<[u8; N]>,
        tracked client_perm: PermissionU64,
    ) -> (tracked r: WriteAllocation<N>)
        requires
            *old(missing_perm) == Some((old(client_token).key(), client_perm.id())),
            old(client_token).id() == old(ctr_auth).id(),
            old(client_token).id() == zero_client.id(),
            old(ctr_auth)@.dom() == old(perm_map).dom().insert(old(missing_perm)->Some_0.0),
            timestamp.client_id == old(client_token).key(),
            timestamp.client_ctr == old(client_token).value().0,
            timestamp.client_ctr < client_perm.value(),
            client_perm.id() == old(client_token).value().1,
            forall|client_id: u64|
                {
                    &&& #[trigger] old(ctr_auth)@.contains_key(client_id)
                    &&& #[trigger] old(perm_map).contains_key(client_id)
                } ==> {
                    &&& old(ctr_auth)@[client_id].0 == old(perm_map)[client_id].value()
                    &&& old(ctr_auth)@[client_id].1 == old(perm_map)[client_id].id()
                },
            forall|ts: Timestamp| #[trigger]
                old(commitment_auth)@.contains_key(ts) ==> {
                    &&& old(ctr_auth)@.contains_key(ts.client_id)
                    &&& ts.client_ctr < old(ctr_auth)@[ts.client_id].0
                },
        ensures
            **final(missing_perm) is None,
            final(ctr_auth).id() == old(ctr_auth).id(),
            final(commitment_auth).id() == old(commitment_auth).id(),
            final(client_token).id() == old(client_token).id(),
            !old(commitment_auth)@.contains_key(timestamp),
            final(commitment_auth)@ == old(commitment_auth)@.insert(timestamp, value),
            final(ctr_auth)@ == old(ctr_auth)@.insert(
                timestamp.client_id,
                (client_perm.value(), client_perm.id()),
            ),
            *final(perm_map) == old(perm_map).insert(timestamp.client_id, client_perm),
            final(ctr_auth)@.dom() == final(perm_map).dom(),
            forall|client_id: u64|
                {
                    &&& #[trigger] final(ctr_auth)@.contains_key(client_id)
                    &&& #[trigger] final(perm_map).contains_key(client_id)
                } ==> {
                    &&& final(ctr_auth)@[client_id].0 == final(perm_map)[client_id].value()
                    &&& final(ctr_auth)@[client_id].1 == final(perm_map)[client_id].id()
                },
            forall|ts: Timestamp| #[trigger]
                final(commitment_auth)@.contains_key(ts) ==> {
                    &&& final(ctr_auth)@.contains_key(ts.client_id)
                    &&& ts.client_ctr < final(ctr_auth)@[ts.client_id].0
                },
            final(client_token).key() == old(client_token).key(),
            final(client_token).value().0 == client_perm.value(),
            final(client_token).value().1 == client_perm.id(),
            r.key() == timestamp,
            r.value() == value,
            r.id() == final(commitment_auth).id(),
    {
        client_token.agree(&*ctr_auth);
        client_token.disjoint(zero_client);
        client_token.update(ctr_auth, (client_perm.value(), client_perm.id()));

        // XXX: load bearing
        assert(perm_map.dom().insert(missing_perm->Some_0.0) == ctr_auth@.dom());

        perm_map.tracked_insert(client_token.key(), client_perm);
        *missing_perm = Ghost(None);
        commitment_auth.insert(timestamp, value)
    }

    pub proof fn return_permission(
        tracked &mut self,
        tracked client_token: &mut ClientCtrToken,
        tracked client_perm: PermissionU64,
    )
        requires
            !old(self).is_full(),
            old(client_token).id() == old(self).client_map_id(),
            old(self).missing_perm() == (old(client_token).key(), client_perm.id()),
            old(client_token).value().0 < client_perm.value(),
            old(client_token).value().1 == client_perm.id(),
        ensures
            final(self).is_full(),
            final(self).ids() == old(self).ids(),
            final(self).allocated() == old(self).allocated(),
            old(self).client_map().contains_key(final(client_token).key()),
            final(self).client_map() == old(self).client_map().insert(
                final(client_token).key(),
                (client_perm.value(), client_perm.id()),
            ),
            final(self).client_perm() == old(self).client_perm().insert(
                final(client_token).key(),
                client_perm,
            ),
            final(client_token).id() == old(client_token).id(),
            final(client_token).key() == old(client_token).key(),
            final(client_token).value().0 == client_perm.value(),
            final(client_token).value().1 == client_perm.id(),
    {
        use_type_invariant(&*self);
        Self::return_perm(
            &mut self.client_perm,
            &mut self.client_ctr_auth,
            &mut self.missing_perm,
            &mut self.commitment_auth,
            &self.zero_client,
            client_token,
            client_perm,
        )
    }

    proof fn return_perm(
        tracked perm_map: &mut Map<u64, PermissionU64>,
        tracked ctr_auth: &mut GhostMapAuth<u64, (u64, int)>,
        tracked missing_perm: &mut Ghost<Option<(u64, int)>>,
        tracked commitment_auth: &mut GhostMapAuth<Timestamp, Option<[u8; N]>>,
        tracked zero_client: &ClientCtrToken,
        tracked client_token: &mut ClientCtrToken,
        tracked client_perm: PermissionU64,
    )
        requires
            *old(missing_perm) == Some((old(client_token).key(), client_perm.id())),
            old(client_token).id() == old(ctr_auth).id(),
            old(client_token).id() == zero_client.id(),
            old(ctr_auth)@.dom() == old(perm_map).dom().insert(old(missing_perm)->Some_0.0),
            old(client_token).value().0 < client_perm.value(),
            old(client_token).value().1 == client_perm.id(),
            forall|ts: Timestamp| #[trigger]
                old(commitment_auth)@.contains_key(ts) ==> {
                    &&& old(ctr_auth)@.contains_key(ts.client_id)
                    &&& ts.client_ctr < old(ctr_auth)@[ts.client_id].0
                },
        ensures
            **final(missing_perm) is None,
            final(ctr_auth).id() == old(ctr_auth).id(),
            final(commitment_auth).id() == old(commitment_auth).id(),
            final(client_token).id() == old(client_token).id(),
            final(commitment_auth)@ == old(commitment_auth)@,
            final(ctr_auth)@ == old(ctr_auth)@.insert(
                final(client_token).key(),
                (client_perm.value(), client_perm.id()),
            ),
            *final(perm_map) == old(perm_map).insert(final(client_token).key(), client_perm),
            final(ctr_auth)@.dom() == final(perm_map).dom(),
            forall|ts: Timestamp| #[trigger]
                final(commitment_auth)@.contains_key(ts) ==> {
                    &&& final(ctr_auth)@.contains_key(ts.client_id)
                    &&& ts.client_ctr < final(ctr_auth)@[ts.client_id].0
                },
            final(client_token).id() == old(client_token).id(),
            final(client_token).key() == old(client_token).key(),
            final(client_token).value().0 == client_perm.value(),
            final(client_token).value().1 == client_perm.id(),
    {
        client_token.agree(&*ctr_auth);
        client_token.disjoint(zero_client);
        client_token.update(ctr_auth, (client_perm.value(), client_perm.id()));

        // XXX: load bearing
        assert(perm_map.dom().insert(missing_perm->Some_0.0) == ctr_auth@.dom());

        perm_map.tracked_insert(client_token.key(), client_perm);
        *missing_perm = Ghost(None);
    }

    pub proof fn agree_commitment(tracked &self, tracked commitment: &WriteCommitment<N>)
        requires
            self.is_full(),
            commitment.id() == self.commitment_id(),
        ensures
            self.allocated().contains_key(commitment.key()),
    {
        use_type_invariant(self);
        commitment.agree(&self.commitment_auth);
    }

    pub proof fn agree_commitment_submap(
        tracked &self,
        tracked commitments: &GhostPersistentSubmap<Timestamp, Option<[u8; N]>>,
    )
        requires
            self.is_full(),
            commitments.id() == self.commitment_id(),
        ensures
            commitments@ <= self.allocated(),
    {
        use_type_invariant(self);
        commitments.agree(&self.commitment_auth);
    }

    pub proof fn agree_allocation(tracked &self, tracked allocation: &WriteAllocation<N>)
        requires
            self.is_full(),
            allocation.id() == self.commitment_id(),
        ensures
            self.allocated().contains_key(allocation.key()),
    {
        use_type_invariant(self);
        allocation.agree(&self.commitment_auth);
    }

    pub proof fn remove_allocation(
        tracked &mut self,
        tracked allocation: WriteAllocation<N>,
        tracked client_ctr_token: &ClientCtrToken,
    )
        requires
            old(self).is_full(),
            allocation.id() == old(self).commitment_id(),
            client_ctr_token.id() == old(self).client_map_id(),
            allocation.key().client_id == client_ctr_token.key(),
        ensures
            final(self).is_full(),
            final(self).ids() == old(self).ids(),
            final(self).allocated() == old(self).allocated().remove(allocation.key()),
            final(self).client_map() == old(self).client_map(),
            old(self).client_map().contains_key(client_ctr_token.key()),
    {
        use_type_invariant(&*self);
        client_ctr_token.agree(&self.client_ctr_auth);
        self.zero_client.disjoint(client_ctr_token);
        allocation.agree(&self.commitment_auth);
        self.commitment_auth.delete_points_to(allocation);
    }

    pub proof fn agree_client_token(tracked &self, tracked client_ctr_token: &ClientCtrToken)
        requires
            self.is_full(),
            client_ctr_token.id() == self.client_map_id(),
        ensures
            self.client_map().contains_key(client_ctr_token.key()),
    {
        use_type_invariant(self);
        client_ctr_token.agree(&self.client_ctr_auth);
    }
}

} // verus!
