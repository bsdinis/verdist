#[cfg(verus_only)]
use crate::invariants::quorum::server_map::raw_extract_lbs;
use crate::invariants::quorum::server_map::ServerMap;
#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
#[cfg(verus_only)]
use crate::invariants::quorum::ServerUniverseLb;
#[cfg(verus_only)]
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
#[cfg(verus_only)]
use crate::timestamp::Timestamp;

#[cfg(verus_only)]
use vstd::map_lib::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;
#[cfg(verus_only)]
use vstd::set::*;
#[cfg(verus_only)]
use vstd::set_lib::*;

verus! {

/// The authoritative snapshot of the server universe
#[allow(dead_code)]
pub tracked struct ServerUniverseAuth {
    tracked map: ServerMap,
}

impl ServerUniverseAuth {
    pub proof fn dummy() -> (tracked r: Self)
        ensures
            r.inv(),
            forall|q: Quorum| #[trigger]
                r.valid_quorum(q) ==> r.quorum_timestamp(q) >= Timestamp::spec_default(),
            forall|id: u64| #[trigger] r.contains_key(id) ==> r[id]@@ is FullRightToAdvance,
    {
        ServerUniverseAuth { map: Map::tracked_empty() }
    }

    pub closed spec fn inv(self) -> bool {
        &&& forall|k: u64| #[trigger]
            self.map.contains_key(k) ==> {
                self.map[k]@@ is HalfRightToAdvance || self.map[k]@@ is FullRightToAdvance
            }
        &&& forall|id: u64| #[trigger]
            self.contains_key(id) && self[id]@@ is FullRightToAdvance ==> self[id]@@.timestamp()
                == Timestamp::spec_default()
    }

    pub closed spec fn dom(self) -> Set<u64> {
        self.map.dom()
    }

    pub closed spec fn contains_key(self, idx: u64) -> bool {
        self.map.contains_key(idx)
    }

    pub closed spec fn spec_index(self, idx: u64) -> Tracked<MonotonicTimestampResource> {
        self.map[idx]
    }

    pub closed spec fn locs(self) -> Map<u64, Loc> {
        self.map.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    /// Get a tracked borrow to a particular resource
    pub proof fn tracked_borrow(tracked &self, server_id: u64) -> (tracked r:
        &MonotonicTimestampResource)
        requires
            self.contains_key(server_id),
        ensures
            *r == self[server_id]@,
    {
        self.map.tracked_borrow(server_id).borrow()
    }

    pub proof fn lemma_locs(self)
        ensures
            self.locs().dom() == self.dom(),
    {
        vlib::map::lemma_map_values_dom(self.map, |r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    /// The dom agrees with the contains_key method
    pub proof fn lemma_dom(self)
        ensures
            forall|id: u64| #[trigger] self.dom().contains(id) <==> self.contains_key(id),
    {
    }

    /// Indexing commutes with taking the locations
    pub proof fn lemma_index_loc(self, id: u64)
        requires
            self.contains_key(id),
        ensures
            self[id]@.loc() == self.locs()[id],
    {
    }

    /// All the ids are authorative
    pub proof fn lemma_inv_advance_right(self, id: u64)
        requires
            self.inv(),
            self.contains_key(id),
        ensures
            self[id]@@ is HalfRightToAdvance || self[id]@@ is FullRightToAdvance,
    {
    }

    proof fn lemma_map_len(self)
        ensures
            self.map.len() == self.dom().len(),
    {
    }

    /// Defines a valid quorum
    pub proof fn lemma_valid_quorum(self, q: Quorum)
        requires
            !q.is_empty(),
            q <= self.dom(),
            2 * q.len() > self.dom().len(),
        ensures
            self.valid_quorum(q),
    {
        self.lemma_map_len();
    }

    /// Defines the reverse of the quorum
    pub proof fn lemma_valid_quorum_bound(self, q: Quorum)
        requires
            self.valid_quorum(q),
        ensures
            !q.is_empty(),
            q <= self.dom(),
            2 * q.len() > self.dom().len(),
    {
        self.lemma_map_len();
    }

    pub closed spec fn valid_quorum(self, q: Quorum) -> bool {
        &&& !q.is_empty()
        &&& q <= self.dom()
        &&& 2 * q.len() > self.map.len()
    }

    pub open spec fn unanimous_quorum(self, q: Quorum, lb: Timestamp) -> bool {
        forall|idx: u64| #[trigger] q.contains(idx) ==> self[idx]@@.timestamp() >= lb
    }

    pub open spec fn quorum_timestamp(self, q: Quorum) -> Timestamp {
        self.quorum_vals(q).find_unique_maximal(Self::ts_leq())
    }

    pub closed spec fn quorum_vals(self, q: Quorum) -> Set<Timestamp> {
        self.map.restrict(q).map_values(
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        ).values()
    }

    pub open spec fn ts_leq() -> spec_fn(Timestamp, Timestamp) -> bool {
        |a: Timestamp, b: Timestamp| a <= b
    }

    pub open spec fn leq(self, other: Self) -> bool {
        &&& self.locs() == other.locs()
        &&& forall|k: u64| #[trigger]
            self.contains_key(k) ==> self[k]@@.timestamp() <= other[k]@@.timestamp()
    }

    pub open spec fn leq_lb(self, other: ServerUniverseLb) -> bool {
        &&& self.locs() == other.locs()
        &&& forall|k: u64| #[trigger]
            self.contains_key(k) ==> self[k]@@.timestamp() <= other[k]@@.timestamp()
    }

    pub proof fn split_auth(tracked &mut self, server_id: u64) -> (tracked r:
        MonotonicTimestampResource)
        requires
            old(self).inv(),
            old(self).contains_key(server_id),
            old(self)[server_id]@@ is FullRightToAdvance,
        ensures
            final(self).dom() == old(self).dom(),
            final(self).locs() == old(self).locs(),
            forall|id: u64| #[trigger]
                old(self).contains_key(id) ==> {
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                    &&& id == server_id ==> final(self)[id]@@ is HalfRightToAdvance
                    &&& id != server_id ==> {
                        &&& old(self)[id]@@ is HalfRightToAdvance
                            ==> final(self)[id]@@ is HalfRightToAdvance
                        &&& old(self)[id]@@ is FullRightToAdvance
                            ==> final(self)[id]@@ is FullRightToAdvance
                    }
                },
            final(self).inv(),
            r.loc() == final(self)[server_id]@.loc(),
            r@ is HalfRightToAdvance,
            r@.timestamp() == Timestamp::spec_default(),
    {
        let ghost old = *self;
        let tracked Tracked(r) = self.map.tracked_remove(server_id);
        let tracked (left, right) = r.split();
        self.map.tracked_insert(server_id, Tracked(left));
        assert forall|id: u64| #[trigger]
            self.contains_key(id) && self[id]@@ is FullRightToAdvance implies self[id]@@.timestamp()
            == Timestamp::spec_default() by {
            assert(old.contains_key(id));
        }
        right
    }

    pub proof fn tracked_remove_auth(tracked &mut self, server_id: u64) -> (tracked r:
        MonotonicTimestampResource)
        requires
            old(self).inv(),
            old(self).contains_key(server_id),
            old(self)[server_id]@@ is HalfRightToAdvance,
        ensures
            final(self).inv(),
            final(self).dom() == old(self).dom().remove(server_id),
            final(self).locs() == old(self).locs().remove(server_id),
            forall|id: u64| #[trigger]
                final(self).contains_key(id) ==> {
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                    &&& old(self)[id]@@ is HalfRightToAdvance
                        ==> final(self)[id]@@ is HalfRightToAdvance
                    &&& old(self)[id]@@ is FullRightToAdvance
                        ==> final(self)[id]@@ is FullRightToAdvance
                },
            r.loc() == old(self)[server_id]@.loc(),
            r@.timestamp() == old(self)[server_id]@@.timestamp(),
            r@ is HalfRightToAdvance,
    {
        let old = *self;
        let tracked Tracked(r) = self.map.tracked_remove(server_id);
        assert(self.map.agrees(old.map));
        assert forall|id: u64| #[trigger]
            self.contains_key(id) && self[id]@@ is FullRightToAdvance implies self[id]@@.timestamp()
            == Timestamp::spec_default() by {
            assert(old.contains_key(id));
        }
        r
    }

    pub proof fn tracked_insert_auth(
        tracked &mut self,
        server_id: u64,
        tracked r: MonotonicTimestampResource,
    )
        requires
            old(self).inv(),
            !old(self).contains_key(server_id),
            r@ is HalfRightToAdvance,
        ensures
            final(self).inv(),
            final(self).dom() == old(self).dom().insert(server_id),
            final(self).locs() == old(self).locs().insert(server_id, r.loc()),
            forall|id: u64| #[trigger]
                old(self).contains_key(id) ==> {
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                    &&& old(self)[id]@@ is HalfRightToAdvance
                        ==> final(self)[id]@@ is HalfRightToAdvance
                    &&& old(self)[id]@@ is FullRightToAdvance
                        ==> final(self)[id]@@ is FullRightToAdvance
                },
            final(self)[server_id]@.loc() == r.loc(),
            final(self)[server_id]@@.timestamp() == r@.timestamp(),
            final(self)[server_id]@@ is HalfRightToAdvance,
    {
        let old = *self;
        self.map.tracked_insert(server_id, Tracked(r));
        assert(self.map.agrees(old.map));
        assert forall|id: u64| #[trigger]
            self.contains_key(id) && self[id]@@ is FullRightToAdvance implies self[id]@@.timestamp()
            == Timestamp::spec_default() by {
            assert(old.contains_key(id));
        }
    }

    /// Duplicate every entry as a fresh lower bound
    pub proof fn extract_lbs(tracked &self) -> (tracked r: ServerUniverseLb)
        requires
            self.inv(),
        ensures
            r.inv(),
            self.locs() =~= r.locs(),
            self.leq_lb(r),
            forall|id: u64| #[trigger]
                self.contains_key(id) ==> {
                    &&& r.contains_key(id)
                    &&& r[id]@@.timestamp() == self[id]@@.timestamp()
                },
            forall|id: u64| #[trigger]
                r.contains_key(id) ==> {
                    &&& self.contains_key(id)
                    &&& r[id]@@.timestamp() == self[id]@@.timestamp()
                },
    {
        let tracked map = raw_extract_lbs(&self.map);
        let tracked r = ServerUniverseLb::from_map(map);
        assert(self.locs() =~= r.locs());
        r
    }

    proof fn lemma_vals(self, q: Quorum) -> (r: (Set<Timestamp>, Timestamp))
        requires
            self.valid_quorum(q),
        ensures
            r.0 == self.quorum_vals(q),
            r.1 == self.quorum_timestamp(q),
            forall|idx: u64| #[trigger] q.contains(idx) ==> r.0.contains(self[idx]@@.timestamp()),
            r.0.len() <= q.len(),
    {
        let ts_leq = Self::ts_leq();
        let ts = self.quorum_timestamp(q);
        let lb_map = self.map.restrict(q);
        let vals = self.quorum_vals(q);

        assert forall|idx: u64| #[trigger] q.contains(idx) implies vals.contains(
            self[idx]@@.timestamp(),
        ) by {
            assert(lb_map.contains_key(idx));
            assert(lb_map.values().contains(self[idx]));
        }

        assert(lb_map.dom() <= q);
        lemma_len_subset(lb_map.dom(), q);
        assert(lb_map.dom().len() <= q.len());

        lb_map.lemma_values_len();
        assert(lb_map.values().len() <= lb_map.dom().len());

        vlib::map::lemma_map_values_commutes(
            lb_map,
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        );
        lemma_map_size_bound(
            lb_map.values(),
            vals,
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        );
        assert(vals.len() <= q.len());

        (vals, ts)
    }

    proof fn lemma_quorum_timestamp_is_upper_bound(self, q: Quorum)
        requires
            self.valid_quorum(q),
        ensures
            forall|idx: u64| #[trigger]
                q.contains(idx) ==> self.quorum_timestamp(q) >= self[idx]@@.timestamp(),
    {
        let ts_leq = Self::ts_leq();
        let (vals, ts) = self.lemma_vals(q);

        self.map.restrict(q).map_values(
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        ).values().find_unique_maximal_ensures(ts_leq);
        vals.lemma_maximal_equivalent_greatest(ts_leq, ts);

        assert(forall|idx: u64| #[trigger] q.contains(idx) ==> ts_leq(self[idx]@@.timestamp(), ts));
    }

    pub proof fn lemma_quorum_timestamp_witness(self, q: Quorum) -> (idx: u64)
        requires
            self.valid_quorum(q),
        ensures
            q.contains(idx),
            self.quorum_timestamp(q) == self[idx]@@.timestamp(),
    {
        let ts_leq = Self::ts_leq();
        let (vals, ts) = self.lemma_vals(q);

        self.map.restrict(q).map_values(
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        ).values().find_unique_maximal_ensures(ts_leq);
        vals.lemma_maximal_equivalent_greatest(ts_leq, ts);

        let witness_idx = choose|idx: u64| #[trigger]
            q.contains(idx) && self[idx]@@.timestamp() == ts;
        assert(q.contains(witness_idx));
        assert(self.quorum_timestamp(q) == self[witness_idx]@@.timestamp());
        witness_idx
    }

    pub proof fn lemma_quorum_witness_implies_lb(self, q: Quorum, witness_idx: u64)
        requires
            self.valid_quorum(q),
            q.contains(witness_idx),
        ensures
            self.quorum_timestamp(q) >= self[witness_idx]@@.timestamp(),
    {
        let ts_leq = Self::ts_leq();
        let (vals, ts) = self.lemma_vals(q);

        self.map.restrict(q).map_values(
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        ).values().find_unique_maximal_ensures(ts_leq);
        vals.lemma_maximal_equivalent_greatest(ts_leq, ts);

        assert(forall|idx: u64| #[trigger] q.contains(idx) ==> ts_leq(self[idx]@@.timestamp(), ts));
        assert(ts_leq(self[witness_idx]@@.timestamp(), ts));
    }

    proof fn lemma_leq_implies_validity(self, other: Self, q: Quorum)
        requires
            self.leq(other) || other.leq(self),
        ensures
            self.valid_quorum(q) <==> other.valid_quorum(q),
    {
        assert(self.locs().dom() == other.locs().dom());
        assert(self.locs().dom() == self.dom());
        assert(self.dom() == other.dom());
        assert(self.map.len() == other.map.len());
    }

    pub proof fn lemma_leq_quorums(self, other: Self, min: Timestamp)
        requires
            self.locs() == other.locs(),
            self.leq(other),
            forall|q: Quorum| #[trigger] self.valid_quorum(q) ==> self.quorum_timestamp(q) >= min,
        ensures
            forall|q: Quorum| #[trigger] other.valid_quorum(q) ==> other.quorum_timestamp(q) >= min,
    {
        assert forall|q: Quorum| #[trigger] other.valid_quorum(q) implies other.quorum_timestamp(q)
            >= min by {
            assert(other.valid_quorum(q));

            self.lemma_leq_implies_validity(other, q);
            assert(self.valid_quorum(q));
            assert(self.quorum_timestamp(q) >= min);

            let witness_idx = self.lemma_quorum_timestamp_witness(q);
            assert(self.contains_key(witness_idx));

            assert(forall|idx: u64| #[trigger]
                self.contains_key(idx) ==> other[idx]@@.timestamp() >= self[idx]@@.timestamp());
            assert(other[witness_idx]@@.timestamp() >= self[witness_idx]@@.timestamp());
            assert(other[witness_idx]@@.timestamp() >= min);

            assert(exists|idx: u64| #[trigger] q.contains(idx) ==> other[idx]@@.timestamp() >= min);
            other.lemma_quorum_witness_implies_lb(q, witness_idx);
            assert(other.quorum_timestamp(q) >= min);
        }
    }

    proof fn lemma_leq_implies_validity_lb(self, other: ServerUniverseLb, q: Quorum)
        requires
            self.leq_lb(other) || other.leq_auth(self),
        ensures
            self.valid_quorum(q) <==> other.valid_quorum(q),
    {
        other.lemma_leq_implies_validity_auth(self, q);
    }

    pub proof fn lemma_leq_quorums_lb(self, other: ServerUniverseLb, min: Timestamp)
        requires
            self.locs() == other.locs(),
            self.leq_lb(other),
            forall|q: Quorum| #[trigger] self.valid_quorum(q) ==> self.quorum_timestamp(q) >= min,
        ensures
            forall|q: Quorum| #[trigger] other.valid_quorum(q) ==> other.quorum_timestamp(q) >= min,
    {
        assert forall|q: Quorum| #[trigger] other.valid_quorum(q) implies other.quorum_timestamp(q)
            >= min by {
            assert(other.valid_quorum(q));

            self.lemma_leq_implies_validity_lb(other, q);
            assert(self.valid_quorum(q));
            assert(self.quorum_timestamp(q) >= min);

            let witness_idx = self.lemma_quorum_timestamp_witness(q);
            assert(self.contains_key(witness_idx));

            assert(forall|idx: u64| #[trigger]
                self.contains_key(idx) ==> other[idx]@@.timestamp() >= self[idx]@@.timestamp());
            assert(other[witness_idx]@@.timestamp() >= self[witness_idx]@@.timestamp());
            assert(other[witness_idx]@@.timestamp() >= min);

            assert(exists|idx: u64| #[trigger] q.contains(idx) ==> other[idx]@@.timestamp() >= min);
            other.lemma_quorum_witness_implies_lb(q, witness_idx);
            assert(other.quorum_timestamp(q) >= min);
        }
    }

    proof fn lemma_quorum_intersection(self, q1: Quorum, q2: Quorum) -> (witness_idx: u64)
        requires
            self.valid_quorum(q1),
            self.valid_quorum(q2),
        ensures
            !q1.disjoint(q2),
            q1.contains(witness_idx),
            q2.contains(witness_idx),
    {
        assert(q1 <= self.dom());
        assert(q2 <= self.dom());
        assert(q1.len() + q2.len() > self.dom().len());
        vstd::assert_by_contradiction!(!q1.disjoint(q2), {
            let u = q1.union(q2);
            assert(u <= self.dom());
            lemma_set_disjoint_lens(q1, q2);

            assert(u.len() == q1.len() + q2.len());
            assert(u.len() > self.dom().len());
            lemma_len_subset(u, self.dom());
        });

        lemma_set_disjoint_iff_empty_intersection(q1, q2);
        let witness_idx = choose|idx: u64| #[trigger] q1.contains(idx) && q2.contains(idx);
        witness_idx
    }

    proof fn lemma_quorum_agree(self, q1: Quorum, q2: Quorum, lb: Timestamp)
        requires
            self.valid_quorum(q1),
            self.valid_quorum(q2),
            self.unanimous_quorum(q1, lb),
        ensures
            forall|idx: u64| #[trigger]
                q1.contains(idx) && q2.contains(idx) ==> self[idx]@@.timestamp() >= lb,
    {
        let restr = self.map.restrict(q1.intersect(q2));
        assert forall|idx: u64| #[trigger]
            q1.contains(idx) && q2.contains(idx) implies self[idx]@@.timestamp() >= lb by {
            assert(restr.contains_key(idx));
            vstd::assert_by_contradiction!(self[idx]@@.timestamp() >= lb, {

            });
        }
    }

    pub proof fn lemma_quorum_lb(self, lb_quorum: Quorum, ts: Timestamp)
        requires
            self.valid_quorum(lb_quorum),
            self.unanimous_quorum(lb_quorum, ts),
        ensures
            forall|q: Quorum| #[trigger] self.valid_quorum(q) ==> self.quorum_timestamp(q) >= ts,
    {
        assert forall|q: Quorum| #[trigger] self.valid_quorum(q) implies self.quorum_timestamp(q)
            >= ts by {
            self.lemma_quorum_agree(lb_quorum, q, ts);
            self.lemma_quorum_timestamp_is_upper_bound(q);
            let witness_idx = self.lemma_quorum_intersection(lb_quorum, q);
            assert(q.contains(witness_idx));
            assert(lb_quorum.contains(witness_idx));
            assert(self[witness_idx]@@.timestamp() >= ts);
            self.lemma_quorum_witness_implies_lb(q, witness_idx);
            assert(self.quorum_timestamp(q) >= ts);
        }
    }
}

} // verus!
