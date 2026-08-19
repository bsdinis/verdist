#[cfg(verus_only)]
use crate::invariants::quorum::server_map::raw_extract_lbs;
#[cfg(verus_only)]
use crate::invariants::quorum::server_map::raw_insert_lb;
#[cfg(verus_only)]
use crate::invariants::quorum::server_map::raw_remove_lb;
use crate::invariants::quorum::server_map::ServerMap;
#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
#[cfg(verus_only)]
use crate::invariants::quorum::ServerUniverseAuth;
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

/// A lower-bound snapshot of the server universe
#[allow(dead_code)]
pub tracked struct ServerUniverseLb {
    tracked map: ServerMap,
}

impl ServerUniverseLb {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        forall|k: u64| #[trigger] self.map.contains_key(k) ==> self.map[k]@@ is LowerBound
    }

    pub open spec fn spec_eq(self, other: Self) -> bool {
        self.eq(other)
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

    /// Lets external callers (e.g. `lb.rs`'s `prove_lower_bound`) get a tracked borrow of a
    /// single entry without naming the private `map` field.
    pub proof fn tracked_borrow(tracked &self, server_id: u64) -> (tracked r:
        &MonotonicTimestampResource)
        requires
            self.contains_key(server_id),
        ensures
            *r == self[server_id]@,
    {
        self.map.tracked_borrow(server_id).borrow()
    }

    pub proof fn lemma_inv(tracked &self)
        ensures
            self.locs().dom() == self.dom(),
            forall|k: u64| #[trigger] self.contains_key(k) ==> self[k]@@ is LowerBound,
            forall|id: u64| #[trigger] self.dom().contains(id) <==> self.contains_key(id),
            forall|id: u64| #[trigger] self.contains_key(id) ==> self[id]@.loc() == self.locs()[id],
    {
        use_type_invariant(self);
        self.lemma_dom_correspondence();
    }

    pub(crate) proof fn lemma_dom_correspondence(self)
        ensures
            self.locs().dom() == self.dom(),
            forall|id: u64| #[trigger] self.dom().contains(id) <==> self.contains_key(id),
            forall|id: u64| #[trigger] self.contains_key(id) ==> self[id]@.loc() == self.locs()[id],
    {
        vlib::map::lemma_map_values_dom(self.map, |r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    /// Indexing commutes with taking the locations
    pub proof fn lemma_index_loc(self, id: u64)
        requires
            self.contains_key(id),
        ensures
            self[id]@.loc() == self.locs()[id],
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

    pub broadcast proof fn lemma_inv_eq(self, other: Self)
        requires
            #[trigger] self.locs() == #[trigger] other.locs(),
        ensures
            forall|id: u64| #[trigger]
                self.contains_key(id) ==> self[id]@.loc() == other[id]@.loc(),
    {
        self.lemma_dom_correspondence();
        other.lemma_dom_correspondence();
        assert forall|id| #[trigger] self.contains_key(id) implies self[id]@.loc()
            == other[id]@.loc() by {
            assert(self.dom().contains(id));
            assert(other.dom().contains(id));
            assert(other.contains_key(id));
        }
    }

    proof fn lemma_inv_eq_auth(self, tracked other: &ServerUniverseAuth)
        requires
            self.locs() == other.locs(),
        ensures
            forall|id: u64| #[trigger]
                self.contains_key(id) ==> self[id]@.loc() == other[id]@.loc(),
    {
        self.lemma_dom_correspondence();
        other.lemma_inv();
        assert forall|id| #[trigger] self.contains_key(id) implies self[id]@.loc()
            == other[id]@.loc() by {
            assert(self.dom().contains(id));
            assert(other.dom().contains(id));
            assert(other.contains_key(id));
        }
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

    pub open spec fn leq_auth(self, other: ServerUniverseAuth) -> bool {
        &&& self.locs() == other.locs()
        &&& forall|k: u64| #[trigger]
            self.contains_key(k) ==> self[k]@@.timestamp() <= other[k]@@.timestamp()
    }

    pub open spec fn eq_timestamp(self, other: Self) -> bool {
        &&& self.locs() == other.locs()
        &&& forall|id: u64| #[trigger]
            self.contains_key(id) ==> {
                &&& self[id]@@.timestamp() == other[id]@@.timestamp()
            }
        &&& forall|id: u64| #[trigger]
            other.contains_key(id) ==> {
                &&& self[id]@@.timestamp() == other[id]@@.timestamp()
            }
    }

    pub open spec fn eq(self, other: Self) -> bool {
        &&& self.locs() == other.locs()
        &&& forall|id: u64| #[trigger]
            self.contains_key(id) ==> {
                &&& self[id]@@.timestamp() == other[id]@@.timestamp()
                &&& self[id]@@ is HalfRightToAdvance == other[id]@@ is HalfRightToAdvance
                &&& self[id]@@ is FullRightToAdvance == other[id]@@ is FullRightToAdvance
                &&& self[id]@@ is LowerBound == other[id]@@ is LowerBound
            }
        &&& forall|id: u64| #[trigger]
            other.contains_key(id) ==> {
                &&& self[id]@@.timestamp() == other[id]@@.timestamp()
                &&& self[id]@@ is HalfRightToAdvance == other[id]@@ is HalfRightToAdvance
                &&& self[id]@@ is FullRightToAdvance == other[id]@@ is FullRightToAdvance
                &&& self[id]@@ is LowerBound == other[id]@@ is LowerBound
            }
    }

    pub proof fn tracked_remove_lb(tracked &mut self, server_id: u64) -> (tracked r:
        MonotonicTimestampResource)
        requires
            old(self).contains_key(server_id),
            old(self)[server_id]@@ is LowerBound,
        ensures
            final(self).dom() == old(self).dom().remove(server_id),
            final(self).locs() == old(self).locs().remove(server_id),
            forall|id: u64| #[trigger]
                final(self).contains_key(id) ==> {
                    &&& old(self)[id]@.loc() == final(self)[id]@.loc()
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                },
            r.loc() == old(self)[server_id]@.loc(),
            r@.timestamp() == old(self)[server_id]@@.timestamp(),
            r@ is LowerBound,
    {
        use_type_invariant(&*self);
        let ghost old = *self;
        let tracked mut map: ServerMap = Map::tracked_empty();
        vstd::modes::tracked_swap(&mut map, &mut self.map);
        let tracked (mut new_map, r) = raw_remove_lb(map, server_id);
        assert forall|id: u64| #[trigger] new_map.contains_key(id) implies {
            &&& new_map[id]@@ is LowerBound
            &&& old.map[id]@.loc() == new_map[id]@.loc()
        } by {
            assert(old.contains_key(id));
            assert(new_map.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc())[id]
                == old.map.remove(server_id).map_values(
                |x: Tracked<MonotonicTimestampResource>| x@.loc(),
            )[id]);
        }
        vstd::modes::tracked_swap(&mut self.map, &mut new_map);
        r
    }

    pub proof fn tracked_insert_lb(
        tracked &mut self,
        server_id: u64,
        tracked r: MonotonicTimestampResource,
    )
        requires
            !old(self).contains_key(server_id),
            r@ is LowerBound,
        ensures
            final(self).dom() == old(self).dom().insert(server_id),
            final(self).locs() == old(self).locs().insert(server_id, r.loc()),
            forall|id: u64| #[trigger]
                old(self).contains_key(id) ==> {
                    &&& old(self)[id]@.loc() == final(self)[id]@.loc()
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                },
            final(self)[server_id]@.loc() == r.loc(),
            final(self)[server_id]@@.timestamp() == r@.timestamp(),
    {
        use_type_invariant(&*self);
        let ghost old = *self;
        let tracked mut map: ServerMap = Map::tracked_empty();
        vstd::modes::tracked_swap(&mut map, &mut self.map);
        let tracked mut new_map = raw_insert_lb(map, server_id, r);
        assert forall|id: u64| #[trigger] new_map.contains_key(id) implies {
            &&& new_map[id]@@ is LowerBound
        } by {
            if id != server_id {
                assert(old.contains_key(id));
            }
        }
        assert forall|id: u64| #[trigger] old.contains_key(id) implies {
            &&& old.map[id]@.loc() == new_map[id]@.loc()
            &&& old.map[id]@@.timestamp() == new_map[id]@@.timestamp()
        } by {
            assert(new_map.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc())[id]
                == old.map.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc())[id]);
        }
        vstd::modes::tracked_swap(&mut self.map, &mut new_map);
    }

    pub proof fn tracked_update_lb(
        tracked &mut self,
        server_id: u64,
        tracked r: MonotonicTimestampResource,
    )
        requires
            old(self).contains_key(server_id),
            r@ is LowerBound,
            old(self)[server_id]@.loc() == r.loc(),
            old(self)[server_id]@@.timestamp() <= r@.timestamp(),
        ensures
            final(self).dom() == old(self).dom(),
            final(self).locs() == old(self).locs(),
            forall|id: u64| #[trigger]
                final(self).contains_key(id) ==> {
                    &&& id != server_id ==> final(self)[id]@@.timestamp() == old(
                        self,
                    )[id]@@.timestamp()
                    &&& id == server_id ==> final(self)[id]@@.timestamp() == r@.timestamp()
                },
            final(self)[server_id]@@.timestamp() == r@.timestamp(),
            old(self).leq(*final(self)),
    {
        use_type_invariant(&*self);
        self.lemma_inv();
        let ghost orig_map = *self;

        let tracked old_r = self.tracked_remove_lb(server_id);
        let ghost unchanged_map = *self;

        self.tracked_insert_lb(server_id, r);

        assert forall|id: u64| #[trigger] self.contains_key(id) implies {
            &&& id != server_id ==> self[id]@@.timestamp() == orig_map[id]@@.timestamp()
            &&& id == server_id ==> self[id]@@.timestamp() == r@.timestamp()
            &&& self[id]@.loc() == orig_map[id]@.loc()
        } by {
            if id != server_id {
                assert(unchanged_map.contains_key(id));
            }
        }

        self.lemma_inv();
        assert forall|id: u64| #[trigger] orig_map.contains_key(id) implies {
            &&& orig_map[id]@@.timestamp() <= self[id]@@.timestamp()
        } by {
            assert(self.contains_key(id));
        }

        assert forall|id: u64| #[trigger] orig_map.contains_key(id) implies {
            self[id]@.loc() == orig_map[id]@.loc()
        } by {
            assert(self.contains_key(id));
        }
        assert(orig_map.locs() == self.locs());
    }

    /// Duplicate every entry of this lower-bound snapshot into a fresh one.
    pub proof fn extract_lbs(tracked &self) -> (tracked r: Self)
        ensures
            self.eq_timestamp(r),
    {
        let tracked map = raw_extract_lbs(&self.map);
        ServerUniverseLb { map }
    }

    /// Build a `ServerUniverseLb` out of a raw `ServerMap` all of whose entries are already
    /// `LowerBound`s. Lets `ServerUniverseAuth::extract_lbs` (which duplicates its own map into a
    /// fresh `ServerMap` via `raw_extract_lbs`) turn that into a `ServerUniverseLb` without
    /// naming the private `map` field from outside this module.
    pub(crate) proof fn from_map(tracked map: ServerMap) -> (tracked r: Self)
        requires
            forall|k: u64| #[trigger] map.contains_key(k) ==> map[k]@@ is LowerBound,
        ensures
            forall|k: u64| #[trigger] r.contains_key(k) <==> map.contains_key(k),
            r.dom() == map.dom(),
            r.locs() == map.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc()),
            forall|k: u64| #[trigger]
                map.contains_key(k) ==> {
                    &&& r[k]@.loc() == map[k]@.loc()
                    &&& r[k]@@.timestamp() == map[k]@@.timestamp()
                },
    {
        ServerUniverseLb { map }
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

    pub proof fn lemma_quorum_vals_nonempty(self, q: Quorum)
        requires
            self.valid_quorum(q),
        ensures
            self.quorum_vals(q).len() > 0,
    {
        let (vals, _ts) = self.lemma_vals(q);
        assert(!q.is_empty());
        let witness = q.choose();
        assert(q.contains(witness));
        assert(vals.contains(self[witness]@@.timestamp()));
        vstd::assert_by_contradiction!(vals.len() > 0, {
            vals.lemma_len0_is_empty();
        });
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

    pub proof fn lemma_leq_trans(a: Self, b: Self, c: Self)
        requires
            a.leq(b),
            b.leq(c),
        ensures
            a.leq(c),
    {
        a.lemma_dom_correspondence();
        b.lemma_dom_correspondence();
        c.lemma_dom_correspondence();
        assert forall|k: u64| #[trigger] a.contains_key(k) implies a[k]@@.timestamp()
            <= c[k]@@.timestamp() by {
            assert(b.contains_key(k));
            assert(c.contains_key(k));
        }
    }

    proof fn lemma_leq_implies_validity_raw(self, other: Self)
        requires
            self.leq(other) || other.leq(self),
        ensures
            self.locs().dom() == other.locs().dom(),
    {
        self.lemma_dom_correspondence();
        other.lemma_dom_correspondence();
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

    pub proof fn lemma_leq_implies_validity(self, other: Self, q: Quorum)
        requires
            self.leq(other) || other.leq(self),
        ensures
            self.valid_quorum(q) <==> other.valid_quorum(q),
    {
        self.lemma_dom_correspondence();
        other.lemma_dom_correspondence();
        assert(self.locs().dom() == other.locs().dom());
        assert(self.locs().dom() == self.dom());
        assert(self.dom() == other.dom());
        assert(self.map.len() == other.map.len());
    }

    pub proof fn lemma_leq_implies_validity_auth(self, other: ServerUniverseAuth, q: Quorum)
        requires
            self.leq_auth(other) || other.leq_lb(self),
        ensures
            self.valid_quorum(q) <==> other.valid_quorum(q),
    {
        self.lemma_dom_correspondence();
        other.lemma_dom_correspondence();
        assert(self.locs().dom() == other.locs().dom());
        assert(self.dom() == other.dom());
        if self.valid_quorum(q) {
            self.lemma_valid_quorum_bound(q);
            other.lemma_valid_quorum(q);
        }
        if other.valid_quorum(q) {
            other.lemma_valid_quorum_bound(q);
            self.lemma_valid_quorum(q);
        }
    }

    pub proof fn lemma_leq_retains_unanimity_auth(
        self,
        other: ServerUniverseAuth,
        q: Quorum,
        lb: Timestamp,
    )
        requires
            self.leq_auth(other),
            self.valid_quorum(q),
        ensures
            self.unanimous_quorum(q, lb) ==> other.unanimous_quorum(q, lb),
    {
        self.lemma_leq_implies_validity_auth(other, q);
        assert(other.valid_quorum(q));
        if self.unanimous_quorum(q, lb) {
            assert forall|idx: u64| #[trigger] q.contains(idx) implies other[idx]@@.timestamp()
                >= lb by {
                assert(self.contains_key(idx));
                assert(self[idx]@@.timestamp() <= other[idx]@@.timestamp());
            }
        }
    }

    pub proof fn lemma_leq_quorum_timestamp(self, other: Self, q: Quorum)
        requires
            self.locs() == other.locs(),
            self.leq(other),
            self.valid_quorum(q),
        ensures
            other.valid_quorum(q),
            self.quorum_timestamp(q) <= other.quorum_timestamp(q),
    {
        self.lemma_leq_implies_validity(other, q);
        assert(other.valid_quorum(q));
        assert(self.valid_quorum(q));

        let witness_idx = self.lemma_quorum_timestamp_witness(q);
        assert(self.contains_key(witness_idx));

        assert(forall|idx: u64| #[trigger]
            self.contains_key(idx) ==> other[idx]@@.timestamp() >= self[idx]@@.timestamp());
        assert(other[witness_idx]@@.timestamp() >= self[witness_idx]@@.timestamp());

        assert(exists|idx: u64| #[trigger]
            q.contains(idx) ==> other[idx]@@.timestamp() >= self.quorum_timestamp(q));
        other.lemma_quorum_witness_implies_lb(q, witness_idx);
        assert(other.quorum_timestamp(q) >= self.quorum_timestamp(q));
    }

    pub proof fn lemma_lb(tracked &mut self, tracked other: &ServerUniverseAuth)
        requires
            old(self).locs() == other.locs(),
        ensures
            final(self).eq(*old(self)),
            final(self).leq_auth(*other),
    {
        self.prove_lower_bound(other, Set::empty());
    }

    proof fn prove_lower_bound(
        tracked &mut self,
        tracked other: &ServerUniverseAuth,
        visited: Set<u64>,
    )
        requires
            old(self).locs() == other.locs(),
            visited <= old(self).dom(),
            forall|id: u64| #[trigger]
                visited.contains(id) ==> old(self)[id]@@.timestamp() <= other[id]@@.timestamp(),
        ensures
            final(self).locs() == old(self).locs(),
            final(self).leq_auth(*other),
            final(self).eq(*old(self)),
        decreases other.dom().difference(visited).len(),
    {
        self.lemma_inv();
        other.lemma_inv();
        self.lemma_inv_eq_auth(other);
        if other.dom().difference(visited).is_empty() {
            vlib::set::lemma_different_sets_with_inclusion_have_difference(visited, other.dom());
            return;
        }
        assert(exists|id: u64| #[trigger] other.dom().contains(id) && !visited.contains(id));
        let server_id = choose|id: u64| #[trigger]
            other.dom().contains(id) && !visited.contains(id);
        assert(other.contains_key(server_id));
        assert(self.dom().contains(server_id));
        assert(self.contains_key(server_id));
        assert(self[server_id]@.loc() == other[server_id]@.loc());

        let tracked Tracked(mut r) = self.map.tracked_remove(server_id);
        r.lemma_lower_bound(other.tracked_borrow(server_id));
        self.map.tracked_insert(server_id, Tracked(r));

        other.dom().lemma_set_insert_diff_decreases(visited, server_id);

        assert(self.locs() == old(self).locs());
        assert forall|id: u64| #[trigger]
            visited.insert(server_id).contains(id) implies self[id]@@.timestamp()
            <= other[id]@@.timestamp() by {
            if id != server_id {
                assert(visited.contains(id));
                assert(old(self)[id]@@.timestamp() <= other[id]@@.timestamp());
            }
        }
        let old_self = *self;
        self.prove_lower_bound(other, visited.insert(server_id));
        Self::lemma_eq_trans(*self, old_self, *old(self));
    }

    pub broadcast proof fn lemma_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.eq(b),
            #[trigger] b.eq(c),
        ensures
            a.eq(c),
    {
        a.lemma_dom_correspondence();
        b.lemma_dom_correspondence();
        c.lemma_dom_correspondence();
        assert(a.locs() == c.locs());
        assert forall|id: u64| #[trigger] a.contains_key(id) implies {
            &&& a[id]@@.timestamp() == c[id]@@.timestamp()
            &&& a[id]@@ is HalfRightToAdvance == c[id]@@ is HalfRightToAdvance
            &&& a[id]@@ is FullRightToAdvance == c[id]@@ is FullRightToAdvance
            &&& a[id]@@ is LowerBound == c[id]@@ is LowerBound
        } by {
            assert(b.contains_key(id));
        }

        assert forall|id: u64| #[trigger] c.contains_key(id) implies {
            &&& c[id]@@.timestamp() == a[id]@@.timestamp()
            &&& c[id]@@ is HalfRightToAdvance == a[id]@@ is HalfRightToAdvance
            &&& c[id]@@ is FullRightToAdvance == a[id]@@ is FullRightToAdvance
            &&& c[id]@@ is LowerBound == a[id]@@ is LowerBound
        } by {
            assert(b.contains_key(id));
        }
    }

    pub broadcast proof fn lemma_eq_refl(a: Self)
        ensures
            #[trigger] a.eq(a),
    {
    }

    pub broadcast proof fn lemma_eq_timestamp_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.eq_timestamp(b),
            #[trigger] b.eq_timestamp(c),
        ensures
            a.eq_timestamp(c),
    {
        a.lemma_dom_correspondence();
        b.lemma_dom_correspondence();
        c.lemma_dom_correspondence();
        assert(a.locs() == c.locs());
        assert forall|id: u64| #[trigger] a.contains_key(id) implies {
            a[id]@@.timestamp() == c[id]@@.timestamp()
        } by {
            assert(b.contains_key(id));
        }

        assert forall|id: u64| #[trigger] c.contains_key(id) implies {
            c[id]@@.timestamp() == a[id]@@.timestamp()
        } by {
            assert(b.contains_key(id));
        }
    }

    pub broadcast proof fn lemma_eq_timestamp_lb_is_eq(a: Self, b: Self)
        requires
            #[trigger] a.eq_timestamp(b),
            forall|k: u64| #[trigger] a.contains_key(k) ==> a[k]@@ is LowerBound,
            forall|k: u64| #[trigger] b.contains_key(k) ==> b[k]@@ is LowerBound,
        ensures
            a.eq(b),
    {
        assert forall|id| #[trigger] a.contains_key(id) implies {
            &&& a[id]@@.timestamp() == b[id]@@.timestamp()
            &&& a[id]@@ is HalfRightToAdvance == b[id]@@ is HalfRightToAdvance
            &&& a[id]@@ is FullRightToAdvance == b[id]@@ is FullRightToAdvance
            &&& a[id]@@ is LowerBound == b[id]@@ is LowerBound
        } by {
            assert(b.contains_key(id));
            assert(a[id]@@.timestamp() == b[id]@@.timestamp());
            assert(a[id]@@ is LowerBound);
            assert(b[id]@@ is LowerBound);
        }
        assert forall|id| #[trigger] b.contains_key(id) implies {
            &&& a[id]@@.timestamp() == b[id]@@.timestamp()
            &&& a[id]@@ is HalfRightToAdvance == b[id]@@ is HalfRightToAdvance
            &&& a[id]@@ is FullRightToAdvance == b[id]@@ is FullRightToAdvance
            &&& a[id]@@ is LowerBound == b[id]@@ is LowerBound
        } by {
            assert(a.contains_key(id));
            assert(a[id]@@.timestamp() == b[id]@@.timestamp());
            assert(a[id]@@ is LowerBound);
            assert(b[id]@@ is LowerBound);
        }
    }

    pub proof fn lemma_eq(self, other: Self)
        requires
            self.eq_timestamp(other),
        ensures
            forall|q: Quorum| #[trigger] self.valid_quorum(q) <==> other.valid_quorum(q),
            forall|q: Quorum| #[trigger]
                self.valid_quorum(q) ==> {
                    &&& self.quorum_timestamp(q) == other.quorum_timestamp(q)
                    &&& forall|ts: Timestamp| #[trigger]
                        self.unanimous_quorum(q, ts) <==> other.unanimous_quorum(q, ts)
                },
    {
        self.lemma_dom_correspondence();
        other.lemma_dom_correspondence();
        assert(self.leq(other));
        assert(other.leq(self));
        assert forall|q: Quorum| #[trigger] self.valid_quorum(q) implies {
            &&& other.valid_quorum(q)
        } by {
            other.lemma_leq_implies_validity(self, q);
        }
        assert forall|q: Quorum| #[trigger] other.valid_quorum(q) implies {
            &&& self.valid_quorum(q)
        } by {
            self.lemma_leq_implies_validity(other, q);
        }
        assert(forall|q: Quorum| #[trigger] self.valid_quorum(q) <==> other.valid_quorum(q));
        assert forall|q: Quorum| #[trigger] self.valid_quorum(q) implies {
            &&& self.quorum_timestamp(q) == other.quorum_timestamp(q)
        } by {
            assert(forall|id: u64| #[trigger]
                self.contains_key(id) ==> self[id]@@.timestamp() == other[id]@@.timestamp());
            let self_vals = self.quorum_vals(q);
            let other_vals = other.quorum_vals(q);
            let self_quorum = self.map.restrict(q);
            let other_quorum = other.map.restrict(q);
            assert(self_quorum.dom() == other_quorum.dom());
            assert forall|id: u64| #[trigger]
                self_quorum.contains_key(id) implies self_quorum[id]@@.timestamp()
                == other_quorum[id]@@.timestamp() by {
                assert(self.contains_key(id));
            }
            assert(self_quorum.values().map(
                |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
            ) == other_quorum.values().map(
                |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
            )) by {
                let f = |r: Tracked<MonotonicTimestampResource>| r@@.timestamp();
                let s = self_quorum.values().map(f);
                let o = other_quorum.values().map(f);
                assert forall|v| #[trigger] s.contains(v) implies o.contains(v) by {
                    assert(exists|id: u64| #[trigger]
                        self_quorum.contains_key(id) && f(self_quorum[id]) == v);
                    let id = choose|id: u64| #[trigger]
                        self_quorum.contains_key(id) && f(self_quorum[id]) == v;
                    assert(other_quorum.contains_key(id));
                    assert(other_quorum[id]@@.timestamp() == self_quorum[id]@@.timestamp());
                    assert(other_quorum.values().contains(other_quorum[id]));
                    assert(o.contains(v));
                }
                assert forall|v| #[trigger] o.contains(v) implies s.contains(v) by {
                    assert(exists|id: u64| #[trigger]
                        other_quorum.contains_key(id) && f(other_quorum[id]) == v);
                    let id = choose|id: u64| #[trigger]
                        other_quorum.contains_key(id) && f(other_quorum[id]) == v;
                    assert(self_quorum.contains_key(id));
                    assert(self_quorum[id]@@.timestamp() == other_quorum[id]@@.timestamp());
                    assert(self_quorum.values().contains(self_quorum[id]));
                    assert(s.contains(v));
                }
            }
            assert(self_vals == other_vals);
        }
        assert forall|q: Quorum| #[trigger] self.valid_quorum(q) implies {
            forall|ts: Timestamp| #[trigger]
                self.unanimous_quorum(q, ts) <==> other.unanimous_quorum(q, ts)
        } by {
            assert forall|ts: Timestamp| #[trigger]
                self.unanimous_quorum(q, ts) implies other.unanimous_quorum(q, ts) by {
                assert forall|id: u64| #[trigger] q.contains(id) implies other[id]@@.timestamp()
                    >= ts by {
                    assert(self.contains_key(id));
                    assert(other.contains_key(id));
                    assert(self[id]@@.timestamp() >= ts);
                    assert(self[id]@@.timestamp() == other[id]@@.timestamp());
                }
            }
            assert forall|ts: Timestamp| #[trigger]
                other.unanimous_quorum(q, ts) implies self.unanimous_quorum(q, ts) by {
                assert forall|id: u64| #[trigger] q.contains(id) implies self[id]@@.timestamp()
                    >= ts by {
                    assert(self.contains_key(id));
                    assert(other.contains_key(id));
                    assert(other[id]@@.timestamp() >= ts);
                    assert(self[id]@@.timestamp() == other[id]@@.timestamp());
                }
            }
        }
    }
}

} // verus!
