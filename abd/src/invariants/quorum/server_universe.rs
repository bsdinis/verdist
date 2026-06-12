#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
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

pub tracked struct ServerUniverse {
    /// mapping from server id to its lower bound
    pub tracked map: Map<u64, Tracked<MonotonicTimestampResource>>,
}

impl ServerUniverse {
    pub proof fn dummy() -> (tracked r: Self)
        ensures
            r.inv(),
            r.is_auth(),
            forall|q: Quorum| #[trigger]
                r.valid_quorum(q) ==> r.quorum_timestamp(q) >= Timestamp::spec_default(),
            forall|id| #[trigger] r.contains_key(id) ==> r[id]@@ is FullRightToAdvance,
    {
        ServerUniverse { map: Map::tracked_empty() }
    }

    pub open spec fn inv(self) -> bool {
        &&& forall|id| #[trigger]
            self.contains_key(id) && self[id]@@ is FullRightToAdvance ==> self[id]@@.timestamp()
                == Timestamp::spec_default()
    }

    pub open spec fn is_auth(self) -> bool
        recommends
            self.inv(),
    {
        forall|k: u64| #[trigger]
            self.map.contains_key(k) ==> {
                self.map[k]@@ is HalfRightToAdvance || self.map[k]@@ is FullRightToAdvance
            }
    }

    pub open spec fn is_lb(self) -> bool
        recommends
            self.inv(),
    {
        forall|k: u64| #[trigger] self.map.contains_key(k) ==> self.map[k]@@ is LowerBound
    }

    pub open spec fn dom(self) -> Set<u64> {
        self.map.dom()
    }

    pub open spec fn contains_key(self, idx: u64) -> bool {
        self.map.contains_key(idx)
    }

    pub open spec fn spec_index(self, idx: u64) -> Tracked<MonotonicTimestampResource> {
        self.map[idx]
    }

    pub open spec fn locs(self) -> Map<u64, Loc>
        recommends
            self.inv(),
    {
        self.map.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    pub proof fn lemma_locs(self)
        requires
            self.inv(),
        ensures
            self.locs().dom() == self.dom(),
    {
        vlib::map::lemma_map_values_dom(self.map, |r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    pub broadcast proof fn lemma_locs_eq(self, other: Self)
        requires
            self.inv(),
            other.inv(),
            #[trigger] self.locs() == #[trigger] other.locs(),
        ensures
            forall|id: u64| #[trigger]
                self.contains_key(id) ==> self[id]@.loc() == other[id]@.loc(),
    {
        self.lemma_locs();
        other.lemma_locs();
        assert forall|id| #[trigger] self.contains_key(id) implies self[id]@.loc()
            == other[id]@.loc() by {
            let loc = self.locs()[id];
            assert(self.map[id]@.loc() == loc);
        }
    }

    pub open spec fn valid_quorum(self, q: Quorum) -> bool
        recommends
            self.inv(),
    {
        &&& !q.is_empty()
        &&& q <= self.dom()
        &&& 2 * q.len() > self.map.len()
    }

    pub open spec fn unanimous_quorum(self, q: Quorum, lb: Timestamp) -> bool
        recommends
            self.valid_quorum(q),
    {
        forall|idx: u64| #[trigger] q.contains(idx) ==> self[idx]@@.timestamp() >= lb
    }

    pub open spec fn quorum_timestamp(self, q: Quorum) -> Timestamp
        recommends
            self.inv(),
            self.valid_quorum(q),
    {
        self.quorum_vals(q).find_unique_maximal(Self::ts_leq())
    }

    pub open spec fn quorum_vals(self, q: Quorum) -> Set<Timestamp>
        recommends
            self.inv(),
            self.valid_quorum(q),
    {
        self.map.restrict(q).map_values(
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        ).values()
    }

    pub proof fn split_auth(tracked &mut self, server_id: u64) -> (tracked r:
        MonotonicTimestampResource)
        requires
            old(self).inv(),
            old(self).is_auth(),
            old(self).contains_key(server_id),
            old(self)[server_id]@@ is FullRightToAdvance,
        ensures
            final(self).dom() == old(self).dom(),
            final(self).locs() == old(self).locs(),
            forall|id| #[trigger]
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
            final(self).is_auth(),
            r.loc() == final(self)[server_id]@.loc(),
            r@ is HalfRightToAdvance,
            r@.timestamp() == Timestamp::spec_default(),
    {
        let ghost old = *self;
        let tracked Tracked(r) = self.map.tracked_remove(server_id);
        let tracked (left, right) = r.split();
        self.map.tracked_insert(server_id, Tracked(left));
        assert forall|id| #[trigger]
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
            old(self).is_auth(),
            old(self).contains_key(server_id),
            old(self)[server_id]@@ is HalfRightToAdvance,
        ensures
            final(self).inv(),
            final(self).is_auth(),
            final(self).dom() == old(self).dom().remove(server_id),
            final(self).locs() == old(self).locs().remove(server_id),
            forall|id| #[trigger]
                final(self).contains_key(id) ==> {
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                    &&& old(self)[id]@@ is HalfRightToAdvance
                        ==> final(self)[id]@@ is HalfRightToAdvance
                    &&& old(self)[id]@@ is FullRightToAdvance
                        ==> final(self)[id]@@ is FullRightToAdvance
                    &&& old(self)[id]@@ is LowerBound ==> final(self)[id]@@ is LowerBound
                },
            r.loc() == old(self)[server_id]@.loc(),
            r@.timestamp() == old(self)[server_id]@@.timestamp(),
            r@ is HalfRightToAdvance,
    {
        let old = *self;
        let tracked Tracked(r) = self.map.tracked_remove(server_id);
        assert(self.map.agrees(old.map));
        assert forall|id| #[trigger]
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
            old(self).is_auth(),
            !old(self).contains_key(server_id),
            r@ is HalfRightToAdvance,
        ensures
            final(self).inv(),
            final(self).is_auth(),
            final(self).dom() == old(self).dom().insert(server_id),
            final(self).locs() == old(self).locs().insert(server_id, r.loc()),
            forall|id| #[trigger]
                old(self).contains_key(id) ==> {
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                    &&& old(self)[id]@@ is HalfRightToAdvance
                        ==> final(self)[id]@@ is HalfRightToAdvance
                    &&& old(self)[id]@@ is FullRightToAdvance
                        ==> final(self)[id]@@ is FullRightToAdvance
                    &&& old(self)[id]@@ is LowerBound ==> final(self)[id]@@ is LowerBound
                },
            final(self)[server_id]@.loc() == r.loc(),
            final(self)[server_id]@@.timestamp() == r@.timestamp(),
            final(self)[server_id]@@ is HalfRightToAdvance,
    {
        let old = *self;
        self.map.tracked_insert(server_id, Tracked(r));
        assert(self.map.agrees(old.map));
        assert forall|id| #[trigger]
            self.contains_key(id) && self[id]@@ is FullRightToAdvance implies self[id]@@.timestamp()
            == Timestamp::spec_default() by {
            assert(old.contains_key(id));
        }
    }

    pub proof fn tracked_remove_lb(tracked &mut self, server_id: u64) -> (tracked r:
        MonotonicTimestampResource)
        requires
            old(self).inv(),
            old(self).is_lb(),
            old(self).contains_key(server_id),
            old(self)[server_id]@@ is LowerBound,
        ensures
            final(self).inv(),
            final(self).is_lb(),
            final(self).dom() == old(self).dom().remove(server_id),
            final(self).locs() == old(self).locs().remove(server_id),
            forall|id| #[trigger]
                final(self).contains_key(id) ==> {
                    &&& old(self)[id]@.loc() == final(self)[id]@.loc()
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                    &&& old(self)[id]@@ is HalfRightToAdvance
                        ==> final(self)[id]@@ is HalfRightToAdvance
                    &&& old(self)[id]@@ is FullRightToAdvance
                        ==> final(self)[id]@@ is FullRightToAdvance
                    &&& old(self)[id]@@ is LowerBound ==> final(self)[id]@@ is LowerBound
                },
            r.loc() == old(self)[server_id]@.loc(),
            r@.timestamp() == old(self)[server_id]@@.timestamp(),
            r@ is LowerBound,
    {
        let old = *self;
        let tracked Tracked(r) = self.map.tracked_remove(server_id);
        assert(self.map.agrees(old.map));
        assert forall|id| #[trigger]
            self.contains_key(id) && self[id]@@ is FullRightToAdvance implies self[id]@@.timestamp()
            == Timestamp::spec_default() by {
            assert(old.contains_key(id));
        }
        r
    }

    pub proof fn tracked_insert_lb(
        tracked &mut self,
        server_id: u64,
        tracked r: MonotonicTimestampResource,
    )
        requires
            old(self).inv(),
            old(self).is_lb(),
            !old(self).contains_key(server_id),
            r@ is LowerBound,
        ensures
            final(self).inv(),
            final(self).is_lb(),
            final(self).dom() == old(self).dom().insert(server_id),
            final(self).locs() == old(self).locs().insert(server_id, r.loc()),
            forall|id| #[trigger]
                old(self).contains_key(id) ==> {
                    &&& old(self)[id]@.loc() == final(self)[id]@.loc()
                    &&& old(self)[id]@@.timestamp() == final(self)[id]@@.timestamp()
                    &&& old(self)[id]@@ is HalfRightToAdvance
                        ==> final(self)[id]@@ is HalfRightToAdvance
                    &&& old(self)[id]@@ is FullRightToAdvance
                        ==> final(self)[id]@@ is FullRightToAdvance
                    &&& old(self)[id]@@ is LowerBound ==> final(self)[id]@@ is LowerBound
                },
            final(self)[server_id]@.loc() == r.loc(),
            final(self)[server_id]@@.timestamp() == r@.timestamp(),
            final(self)[server_id]@@ is LowerBound,
    {
        let old = *self;
        self.map.tracked_insert(server_id, Tracked(r));
        assert(self.map.agrees(old.map));
        assert forall|id| #[trigger]
            self.contains_key(id) && self[id]@@ is FullRightToAdvance implies self[id]@@.timestamp()
            == Timestamp::spec_default() by {
            assert(old.contains_key(id));
        }
    }

    pub proof fn tracked_update_lb(
        tracked &mut self,
        server_id: u64,
        tracked r: MonotonicTimestampResource,
    )
        requires
            old(self).inv(),
            old(self).is_lb(),
            old(self).contains_key(server_id),
            r@ is LowerBound,
            old(self)[server_id]@.loc() == r.loc(),
            old(self)[server_id]@@.timestamp() <= r@.timestamp(),
        ensures
            final(self).inv(),
            final(self).is_lb(),
            final(self).dom() == old(self).dom(),
            final(self).locs() == old(self).locs(),
            forall|id| #[trigger]
                final(self).contains_key(id) ==> {
                    &&& id != server_id ==> final(self)[id]@@.timestamp() == old(
                        self,
                    )[id]@@.timestamp()
                    &&& id == server_id ==> final(self)[id]@@.timestamp() == r@.timestamp()
                },
            final(self)[server_id]@@.timestamp() == r@.timestamp(),
            old(self).leq(*final(self)),
    {
        let ghost orig_map = *self;
        self.lemma_locs();
        orig_map.lemma_locs();

        let tracked old_r = self.tracked_remove_lb(server_id);
        let ghost unchanged_map = *self;

        self.tracked_insert_lb(server_id, r);

        assert forall|id| #[trigger] self.contains_key(id) implies {
            &&& id != server_id ==> self[id]@@.timestamp() == orig_map[id]@@.timestamp()
            &&& id == server_id ==> self[id]@@.timestamp() == r@.timestamp()
            &&& self[id]@.loc() == orig_map[id]@.loc()
        } by {
            if id != server_id {
                assert(unchanged_map.contains_key(id));
            }
        }

        self.lemma_locs();
        assert forall|id| #[trigger] orig_map.contains_key(id) implies {
            &&& orig_map[id]@@.timestamp() <= self[id]@@.timestamp()
        } by {
            assert(self.contains_key(id));
        }

        assert forall|id| #[trigger] orig_map.contains_key(id) implies {
            self[id]@.loc() == orig_map[id]@.loc()
        } by {
            assert(self.contains_key(id));
        }
        assert(orig_map.locs() == self.locs());
    }

    proof fn lemma_vals(self, q: Quorum) -> (r: (Set<Timestamp>, Timestamp))
        requires
            self.inv(),
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
            self.inv(),
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
            self.inv(),
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
            self.inv(),
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

    pub open spec fn ts_leq() -> spec_fn(Timestamp, Timestamp) -> bool {
        |a: Timestamp, b: Timestamp| a <= b
    }

    pub open spec fn leq(self, other: ServerUniverse) -> bool
        recommends
            self.inv(),
            other.inv(),
    {
        &&& self.locs() == other.locs()
        &&& forall|k: u64| #[trigger]
            self.contains_key(k) ==> self[k]@@.timestamp() <= other[k]@@.timestamp()
    }

    pub open spec fn eq(self, other: ServerUniverse) -> bool
        recommends
            self.inv(),
            other.inv(),
    {
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

    pub open spec fn spec_eq(self, other: Self) -> bool {
        &&& self.inv()
        &&& other.inv()
        &&& self.is_lb()
        &&& other.is_lb()
        &&& self.eq(other)
    }

    pub broadcast proof fn lemma_eq_trans(a: Self, b: Self, c: Self)
        requires
            a.inv(),
            b.inv(),
            c.inv(),
            #[trigger] a.eq(b),
            #[trigger] b.eq(c),
        ensures
            a.eq(c),
    {
        a.lemma_locs();
        b.lemma_locs();
        c.lemma_locs();
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
        requires
            #[trigger] a.inv(),
        ensures
            a.eq(a),
    {
        a.lemma_locs();
    }

    pub open spec fn eq_timestamp(self, other: ServerUniverse) -> bool
        recommends
            self.inv(),
            other.inv(),
    {
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

    pub broadcast proof fn lemma_eq_timestamp_trans(a: Self, b: Self, c: Self)
        requires
            a.inv(),
            b.inv(),
            c.inv(),
            #[trigger] a.eq_timestamp(b),
            #[trigger] b.eq_timestamp(c),
        ensures
            a.eq_timestamp(c),
    {
        a.lemma_locs();
        b.lemma_locs();
        c.lemma_locs();
        assert(a.locs() == c.locs());
        assert forall|id: u64| #[trigger] a.contains_key(id) implies {
            &&& a[id]@@.timestamp() == c[id]@@.timestamp()
        } by {
            assert(b.contains_key(id));
        }

        assert forall|id: u64| #[trigger] c.contains_key(id) implies {
            &&& c[id]@@.timestamp() == a[id]@@.timestamp()
        } by {
            assert(b.contains_key(id));
        }
    }

    pub broadcast proof fn lemma_eq_timestamp_lb_is_eq(a: Self, b: Self)
        requires
            a.inv(),
            b.inv(),
            a.is_lb(),
            b.is_lb(),
            #[trigger] a.eq_timestamp(b),
        ensures
            a.eq(b),
    {
        a.lemma_locs();
        b.lemma_locs();
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
    }

    pub proof fn lemma_leq_implies_validity(self, other: ServerUniverse, q: Quorum)
        requires
            self.inv(),
            other.inv(),
            self.leq(other) || other.leq(self),
        ensures
            self.valid_quorum(q) <==> other.valid_quorum(q),
    {
        assert(self.locs().dom() == other.locs().dom());
        assert(self.locs().dom() == self.dom());
        assert(self.dom() == other.dom());
        assert(self.map.len() == other.map.len());

        let dom = self.dom();
        let len = self.map.len();

        if self.valid_quorum(q) {
            assert(q <= dom);
            assert(2 * q.len() > len);
        }
    }

    pub proof fn lemma_leq_retains_unanimity(self, other: ServerUniverse, q: Quorum, lb: Timestamp)
        requires
            self.inv(),
            other.inv(),
            self.leq(other),
            self.valid_quorum(q),
        ensures
            self.unanimous_quorum(q, lb) ==> other.unanimous_quorum(q, lb),
    {
        self.lemma_leq_implies_validity(other, q);
        assert(other.valid_quorum(q));
        if self.unanimous_quorum(q, lb) {
            assert forall|idx: u64| #[trigger] q.contains(idx) implies other[idx]@@.timestamp()
                >= lb by {
                assert(self.contains_key(idx));
                assert(self[idx]@@.timestamp() <= other[idx]@@.timestamp());
            }
        }
    }

    pub proof fn lemma_leq_quorum_timestamp(self, other: ServerUniverse, q: Quorum)
        requires
            self.inv(),
            other.inv(),
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

    pub proof fn lemma_leq_quorums(self, other: ServerUniverse, min: Timestamp)
        requires
            self.inv(),
            other.inv(),
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

    pub proof fn lemma_leq_trans(a: Self, b: Self, c: Self)
        requires
            a.inv(),
            b.inv(),
            c.inv(),
            a.leq(b),
            b.leq(c),
        ensures
            a.leq(c),
    {
        a.lemma_locs();
        b.lemma_locs();
        c.lemma_locs();
        assert forall|k: u64| #[trigger] a.contains_key(k) implies a[k]@@.timestamp()
            <= c[k]@@.timestamp() by {
            assert(b.contains_key(k));
            assert(c.contains_key(k));
        }
    }

    pub proof fn lemma_eq(self, other: ServerUniverse)
        requires
            self.inv(),
            other.inv(),
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
        self.lemma_locs();
        other.lemma_locs();
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
                    assert(exists|id| #[trigger]
                        self_quorum.contains_key(id) && f(self_quorum[id]) == v);
                    let id = choose|id| #[trigger]
                        self_quorum.contains_key(id) && f(self_quorum[id]) == v;
                    assert(other_quorum.contains_key(id));
                    assert(other_quorum[id]@@.timestamp() == self_quorum[id]@@.timestamp());
                    assert(other_quorum.values().contains(other_quorum[id]));
                    assert(o.contains(v));
                }
                assert forall|v| #[trigger] o.contains(v) implies s.contains(v) by {
                    assert(exists|id| #[trigger]
                        other_quorum.contains_key(id) && f(other_quorum[id]) == v);
                    let id = choose|id| #[trigger]
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

    pub proof fn lemma_lb(tracked &mut self, tracked other: &Self)
        requires
            old(self).inv(),
            old(self).is_lb(),
            other.inv(),
            other.is_auth(),
            old(self).locs() == other.locs(),
        ensures
            final(self).inv(),
            final(self).is_lb(),
            final(self).eq(*old(self)),
            final(self).leq(*other),
    {
        self.prove_lower_bound(other, Set::empty());
    }

    proof fn prove_lower_bound(tracked &mut self, tracked other: &Self, visited: Set<u64>)
        requires
            old(self).inv(),
            old(self).is_lb(),
            other.inv(),
            other.is_auth(),
            old(self).locs() == other.locs(),
            visited <= old(self).dom(),
            forall|id| #[trigger]
                visited.contains(id) ==> old(self)[id]@@.timestamp() <= other[id]@@.timestamp(),
        ensures
            final(self).inv(),
            final(self).is_lb(),
            final(self).locs() == old(self).locs(),
            final(self).leq(*other),
            final(self).eq(*old(self)),
        decreases other.dom().difference(visited).len(),
    {
        self.lemma_locs();
        other.lemma_locs();
        self.lemma_locs_eq(*other);
        if other.dom().difference(visited).is_empty() {
            vlib::set::lemma_different_sets_with_inclusion_have_difference(visited, other.dom());
            return;
        }
        assert(exists|id| #[trigger] other.dom().contains(id) && !visited.contains(id));
        let server_id = choose|id| #[trigger] other.dom().contains(id) && !visited.contains(id);
        assert(self.contains_key(server_id));
        assert(self[server_id]@.loc() == other[server_id]@.loc());

        let tracked Tracked(mut r) = self.map.tracked_remove(server_id);
        r.lemma_lower_bound(other.map.tracked_borrow(server_id).borrow());
        self.map.tracked_insert(server_id, Tracked(r));

        other.dom().lemma_set_insert_diff_decreases(visited, server_id);

        assert(self.locs() == old(self).locs());
        assert(self.eq(*old(self)));
        let old_self = *self;
        self.prove_lower_bound(other, visited.insert(server_id));
        assert(self.eq(old_self));
        Self::lemma_eq_trans(*self, old_self, *old(self));
    }

    // This is the big quorum lemma
    pub proof fn lemma_quorum_lb(self, lb_quorum: Quorum, ts: Timestamp)
        requires
            self.inv(),
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

    proof fn lemma_quorum_intersection(self, q1: Quorum, q2: Quorum) -> (witness_idx: u64)
        requires
            self.inv(),
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
            self.inv(),
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
            vstd::assert_by_contradiction!(self[idx]@@.timestamp() >= lb,
            {

            });
        }
    }

    pub proof fn extract_lbs(tracked &self) -> (tracked r: ServerUniverse)
        requires
            self.inv(),
        ensures
            r.inv(),
            r.is_lb(),
            self.eq_timestamp(r),
    {
        let tracked mut map = Map::tracked_empty();
        Self::duplicate_map(&self.map, &mut map);

        ServerUniverse { map }
    }

    proof fn duplicate_map(
        tracked m: &Map<u64, Tracked<MonotonicTimestampResource>>,
        tracked other: &mut Map<u64, Tracked<MonotonicTimestampResource>>,
    )
        requires
            forall|k| #[trigger]
                old(other).contains_key(k) ==> {
                    &&& m.contains_key(k) && old(other)[k]@@ is LowerBound && old(
                        other,
                    )[k]@@.timestamp() == m[k]@@.timestamp() && old(other)[k]@.loc() == m[k]@.loc()
                },
            old(other).map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc())
                <= m.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc()),
        ensures
            final(other).dom() == m.dom(),
            forall|k| #[trigger]
                final(other).contains_key(k) ==> {
                    &&& m.contains_key(k)
                    &&& final(other)[k]@@ is LowerBound
                    &&& final(other)[k]@@.timestamp() == m[k]@@.timestamp()
                    &&& final(other)[k]@.loc() == m[k]@.loc()
                },
            final(other).map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc())
                == m.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc()),
        decreases m.dom().difference(old(other).dom()).len(),
    {
        broadcast use vstd::set::Set::lemma_set_insert_diff_decreases;

        let ghost diff = m.dom().difference(other.dom());
        if diff.len() == 0 {
            diff.lemma_len0_is_empty();
            vlib::set::lemma_different_sets_with_inclusion_have_difference(other.dom(), m.dom());
            return;
        }
        vstd::assert_by_contradiction!(!diff.is_empty(), {
            diff.lemma_len0_is_empty();
        });
        let new_k = diff.choose();
        let tracked lb = m.tracked_borrow(new_k).borrow().extract_lower_bound();
        other.tracked_insert(new_k, Tracked(lb));

        Self::duplicate_map(m, other)
    }
}

} // verus!
