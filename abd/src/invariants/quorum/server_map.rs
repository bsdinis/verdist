use vstd::prelude::*;

use crate::resource::monotonic_timestamp::MonotonicTimestampResource;

verus! {

pub(crate) type ServerMap = Map<u64, Tracked<MonotonicTimestampResource>>;

// Duplicates every entry of `m` into a fresh `LowerBound`-only map, regardless of what kind of
// entries `m` itself holds (this is how a `ServerUniverseLb` is derived from either a
// `ServerUniverseAuth` or another `ServerUniverseLb`). Kept as a shared tracked-permission
// helper (not a spec predicate), since it only manipulates resources, not quorum-comparison
// facts that must line up across the two public types.
pub(crate) proof fn raw_extract_lbs(tracked m: &ServerMap) -> (tracked r: ServerMap)
    ensures
        r.dom() == m.dom(),
        forall|k: u64| #[trigger]
            r.contains_key(k) ==> {
                &&& r[k]@@ is LowerBound
                &&& r[k]@@.timestamp() == m[k]@@.timestamp()
                &&& r[k]@.loc() == m[k]@.loc()
            },
        r.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc()) == m.map_values(
            |r: Tracked<MonotonicTimestampResource>| r@.loc(),
        ),
{
    let tracked mut out = Map::tracked_empty();
    raw_duplicate_map(m, &mut out);
    out
}

pub(crate) proof fn raw_duplicate_map(tracked m: &ServerMap, tracked other: &mut ServerMap)
    requires
        forall|k: u64| #[trigger]
            old(other).contains_key(k) ==> {
                &&& m.contains_key(k) && old(other)[k]@@ is LowerBound && old(
                    other,
                )[k]@@.timestamp() == m[k]@@.timestamp() && old(other)[k]@.loc() == m[k]@.loc()
            },
        old(other).map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc()) <= m.map_values(
            |r: Tracked<MonotonicTimestampResource>| r@.loc(),
        ),
    ensures
        final(other).dom() == m.dom(),
        forall|k: u64| #[trigger]
            final(other).contains_key(k) ==> {
                &&& m.contains_key(k)
                &&& final(other)[k]@@ is LowerBound
                &&& final(other)[k]@@.timestamp() == m[k]@@.timestamp()
                &&& final(other)[k]@.loc() == m[k]@.loc()
            },
        final(other).map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc()) == m.map_values(
            |r: Tracked<MonotonicTimestampResource>| r@.loc(),
        ),
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

    raw_duplicate_map(m, other)
}

} // verus!
