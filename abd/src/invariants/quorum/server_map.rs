#[cfg(verus_only)]
use crate::timestamp::Timestamp;
use vstd::prelude::*;

use crate::resource::monotonic_timestamp::MonotonicTimestampResource;

verus! {

pub(crate) type ServerMap = Map<u64, Tracked<MonotonicTimestampResource>>;

// The following `raw_*` helpers each take/return a `tracked ServerMap` *by value* rather than
// mutating a `&mut ServerMap` field in place. This lets `ServerUniverseAuth`'s methods (which
// hold `tracked &mut self` and have `inv()` as a `#[verifier::type_invariant]`) perform a
// multi-step edit (remove+split+insert, etc.) on a local copy — obtained via
// `vstd::modes::tracked_swap` — without Verus re-checking `self`'s type invariant after each
// intermediate field mutation; the invariant is only re-established once, when the finished map
// is swapped back into `self.map`.
// Splits a `FullRightToAdvance` entry into the two halves, keeping the `HalfRightToAdvance` half
// in the map and returning the other.
pub(crate) proof fn raw_split_auth(tracked map: ServerMap, server_id: u64) -> (tracked r: (
    ServerMap,
    MonotonicTimestampResource,
))
    requires
        map.contains_key(server_id),
        map[server_id]@@ is FullRightToAdvance,
        map[server_id]@@.timestamp() == Timestamp::spec_default(),
    ensures
        r.0.dom() == map.dom(),
        r.0.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc()) == map.map_values(
            |x: Tracked<MonotonicTimestampResource>| x@.loc(),
        ),
        forall|id: u64| #[trigger]
            map.contains_key(id) ==> {
                &&& map[id]@@.timestamp() == r.0[id]@@.timestamp()
                &&& id == server_id ==> r.0[id]@@ is HalfRightToAdvance
                &&& id != server_id ==> {
                    &&& map[id]@@ is HalfRightToAdvance ==> r.0[id]@@ is HalfRightToAdvance
                    &&& map[id]@@ is FullRightToAdvance ==> r.0[id]@@ is FullRightToAdvance
                }
            },
        r.1.loc() == r.0[server_id]@.loc(),
        r.1@ is HalfRightToAdvance,
        r.1@.timestamp() == Timestamp::spec_default(),
{
    let tracked mut map = map;
    let tracked Tracked(r) = map.tracked_remove(server_id);
    let tracked (left, right) = r.split();
    map.tracked_insert(server_id, Tracked(left));
    (map, right)
}

// Removes a `HalfRightToAdvance` entry from the map, returning it.
pub(crate) proof fn raw_remove_auth(tracked map: ServerMap, server_id: u64) -> (tracked r: (
    ServerMap,
    MonotonicTimestampResource,
))
    requires
        map.contains_key(server_id),
        map[server_id]@@ is HalfRightToAdvance,
    ensures
        r.0.dom() == map.dom().remove(server_id),
        r.0.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc()) == map.remove(
            server_id,
        ).map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc()),
        forall|id: u64| #[trigger]
            r.0.contains_key(id) ==> {
                &&& map.contains_key(id)
                &&& map[id]@@.timestamp() == r.0[id]@@.timestamp()
                &&& map[id]@@ is HalfRightToAdvance ==> r.0[id]@@ is HalfRightToAdvance
                &&& map[id]@@ is FullRightToAdvance ==> r.0[id]@@ is FullRightToAdvance
            },
        r.1.loc() == map[server_id]@.loc(),
        r.1@.timestamp() == map[server_id]@@.timestamp(),
        r.1@ is HalfRightToAdvance,
{
    let tracked mut map = map;
    let tracked Tracked(r) = map.tracked_remove(server_id);
    (map, r)
}

// Removes a `LowerBound` entry from the map, returning it.
pub(crate) proof fn raw_remove_lb(tracked map: ServerMap, server_id: u64) -> (tracked r: (
    ServerMap,
    MonotonicTimestampResource,
))
    requires
        map.contains_key(server_id),
        map[server_id]@@ is LowerBound,
    ensures
        r.0.dom() == map.dom().remove(server_id),
        r.0.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc()) == map.remove(
            server_id,
        ).map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc()),
        forall|id: u64| #[trigger]
            r.0.contains_key(id) ==> {
                &&& map.contains_key(id)
                &&& map[id]@@.timestamp() == r.0[id]@@.timestamp()
                &&& map[id]@@ is LowerBound ==> r.0[id]@@ is LowerBound
            },
        r.1.loc() == map[server_id]@.loc(),
        r.1@.timestamp() == map[server_id]@@.timestamp(),
        r.1@ is LowerBound,
{
    let tracked mut map = map;
    let tracked Tracked(r) = map.tracked_remove(server_id);
    (map, r)
}

// Inserts a fresh `HalfRightToAdvance` entry into the map.
pub(crate) proof fn raw_insert_auth(
    tracked map: ServerMap,
    server_id: u64,
    tracked r: MonotonicTimestampResource,
) -> (tracked out: ServerMap)
    requires
        !map.contains_key(server_id),
        r@ is HalfRightToAdvance,
    ensures
        out.dom() == map.dom().insert(server_id),
        out.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc()) == map.map_values(
            |x: Tracked<MonotonicTimestampResource>| x@.loc(),
        ).insert(server_id, r.loc()),
        forall|id: u64| #[trigger]
            map.contains_key(id) ==> {
                &&& map[id]@@.timestamp() == out[id]@@.timestamp()
                &&& map[id]@@ is HalfRightToAdvance ==> out[id]@@ is HalfRightToAdvance
                &&& map[id]@@ is FullRightToAdvance ==> out[id]@@ is FullRightToAdvance
            },
        out[server_id]@.loc() == r.loc(),
        out[server_id]@@.timestamp() == r@.timestamp(),
        out[server_id]@@ is HalfRightToAdvance,
{
    let tracked mut map = map;
    map.tracked_insert(server_id, Tracked(r));
    map
}

// Inserts a fresh `LowerBound` entry into the map.
pub(crate) proof fn raw_insert_lb(
    tracked map: ServerMap,
    server_id: u64,
    tracked r: MonotonicTimestampResource,
) -> (tracked out: ServerMap)
    requires
        !map.contains_key(server_id),
        r@ is LowerBound,
    ensures
        out.dom() == map.dom().insert(server_id),
        out.map_values(|x: Tracked<MonotonicTimestampResource>| x@.loc()) == map.map_values(
            |x: Tracked<MonotonicTimestampResource>| x@.loc(),
        ).insert(server_id, r.loc()),
        forall|id: u64| #[trigger]
            map.contains_key(id) ==> {
                &&& map[id]@@.timestamp() == out[id]@@.timestamp()
                &&& map[id]@@ is LowerBound ==> out[id]@@ is LowerBound
            },
        out[server_id]@.loc() == r.loc(),
        out[server_id]@@.timestamp() == r@.timestamp(),
        out[server_id]@@ is LowerBound,
{
    let tracked mut map = map;
    map.tracked_insert(server_id, Tracked(r));
    map
}

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
