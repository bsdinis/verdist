use vstd::prelude::*;

verus! {

pub proof fn lemma_map_values_dom<K, V, W>(a: Map<K, V>, f: spec_fn(V) -> W)
    ensures
        a.map_values(f).dom() == a.dom(),
{
    let b = a.map_values(f);
    assert forall|k: K| #[trigger] a.contains_key(k) implies b.contains_key(k) by {}

    assert forall|k: K| #[trigger] b.contains_key(k) implies a.contains_key(k) by {}
}

pub proof fn lemma_map_values_commutes<K, V, W>(a: Map<K, V>, f: spec_fn(V) -> W)
    ensures
        a.map_values(f).values() == a.values().map(f),
{
    let vals = a.values().map(f);
    assert forall|k: K| #[trigger] a.contains_key(k) implies vals.contains(f(a[k])) by {
        assert(a.values().contains(a[k]));
        assert(vals.contains(f(a[k])));
    }

    let b = a.map_values(f);
    lemma_map_values_dom(a, f);
    assert forall|k: K| #[trigger] b.contains_key(k) implies vals.contains(b[k]) by {
        assert(a.contains_key(k));
    }
}

} // verus!
