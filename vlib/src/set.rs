use vstd::prelude::*;

verus! {

pub proof fn lemma_different_sets_with_inclusion_have_difference<T>(a: Set<T>, b: Set<T>)
    requires
        a <= b,
    ensures
        a == b <==> b.difference(a).is_empty(),
{
    let diff = b.difference(a);
    if a != b {
        vstd::assert_by_contradiction!(exists |x: T| b.contains(x) && !a.contains(x), {
            assert(forall |x: T| !b.contains(x) || a.contains(x));
            assert(forall |x: T| b.contains(x) ==> a.contains(x));
            assert(b <= a);
            assert(a == b);
        });

        let x = choose|x: T| b.contains(x) && !a.contains(x);
        assert(diff.contains(x));
    }
}

} // verus!
