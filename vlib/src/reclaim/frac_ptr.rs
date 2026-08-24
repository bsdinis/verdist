//! Generic, reusable primitives for handing out lock-free, multi-reader shared access to
//! heap-allocated, non-`Copy` data, backed by `vstd::resource::frac_opt::Frac<PointsTo<T>>`
//! (a pre-existing, already-trusted `vstd` combinator -- not something new we're adding).
//!
//! The key fact that makes this axiom-free: `Frac::borrow()` is a **proof-only** function, so it
//! can be called anywhere, not just inside an atomic invariant's single-atomic-op window. A share
//! of the `Frac<PointsTo<T>>` can be peeled off *inside* an atomic invariant (a proof-only
//! `split_to`, alongside the one real atomic op -- the same "atomic op + arbitrary proof-only
//! ghost mutation" pattern already used by `EpochGlobal::advance`/`current`), then carried outside
//! the invariant, where `borrow_shared` below turns it into a real `&T` via `ptr_ref2` (which
//! itself requires `opens_invariants none`, i.e. must run outside any open invariant anyway).
//!
//! Since a generation's data is only ever read after publish (each write allocates a fresh
//! generation instead of mutating in place), multiple concurrently-live `&T` shares are always
//! sound, regardless of whether `T` is `Copy`.
use vstd::layout::layout_for_type_is_valid;
use vstd::prelude::*;
use vstd::raw_ptr::Dealloc;
use vstd::raw_ptr::PointsTo;
use vstd::raw_ptr::SharedReference;
use vstd::raw_ptr::allocate;
use vstd::raw_ptr::cast_ptr_to_thin_ptr;
use vstd::raw_ptr::deallocate;
use vstd::raw_ptr::ptr_mut_write;
use vstd::raw_ptr::ptr_ref2;
use vstd::resource::frac_opt::Frac;

verus! {

// Allocates heap memory for a `T`, initialized with `v`. Mirrors
// `vstd::simple_pptr::PPtr::new`, but keeps the `raw_ptr::PointsTo<T>` un-wrapped (`simple_pptr`
// bundles it privately with no accessor) so it can be handed to `Frac::new`/`ptr_ref2`.
pub fn epoch_alloc<T>(v: T) -> (result: (*mut T, Tracked<PointsTo<T>>, Tracked<Dealloc>))
    requires
        core::mem::size_of::<T>() != 0,
    ensures
        result.1@.ptr() == result.0,
        result.1@.is_init(),
        result.1@.value() == v,
    opens_invariants none
{
    layout_for_type_is_valid::<T>();
    let (p, Tracked(points_to_raw), Tracked(dealloc)) = allocate(
        core::mem::size_of::<T>(),
        core::mem::align_of::<T>(),
    );
    let ptr: *mut T = cast_ptr_to_thin_ptr::<u8, T>(p);
    let tracked mut points_to = points_to_raw.into_typed::<T>(ptr.addr());
    ptr_mut_write(ptr, Tracked(&mut points_to), v);
    (ptr, Tracked(points_to), Tracked(dealloc))
}

// Frees memory previously allocated by `epoch_alloc`. Only ever called by the collector, once
// it has established no reader can still be dereferencing `ptr` (all `Frac` shares returned).
pub fn epoch_free<T>(ptr: *mut T, Tracked(points_to): Tracked<PointsTo<T>>, Tracked(dealloc): Tracked<Dealloc>)
    requires
        points_to.ptr() == ptr,
        points_to.is_init(),
        dealloc.addr() == ptr.addr(),
        dealloc.size() == core::mem::size_of::<T>(),
        dealloc.align() == core::mem::align_of::<T>(),
        dealloc.provenance() == points_to.ptr()@.provenance,
    opens_invariants none
{
    let tracked mut points_to = points_to;
    proof {
        points_to.leak_contents();
    }
    let tracked points_to_raw = points_to.into_raw();
    let p: *mut u8 = cast_ptr_to_thin_ptr::<T, u8>(ptr);
    deallocate(
        p,
        core::mem::size_of::<T>(),
        core::mem::align_of::<T>(),
        Tracked(points_to_raw),
        Tracked(dealloc),
    );
}

// Turns a fractional share of a `PointsTo<T>` into a real shared reference, without ever
// requiring the caller to have an invariant open at the call site (matching `ptr_ref2`'s own
// `opens_invariants none` requirement). Callers obtain `share` by peeling it off an
// invariant-protected `Frac<PointsTo<T>>` accumulator (see `Generation::split_share`) *before*
// calling this, and return it (see `Generation::return_share`) once done with the reference.
pub fn borrow_shared<'a, T>(ptr: *const T, Tracked(share): Tracked<&'a Frac<PointsTo<T>>>) -> (result: SharedReference<
    'a,
    T,
>)
    requires
        share.resource().ptr() == ptr,
        share.resource().is_init(),
    ensures
        result.value() == share.resource().value(),
    opens_invariants none
{
    let tracked perm_ref = share.borrow();
    ptr_ref2(ptr, Tracked(perm_ref))
}

} // verus!
