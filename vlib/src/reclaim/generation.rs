//! `Generation<T>`: a heap-allocated, address-stable holder for one "version" of a
//! lock-free-published value, together with the `Frac<PointsTo<T>>` accumulator that gates
//! fractional read access to it (see `reclaim::frac_ptr` for why this is axiom-free).
//!
//! A `Generation<T>` is created once (by the writer, holding the freshly-allocated value
//! exclusively) and from then on is only ever *read* -- readers borrow a share of the
//! accumulator (`split_share`), dereference through it (via `frac_ptr::borrow_shared`), and give
//! the share back (`return_share`). Reclaiming the backing memory is deliberately *not* done by
//! `Generation` itself: `into_reclaimable` just hands back whatever fraction the accumulator
//! currently holds (which may be less than 1 if shares are still outstanding), and the free
//! function `reclaim` requires `frac() == 1` to actually free. Proving that precondition -- that
//! every share ever split off has been returned -- is the collector's job (tied to `ReaderSlot`
//! quiescence), not something `Generation` can determine on its own.
use crate::reclaim::frac_ptr;

use vstd::atomic_ghost::AtomicBool;
use vstd::atomic_ghost::AtomicInvariantPredicate;
use vstd::atomic_ghost::atomic_with_ghost;
use vstd::prelude::*;
use vstd::raw_ptr::Dealloc;
use vstd::raw_ptr::PointsTo;
use vstd::resource::Loc;
use vstd::resource::frac_opt::Frac;

verus! {

pub struct GenerationFracPred<T> {
    dummy: core::marker::PhantomData<T>,
}

// The physical `bool` payload is vestigial (same idiom as `ReaderSlot`/`ShardLoad`): the atomic
// exists only to give `Sync`-safe, invariant-protected access to the *real* payload, the ghost
// `Frac<PointsTo<T>>` accumulator. `k = (ptr, loc)` pins the accumulator to always agree on which
// pointer it's for *and* fixes its resource location, so callers can state (and this module can
// check) "this share came from this generation" via `Frac::id()` without needing to open the
// invariant just to find out.
impl<T> AtomicInvariantPredicate<(*mut T, Loc), bool, Frac<PointsTo<T>>> for GenerationFracPred<T> {
    open spec fn atomic_inv(k: (*mut T, Loc), v: bool, g: Frac<PointsTo<T>>) -> bool {
        &&& g.resource().ptr() == k.0
        &&& g.resource().is_init()
        &&& g.id() == k.1
    }
}

pub struct Generation<T> {
    ptr: *mut T,
    dealloc: Tracked<Dealloc>,
    frac_gate: AtomicBool<(*mut T, Loc), Frac<PointsTo<T>>, GenerationFracPred<T>>,
}

impl<T> Generation<T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.frac_gate.well_formed()
        &&& self.frac_gate.constant().0 == self.ptr
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    pub closed spec fn loc(self) -> Loc {
        self.frac_gate.constant().1
    }

    pub fn new(v: T) -> (result: Self)
        requires
            core::mem::size_of::<T>() != 0,
    {
        let (ptr, Tracked(points_to), dealloc) = frac_ptr::epoch_alloc(v);
        let tracked frac = Frac::new(points_to);
        let ghost loc = frac.id();
        let frac_gate = AtomicBool::new(Ghost((ptr, loc)), true, Tracked(frac));
        let result = Generation { ptr, dealloc, frac_gate };
        assert(result.inv());
        result
    }

    // Peels off half of whatever the accumulator currently holds. Always succeeds regardless of
    // how many shares are already outstanding (`Frac::split` only ever needs `frac() > 0`, which
    // the accumulator's own type invariant guarantees) -- so no static bound on the number of
    // concurrent readers is needed.
    pub fn split_share(&self) -> (result: Tracked<Frac<PointsTo<T>>>)
        ensures
            result@.resource().ptr() == self.ptr(),
            result@.resource().is_init(),
            result@.id() == self.loc(),
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut share_out: Option<Frac<PointsTo<T>>> = None;
        atomic_with_ghost!(&self.frac_gate => load(); ghost g => {
            share_out = Some(g.split());
        });
        Tracked(share_out.tracked_unwrap())
    }

    // Merges a previously-split share back into the accumulator. The share must have come from
    // *this* generation's accumulator (same resource location) -- always true for a share
    // obtained from `split_share` on this same `Generation`.
    pub fn return_share(&self, Tracked(share): Tracked<Frac<PointsTo<T>>>)
        requires
            share.id() == self.loc(),
    {
        proof {
            use_type_invariant(self);
        }
        atomic_with_ghost!(&self.frac_gate => load(); ghost g => {
            g.combine(share);
        });
    }

    // Consumes the generation, handing back its pointer, `Dealloc` permission, and whatever
    // fraction the accumulator currently holds. Does *not* require or check `frac() == 1` --
    // proving that is the collector's job (see module docs); this is just the raw extraction.
    pub fn into_reclaimable(self) -> (result: (*mut T, Tracked<Frac<PointsTo<T>>>, Tracked<Dealloc>))
        ensures
            result.1@.resource().ptr() == result.0,
            result.1@.resource().is_init(),
    {
        proof {
            use_type_invariant(&self);
        }
        let Generation { ptr, dealloc, frac_gate } = self;
        let (_dummy, Tracked(g)) = frac_gate.into_inner();
        (ptr, Tracked(g), dealloc)
    }
}

// Actually frees a generation's backing memory. Only sound once `full` represents *all*
// outstanding fractions recombined (`frac() == 1`) -- i.e. once the collector has established,
// via `ReaderSlot` quiescence, that every share ever split off has been returned.
pub fn reclaim<T>(ptr: *mut T, Tracked(full): Tracked<Frac<PointsTo<T>>>, Tracked(dealloc): Tracked<Dealloc>) -> (result: T)
    requires
        full.frac() == 1 as real,
        full.resource().ptr() == ptr,
        full.resource().is_init(),
        dealloc.addr() == ptr.addr(),
        dealloc.size() == core::mem::size_of::<T>(),
        dealloc.align() == core::mem::align_of::<T>(),
        dealloc.provenance() == full.resource().ptr()@.provenance,
    ensures
        result == full.resource().value(),
{
    let tracked (mut points_to, _empty) = full.take_resource();
    let v = vstd::raw_ptr::ptr_mut_read(ptr, Tracked(&mut points_to));
    let tracked points_to_raw = points_to.into_raw();
    let p: *mut u8 = vstd::raw_ptr::cast_ptr_to_thin_ptr::<T, u8>(ptr);
    vstd::raw_ptr::deallocate(
        p,
        core::mem::size_of::<T>(),
        core::mem::align_of::<T>(),
        Tracked(points_to_raw),
        Tracked(dealloc),
    );
    v
}

} // verus!
