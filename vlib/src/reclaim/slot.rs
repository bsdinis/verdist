//! `Slot<T>`: a heap-address-stable, *reusable* holder for a lock-free-published value, gated by
//! a `Frac<PointsTo<T>>` accumulator (see `reclaim::frac_ptr` for why this is axiom-free).
//!
//! Unlike a one-shot generation, a `Slot<T>` cycles between two ghost states:
//!   - `Vacant`: nothing installed. A zero-content enum variant -- trivially, freely
//!     constructible (like `None`), no allocation, no placeholder, no leak.
//!   - `Occupied { frac, dealloc }`: a value is installed; `frac` gates fractional read access
//!     to it exactly like the earlier one-shot design (readers `split`/`combine` shares), and
//!     `dealloc` is kept alongside so the *specific* allocation currently installed can be freed
//!     later without needing a separate, install-spanning field.
//!
//! A `Slot<T>` is created once (`new_vacant`/`new_occupied`), then installed/reinstalled any
//! number of times via `take`/`put`: `take` unconditionally swaps the slot to `Vacant` and hands
//! back whatever was there (always safe to call); `put` requires an `old: SlotState<T>` argument
//! satisfying `is_vacant()`. Note this is *not* a real type-level guarantee against double-install
//! -- `Vacant` is a zero-content variant, so any caller can trivially fabricate one regardless of
//! the slot's actual live state. It's `EpochAtomicPtr`'s job (not `Slot`'s) to only ever call
//! `put` using a witness genuinely obtained from a preceding `take` on the same slot.
//!
//! What `Slot` deliberately does *not* decide: whether it's actually *safe* to reclaim an
//! `Occupied` value (i.e. that every share ever split off it has been returned, `frac() == 1`).
//! That's the collector's job (tied to `ReaderSlot` quiescence), kept out of this module exactly
//! as it was for the one-shot design.
use crate::reclaim::frac_ptr;

use vstd::atomic_ghost::atomic_with_ghost;
use vstd::atomic_ghost::AtomicInvariantPredicate;
use vstd::atomic_ghost::AtomicPtr;
use vstd::prelude::*;
use vstd::raw_ptr::Dealloc;
use vstd::raw_ptr::PointsTo;
use vstd::resource::frac_opt::Frac;

verus! {

pub tracked enum SlotState<T> {
    Vacant,
    Occupied { frac: Frac<PointsTo<T>>, dealloc: Dealloc },
}

impl<T> SlotState<T> {
    pub open spec fn is_vacant(&self) -> bool {
        self is Vacant
    }
}

pub struct SlotPred<T> {
    dummy: core::marker::PhantomData<T>,
}

// Bidirectional: `Vacant` iff the physical pointer is null. This is what lets callers use a
// plain, executable `ptr.addr() != 0` check as a stand-in for "is this ghost state Occupied",
// instead of needing to pattern-match ghost data and assume the "shouldn't happen" arm away
// (see `Slot::take`/`split_share` and `EpochAtomicPtr::pin`/`write`, which rely on this).
impl<T> AtomicInvariantPredicate<(), *mut T, SlotState<T>> for SlotPred<T> {
    open spec fn atomic_inv(_k: (), v: *mut T, g: SlotState<T>) -> bool {
        match g {
            SlotState::Vacant => v.addr() == 0,
            SlotState::Occupied { frac, dealloc } => {
                &&& frac.resource().ptr() == v
                &&& frac.resource().is_init()
                &&& v.addr() != 0
                &&& dealloc.addr() == v.addr()
                &&& dealloc.size() == core::mem::size_of::<T>()
                &&& dealloc.align() == core::mem::align_of::<T>()
                &&& dealloc.provenance() == frac.resource().ptr()@.provenance
            },
        }
    }
}

pub struct Slot<T> {
    gate: AtomicPtr<T, (), SlotState<T>, SlotPred<T>>,
}

impl<T> Slot<T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        self.gate.well_formed()
    }

    pub fn new_vacant() -> (result: Self) {
        let gate = AtomicPtr::new(Ghost(()), core::ptr::null_mut(), Tracked(SlotState::Vacant));
        let result = Slot { gate };
        assert(result.inv());
        result
    }

    // Convenience for the very first install, avoiding an awkward `new_vacant` + `put` dance
    // (`put` needs a `Vacant` witness in hand, which `new_vacant` doesn't hand back).
    pub fn new_occupied(v: T) -> (result: Self)
        requires
            core::mem::size_of::<T>() != 0,
    {
        let (ptr, Tracked(points_to), Tracked(dealloc)) = frac_ptr::epoch_alloc(v);
        let tracked frac = Frac::new(points_to);
        let gate = AtomicPtr::new(Ghost(()), ptr, Tracked(SlotState::Occupied { frac, dealloc }));
        let result = Slot { gate };
        assert(result.inv());
        result
    }

    // Unconditionally swaps the slot to `Vacant`, handing back the physical pointer it was
    // gating (needed to actually free the backing memory) together with whatever ghost state was
    // there. Always safe to call -- it's the *caller's* job to know whether what comes back is
    // actually reclaimable (frac() == 1) before trying to free it, or to `put` a fresh value in
    // its place.
    pub fn take(&self) -> (result: (*mut T, Tracked<SlotState<T>>))
        ensures
            result.0.addr() != 0 ==> result.1@ is Occupied,
            result.1@ is Occupied ==> {
                &&& result.1@->Occupied_frac.resource().ptr() == result.0
                &&& result.1@->Occupied_frac.resource().is_init()
                &&& result.1@->Occupied_dealloc.addr() == result.0.addr()
                &&& result.1@->Occupied_dealloc.size() == core::mem::size_of::<T>()
                &&& result.1@->Occupied_dealloc.align() == core::mem::align_of::<T>()
                &&& result.1@->Occupied_dealloc.provenance()
                    == result.1@->Occupied_frac.resource().ptr()@.provenance
            },
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut out: Option<SlotState<T>> = None;
        let null_ptr: *mut T = core::ptr::null_mut();
        let old_ptr =
            atomic_with_ghost!(&self.gate => swap(null_ptr); ghost g => {
            out = Some(g);
            g = SlotState::Vacant;
        });
        (old_ptr, Tracked(out.tracked_unwrap()))
    }

    // Installs a fresh value, consuming a `Vacant` witness (from `take` or `new_vacant`) as
    // proof that nothing is currently occupying the slot.
    pub fn put(&self, v: T, Tracked(old): Tracked<SlotState<T>>)
        requires
            core::mem::size_of::<T>() != 0,
            old.is_vacant(),
    {
        proof {
            use_type_invariant(self);
        }
        let (ptr, Tracked(points_to), Tracked(dealloc)) = frac_ptr::epoch_alloc(v);
        let tracked frac = Frac::new(points_to);
        atomic_with_ghost!(&self.gate => store(ptr); ghost g => {
            g = SlotState::Occupied { frac, dealloc };
        });
    }

    // Peels off half of the currently-installed occupant's accumulator, if any, together with
    // the physical pointer it currently gates (captured in the *same* atomic operation, so
    // they're guaranteed consistent -- the share's `resource().ptr()` matches the returned
    // pointer). `None` if the slot is vacant -- callers relying on "this slot is definitely
    // occupied right now" must establish that externally (e.g. the `EpochAtomicPtr` invariant
    // that its current index always names an occupied slot).
    pub fn split_share(&self) -> (result: (*mut T, Tracked<Option<Frac<PointsTo<T>>>>))
        ensures
            result.0.addr() != 0 ==> result.1@ is Some,
            result.1@ is Some ==> {
                &&& result.1@->Some_0.resource().ptr() == result.0
                &&& result.1@->Some_0.resource().is_init()
            },
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut share_out: Option<Frac<PointsTo<T>>> = None;
        let ptr =
            atomic_with_ghost!(&self.gate => load(); ghost g => {
            g = match g {
                SlotState::Vacant => SlotState::Vacant,
                SlotState::Occupied { frac: mut frac, dealloc } => {
                    share_out = Some(frac.split());
                    SlotState::Occupied { frac, dealloc }
                },
            };
        });
        (ptr, Tracked(share_out))
    }

    // Merges a previously-split share back in, *if* the slot is still occupied by the same
    // resource the share came from (same `Frac` location) -- true by construction as long as
    // the caller only ever returns a share to the slot it was split from, before that slot has
    // been reinstalled with something else in between (the collector's `ReaderSlot`-quiescence
    // reasoning is what guarantees that in practice -- see `EpochAtomicPtr`'s module docs).
    //
    // No trust escape needed: rather than *assuming* the slot is still occupied by a
    // matching-id resource, this makes both "shouldn't happen" cases (reinstalled with a
    // different occupant, or already vacated) total, safe fallbacks instead of assumed-away
    // branches. In either case `share` is simply dropped without being combined back -- at
    // worst this leaks that one fraction forever (the accumulator's `frac()` can never reach 1
    // again for that generation, so it can never be reclaimed) -- a liveness degradation, never
    // a soundness issue, and one that (given correct quiescence-gated retirement) never actually
    // happens.
    pub fn return_share(&self, Tracked(share): Tracked<Frac<PointsTo<T>>>) {
        proof {
            use_type_invariant(self);
        }
        atomic_with_ghost!(&self.gate => load(); ghost g => {
            g = match g {
                SlotState::Occupied { frac: mut frac, dealloc } => {
                    if frac.id() == share.id() {
                        frac.combine(share);
                    }
                    SlotState::Occupied { frac, dealloc }
                },
                SlotState::Vacant => SlotState::Vacant,
            };
        });
    }
}

// Actually frees a fully-drained occupant's backing memory. Only sound once `frac() == 1` --
// i.e. once the collector has established, via `ReaderSlot` quiescence, that every share ever
// split off this occupant has been returned. Takes the `SlotState<T>` obtained from `Slot::take`
// directly, so there's no way to call this without having first taken the slot to `Vacant`.
pub fn reclaim<T>(ptr: *mut T, Tracked(occupant): Tracked<SlotState<T>>) -> (result: T)
    requires
        occupant is Occupied,
        occupant->Occupied_frac.frac() == 1 as real,
        occupant->Occupied_frac.resource().ptr() == ptr,
        occupant->Occupied_frac.resource().is_init(),
        occupant->Occupied_dealloc.addr() == ptr.addr(),
        occupant->Occupied_dealloc.size() == core::mem::size_of::<T>(),
        occupant->Occupied_dealloc.align() == core::mem::align_of::<T>(),
        occupant->Occupied_dealloc.provenance()
            == occupant->Occupied_frac.resource().ptr()@.provenance,
    ensures
        result == occupant->Occupied_frac.resource().value(),
{
    let tracked (frac, dealloc) = match occupant {
        SlotState::Occupied { frac, dealloc } => (frac, dealloc),
        SlotState::Vacant => proof_from_false(),
    };
    let tracked (mut points_to, _empty) = frac.take_resource();
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
