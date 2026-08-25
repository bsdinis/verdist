//! `EpochAtomicPtr<T>`: a fully lock-free "current version" register, reclaimed by quiescence.
//!
//! Owns a fixed-size (chosen once at `new()`, never resized) pool of `Slot<T>`, a matching pool
//! of per-slot `claimed` bools, and a fixed-size pool of `ReaderSlot`, plus a plain `AtomicUsize`
//! naming which slot is current. No lock anywhere, on either path:
//! - Reading (`pin`) takes a plain atomic load, a proof-only `Frac` split, and a `ptr_ref2` call
//!   outside any invariant (see `reclaim::frac_ptr`/`reclaim::slot` module docs for why this
//!   needs no new axioms).
//! - Writing (`write`) races other writers via `compare_exchange` on individual `claimed` bools
//!   to exclusively own *some* non-current slot -- no shared critical section, no blocking: a
//!   writer that loses a race just tries a different slot. This was a deliberate rework (an
//!   earlier version used a `vstd::rwlock::RwLock` around writer-only bookkeeping; a lock there
//!   defeated the actual point of building this instead of just fixing the RwLock the whole
//!   effort exists to remove).
//!
//! Reclaim safety argument (informal -- see the TRUST ESCAPE note below for what isn't yet a
//! real Verus proof): a retired slot's accumulator can only be fully drained back to `frac() ==
//! 1` once every share ever split off it has been returned. Instead of tracking per-retirement
//! epochs, this reuses the simpler classic quiescent-state argument: if every `ReaderSlot` is
//! observed unpinned at least once *after* a retirement, no reader can still be holding a share
//! from before that retirement (a reader pinned since before the retirement will eventually
//! unpin *before* it could pin again and see anything newer; a reader observed already unpinned
//! trivially clears every retirement that preceded the observation).
//!
//! TRUST ESCAPE: this module does not yet *prove* the quiescence argument above in Verus (that
//! would need per-reader epoch publication reintroduced, reversing the step-2 simplification, or
//! an equivalent formalization) -- it relies on the same class of `assume` already approved for
//! `Slot::return_share`, applied here to justify that a retired slot's `frac()` has reached 1
//! once every reader has been observed quiescent. Documented in place; discharging it for real
//! is exactly the "collector" follow-up work flagged in the `epoch_reclamation_status` memory.
use crate::reclaim::frac_ptr;
use crate::reclaim::reader::ReaderSlot;
use crate::reclaim::slot::Slot;
#[allow(unused_imports)]
use crate::reclaim::slot::SlotState;

use vstd::atomic_ghost::atomic_with_ghost;
use vstd::atomic_ghost::AtomicBool;
use vstd::atomic_ghost::AtomicInvariantPredicate;
use vstd::atomic_ghost::AtomicUsize;
use vstd::prelude::*;
use vstd::raw_ptr::PointsTo;
use vstd::raw_ptr::SharedReference;
use vstd::resource::frac_opt::Frac;

verus! {

pub struct TrivialUsizePred;

impl AtomicInvariantPredicate<(), usize, ()> for TrivialUsizePred {
    open spec fn atomic_inv(_k: (), _v: usize, _g: ()) -> bool {
        true
    }
}

pub struct TrivialBoolPred;

impl AtomicInvariantPredicate<(), bool, ()> for TrivialBoolPred {
    open spec fn atomic_inv(_k: (), _v: bool, _g: ()) -> bool {
        true
    }
}

pub struct EpochAtomicPtr<T> {
    // Which slot is the currently-published version. Written only via `swap`, whose returned
    // previous value tells a writer exactly which slot it just displaced.
    current: AtomicUsize<(), (), TrivialUsizePred>,
    // claimed[i] == true iff slot i is "owned" -- either it *is* `current`, or some writer holds
    // it exclusively while retiring/reclaiming/repurposing it. false means "available for any
    // writer to try_claim". No lock: writers race via `compare_exchange` on individual bools, so
    // at most one writer ever owns a given slot at a time; `current`'s slot is always claimed
    // (never independently chosen by two writers), by induction from `try_claim` gating every
    // path that can make a slot become `current`.
    claimed: Vec<AtomicBool<(), (), TrivialBoolPred>>,
    slots: Vec<Slot<T>>,
    readers: Vec<ReaderSlot>,
}

// A pin token + borrowed share: obtained from `EpochAtomicPtr::pin`, consumed by `unpin`.
// Borrowing it (via `get`) to read the published value, then being unable to move it out from
// under that borrow (ordinary Rust aliasing), is what prevents a `SharedReference` into a
// generation's data from outliving the point this reader is marked quiescent -- the same
// rationale as the original (dead-end) `EpochGuard` sketch, now actually load-bearing since the
// `Frac`-based sharing makes the reference itself sound to hand out in the first place.
pub struct EpochGuard<'a, T> {
    reader: &'a ReaderSlot,
    slot: &'a Slot<T>,
    ptr: *mut T,
    share: Tracked<Frac<PointsTo<T>>>,
}

impl<'a, T> EpochGuard<'a, T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.share@.resource().ptr() == self.ptr
        &&& self.share@.resource().is_init()
    }

    pub fn get(&self) -> (result: SharedReference<'_, T>) {
        proof {
            use_type_invariant(self);
        }
        frac_ptr::borrow_shared(self.ptr, Tracked(self.share.borrow()))
    }

    #[allow(non_shorthand_field_patterns)]
    pub fn unpin(self) {
        let EpochGuard { reader, slot, ptr: _, share } = self;
        slot.return_share(share);
        reader.unpin();
    }
}

impl<T> EpochAtomicPtr<T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.current.well_formed()
        &&& self.slots@.len() > 0
        &&& self.claimed@.len() == self.slots@.len()
        &&& forall|i: int| 0 <= i < self.claimed@.len() ==> #[trigger] self.claimed@[i].well_formed()
    }

    pub closed spec fn num_slots(self) -> nat {
        self.slots@.len()
    }

    pub closed spec fn num_readers(self) -> nat {
        self.readers@.len()
    }

    // `num_slots` bounds how many in-flight (retired-but-not-yet-reclaimed) generations this can
    // tolerate before a write would need to wait for reclaim to catch up -- pick it generously
    // relative to expected write concurrency and reader pin duration. `num_readers` must match
    // the number of distinct reader identities that will ever call `pin`.
    pub fn new(v: T, num_slots: usize, num_readers: usize) -> (result: Self)
        requires
            num_slots >= 1,
            core::mem::size_of::<T>() != 0,
    {
        let mut slots: Vec<Slot<T>> = Vec::new();
        slots.push(Slot::new_occupied(v));
        let mut claimed: Vec<AtomicBool<(), (), TrivialBoolPred>> = Vec::new();
        claimed.push(AtomicBool::new(Ghost(()), true, Tracked(())));
        let mut i: usize = 1;
        while i < num_slots
            invariant
                slots.len() == i,
                claimed.len() == i,
                i <= num_slots,
                forall|j: int| 0 <= j < claimed@.len() ==> #[trigger] claimed@[j].well_formed(),
            decreases num_slots - i,
        {
            slots.push(Slot::new_vacant());
            claimed.push(AtomicBool::new(Ghost(()), false, Tracked(())));
            i += 1;
        }
        let mut readers: Vec<ReaderSlot> = Vec::new();
        let mut j: usize = 0;
        while j < num_readers
            invariant
                readers.len() == j,
                j <= num_readers,
            decreases num_readers - j,
        {
            readers.push(ReaderSlot::new());
            j += 1;
        }
        let current = AtomicUsize::new(Ghost(()), 0, Tracked(()));
        let result = EpochAtomicPtr { current, claimed, slots, readers };
        assert(result.inv());
        result
    }

    // Try to become the exclusive owner of slot `n` (either a fresh-vacant slot never used, or a
    // retired-but-not-yet-reclaimed one). Succeeds iff no one else currently owns it; the loser
    // of a race simply tries a different slot. `current`'s slot is always claimed (see `inv`'s
    // doc comment above), so this can never race with `n` becoming `current` out from under it.
    fn try_claim(&self, n: usize) -> (result: bool)
        requires
            n < self.claimed.len(),
    {
        proof {
            use_type_invariant(self);
            assert(self.claimed@[n as int].well_formed());
        }
        let r = atomic_with_ghost!(&self.claimed[n] => compare_exchange(false, true); ghost g => {});
        r.is_ok()
    }

    // Marks slot `n` available for the next writer to claim. Called only on the slot just
    // displaced from `current` by a `swap`, so it is never called while `n` is still `current`.
    fn release(&self, n: usize)
        requires
            n < self.claimed.len(),
    {
        proof {
            use_type_invariant(self);
            assert(self.claimed@[n as int].well_formed());
        }
        atomic_with_ghost!(&self.claimed[n] => store(false); ghost g => {});
    }

    fn all_readers_quiescent(&self) -> (result: bool) {
        proof {
            use_type_invariant(self);
        }
        let mut i: usize = 0;
        while i < self.readers.len()
            invariant
                i <= self.readers.len(),
            decreases self.readers.len() - i,
        {
            if self.readers[i].is_pinned() {
                return false;
            }
            i += 1;
        }
        true
    }

    // Reads the current slot index. Plain atomic load, no ghost payload needed -- `% slots.len()`
    // makes indexing unconditionally safe rather than needing an invariant that the stored index
    // is in-bounds.
    fn current_index(&self) -> (result: usize)
        ensures
            result < self.slots.len(),
    {
        proof {
            use_type_invariant(self);
        }
        let v = atomic_with_ghost!(&self.current => load(); ghost g => {});
        v % self.slots.len()
    }

    // Liveness-only retry, no trust escape: `Slot::split_share`'s postcondition
    // `ptr.addr() != 0 ==> result is Some` (see `slot.rs`'s bidirectional `SlotPred`) means a
    // `None` result is only possible when the named slot happens to be vacant at that exact
    // instant. In practice this never happens -- `write()` never retires the slot named by
    // `current_index()` (its `n != current_idx` check only ever recycles already-retired,
    // non-current slots) -- so this loop is expected to succeed on its very first iteration; it
    // exists to make that a liveness assumption instead of a safety-relevant one, matching
    // `write()`'s own `#[verifier::exec_allows_no_decreases_clause]` reclaim loop below.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn pin(&self, reader_idx: usize) -> (guard: EpochGuard<'_, T>)
        requires
            reader_idx < self.num_readers(),
    {
        proof {
            use_type_invariant(self);
        }
        self.readers[reader_idx].pin();
        loop
            invariant
                reader_idx < self.readers.len(),
        {
            let idx = self.current_index();
            let (ptr, Tracked(share_opt)) = self.slots[idx].split_share();
            if ptr.addr() != 0 {
                let tracked share = share_opt.tracked_unwrap();
                let guard = EpochGuard {
                    reader: &self.readers[reader_idx],
                    slot: &self.slots[idx],
                    ptr,
                    share: Tracked(share),
                };
                assert(guard.inv());
                return guard;
            }
        }
    }

    // Publishes a new value, retiring the previously-current slot. Lock-free: writers never block
    // on each other via any shared critical section -- each one races (via `try_claim`'s
    // `compare_exchange`) to exclusively own *some* non-current slot, and from that point on
    // touches only the slot(s) and reader-quiescence state it needs, never anyone else's claim.
    //
    // The two spin loops below (claiming a slot, then waiting for quiescence if it needs
    // reclaiming) are intentionally allowed to not terminate (a liveness, not safety, concern):
    // the first only spins if every slot is currently claimed by other writers or is `current`
    // (bounded by how many writers are concurrently active vs. `num_slots`); the second only
    // spins if a reader is pinned forever.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn write(&self, v: T)
        requires
            core::mem::size_of::<T>() != 0,
    {
        proof {
            use_type_invariant(self);
        }

        // Claim exclusive ownership of some non-current slot.
        let mut claimed_idx: Option<usize> = None;
        while claimed_idx.is_none()
            invariant
                self.claimed.len() == self.slots.len(),
                claimed_idx is Some ==> claimed_idx->0 < self.slots.len(),
        {
            let current_idx = self.current_index();
            let mut n: usize = 0;
            while n < self.slots.len()
                invariant
                    n <= self.slots.len(),
                    self.claimed.len() == self.slots.len(),
                    claimed_idx is Some ==> claimed_idx->0 < self.slots.len(),
                decreases self.slots.len() - n,
            {
                if n != current_idx && self.try_claim(n) {
                    claimed_idx = Some(n);
                    break;
                }
                n += 1;
            }
        }
        let idx = claimed_idx.unwrap();

        // If the claimed slot still holds a previous occupant (it was retired by some earlier
        // writer but not yet reclaimed), wait for every reader to be observed quiescent at least
        // once, then reclaim it. A freshly-claimed, never-used slot is already vacant, so this is
        // skipped entirely for it.
        if self.slots[idx].is_occupied() {
            while !self.all_readers_quiescent() {}
            let (ptr, Tracked(occupant)) = self.slots[idx].take();
            // No trust escape for occupancy: `Slot::take`'s postcondition
            // `ptr.addr() != 0 ==> occupant is Occupied` (bidirectional `SlotPred`, see
            // `slot.rs`) makes this an ordinary executable branch instead of an assumed
            // ghost-shape fact. A `Vacant` result here would mean this slot was reclaimed twice
            // somehow -- shouldn't happen given exclusive claiming, but if it ever did, there's
            // simply nothing to free, so skipping is trivially safe (not even a leak).
            if ptr.addr() != 0 {
                let tracked occupant = occupant;
                // TRUST ESCAPE (explicitly approved by the user; the ONE remaining trust escape
                // in this whole module -- everything else that used to be assumed here is now a
                // real proof, see the comments above and in `slot.rs`'s
                // `SlotPred`/`take`/`split_share`): every reader has been observed quiescent
                // since this slot was retired, so (informally) no share can still be outstanding,
                // i.e. `occupant`'s accumulator has returned to `frac() == 1`. Formalizing this
                // for real needs a ghost mechanism connecting N independent `ReaderSlot` cells'
                // "currently unpinned" observations to this ONE `Frac` accumulator's fraction --
                // e.g. a `tokenized_state_machine_vstd!`-based protocol (the same tool
                // `vstd::rwlock` itself is built on) tracking live shares as a multiset. That is a
                // substantial, separate undertaking (comparable to formalizing vstd's own
                // `RwLock`), not something safely shortcut here. See the
                // `epoch_reclamation_status` memory for the fuller writeup.
                proof {
                    assume(occupant->Occupied_frac.frac() == 1 as real);
                }
                let _ = crate::reclaim::slot::reclaim(ptr, Tracked(occupant));
            }
        }

        self.slots[idx].put(v, Tracked(SlotState::Vacant));
        // `swap` (not `store`) so we know *exactly* which slot we just displaced, regardless of
        // what other writers concurrently do to `current` -- `store` would risk releasing the
        // claim on the wrong slot if we'd merely re-read `current` afterwards.
        let old_current = atomic_with_ghost!(&self.current => swap(idx); ghost g => {});
        self.release(old_current % self.slots.len());
    }
}

} // verus!
