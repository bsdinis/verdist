//! `EpochAtomicPtr<T>`: a lock-free-for-readers, quiescence-reclaimed "current version" register.
//!
//! Owns a fixed-size (chosen once at `new()`, never resized) pool of `Slot<T>` and a fixed-size
//! pool of `ReaderSlot`, plus a plain `AtomicUsize` naming which slot is current. Reading never
//! blocks on a writer: `pin` takes a plain atomic load, a proof-only `Frac` split, and a
//! `ptr_ref2` call outside any invariant (see `reclaim::frac_ptr`/`reclaim::slot` module docs for
//! why this needs no new axioms). Writing serializes against *other writers only* (never against
//! readers) via a plain `vstd::rwlock::RwLock` guarding just the small, exclusively-writer-owned
//! bookkeeping (which slots are retired and pending reclaim) -- this is a deliberate, pragmatic
//! choice: it doesn't touch the reader path at all, and ABD's actual bottleneck (per the
//! motivating profiling) was reader-vs-writer contention, not writer-vs-writer.
//!
//! Reclaim safety argument (informal -- see the TRUST ESCAPE note below for what isn't yet a
//! real Verus proof): a retired slot's accumulator can only be fully drained back to `frac() ==
//! 1` once every share ever split off it has been returned. Instead of tracking per-retirement
//! epochs, this reuses the simpler classic quiescent-state argument: if every `ReaderSlot` is
//! observed unpinned at least once *after* a retirement, no reader can still be holding a share
//! from before that retirement (a reader pinned since before the retirement will eventually
//! unpin *before* it could pin again and see anything newer; a reader observed already unpinned
//! trivially clears every retirement that preceded the observation). One joint scan over all
//! readers therefore clears *every* currently-pending retirement at once, so `pending` is a
//! plain list rather than needing per-slot per-reader bookkeeping.
//!
//! TRUST ESCAPE: this module does not yet *prove* the quiescence argument above in Verus (that
//! would need per-reader epoch publication reintroduced, reversing the step-2 simplification, or
//! an equivalent formalization) -- it relies on the same class of `assume` already approved for
//! `Slot::return_share`, applied here to justify (a) that `split_share`'s result is always
//! `Some` when `idx` is the current index, and (b) that a retired slot's `frac()` has reached 1
//! once every reader has been observed quiescent. Both are documented in place; discharging them
//! for real is exactly the "collector" follow-up work flagged in the `epoch_reclamation_status`
//! memory.
use crate::reclaim::frac_ptr;
use crate::reclaim::reader::ReaderSlot;
use crate::reclaim::slot::Slot;
#[allow(unused_imports)]
use crate::reclaim::slot::SlotState;

use vstd::atomic_ghost::atomic_with_ghost;
use vstd::atomic_ghost::AtomicInvariantPredicate;
use vstd::atomic_ghost::AtomicUsize;
use vstd::prelude::*;
use vstd::raw_ptr::PointsTo;
use vstd::raw_ptr::SharedReference;
use vstd::resource::frac_opt::Frac;
use vstd::rwlock::RwLock;
use vstd::rwlock::RwLockPredicate;

verus! {

pub struct TrivialUsizePred;

impl AtomicInvariantPredicate<(), usize, ()> for TrivialUsizePred {
    open spec fn atomic_inv(_k: (), _v: usize, _g: ()) -> bool {
        true
    }
}

// Which slots have been swapped out of `current` but not yet confirmed reclaimable. Exclusive to
// the writer path via `write_lock`; never touched by readers.
pub struct PendingRetirements {
    pub indices: Vec<usize>,
}

// Parametrized (not trivial) so that every index ever pushed into `pending.indices` is provably
// in-bounds for `self.slots` -- avoids needing an `assume` at each read site in `write()`'s
// reclaim loop.
pub struct PendingPred {
    pub num_slots: nat,
}

impl RwLockPredicate<PendingRetirements> for PendingPred {
    open spec fn inv(self, v: PendingRetirements) -> bool {
        forall|i: int| 0 <= i < v.indices@.len() ==> #[trigger] v.indices@[i] < self.num_slots
    }
}

pub struct EpochAtomicPtr<T> {
    current: AtomicUsize<(), (), TrivialUsizePred>,
    slots: Vec<Slot<T>>,
    readers: Vec<ReaderSlot>,
    write_lock: RwLock<PendingRetirements, PendingPred>,
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
        &&& self.write_lock.pred().num_slots == self.slots@.len()
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
        let mut i: usize = 1;
        while i < num_slots
            invariant
                slots.len() == i,
                i <= num_slots,
            decreases num_slots - i,
        {
            slots.push(Slot::new_vacant());
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
        let write_lock = RwLock::new(
            PendingRetirements { indices: Vec::new() },
            Ghost(PendingPred { num_slots: slots.len() as nat }),
        );
        let result = EpochAtomicPtr { current, slots, readers, write_lock };
        assert(result.inv());
        result
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

    // Publishes a new value, retiring the previously-current slot. Serializes against other
    // writers (never against readers) via `write_lock`.
    //
    // The spin-retry loop below is intentionally allowed to not terminate (a liveness, not
    // safety, concern -- see its comment): it only fails to make progress if a reader is pinned
    // forever or `num_slots` was chosen too small.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(unused_assignments)]
    pub fn write(&self, v: T)
        requires
            core::mem::size_of::<T>() != 0,
    {
        proof {
            use_type_invariant(self);
        }
        let (mut pending, handle) = self.write_lock.acquire_write();

        // Spin until a free slot turns up. Reclaiming pending retirements only requires every
        // reader to be observed quiescent *once* (see module docs) -- readers pin briefly per
        // request, so in practice this loop runs at most a handful of iterations; it only spins
        // indefinitely in the pathological case of a reader pinned forever, which is a liveness
        // (not safety) concern, and only bites if `num_slots` was chosen too small to begin with.
        let mut idx: usize = 0;
        let mut retired_idx: usize = 0;
        loop
            invariant
                idx < self.slots.len(),
                retired_idx < self.slots.len(),
                self.write_lock.pred().inv(pending),
                self.write_lock.pred().num_slots == self.slots.len(),
        {
            if self.all_readers_quiescent() {
                let mut k: usize = 0;
                while k < pending.indices.len()
                    invariant
                        k <= pending.indices.len(),
                        self.write_lock.pred().inv(pending),
                        self.write_lock.pred().num_slots == self.slots.len(),
                    decreases pending.indices.len() - k,
                {
                    // No trust escape: `self.write_lock.pred().inv(pending)` (from
                    // `PendingPred`, tied to `self.slots.len()` via the type invariant) already
                    // proves every entry of `pending.indices` is in-bounds.
                    let idx = pending.indices[k];
                    let (ptr, Tracked(occupant)) = self.slots[idx].take();
                    // No trust escape for occupancy: `Slot::take`'s postcondition
                    // `ptr.addr() != 0 ==> occupant is Occupied` (bidirectional `SlotPred`, see
                    // `slot.rs`) makes this an ordinary executable branch instead of an assumed
                    // ghost-shape fact. A `Vacant` result here would mean this index was
                    // reclaimed twice somehow -- shouldn't happen given each `pending` entry is
                    // consumed exactly once by this loop, but if it ever did, there's simply
                    // nothing to free, so skipping is trivially safe (not even a leak).
                    if ptr.addr() != 0 {
                        let tracked occupant = occupant;
                        // TRUST ESCAPE (explicitly approved by the user; the ONE remaining
                        // trust escape in this whole module -- everything else that used to be
                        // assumed here is now a real proof, see the comments above and in
                        // `slot.rs`'s `SlotPred`/`take`/`split_share`): every reader has been
                        // observed quiescent since this slot was retired, so (informally) no
                        // share can still be outstanding, i.e. `occupant`'s accumulator has
                        // returned to `frac() == 1`. Formalizing this for real needs a ghost
                        // mechanism connecting N independent `ReaderSlot` cells' "currently
                        // unpinned" observations to this ONE `Frac` accumulator's fraction --
                        // e.g. a `tokenized_state_machine_vstd!`-based protocol (the same tool
                        // `vstd::rwlock` itself is built on) tracking live shares as a
                        // multiset. That is a substantial, separate undertaking (comparable to
                        // formalizing vstd's own `RwLock`), not something safely shortcut here.
                        // See the `epoch_reclamation_status` memory for the fuller writeup.
                        proof {
                            assume(occupant->Occupied_frac.frac() == 1 as real);
                        }
                        let _ = crate::reclaim::slot::reclaim(ptr, Tracked(occupant));
                    }
                    k += 1;
                }
                pending.indices = Vec::new();
            }
            let current_idx = self.current_index();
            let mut chosen: Option<usize> = None;
            let mut n: usize = 0;
            while n < self.slots.len()
                invariant
                    n <= self.slots.len(),
                    chosen is Some ==> chosen->0 < self.slots.len(),
                decreases self.slots.len() - n,
            {
                let mut already_pending = false;
                let mut p: usize = 0;
                while p < pending.indices.len()
                    invariant
                        p <= pending.indices.len(),
                    decreases pending.indices.len() - p,
                {
                    if pending.indices[p] == n {
                        already_pending = true;
                        break;
                    }
                    p += 1;
                }
                if n != current_idx && !already_pending {
                    chosen = Some(n);
                    break;
                }
                n += 1;
            }
            if let Some(i) = chosen {
                idx = i;
                retired_idx = current_idx;
                break;
            }
        }

        self.slots[idx].put(v, Tracked(SlotState::Vacant));
        atomic_with_ghost!(&self.current => store(idx); ghost g => {});
        pending.indices.push(retired_idx);
        assert(self.write_lock.pred().inv(pending)) by {
            assert forall|i: int| 0 <= i < pending.indices@.len() implies #[trigger] pending.indices@[i]
                < self.write_lock.pred().num_slots by {}
        };

        handle.release_write(pending);
    }
}

} // verus!
