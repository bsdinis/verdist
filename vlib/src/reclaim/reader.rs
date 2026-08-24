//! A reader slot for epoch-based reclamation: one per (bounded, statically-known) concurrent
//! reader (e.g. one per shard worker thread), recording only whether that reader is currently
//! pinned -- i.e. potentially holding a reference obtained from an `EpochAtomicPtr` load.
//!
//! Deliberately *not* an epoch-valued slot: the collector doesn't need to know *which* epoch a
//! reader pinned at, only that it has been unpinned at least once since a given retirement. A
//! reader pinned before a retirement will eventually unpin; a reader that pins after a
//! retirement can only ever observe the post-retirement pointer. So "every slot has been seen
//! unpinned since retirement R" is sufficient for R's garbage to be freed -- the classic
//! RCU/EBR quiescent-state argument. That keeps this type a trivial boolean atomic (the same
//! shape as `verdist::service::ShardLoad`, this codebase's existing idiom for "atomic +
//! trivial ghost invariant"), with all of the real bookkeeping (which slots have quiesced since
//! which retirement) living in the collector's own exclusively-owned state, not here.
use vstd::atomic_ghost::atomic_with_ghost;
use vstd::atomic_ghost::AtomicBool;
use vstd::atomic_ghost::AtomicInvariantPredicate;
use vstd::prelude::*;

verus! {

pub struct ReaderSlotPred;

impl AtomicInvariantPredicate<(), bool, ()> for ReaderSlotPred {
    open spec fn atomic_inv(k: (), v: bool, g: ()) -> bool {
        true
    }
}

pub struct ReaderSlot {
    pinned: AtomicBool<(), (), ReaderSlotPred>,
}

impl ReaderSlot {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        self.pinned.well_formed()
    }

    pub fn new() -> (result: Self) {
        let pinned = AtomicBool::new(Ghost(()), false, Tracked(()));
        let result = ReaderSlot { pinned };
        assert(result.inv());
        result
    }

    // Marks this slot as pinned. Must be called before dereferencing anything obtained from
    // an `EpochAtomicPtr` load, and matched with `unpin()` once done.
    pub fn pin(&self) {
        proof {
            use_type_invariant(self);
        }
        atomic_with_ghost!(&self.pinned => store(true); ghost g => {});
    }

    // Marks this slot as unpinned, witnessing (for the collector) that this reader is done
    // with anything it may have loaded while pinned.
    pub fn unpin(&self) {
        proof {
            use_type_invariant(self);
        }
        atomic_with_ghost!(&self.pinned => store(false); ghost g => {});
    }

    // Used only by the collector's scan; not correctness-relevant on its own (it's the
    // *sequence* of observations over time -- "seen false since retirement R" -- that the
    // collector's bookkeeping turns into a safety argument, not any single snapshot read).
    pub fn is_pinned(&self) -> (b: bool) {
        proof {
            use_type_invariant(self);
        }
        atomic_with_ghost!(&self.pinned => load(); ghost g => {})
    }
}

} // verus!
