//! `EpochAtomicPtr<T>`: a fully lock-free "current version" register, reclaimed via a hand-rolled
//! CSL (concurrent separation logic) resource argument -- no locks, no `assume`, no
//! `tokenized_state_machine_vstd!` or other state-machine macro anywhere.
//!
//! Owns a fixed-size (chosen once at `new()`, never resized) pool of `Slot<T>` (each of which owns
//! its own exclusive-claim flag, see `reclaim::slot`), plus an `AtomicUsize` naming which slot is
//! current -- whose own ghost payload carries *that* slot's retirer ledger fragment (see `Slot`'s
//! module docs), threaded from whichever `write` last installed it, and handed to whichever
//! `write` next displaces it (via `Slot::release`).
//! - Reading (`pin`) takes a plain atomic load and a pre-allocated `Frac` fragment checkout (see
//!   `reclaim::slot`), plus a `ptr_ref2` call outside any invariant (see `reclaim::frac_ptr`'s
//!   module docs for why this needs no new axioms).
//! - Writing (`write`) races other writers via `Slot::try_claim`'s `compare_exchange` to
//!   exclusively own *some* non-current slot -- no shared critical section, no blocking.
//!
//! Reclaim safety, formalized (no `assume`): this follows the hazard-pointer proof of Jung et al.,
//! *Modular Verification of Safe Memory Reclamation in Concurrent Separation Logic* (OOPSLA 2023)
//! -- split the value's `Frac<PointsTo<T>>` into one fixed share per reader *up front* (at
//! `writer_put`/`new_occupied` time, see `Slot`), rather than dynamically per pin. Once every
//! reader's stash cell for a retiring slot is observed to hold its share, `write` extracts the
//! slot's managed share (`Slot::writer_extract_gate`) and drains every reader's cell
//! (`Slot::drain_and_extract`), combining each share into that now-local managed share via
//! `Frac::combine` (already-trusted `vstd` machinery) -- reconstructing `frac() == 1` for real, not
//! assumed.
//!
//! What makes that proof go through across the *many separate atomic opens* the sequence needs --
//! without ever comparing `Loc`s at runtime (they have no executable representation) and without
//! assuming anything survives unchanged between opens -- is the slot's ledger (see `Slot`'s module
//! docs): a `GhostMapAuth` keyed by `-1` (the retirer, the paper's `★`) plus one key per reader.
//! `Slot::try_claim` hands back the retirer's ledger fragment; `write` holds it as an ordinary
//! local across the whole sequence, and each `Slot` call it passes it to re-derives the current
//! generation from it *freshly*, by `agree` against the authority at that exact open. A second
//! fragment -- the one `writer_put` mints and `current`'s own ghost payload carries -- is what lets
//! `Slot::release`, called on a slot displaced by some *other* `write` invocation long after its
//! own reclaim finished, discharge that slot's claim clause with no assumption either.
use crate::reclaim::frac_ptr;
use crate::reclaim::slot::Slot;
#[allow(unused_imports)]
use crate::reclaim::slot::SlotState;
#[allow(unused_imports)]
use crate::reclaim::slot::StashedPiece;

use vstd::atomic_ghost::atomic_with_ghost;
use vstd::atomic_ghost::AtomicInvariantPredicate;
use vstd::atomic_ghost::AtomicUsize;
use vstd::prelude::*;
use vstd::raw_ptr::PointsTo;
use vstd::raw_ptr::SharedReference;
use vstd::resource::frac_opt::Frac;
use vstd::resource::map::GhostPointsTo;
use vstd::resource::map::GhostSubmap;
use vstd::resource::Loc;

verus! {

// `current`'s stored `usize` is *packed*: the low 20 bits are the slot index, everything above
// that is a sequence number bumped on every successful publish, by either `write` or
// `try_write`. Its only job is ABA-avoidance for `try_write`'s conditional publish: a slot can
// be reclaimed and reused by a completely different generation, so a compare_exchange gated on
// the bare index alone could be fooled by `current` cycling back to the same index between a
// reader's observation and its own publish attempt. Packing a monotonic nonce alongside the
// index closes that window with a single CAS instruction, without needing two atomics
// compared-and-swapped as if they were one.
//
// This is a plain engineering/liveness concern, not a formally-verified one: neither `write` nor
// `try_write` make any linearizability claim in their specs (only the memory-safety ones this
// whole module is about), so the sequence number's own wraparound is not a soundness question.
// It is also not a practical one: colliding would need another writer to complete exactly
// `INDEX_SPACE`-many further publishes and land back on this exact packed value, all within the
// wall-clock span of one `try_write` attempt. Using a plain bit-shift to place the sequence
// (rather than an overflow-freedom precondition on it) is deliberate -- that precondition could
// never be discharged forever for an unconditionally-incrementing counter, exactly the problem
// `reclaim::epoch`'s own module docs flag and defer for the same reason. A shift, unlike `+`/`*`,
// has no such precondition to begin with: bits shifted past the top of the word are simply gone,
// by definition, for any `seq`.
pub const INDEX_SPACE: usize = 1 << 20;

pub open spec fn spec_unpack_index(packed: usize) -> usize {
    packed & 0xfffffusize
}

// Packs `idx` into the low 20 bits and `seq` into the rest via a plain shift-and-or -- no
// overflow-freedom precondition on `seq` (see module docs above). `idx < INDEX_SPACE` is exactly
// what keeps `idx` from spilling into the bits `seq` occupies, which is the whole of what this
// lemma checks, via Verus's native bit-vector decision procedure rather than any numeric fact
// about `usize::MAX`.
fn pack_current(seq: usize, idx: usize) -> (result: usize)
    requires
        idx < INDEX_SPACE,
    ensures
        spec_unpack_index(result) == idx,
{
    let packed = (seq << 20) | idx;
    assert(INDEX_SPACE == 0x100000usize) by (compute);
    assert(((seq << 20) | idx) & 0xfffffusize == idx) by (bit_vector)
        requires
            idx < 0x100000usize,
    ;
    packed
}

fn unpack_index_exec(packed: usize) -> (result: usize)
    ensures
        result == spec_unpack_index(packed),
{
    packed & 0xfffffusize
}

pub struct CurrentGenPred;

impl AtomicInvariantPredicate<Seq<Loc>, usize, GhostPointsTo<int, Loc>> for CurrentGenPred {
    open spec fn atomic_inv(k: Seq<Loc>, v: usize, g: GhostPointsTo<int, Loc>) -> bool {
        &&& (spec_unpack_index(v) as int) < k.len()
        &&& g.id() == k[spec_unpack_index(v) as int]
        &&& g.key() == crate::reclaim::slot::retirer_key()
    }
}

// No ghost payload of its own -- this atomic exists purely to hand out a fresh, monotonically
// bumped nonce per publish (see the packing comment above `INDEX_SPACE`), so its invariant is
// trivially true for every value.
pub struct TrivialPred;

impl AtomicInvariantPredicate<(), usize, ()> for TrivialPred {
    open spec fn atomic_inv(k: (), v: usize, g: ()) -> bool {
        true
    }
}

// `reject_recursive_types(T)`: propagated up from `Slot<T>` (see its own doc comment in
// `reclaim::slot`) -- `T` occurs in `SlotKey<T>`'s `content: spec_fn(T) -> bool` field, embedded
// here transitively via `slots: Vec<Slot<T>>`.
#[verifier::reject_recursive_types(T)]
pub struct EpochAtomicPtr<T> {
    // Which slot is the currently-published version. Written only via `swap`, whose returned
    // previous value tells a writer exactly which slot it just displaced. Its ghost payload
    // carries *that same* slot's retirer ledger fragment, handed over at each swap.
    current: AtomicUsize<Seq<Loc>, GhostPointsTo<int, Loc>, CurrentGenPred>,
    // Source of the monotonic sequence number packed alongside `current`'s slot index -- see the
    // packing comment above `INDEX_SPACE`. Bumped by every successful publish (`write` today,
    // `try_write` later), never read back for anything but that nonce.
    write_seq: AtomicUsize<(), (), TrivialPred>,
    slots: Vec<Slot<T>>,
}

// A pin token + checked-out fragment: obtained from `EpochAtomicPtr::pin`, consumed by `unpin`.
// Borrowing it (via `get`) to read the published value, then being unable to move it out from
// under that borrow (ordinary Rust aliasing), is what prevents a `SharedReference` into a
// generation's data from outliving the point this reader checks its fragment back in.
// `reject_recursive_types(T)`: same propagation as `EpochAtomicPtr<T>` above, via `slot: &'a
// Slot<T>`.
#[verifier::reject_recursive_types(T)]
pub struct EpochGuard<'a, T> {
    reader_idx: usize,
    slot: &'a Slot<T>,
    ptr: *mut T,
    share: Tracked<Frac<PointsTo<T>>>,
    // This reader's ledger fragment, from `Slot::checkout` -- carried unchanged across the whole
    // pin period and handed back to `Slot::checkin`, which is what lets `checkin` prove `share`
    // still belongs to the *current* generation (by agreement against the authority at its own
    // open) without assuming anything survived unchanged in between.
    gen_witness: Tracked<GhostPointsTo<int, Loc>>,
}

impl<'a, T> EpochGuard<'a, T> {
    // No new field: read it off the slot this guard was checked out of -- same idiom as
    // `EpochAtomicPtr::content()`.
    pub closed spec fn content(self) -> spec_fn(T) -> bool {
        self.slot.content()
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.share@.resource().ptr() == self.ptr
        &&& self.share@.resource().is_init()
        // Carried across the whole pin period so `unpin` can discharge `Slot::checkin`'s own
        // fraction precondition (the one `SlotBigPred::inv`'s `Present` arm demands).
        &&& self.share@.frac() == 1 as real / (self.slot.num_readers() as real + 1 as real)
        &&& self.ptr.addr() != 0
        &&& (self.reader_idx as nat) < self.slot.num_readers()
        &&& self.gen_witness@.id() == self.slot.gen_loc()
        &&& self.gen_witness@.key() == self.reader_idx as int
        &&& self.share@.id()
            == self.gen_witness@.value()
        // The published value satisfies the content invariant -- carried through from
        // `Slot::checkout`'s own postcondition (see `reclaim::slot`'s module docs).
        &&& (self.content())(self.share@.resource().value())
    }

    pub fn get(&self) -> (result: SharedReference<'_, T>)
        ensures
            (self.content())(result.value()),
    {
        proof {
            use_type_invariant(self);
        }
        frac_ptr::borrow_shared(self.ptr, Tracked(self.share.borrow()))
    }

    // Sibling of `get()` returning a plain `&T` instead of the opaque `SharedReference` wrapper.
    // `SharedReference`'s own accessors are private to `vstd::raw_ptr`, so `get()` alone gives an
    // external (non-`vstd`) caller no way to actually read the value -- this is what makes an
    // `EpochGuard` usable from ordinary code, verified or not (e.g. a plain benchmark).
    pub fn get_ref(&self) -> (result: &T)
        ensures
            (self.content())(*result),
    {
        proof {
            use_type_invariant(self);
        }
        frac_ptr::borrow_shared_ref(self.ptr, Tracked(self.share.borrow()))
    }

    // `non_shorthand_field_patterns`: the `verus!` macro re-emits this destructuring in
    // `field: field` form, which the plain-Rust lint then flags.
    #[allow(non_shorthand_field_patterns)]
    pub fn unpin(self) {
        proof {
            use_type_invariant(&self);
        }
        let EpochGuard { reader_idx, slot, ptr, share, gen_witness } = self;
        let Tracked(share) = share;
        let Tracked(gen_witness) = gen_witness;
        slot.checkin(reader_idx, ptr, Tracked(share), Tracked(gen_witness));
    }
}

impl<T> EpochAtomicPtr<T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.current.well_formed()
        &&& self.write_seq.well_formed()
        &&& self.slots@.len() > 0
        &&& self.current.constant().len() == self.slots@.len()
        &&& forall|i: int|
            0 <= i < self.slots@.len() ==> #[trigger] self.slots@[i].num_readers()
                == self.slots@[0].num_readers()
        &&& forall|i: int|
            0 <= i < self.slots@.len() ==> #[trigger] self.slots@[i].content()
                == self.slots@[0].content()
        &&& forall|i: int|
            0 <= i < self.slots@.len() ==> #[trigger] self.current.constant()[i]
                == self.slots@[i].gen_loc()
        &&& self.slots@.len() <= INDEX_SPACE
    }

    pub closed spec fn num_slots(self) -> nat {
        self.slots@.len()
    }

    pub closed spec fn num_readers(self) -> nat {
        self.slots@[0].num_readers()
    }

    // No new field: read it off slot 0, with `inv()`'s own agreement clause below keeping every
    // slot in agreement -- exactly parallel to `num_readers()` above.
    pub closed spec fn content(self) -> spec_fn(T) -> bool {
        self.slots@[0].content()
    }

    // `num_slots` bounds how many in-flight (retired-but-not-yet-reclaimed) generations this can
    // tolerate before a write would need to wait for reclaim to catch up -- pick it generously
    // relative to expected write concurrency and reader pin duration. `num_readers` must match
    // the number of distinct reader identities that will ever call `pin`. `content`: every value
    // ever installed here (via `v` now, or `write`/`try_write` later) must satisfy this predicate
    // -- see `reclaim::slot`'s module docs for why it exists.
    pub fn new(
        v: T,
        num_slots: usize,
        num_readers: usize,
        Ghost(content): Ghost<spec_fn(T) -> bool>,
    ) -> (result: Self)
        requires
            num_slots >= 1,
            num_slots <= INDEX_SPACE,
            core::mem::size_of::<T>() != 0,
            content(v),
        ensures
            result.num_readers() == num_readers,
            result.num_slots() == num_slots,
            result.content() == content,
    {
        let mut slots: Vec<Slot<T>> = Vec::new();
        let (slot0, Tracked(witness0)) = Slot::new_occupied(v, num_readers, Ghost(content));
        slots.push(slot0);
        let mut i: usize = 1;
        while i < num_slots
            invariant
                slots.len() == i,
                1 <= i <= num_slots,
                // `current`'s own `CurrentGenPred` needs `witness0.id() == k[0]`, i.e.
                // `slots@[0].gen_loc()`. Appending later slots must be shown not to
                // disturb slot 0 -- otherwise `witness0`'s linkage is lost by the time
                // `AtomicUsize::new` checks it.
                slots@[0].gen_loc() == slot0.gen_loc(),
                slots@[0].content() == content,
                forall|j: int|
                    0 <= j < slots@.len() ==> #[trigger] slots@[j].num_readers() == num_readers,
                forall|j: int| 0 <= j < slots@.len() ==> #[trigger] slots@[j].content() == content,
            decreases num_slots - i,
        {
            slots.push(Slot::new_vacant(num_readers, Ghost(content)));
            i += 1;
        }
        let ghost k = Seq::new(num_slots as nat, |j: int| slots@[j].gen_loc());
        let packed0 = pack_current(0, 0);
        let current = AtomicUsize::new(Ghost(k), packed0, Tracked(witness0));
        let write_seq = AtomicUsize::new(Ghost(()), 0, Tracked(()));
        let result = EpochAtomicPtr { current, write_seq, slots };
        assert(result.inv());
        result
    }

    // Compatibility wrapper for callers that cannot build a `Ghost` value (e.g. a plain, non-Verus
    // benchmark): an unconstrained content invariant, equivalent to `new` before the content
    // invariant existed.
    pub fn new_unconstrained(v: T, num_slots: usize, num_readers: usize) -> (result: Self)
        requires
            num_slots >= 1,
            num_slots <= INDEX_SPACE,
            core::mem::size_of::<T>() != 0,
        ensures
            result.num_readers() == num_readers,
            result.num_slots() == num_slots,
            result.content() == (|_v: T| true),
    {
        Self::new(v, num_slots, num_readers, Ghost(|_v: T| true))
    }

    // Are all readers' stash cells for slot `idx` currently holding their fragment (i.e. none
    // checked out)? Advisory/liveness-gating only, like `Slot::is_occupied` -- the actual
    // `drain` calls in `write`'s reclaim path re-derive this themselves per cell.
    fn all_returned(&self, idx: usize) -> (result: bool)
        requires
            idx < self.slots.len(),
    {
        proof {
            use_type_invariant(self);
        }
        let n = self.slots[idx].stash_len();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                idx < self.slots.len(),
                n == self.slots@[idx as int].num_readers(),
            decreases n - i,
        {
            if !self.slots[idx].stash_has_piece(i) {
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
        unpack_index_exec(v) % self.slots.len()
    }

    // Liveness-only retry, no trust escape: `Slot::checkout`'s postcondition
    // `ptr.addr() != 0 ==> result is Some` means a `None` result is only possible when this
    // reader's cell for the current slot happens to be checked out (or not yet installed) at
    // that exact instant -- which shouldn't happen given each reader only ever holds at most one
    // `EpochGuard` at a time. This loop exists to make that a liveness assumption instead of a
    // safety-relevant one, matching `write`'s own `#[verifier::exec_allows_no_decreases_clause]`
    // reclaim loop below.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn pin(&self, reader_idx: usize) -> (guard: EpochGuard<'_, T>)
        requires
            reader_idx < self.num_readers(),
        ensures
            guard.content() == self.content(),
    {
        proof {
            use_type_invariant(self);
        }
        loop
            invariant
                reader_idx < self.num_readers(),
        {
            let idx = self.current_index();
            proof {
                use_type_invariant(self);
                assert(self.slots@[idx as int].num_readers() == self.slots@[0].num_readers());
                assert(self.slots@[idx as int].content() == self.slots@[0].content());
            }
            let (ptr, Tracked(share_opt)) = self.slots[idx].checkout(reader_idx);
            if ptr.addr() != 0 {
                let tracked (share, gen_witness) = share_opt.tracked_unwrap();
                let guard = EpochGuard {
                    reader_idx,
                    slot: &self.slots[idx],
                    ptr,
                    share: Tracked(share),
                    gen_witness: Tracked(gen_witness),
                };
                assert(guard.inv());
                return guard;
            }
        }
    }

    // Publishes a new value, retiring the previously-current slot. Lock-free: writers never block
    // on each other via any shared critical section -- each one races (via `Slot::try_claim`'s
    // `compare_exchange`) to exclusively own *some* non-current slot, and from that point on
    // touches only the slot(s) and reader-quiescence state it needs, never anyone else's claim.
    //
    // The two spin loops below (claiming a slot, then waiting for quiescence if it needs
    // reclaiming) are intentionally allowed to not terminate (a liveness, not safety, concern):
    // the first only spins if every slot is currently claimed by other writers or is `current`
    // (bounded by how many writers are concurrently active vs. `num_slots`); the second only
    // spins if a reader is pinned forever.
    #[verifier::exec_allows_no_decreases_clause]
    // Makes slot `idx` idle -- any occupant reclaimed, every reader key back in the ledger --
    // and returns those reader keys for the caller to hand to `writer_put` (installing a fresh
    // value) or `release_to_idle` (abandoning a claim without ever installing anything a reader
    // could see). Two call sites, both already holding exactly this shape: `claim_and_install`,
    // evacuating a leftover occupant before installing a new value; and `try_write`'s
    // CAS-failure path, discarding a value it just installed but never published -- since only
    // the `current` slot is ever reachable via `pin`, no real reader could have touched that
    // value, so the drain below always succeeds on its first pass through every cell.
    fn evacuate(&self, idx: usize, Tracked(witness): Tracked<&GhostPointsTo<int, Loc>>) -> (result:
        Tracked<GhostSubmap<int, Loc>>)
        requires
            self.inv(),
            idx < self.slots.len(),
            witness.id() == self.slots@[idx as int].gen_loc(),
            witness.key() == crate::reclaim::slot::retirer_key(),
        ensures
            result@.id() == self.slots@[idx as int].gen_loc(),
            forall|kk: int| #[trigger]
                result@@.contains_key(kk) <==> (0 <= kk < self.slots@[idx as int].num_readers()),
    {
        proof {
            use_type_invariant(self);
        }

        // Try the idle (vacant) path first: `extract_idle_reader_frags` reads `vacant_flag`
        // fresh, in its own single open, and only claims success (`idle == true`) when *that
        // exact read* justified taking every reader key out -- so branching on its own returned
        // `idle` (not a separate, earlier read) is what keeps this sound, with no cross-open
        // persistence assumption linking the two calls. On the not-idle path it hands back an
        // *empty* submap of the same ledger, which is exactly the right seed for the drain loop's
        // accumulator below -- so there is no `Option` to unwrap either way.
        let (idle, Tracked(mut reader_frags)) = self.slots[idx].extract_idle_reader_frags();
        if idle {
            proof {
                assert forall|kk: int| #[trigger]
                    reader_frags@.contains_key(kk) <==> (0 <= kk
                        < self.slots@[idx as int].num_readers()) by {}
            }
            // Vacant (never installed, or already reclaimed to idle): the drain sequence below
            // could never terminate here (no cell has ever been `Present`), so skip it entirely.
            return Tracked(reader_frags);
        }
        // If the claimed slot still holds a previous occupant (it was retired by some earlier
        // writer but not yet reclaimed), wait for every reader's stash cell to hold its fragment
        // (not checked out), then extract and reclaim it.

        if self.slots[idx].is_occupied() {
            // A `while`'s *condition* is checked against the loop invariant alone, so even an
            // empty-bodied spin loop needs `idx`'s bound (and `self.inv()`) restated here --
            // `all_returned`'s own `idx < self.slots.len()` precondition is otherwise unprovable.
            while !self.all_returned(idx)
                invariant
                    self.inv(),
                    idx < self.slots.len(),
            {
            }
        }
        // Extract the managed fragment entirely, out of the shared invariant and into this
        // ordinary (tracked) local variable -- sound because the caller's exclusive claim on
        // `idx` means no other writer can be doing the same concurrently, and no reader ever
        // touches the gate. From here on this is ordinary, single-threaded proof bookkeeping: no
        // more cross-atomic-open reasoning is needed.

        let (ptr, Tracked(o)) = self.slots[idx].writer_extract_gate(Tracked(witness));
        let tracked mut occupant: SlotState<T> = o;
        // No trust escape for occupancy: `writer_extract_gate`'s postcondition
        // `ptr.addr() != 0 ==> occupant is Occupied` makes this an ordinary executable branch
        // instead of an assumed ghost-shape fact.
        // Drain every reader's stash cell, combining its fragment directly into `occupant` via
        // `Frac::combine` -- ordinary sequential proof code, since `occupant` is now a plain
        // local variable rather than something living inside a shared invariant.
        // `drain_and_extract`'s postcondition ties each extracted piece's id to `witness`'s own
        // generation, which is exactly `occupant`'s id (from `writer_extract_gate`), so
        // `combine`'s `id()`-equality precondition is a proven fact, not a guess. Retried
        // per-cell (liveness-only, matching `all_returned`'s own spirit) until it succeeds, rather
        // than skipping a still-checked-out cell: the caller needs every reader key handed back,
        // so every cell must actually be drained.
        let n = self.slots[idx].stash_len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.inv(),
                i <= n,
                idx < self.slots.len(),
                witness.id() == self.slots@[idx as int].gen_loc(),
                witness.key() == crate::reclaim::slot::retirer_key(),
                n == self.slots@[idx as int].num_readers(),
                ptr.addr() != 0 ==> occupant is Occupied,
                ptr.addr() != 0 ==> occupant->Occupied_frac.resource().ptr() == ptr,
                ptr.addr() != 0 ==> occupant->Occupied_frac.resource().is_init(),
                ptr.addr() != 0 ==> occupant->Occupied_frac.id() == witness.value(),
                ptr.addr() != 0 ==> occupant->Occupied_dealloc.addr() == ptr.addr(),
                ptr.addr() != 0 ==> occupant->Occupied_dealloc.size() == core::mem::size_of::<T>(),
                ptr.addr() != 0 ==> occupant->Occupied_dealloc.align() == core::mem::align_of::<
                    T,
                >(),
                ptr.addr() != 0 ==> occupant->Occupied_dealloc.provenance()
                    == occupant->Occupied_frac.resource().ptr()@.provenance,
                ptr.addr() != 0 ==> occupant->Occupied_frac.frac() == (i as real + 1 as real) / (
                n as real + 1 as real),
                // The accumulator is a submap now, so what used to be a per-index `Seq` fact
                // (needing a `tracked_push` trigger dance every iteration) is one domain
                // equation.
                reader_frags.id() == self.slots@[idx as int].gen_loc(),
                forall|kk: int| #[trigger] reader_frags@.contains_key(kk) <==> (0 <= kk < i as int),
            decreases n - i,
        {
            let mut drained_ptr: *mut T = core::ptr::null_mut();
            let tracked mut piece_and_frag_opt: Option<StashedPiece<T>> = None;
            while drained_ptr.addr() == 0
                invariant
                    self.inv(),
                    idx < self.slots.len(),
                    i < n,
                    witness.id() == self.slots@[idx as int].gen_loc(),
                    witness.key() == crate::reclaim::slot::retirer_key(),
                    n == self.slots@[idx as int].num_readers(),
                    drained_ptr.addr() != 0 ==> piece_and_frag_opt is Some,
                    // `drain_and_extract`'s postcondition has to be *carried* out of this retry
                    // loop, not just observed inside it -- the code after the loop consumes the
                    // piece and its ledger fragment.
                    piece_and_frag_opt is Some ==> {
                        &&& piece_and_frag_opt->Some_0.0.resource().ptr() == drained_ptr
                        &&& piece_and_frag_opt->Some_0.0.resource().is_init()
                        &&& piece_and_frag_opt->Some_0.0.id() == witness.value()
                        &&& piece_and_frag_opt->Some_0.0.frac() == 1 as real / (n as real
                            + 1 as real)
                        &&& piece_and_frag_opt->Some_0.1.id() == self.slots@[idx as int].gen_loc()
                        &&& piece_and_frag_opt->Some_0.1.key() == i as int
                    },
            {
                let (dp, Tracked(tracked_opt)) = self.slots[idx].drain_and_extract(
                    i,
                    Tracked(witness),
                );
                if dp.addr() != 0 {
                    drained_ptr = dp;
                    proof {
                        piece_and_frag_opt = tracked_opt;
                    }
                }
            }
            let tracked (piece, gen_frag) = piece_and_frag_opt.tracked_unwrap();
            if ptr.addr() != 0 {
                let ghost piece_frac_val = piece.frac();
                let ghost pre_frac_val = occupant->Occupied_frac.frac();
                let tracked occupant_inner = occupant;
                proof {
                    match occupant_inner {
                        SlotState::Occupied { frac: f, dealloc } => {
                            let tracked mut frac = f;
                            frac.combine(piece);
                            occupant = SlotState::Occupied { frac, dealloc };
                        },
                        SlotState::Vacant => {
                            assert(false);
                            occupant = SlotState::Vacant;
                        },
                    }
                }
                proof {
                    assert(occupant->Occupied_frac.frac() == pre_frac_val + piece_frac_val);
                    assert(occupant->Occupied_frac.frac() == (i as real + 1 as real + 1 as real) / (
                    n as real + 1 as real)) by (nonlinear_arith)
                        requires
                            pre_frac_val == (i as real + 1 as real) / (n as real + 1 as real),
                            piece_frac_val == 1 as real / (n as real + 1 as real),
                            occupant->Occupied_frac.frac() == pre_frac_val + piece_frac_val,
                    ;
                }
            } else {
                proof {
                    let tracked _dropped = piece;
                }
            }
            proof {
                reader_frags.combine_points_to(gen_frag);
                assert forall|kk: int| #[trigger]
                    reader_frags@.contains_key(kk) <==> (0 <= kk < (i + 1) as int) by {}
            }
            i += 1;
        }
        if ptr.addr() != 0 {
            proof {
                assert(occupant->Occupied_frac.frac() == 1 as real) by (nonlinear_arith)
                    requires
                        occupant->Occupied_frac.frac() == (n as real + 1 as real) / (n as real
                            + 1 as real),
                ;
            }
            let _ = crate::reclaim::slot::reclaim(ptr, Tracked(occupant));
        } else {
            proof {
                let tracked _dropped = occupant;
            }
        }
        Tracked(reader_frags)
    }

    // Claims exclusive ownership of a non-current slot, evacuates it, and installs `v` -- the
    // part `write` (unconditional publish) and `try_write` (RMW's claim-a-candidate-slot step,
    // before its own conditional publish attempt) share verbatim. Lock-free: writers never block
    // on each other via any shared critical section -- each one races (via `Slot::try_claim`'s
    // `compare_exchange`) to exclusively own *some* non-current slot, and from that point on
    // touches only the slot(s) and reader-quiescence state it needs, never anyone else's claim.
    //
    // The two spin loops involved (claiming a slot here, then `evacuate`'s own quiescence wait if
    // it needs reclaiming) are intentionally allowed to not terminate (a liveness, not safety,
    // concern): the first only spins if every slot is currently claimed by other writers or is
    // `current` (bounded by how many writers are concurrently active vs. `num_slots`); the second
    // only spins if a reader is pinned forever.
    #[verifier::exec_allows_no_decreases_clause]
    fn claim_and_install(&self, v: T) -> (result: (usize, Tracked<GhostPointsTo<int, Loc>>))
        requires
            self.inv(),
            core::mem::size_of::<T>() != 0,
            self.content()(v),
        ensures
            result.0 < self.slots.len(),
            result.1@.id() == self.slots@[result.0 as int].gen_loc(),
            result.1@.key() == crate::reclaim::slot::retirer_key(),
    {
        proof {
            use_type_invariant(self);
        }

        // Claim exclusive ownership of some non-current slot, getting back that slot's retirer
        // ledger fragment (see `Slot::try_claim`'s doc comment).
        let mut claimed_idx: Option<usize> = None;
        let tracked mut witness_opt: Option<GhostPointsTo<int, Loc>> = None;
        // The fragment's *id* linkage to `claimed_idx` has to be recorded by both loops: without
        // it the fact is lost at `unwrap` below, and every later `Slot` call that needs
        // `witness.id() == self.slots@[idx].gen_loc()` (`evacuate`, `writer_put`) becomes
        // unprovable. `self.inv()` likewise has to be restated per loop -- a
        // `use_type_invariant(self)` before the loop does not carry in.
        while claimed_idx.is_none()
            invariant
                self.inv(),
                claimed_idx is Some ==> claimed_idx->0 < self.slots.len(),
                claimed_idx is Some ==> witness_opt is Some,
                claimed_idx is Some ==> witness_opt->0.id()
                    == self.slots@[claimed_idx->0 as int].gen_loc(),
                claimed_idx is Some ==> witness_opt->0.key() == crate::reclaim::slot::retirer_key(),
        {
            let current_idx = self.current_index();
            let mut n: usize = 0;
            while n < self.slots.len()
                invariant
                    self.inv(),
                    n <= self.slots.len(),
                    claimed_idx is Some ==> claimed_idx->0 < self.slots.len(),
                    claimed_idx is Some ==> witness_opt is Some,
                    claimed_idx is Some ==> witness_opt->0.id()
                        == self.slots@[claimed_idx->0 as int].gen_loc(),
                    claimed_idx is Some ==> witness_opt->0.key()
                        == crate::reclaim::slot::retirer_key(),
                decreases self.slots.len() - n,
            {
                if n != current_idx {
                    let (ok, Tracked(w)) = self.slots[n].try_claim();
                    if ok {
                        claimed_idx = Some(n);
                        proof {
                            witness_opt = w;
                        }
                        break;
                    }
                }
                n += 1;
            }
        }
        let idx = claimed_idx.unwrap();
        let tracked witness = witness_opt.tracked_unwrap();
        let Tracked(reader_frags) = self.evacuate(idx, Tracked(&witness));
        // `self.inv()`'s content-agreement clause carries `self.content()(v)` (this function's
        // own `requires`) over to the specific slot `writer_put` is about to install into.
        proof {
            assert(self.slots@[idx as int].content() == self.slots@[0].content());
        }
        let Tracked(current_witness) = self.slots[idx].writer_put(
            v,
            Tracked(witness),
            Tracked(reader_frags),
        );
        (idx, Tracked(current_witness))
    }

    // Publishes a new value, retiring the previously-current slot unconditionally. See
    // `try_write` for the conditional (RMW) counterpart that shares `claim_and_install` with this.
    pub fn write(&self, v: T)
        requires
            core::mem::size_of::<T>() != 0,
            self.content()(v),
    {
        proof {
            use_type_invariant(self);
        }
        let (idx, Tracked(current_witness)) = self.claim_and_install(v);
        // `swap` (not `store`) so we know *exactly* which slot we just displaced, regardless of
        // what other writers concurrently do to `current` -- `store` would risk releasing the
        // claim on the wrong slot if we'd merely re-read `current` afterwards. The ghost payload
        // exchanged here is `current`'s own witness for whichever slot it *was* pointing to --
        // handed straight to that slot's `release` below -- for `idx`'s freshly-minted witness.
        // Mint a fresh sequence number and pack it with the slot we just installed -- see the
        // packing comment above `INDEX_SPACE`. `idx < self.slots.len() <= INDEX_SPACE`
        // (`self.inv()`) is exactly `pack_current`'s precondition.
        let seq = atomic_with_ghost!(&self.write_seq => fetch_add_wrapping(1); ghost g => {});
        let new_packed = pack_current(seq, idx);
        let tracked mut old_witness_opt: Option<GhostPointsTo<int, Loc>> = None;
        let old_current =
            atomic_with_ghost!(&self.current => swap(new_packed);
            update prev -> next;
            returning ret;
            ghost g => {
                // `CurrentGenPred::atomic_inv` holds here for the *pre*-swap state, which is
                // exactly what pins the displaced slot's index in range and ties `g`'s id to that
                // slot's own ledger. `release` needs both, and `swap`'s own contract
                // (`ret == prev`) is what carries them out to the exec result.
                assert((spec_unpack_index(ret) as int) < self.current.constant().len());
                let tracked mut placeholder = current_witness;
                vstd::modes::tracked_swap(&mut g, &mut placeholder);
                old_witness_opt = Some(placeholder);
                assert(
                    old_witness_opt->Some_0.id()
                        == self.current.constant()[spec_unpack_index(ret) as int]
                );
                assert(old_witness_opt->Some_0.key() == crate::reclaim::slot::retirer_key());
            });
        let tracked old_witness = old_witness_opt.tracked_unwrap();
        let old_idx = unpack_index_exec(old_current);
        // No `% self.slots.len()` needed here (unlike `current_index`): `CurrentGenPred` pins the
        // unpacked index in range, and the clause asserted inside the swap above carries that out,
        // so this indexes the displaced slot directly.
        assert(old_idx < self.slots.len());
        self.slots[old_idx].release(Tracked(old_witness));
    }

    // Sibling of `pin` used internally by `try_write`: same checkout-retry loop, but also hands
    // back the raw *packed* `current` value observed at the exact load that produced the
    // returned guard's generation -- `pin`'s own `current_index` throws that nonce away (it only
    // needs the index, safety-wise), but `try_write`'s conditional publish needs the full packed
    // value to `compare_exchange` against later.
    #[verifier::exec_allows_no_decreases_clause]
    fn pin_for_write(&self, reader_idx: usize) -> (result: (EpochGuard<'_, T>, usize))
        requires
            reader_idx < self.num_readers(),
    {
        proof {
            use_type_invariant(self);
        }
        loop
            invariant
                reader_idx < self.num_readers(),
        {
            proof {
                use_type_invariant(self);
            }
            // One load, not two: deriving both the packed value we'll later CAS against and the
            // index we check out from the *same* read is what makes them describe the same
            // generation -- a separate `current_index()` call here could race a concurrent
            // publish in between.
            let packed = atomic_with_ghost!(&self.current => load(); ghost g => {});
            let idx = unpack_index_exec(packed) % self.slots.len();
            proof {
                use_type_invariant(self);
                assert(self.slots@[idx as int].num_readers() == self.slots@[0].num_readers());
            }
            let (ptr, Tracked(share_opt)) = self.slots[idx].checkout(reader_idx);
            if ptr.addr() != 0 {
                let tracked (share, gen_witness) = share_opt.tracked_unwrap();
                let guard = EpochGuard {
                    reader_idx,
                    slot: &self.slots[idx],
                    ptr,
                    share: Tracked(share),
                    gen_witness: Tracked(gen_witness),
                };
                assert(guard.inv());
                return (guard, packed);
            }
        }
    }

    // Lock-free read-modify-write: pins the current value, asks `f` whether (and what) to
    // publish, and -- if so -- attempts a conditional swap from exactly the generation `f` saw.
    // On a losing race (some other writer published first), abandons the just-prepared candidate
    // slot via `evacuate` + `release_to_idle` (cheap: nothing ever made it reachable via `pin`,
    // so no reader could have touched it, per `evacuate`'s own doc comment) and retries against
    // the new current value. Returns `false` without ever claiming a slot if `f` declines
    // (`None`) on its very first read.
    //
    // No linearizability claim is made here (see the module docs above `INDEX_SPACE`): `f` is an
    // arbitrary closure, and nothing here proves the sequence of published values it produces is
    // any particular protocol's set of legal transitions. That has to come from whatever calls
    // `try_write` (e.g. ABD's own timestamp-ordering proof), the same way `write`'s unconditional
    // publish never claimed anything about *which* value goes in.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn try_write<F: Fn(&T) -> Option<T>>(&self, reader_idx: usize, f: F) -> (result: bool)
        requires
            core::mem::size_of::<T>() != 0,
            reader_idx < self.num_readers(),
            forall|x: &T| f.requires((x,)),
            // Whatever `f` proposes to publish must satisfy the content invariant -- checked once
            // here, rather than at every candidate `f` produces, since `claim_and_install`
            // (transitively `Slot::writer_put`) needs exactly this fact about `v` below.
            forall|x: &T, y: T| f.ensures((x,), Some(y)) ==> self.content()(y),
    {
        proof {
            use_type_invariant(self);
        }
        loop
            invariant
                self.inv(),
                reader_idx < self.num_readers(),
                core::mem::size_of::<T>() != 0,
                forall|x: &T| f.requires((x,)),
                forall|x: &T, y: T| f.ensures((x,), Some(y)) ==> self.content()(y),
        {
            let (guard, observed_packed) = self.pin_for_write(reader_idx);
            let new_value_opt = f(guard.get_ref());
            guard.unpin();
            let v = match new_value_opt {
                Some(v) => v,
                None => {
                    return false;
                },
            };
            proof {
                assert(self.content()(v));
            }

            let (idx, Tracked(current_witness)) = self.claim_and_install(v);
            let seq = atomic_with_ghost!(&self.write_seq => fetch_add_wrapping(1); ghost g => {});
            let new_packed = pack_current(seq, idx);

            let tracked mut old_witness_opt: Option<GhostPointsTo<int, Loc>> = None;
            let tracked mut abandoned_witness_opt: Option<GhostPointsTo<int, Loc>> = None;
            let cas_result =
                atomic_with_ghost!(&self.current => compare_exchange(observed_packed, new_packed);
                update prev -> next;
                returning ret;
                ghost g => {
                    // `current_witness` is retired unconditionally, right here -- rather than
                    // only along the winning branch -- so the compiler sees it consumed exactly
                    // once no matter which way the race goes, instead of a partial move that a
                    // later, separate `match` on `cas_result` could never statically line up
                    // with. `prev == observed_packed` is exactly the "won the race" case
                    // (`compare_exchange`'s own contract): only then does `next` actually become
                    // `new_packed`, so only then may `current_witness` be handed over as `g`'s
                    // new payload; otherwise it's stashed in `abandoned_witness_opt` for the
                    // losing-branch cleanup below. On the losing branch `g` is left untouched --
                    // `next == prev` already re-establishes the invariant with the *old* `g`.
                    let tracked cw = current_witness;
                    if prev == observed_packed {
                        assert((spec_unpack_index(prev) as int) < self.current.constant().len());
                        let tracked mut placeholder = cw;
                        vstd::modes::tracked_swap(&mut g, &mut placeholder);
                        old_witness_opt = Some(placeholder);
                        assert(
                            old_witness_opt->Some_0.id()
                                == self.current.constant()[spec_unpack_index(prev) as int]
                        );
                        assert(
                            old_witness_opt->Some_0.key() == crate::reclaim::slot::retirer_key()
                        );
                    } else {
                        abandoned_witness_opt = Some(cw);
                    }
                });
            match cas_result {
                Result::Ok(old_packed) => {
                    let tracked old_witness = old_witness_opt.tracked_unwrap();
                    // No `% self.slots.len()` needed here (unlike `pin_for_write`'s defensive
                    // indexing): `old_packed == prev` in this branch, and the assert inside the
                    // block above already pins `spec_unpack_index(prev)` in range.
                    let old_idx = unpack_index_exec(old_packed);
                    assert(old_idx < self.slots.len());
                    self.slots[old_idx].release(Tracked(old_witness));
                    return true;
                },
                Result::Err(_) => {
                    // Lost the race: abandon the slot we just prepared -- give its ledger
                    // fragments back and mark it idle again -- and retry against whatever is
                    // current now.
                    let tracked cw = abandoned_witness_opt.tracked_unwrap();
                    let Tracked(reader_frags) = self.evacuate(idx, Tracked(&cw));
                    self.slots[idx].release_to_idle(Tracked(cw), Tracked(reader_frags));
                },
            }
        }
    }
}

} // verus!
