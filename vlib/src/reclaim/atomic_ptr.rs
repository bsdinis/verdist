//! `EpochAtomicPtr<T>`: a fully lock-free "current version" register, reclaimed via a hand-rolled
//! CSL (concurrent separation logic) resource argument -- no locks, no `assume`, no
//! `tokenized_state_machine_vstd!` or other state-machine macro anywhere.
//!
//! Owns a fixed-size (chosen once at `new()`, never resized) pool of `Slot<T>` (each of which owns
//! its own exclusive-claim flag, see `reclaim::slot`), plus an `AtomicUsize` naming which slot is
//! current -- whose own ghost payload carries a witness fragment of *that* slot's `current_gen`
//! (see `Slot`'s module docs), threaded from whichever `write` last installed it, and handed to
//! whichever `write` next displaces it (via `Slot::release`).
//! - Reading (`pin`) takes a plain atomic load and a pre-allocated `Frac` fragment checkout (see
//!   `reclaim::slot`), plus a `ptr_ref2` call outside any invariant (see `reclaim::frac_ptr`'s
//!   module docs for why this needs no new axioms).
//! - Writing (`write`) races other writers via `Slot::try_claim`'s `compare_exchange` to
//!   exclusively own *some* non-current slot -- no shared critical section, no blocking.
//!
//! Reclaim safety, formalized (no `assume`): this follows the hazard-pointer proof technique of
//! Jung et al., *Modular Verification of Safe Memory Reclamation in Concurrent Separation Logic*
//! (OOPSLA 2023) -- split the resource into one fixed fragment per reader *up front* (at
//! `put`/`new_occupied` time, see `Slot`), rather than dynamically per pin. Once every reader's
//! stash cell for a retiring slot is observed to hold its fragment (not checked out), `write`
//! extracts the slot's managed fragment entirely (`Slot::writer_extract_gate`) and drains every
//! reader's cell (`Slot::drain_and_extract`), combining each fragment directly into that now-local
//! managed fragment via `Frac::combine` (already-trusted `vstd` machinery) -- reconstructing
//! `frac() == 1` for real, not assumed. The witness fragment handed back by `Slot::try_claim` is
//! what lets this proof go through without ever comparing `Loc`s at runtime (they have no
//! executable representation) and without assuming anything survives unchanged across the many
//! separate atomic opens this needs: it is an ordinary, locally-held value threaded through
//! `writer_extract_gate` and every `drain_and_extract` call, each of which relates it to the slot's
//! shared `current_gen` resource fresh, via `Frac::agree`, at that exact open. A second, similarly
//! threaded witness (minted by `writer_put`, carried through `current`'s own ghost payload) is
//! what lets `Slot::release` -- called on a slot displaced by some *other* `write` invocation,
//! long after its own claim/reclaim sequence finished -- discharge that slot's own gating clause
//! without needing any assumption either.
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
use vstd::resource::frac::FracGhost;
use vstd::resource::frac_opt::Frac;
use vstd::resource::Loc;

verus! {

pub struct CurrentGenPred;

impl AtomicInvariantPredicate<Seq<Loc>, usize, FracGhost<Loc>> for CurrentGenPred {
    open spec fn atomic_inv(k: Seq<Loc>, v: usize, g: FracGhost<Loc>) -> bool {
        &&& (v as int) < k.len()
        &&& g.id() == k[v as int]
        &&& g.frac() == 1 as real / 2 as real
    }
}

pub struct EpochAtomicPtr<T> {
    // Which slot is the currently-published version. Written only via `swap`, whose returned
    // previous value tells a writer exactly which slot it just displaced. Its ghost payload
    // carries a witness of *that same* slot's `current_gen`, handed over at each swap.
    current: AtomicUsize<Seq<Loc>, FracGhost<Loc>, CurrentGenPred>,
    slots: Vec<Slot<T>>,
}

// A pin token + checked-out fragment: obtained from `EpochAtomicPtr::pin`, consumed by `unpin`.
// Borrowing it (via `get`) to read the published value, then being unable to move it out from
// under that borrow (ordinary Rust aliasing), is what prevents a `SharedReference` into a
// generation's data from outliving the point this reader checks its fragment back in.
pub struct EpochGuard<'a, T> {
    reader_idx: usize,
    slot: &'a Slot<T>,
    ptr: *mut T,
    share: Tracked<Frac<PointsTo<T>>>,
    // Witness fragment of this slot's `cell_gen[reader_idx]`, from `Slot::checkout` -- carried
    // unchanged across the whole pin period and handed back to `Slot::checkin`, which is what
    // lets `checkin` prove `share`'s id still matches the *current* generation without assuming
    // anything survived unchanged in between (see `Slot::checkin`'s doc comment).
    gen_witness: Tracked<FracGhost<Loc>>,
}

impl<'a, T> EpochGuard<'a, T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.share@.resource().ptr() == self.ptr
        &&& self.share@.resource().is_init()
        // Carried across the whole pin period so `unpin` can discharge `Slot::checkin`'s own
        // fraction precondition (the one `SlotBigPred::inv`'s `Present` arm demands).
        &&& self.share@.frac() == 1 as real / (self.slot.num_readers() as real + 1 as real)
        &&& self.ptr.addr() != 0
        &&& (self.reader_idx as nat) < self.slot.num_readers()
        &&& self.gen_witness@.id() == self.slot.cell_gen_id(self.reader_idx as int)
        &&& self.gen_witness@.frac() == 1 as real / 2 as real
        &&& self.share@.id() == self.gen_witness@@
    }

    pub fn get(&self) -> (result: SharedReference<'_, T>) {
        proof {
            use_type_invariant(self);
        }
        frac_ptr::borrow_shared(self.ptr, Tracked(self.share.borrow()))
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
        &&& self.slots@.len() > 0
        &&& self.current.constant().len() == self.slots@.len()
        &&& forall|i: int|
            0 <= i < self.slots@.len() ==> #[trigger] self.slots@[i].num_readers()
                == self.slots@[0].num_readers()
        &&& forall|i: int|
            0 <= i < self.slots@.len() ==> #[trigger] self.current.constant()[i]
                == self.slots@[i].current_gen_id()
    }

    pub closed spec fn num_slots(self) -> nat {
        self.slots@.len()
    }

    pub closed spec fn num_readers(self) -> nat {
        self.slots@[0].num_readers()
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
        let (slot0, Tracked(witness0)) = Slot::new_occupied(v, num_readers);
        slots.push(slot0);
        let mut i: usize = 1;
        while i < num_slots
            invariant
                slots.len() == i,
                1 <= i <= num_slots,
                // `current`'s own `CurrentGenPred` needs `witness0.id() == k[0]`, i.e.
                // `slots@[0].current_gen_id()`. Appending later slots must be shown not to
                // disturb slot 0 -- otherwise `witness0`'s linkage is lost by the time
                // `AtomicUsize::new` checks it.
                slots@[0].current_gen_id() == slot0.current_gen_id(),
                forall|j: int|
                    0 <= j < slots@.len() ==> #[trigger] slots@[j].num_readers() == num_readers,
            decreases num_slots - i,
        {
            slots.push(Slot::new_vacant(num_readers));
            i += 1;
        }
        let ghost k = Seq::new(num_slots as nat, |j: int| slots@[j].current_gen_id());
        let current = AtomicUsize::new(Ghost(k), 0, Tracked(witness0));
        let result = EpochAtomicPtr { current, slots };
        assert(result.inv());
        result
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
        v % self.slots.len()
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
    pub fn write(&self, v: T)
        requires
            core::mem::size_of::<T>() != 0,
    {
        proof {
            use_type_invariant(self);
        }

        // Claim exclusive ownership of some non-current slot, getting back a witness fragment of
        // that slot's `current_gen` (see `Slot::try_claim`'s doc comment).
        let mut claimed_idx: Option<usize> = None;
        let tracked mut witness_opt: Option<FracGhost<Loc>> = None;
        // The witness's *id* linkage to `claimed_idx` has to be recorded by both loops: without
        // it the fact is lost at `unwrap` below, and every later `Slot` call that needs
        // `witness.id() == self.slots@[idx].current_gen_id()` (`writer_extract_gate`,
        // `drain_and_extract`, `writer_put`) becomes unprovable. `self.inv()` likewise has to be
        // restated per loop -- a `use_type_invariant(self)` before the loop does not carry in.
        while claimed_idx.is_none()
            invariant
                self.inv(),
                claimed_idx is Some ==> claimed_idx->0 < self.slots.len(),
                claimed_idx is Some ==> witness_opt is Some,
                claimed_idx is Some ==> witness_opt->0.id()
                    == self.slots@[claimed_idx->0 as int].current_gen_id(),
                claimed_idx is Some ==> witness_opt->0.frac() == 1 as real / 2 as real,
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
                        == self.slots@[claimed_idx->0 as int].current_gen_id(),
                    claimed_idx is Some ==> witness_opt->0.frac() == 1 as real / 2 as real,
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

        let tracked cell_witnesses: Seq<FracGhost<Loc>>;

        // Try the fresh (never-installed) path first: `extract_fresh_cell_gen_witnesses` reads
        // `installed_flag` fresh, in its own single open, and only claims success (`fresh ==
        // true`) when *that exact read* justified extracting every `cell_gen` witness -- so
        // branching on its own returned `fresh` (not a separate, earlier read) is what keeps this
        // sound, with no cross-open persistence assumption linking the two calls.
        let (fresh, Tracked(fresh_witnesses)) = self.slots[idx].extract_fresh_cell_gen_witnesses();
        if fresh {
            // Never installed before: the drain sequence below could never terminate here (no
            // cell has ever been `Present`), so skip it entirely.
            proof {
                cell_witnesses = fresh_witnesses;
                // Restate `writer_put`'s precondition here, in this branch's own terms, rather
                // than relying on the join point below to merge two differently-triggered facts.
                assert(cell_witnesses.len() == self.slots@[idx as int].num_readers());
                assert forall|j: int| 0 <= j < cell_witnesses.len() implies {
                    &&& #[trigger] cell_witnesses[j].id() == self.slots@[idx as int].cell_gen_id(j)
                    &&& cell_witnesses[j].frac() == 1 as real / 2 as real
                } by {
                    assert(fresh_witnesses[j].id() == self.slots@[idx as int].cell_gen_id(j));
                }
            }
        } else {
            proof {
                let tracked _dropped = fresh_witnesses;
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
            // ordinary (tracked) local variable -- sound because `try_claim` gave us exclusive
            // ownership of `idx`, so no other writer can be doing the same concurrently, and no
            // reader ever touches the gate. From here on this is ordinary, single-threaded proof
            // bookkeeping: no more cross-atomic-open reasoning is needed.

            let (ptr, Tracked(o)) = self.slots[idx].writer_extract_gate(Tracked(&witness));
            let tracked mut occupant: SlotState<T> = o;
            // No trust escape for occupancy: `writer_extract_gate`'s postcondition
            // `ptr.addr() != 0 ==> occupant is Occupied` makes this an ordinary executable branch
            // instead of an assumed ghost-shape fact.
            // Drain every reader's stash cell, combining its fragment directly into `occupant` via
            // `Frac::combine` -- ordinary sequential proof code, since `occupant` is now a plain
            // local variable rather than something living inside a shared invariant.
            // `drain_and_extract`'s postcondition ties each extracted piece's id and fraction to
            // `witness`'s wrapped value, which is exactly `occupant`'s own id (from
            // `writer_extract_gate`), so `combine`'s `id()`-equality precondition is a proven fact,
            // not a guess. Retried per-cell (liveness-only, matching `all_returned`'s own spirit)
            // until it succeeds, rather than skipping a still-checked-out cell: `writer_put` needs
            // every cell's `cell_gen` witness handed back, so every cell must actually be drained.
            let n = self.slots[idx].stash_len();
            let mut i: usize = 0;
            let tracked mut cell_witnesses_acc: Seq<FracGhost<Loc>> = Seq::tracked_empty();
            while i < n
                invariant
                    self.inv(),
                    i <= n,
                    idx < self.slots.len(),
                    witness.id() == self.slots@[idx as int].current_gen_id(),
                    n == self.slots@[idx as int].num_readers(),
                    ptr.addr() != 0 ==> occupant is Occupied,
                    ptr.addr() != 0 ==> occupant->Occupied_frac.resource().ptr() == ptr,
                    ptr.addr() != 0 ==> occupant->Occupied_frac.resource().is_init(),
                    ptr.addr() != 0 ==> occupant->Occupied_frac.id() == witness@,
                    ptr.addr() != 0 ==> occupant->Occupied_dealloc.addr() == ptr.addr(),
                    ptr.addr() != 0 ==> occupant->Occupied_dealloc.size() == core::mem::size_of::<
                        T,
                    >(),
                    ptr.addr() != 0 ==> occupant->Occupied_dealloc.align() == core::mem::align_of::<
                        T,
                    >(),
                    ptr.addr() != 0 ==> occupant->Occupied_dealloc.provenance()
                        == occupant->Occupied_frac.resource().ptr()@.provenance,
                    ptr.addr() != 0 ==> occupant->Occupied_frac.frac() == (i as real + 1 as real)
                        / (n as real + 1 as real),
                    cell_witnesses_acc.len() == i,
                    forall|k: int|
                        0 <= k < i ==> {
                            &&& #[trigger] cell_witnesses_acc[k].id()
                                == self.slots@[idx as int].cell_gen_id(k)
                            &&& cell_witnesses_acc[k].frac() == 1 as real / 2 as real
                        },
                decreases n - i,
            {
                let mut drained_ptr: *mut T = core::ptr::null_mut();
                let tracked mut piece_and_cellgen_opt: Option<StashedPiece<T>> = None;
                while drained_ptr.addr() == 0
                    invariant
                        self.inv(),
                        idx < self.slots.len(),
                        i < n,
                        witness.id() == self.slots@[idx as int].current_gen_id(),
                        n == self.slots@[idx as int].num_readers(),
                        drained_ptr.addr() != 0 ==> piece_and_cellgen_opt is Some,
                        // `drain_and_extract`'s postcondition has to be *carried* out of this retry
                        // loop, not just observed inside it -- the code after the loop consumes the
                        // piece and its `cell_gen` witness.
                        piece_and_cellgen_opt is Some ==> {
                            &&& piece_and_cellgen_opt->Some_0.0.resource().ptr() == drained_ptr
                            &&& piece_and_cellgen_opt->Some_0.0.resource().is_init()
                            &&& piece_and_cellgen_opt->Some_0.0.id() == witness@
                            &&& piece_and_cellgen_opt->Some_0.0.frac() == 1 as real / (n as real
                                + 1 as real)
                            &&& piece_and_cellgen_opt->Some_0.1.id()
                                == self.slots@[idx as int].cell_gen_id(i as int)
                            &&& piece_and_cellgen_opt->Some_0.1.frac() == 1 as real / 2 as real
                        },
                {
                    let (dp, Tracked(tracked_opt)) = self.slots[idx].drain_and_extract(
                        i,
                        Tracked(&witness),
                    );
                    if dp.addr() != 0 {
                        drained_ptr = dp;
                        proof {
                            piece_and_cellgen_opt = tracked_opt;
                        }
                    }
                }
                let tracked (piece, cell_gen_witness) = piece_and_cellgen_opt.tracked_unwrap();
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
                        assert(occupant->Occupied_frac.frac() == (i as real + 1 as real + 1 as real)
                            / (n as real + 1 as real)) by (nonlinear_arith)
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
                    broadcast use vstd::seq::group_seq_lemmas;

                    let ghost old_cell_witnesses: Seq<FracGhost<Loc>> = cell_witnesses_acc;
                    // Snapshot before the push: `tracked_push` consumes `cell_gen_witness`, so the
                    // `k == i` case below cannot name it afterwards.
                    let ghost pushed: FracGhost<Loc> = cell_gen_witness;
                    cell_witnesses_acc.tracked_push(cell_gen_witness);
                    assert(cell_witnesses_acc == old_cell_witnesses.push(pushed));
                    assert forall|k: int| 0 <= k < i + 1 implies {
                        &&& #[trigger] cell_witnesses_acc[k].id()
                            == self.slots@[idx as int].cell_gen_id(k)
                        &&& cell_witnesses_acc[k].frac() == 1 as real / 2 as real
                    } by {
                        assert(cell_witnesses_acc[k] == old_cell_witnesses.push(pushed)[k]);
                        if k < i {
                            // Mentions the loop invariant's trigger term, not just the element.
                            assert(old_cell_witnesses[k].id()
                                == self.slots@[idx as int].cell_gen_id(k));
                            assert(old_cell_witnesses.push(pushed)[k] == old_cell_witnesses[k]);
                        } else {
                            assert(old_cell_witnesses.push(pushed)[k] == pushed);
                        }
                    }
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
            proof {
                cell_witnesses = cell_witnesses_acc;
                // Same restatement as the fresh branch above, from the drain loop's own accumulator.
                assert(cell_witnesses.len() == self.slots@[idx as int].num_readers());
                assert forall|j: int| 0 <= j < cell_witnesses.len() implies {
                    &&& #[trigger] cell_witnesses[j].id() == self.slots@[idx as int].cell_gen_id(j)
                    &&& cell_witnesses[j].frac() == 1 as real / 2 as real
                } by {
                    assert(cell_witnesses_acc[j].id() == self.slots@[idx as int].cell_gen_id(j));
                }
            }
        }

        let Tracked(current_witness) = self.slots[idx].writer_put(
            v,
            Tracked(witness),
            Tracked(cell_witnesses),
        );
        // `swap` (not `store`) so we know *exactly* which slot we just displaced, regardless of
        // what other writers concurrently do to `current` -- `store` would risk releasing the
        // claim on the wrong slot if we'd merely re-read `current` afterwards. The ghost payload
        // exchanged here is `current`'s own witness for whichever slot it *was* pointing to --
        // handed straight to that slot's `release` below -- for `idx`'s freshly-minted witness.
        let tracked mut old_witness_opt: Option<FracGhost<Loc>> = None;
        let old_current =
            atomic_with_ghost!(&self.current => swap(idx);
            update prev -> next;
            returning ret;
            ghost g => {
                // `CurrentGenPred::atomic_inv` holds here for the *pre*-swap state, which is
                // exactly what pins the displaced slot's index in range and ties `g`'s id to that
                // slot's own `current_gen`. `release` needs both, and `swap`'s own contract
                // (`ret == prev`) is what carries them out to the exec result.
                assert((ret as int) < self.current.constant().len());
                let tracked mut placeholder = current_witness;
                vstd::modes::tracked_swap(&mut g, &mut placeholder);
                old_witness_opt = Some(placeholder);
                assert(old_witness_opt->Some_0.id() == self.current.constant()[ret as int]);
            });
        let tracked old_witness = old_witness_opt.tracked_unwrap();
        // No `% self.slots.len()` needed here (unlike `current_index`): `CurrentGenPred` pins the
        // stored index in range, and the clause asserted inside the swap above carries that out,
        // so this indexes the displaced slot directly.
        assert(old_current < self.slots.len());
        self.slots[old_current].release(Tracked(old_witness));
    }
}

} // verus!
