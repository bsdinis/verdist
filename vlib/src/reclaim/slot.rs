//! `Slot<T>`: a heap-address-stable, *reusable* holder for a lock-free-published value, together
//! with one pre-split fractional reader fragment per reader (the "stash"), all governed by a
//! single, hand-rolled `AtomicInvariant` spanning the slot's own pointer, every stash cell's
//! pointer, *and* the slot's own exclusive-claim flag (raw `vstd::invariant`/`PAtomicPtr`, not the
//! `atomic_ghost` convenience wrapper, and not any state-machine macro).
//!
//! This follows the CSL "hazard pointer" proof technique of Jung et al., *Modular Verification of
//! Safe Memory Reclamation in Concurrent Separation Logic* (OOPSLA 2023): split the resource into
//! one fixed fragment per reader *once, up front* (at `writer_put`/`new_occupied` time) rather
//! than per-pin.
//!
//! Ghost state:
//!   - `SlotState`: `Vacant`, or `Occupied { frac, dealloc }` where `frac` is the "managed"
//!     remainder kept after splitting off one piece per reader into `stash`.
//!   - `StashSlot`: `Empty`, or `Present(piece)` -- one per reader, tied to the *same* physical
//!     cell (bidirectional: `Empty` iff the physical pointer is null).
//!   - `current_gen: Frac<Loc>` -- a *separate* fractional resource (distinct from any single
//!     reader's or the gate's own `Frac<PointsTo<T>>`) whose wrapped value is the id shared by
//!     whichever generation's pieces are (or were last) installed in `gate`/`stash`. Unlike the
//!     gate's own fraction, `current_gen` is *never* exposed to callers as split fragments handed
//!     out per-reader; it exists purely so `Slot::try_claim` can hand back a *witness* fragment
//!     that `EpochAtomicPtr::write` can hold locally (as an ordinary, non-shared proof value)
//!     across the several separate atomic opens its reclaim sequence needs, using
//!     `Frac::agree` (already-trusted `vstd` machinery) to prove -- fresh, at each open -- that a
//!     drained stash piece's id matches the witness's, with no cross-open persistence assumption.
//!
//! Exclusivity, formalized: `SlotBigPred`'s last two clauses pin `current_gen.frac()` down
//! *exactly* by `claimed`'s own value -- `1` when unclaimed, `1/2` whenever claimed (covering both
//! the reclaim window between `try_claim` and `writer_put`, *and* the "is currently published"
//! window between `writer_put` and `release`, which re-splits and re-combines respectively so the
//! invariant is exactly maintained across both). This is what makes every split/combine sound
//! without needing a separately-threaded exclusivity token: the claim flag *is* the token,
//! spanning the same invariant as the resource it gates, and each transition either splits within
//! the very open where the pre-state (per the invariant) guarantees the needed fraction, or
//! combines a witness whose id is statically tied to this slot via `current_gen_id()`.
use crate::reclaim::frac_ptr;

use vstd::atomic::PAtomicBool;
use vstd::atomic::PAtomicPtr;
use vstd::atomic::PermissionBool;
use vstd::atomic::PermissionPtr;
use vstd::invariant::AtomicInvariant;
use vstd::invariant::InvariantPredicate;
use vstd::open_atomic_invariant;
use vstd::prelude::*;
use vstd::raw_ptr::Dealloc;
use vstd::raw_ptr::PointsTo;
use vstd::resource::frac::FracGhost;
use vstd::resource::frac_opt::Frac;
use vstd::resource::Loc;

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

pub tracked enum StashSlot<T> {
    Empty,
    Present(Frac<PointsTo<T>>),
}

/// What a reader's `checkout` (or the writer's `drain_and_extract`) takes out of a stash cell:
/// the `PointsTo` share itself, plus the `cell_gen` witness fragment that pins *which* generation
/// that share belongs to. The two always travel together -- the witness is what lets `checkin`
/// re-derive the share's generation at its own atomic open, with no cross-open persistence
/// assumption.
pub type StashedPiece<T> = (Frac<PointsTo<T>>, FracGhost<Loc>);

// The invariant's constant: which physical atomics (by id) this instance governs, plus the fixed
// identity of the `current_gen` resource. Fixed forever once the `Slot` is constructed.
pub struct SlotKey {
    pub gate_id: int,
    pub stash_ids: Seq<int>,
    pub claimed_id: int,
    pub current_gen_id: Loc,
    pub cell_gen_ids: Seq<Loc>,
    pub installed_flag_id: int,
}

// The invariant's tracked payload: everything needed to describe the current state of the gate
// atomic, every stash atomic, and the claim flag together.
pub tracked struct SlotBig<T> {
    pub gate_perm: PermissionPtr<T>,
    pub gate_state: SlotState<T>,
    pub stash_perms: Seq<PermissionPtr<T>>,
    pub stash_states: Seq<StashSlot<T>>,
    pub claimed_perm: PermissionBool,
    pub current_gen: FracGhost<Loc>,
    // Per-cell mirror of `current_gen`'s wrapped *value*, touched *only* by `writer_put` (which
    // always updates it together with `current_gen` itself, in the same proof step). Unlike
    // `current_gen`, each `cell_gen[i]`'s own *fraction* is pinned by `stash_states[i]`'s own
    // Empty/Present status -- `1` when Present, `1/2` whenever Empty (covering both a reader's
    // own checkout/checkin window *and* the writer's drain/reinstall window, symmetrically) --
    // which is what lets `checkout`/`checkin` split/combine a real witness fragment (returned to
    // the reader, carried across their whole pin period) instead of needing to assume the value
    // survives unchanged: `checkin`'s `agree()` against this fragment re-derives it fresh, at
    // that exact open, with no cross-open persistence assumption, exactly mirroring how
    // `current_gen`'s own witness works for the writer side.
    pub cell_gen: Seq<FracGhost<Loc>>,
    // Backed by a *real* physical atomic (`Slot::installed_flag`), set once (and forever) `true`
    // by the very first `writer_put` call this slot ever sees, never reset. This is what lets
    // `write()` (exec code) branch on "never installed" directly -- via an ordinary atomic load,
    // not by trying to infer it from ghost state across separate opens. Distinguishes, for an
    // `Empty` cell, "never installed" (every `cell_gen[i]` still at its from-construction
    // `frac() == 1`, no witness anyone could hold) from "installed, currently checked out by a
    // reader or the writer's own drain" (`frac() == 1/2`, matched by a live witness somewhere) --
    // letting `writer_put`'s very first call update every `cell_gen[i]` directly (no witness
    // needed, nobody could ever have split one off yet) while every later call still needs one,
    // exactly like `current_gen`'s own claimed/unclaimed split.
    pub installed_perm: PermissionBool,
}

pub struct SlotBigPred<T> {
    dummy: core::marker::PhantomData<T>,
}

impl<T> InvariantPredicate<SlotKey, SlotBig<T>> for SlotBigPred<T> {
    open spec fn inv(k: SlotKey, big: SlotBig<T>) -> bool {
        &&& big.gate_perm.id() == k.gate_id
        &&& big.stash_perms.len() == k.stash_ids.len()
        &&& big.stash_states.len() == k.stash_ids.len()
        &&& forall|i: int|
            0 <= i < k.stash_ids.len() ==> #[trigger] big.stash_perms[i].id() == k.stash_ids[i]
        &&& big.claimed_perm.id() == k.claimed_id
        &&& big.installed_perm.id() == k.installed_flag_id
        &&& big.current_gen.id() == k.current_gen_id
        &&& (match big.gate_state {
            SlotState::Vacant => big.gate_perm.value().addr() == 0,
            SlotState::Occupied { frac, dealloc } => {
                &&& frac.resource().ptr() == big.gate_perm.value()
                &&& frac.resource().is_init()
                &&& big.gate_perm.value().addr() != 0
                &&& dealloc.addr() == big.gate_perm.value().addr()
                &&& dealloc.size() == core::mem::size_of::<T>()
                &&& dealloc.align() == core::mem::align_of::<T>()
                &&& dealloc.provenance() == frac.resource().ptr()@.provenance
                &&& frac.id() == big.current_gen@
                &&& frac.frac() == 1 as real / (k.stash_ids.len() as real + 1 as real)
            },
        })
        &&& big.cell_gen.len() == k.cell_gen_ids.len()
        &&& (forall|i: int|
            0 <= i < k.cell_gen_ids.len() ==> #[trigger] big.cell_gen[i].id()
                == k.cell_gen_ids[i])
        // Unconditional: `writer_put` keeps every `cell_gen[i]@` and `current_gen@` in lockstep,
        // updating both to the same new value within the *same* atomic open (the gate-store
        // open also runs `combine_update_split_all_cell_gen` there), so there is never a window
        // where this drifts, even mid-reclaim while cells are still `Empty`.
        &&& (forall|i: int|
            0 <= i < big.cell_gen.len() ==> #[trigger] big.cell_gen[i]@ == big.current_gen@)
        &&& (forall|i: int|
            0 <= i < big.stash_states.len() ==> (match #[trigger] big.stash_states[i] {
                StashSlot::Empty => {
                    &&& big.stash_perms[i].value().addr() == 0
                    &&& (if big.installed_perm.value() {
                        big.cell_gen[i].frac() == 1 as real / 2 as real
                    } else {
                        big.cell_gen[i].frac() == 1 as real
                    })
                },
                StashSlot::Present(piece) => {
                    &&& big.stash_perms[i].value().addr() != 0
                    &&& piece.resource().ptr() == big.stash_perms[i].value()
                    &&& piece.resource().is_init()
                    &&& piece.id() == big.cell_gen[i]@
                    &&& piece.frac() == 1 as real / (k.stash_ids.len() as real + 1 as real)
                    &&& big.cell_gen[i].frac() == 1 as real
                },
            }))
        &&& (!big.installed_perm.value() ==> forall|i: int|
            0 <= i < big.stash_states.len() ==> #[trigger] big.stash_states[i] is Empty)
        &&& (big.claimed_perm.value() ==> big.current_gen.frac() == 1 as real / 2 as real)
        &&& (!big.claimed_perm.value() ==> big.current_gen.frac() == 1 as real)
    }
}

// Splits `cell_gen[0..n]` (each required to be at `frac() == 1`, matching `ids`'ith entry as its
// id) down to `1/2`, returning the other `1/2` of each, index-for-index, as a same-shape `Seq`.
// Written recursively -- on `n`, not by structurally consuming `cell_gen` -- so it can be called
// from *inside* a single `open_atomic_invariant!` block (which Verus disallows containing a
// `while`/`loop`) while still using only lemma-backed `Seq` operations: recursing on the *prefix*
// first and `tracked_push`ing (append, not `push_front`/`insert` -- `vstd::seq` has no bundled
// indexing lemmas for those) the newly-split element only *after* the recursive call returns is
// what keeps every witness landing at the same index it came from.
proof fn split_all_cell_gen(
    tracked cell_gen: &mut Seq<FracGhost<Loc>>,
    n: int,
    ids: Seq<Loc>,
) -> (tracked result: Seq<FracGhost<Loc>>)
    requires
        0 <= n <= old(cell_gen).len(),
        forall|k: int|
            0 <= k < n ==> {
                &&& #[trigger] old(cell_gen)[k].id() == ids[k]
                &&& old(cell_gen)[k].frac() == 1 as real
            },
    ensures
        final(cell_gen).len() == old(cell_gen).len(),
        result.len() == n,
        forall|k: int|
            n <= k < old(cell_gen).len() ==> #[trigger] final(cell_gen)[k] == old(cell_gen)[k],
        forall|k: int|
            0 <= k < n ==> {
                &&& #[trigger] final(cell_gen)[k].id() == ids[k]
                &&& final(cell_gen)[k].frac() == 1 as real / 2 as real
                &&& final(cell_gen)[k]@ == old(cell_gen)[k]@
                &&& result[k].id() == ids[k]
                &&& result[k].frac() == 1 as real / 2 as real
                &&& result[k]@ == old(cell_gen)[k]@
            },
    decreases n,
{
    broadcast use vstd::seq::group_seq_lemmas;

    if n == 0 {
        Seq::tracked_empty()
    } else {
        let ghost cell_gen_before: Seq<FracGhost<Loc>> = *cell_gen;
        assert(cell_gen_before == *old(cell_gen));
        let tracked mut rest_result = split_all_cell_gen(cell_gen, n - 1, ids);
        assert(cell_gen[n - 1] == cell_gen_before[n - 1]);
        assert(cell_gen[n - 1].id() == ids[n - 1]);
        assert(cell_gen[n - 1].frac() == 1 as real);
        let tracked cell_gen_ref = cell_gen.tracked_borrow_mut(n - 1);
        let tracked w = cell_gen_ref.split();
        let ghost old_len = rest_result.len();
        let ghost old_rest: Seq<FracGhost<Loc>> = rest_result;
        rest_result.tracked_push(w);
        assert(rest_result == old_rest.push(w));
        assert forall|k: int| 0 <= k < old_len + 1 implies {
            &&& #[trigger] rest_result[k].id() == ids[k]
            &&& rest_result[k].frac() == 1 as real / 2 as real
            &&& rest_result[k]@ == old(cell_gen)[k]@
        } by {
            assert(rest_result[k] == old_rest.push(w)[k]);
            if k < old_len {
                assert(old_rest.push(w)[k] == old_rest[k]);
                assert(cell_gen[k].id() == ids[k]);
            } else {
                assert(old_rest.push(w)[k] == w);
            }
        }
        rest_result
    }
}

// Companion to `split_all_cell_gen`, for the "already installed, being republished" path: given
// a live `1/2` witness for every element of `cell_gen[0..n]` (from a prior drain or from
// `extract_fresh_cell_gen_witnesses`), updates both `cell_gen[i]` and `witnesses[i]` to
// `new_value` in place, using `FracGhost::update_with` (needs *both* halves' fractions to sum to
// exactly `1`, which it then preserves) -- no `combine`/`split`/`remove`/`push` at all, so there
// is no `Seq` restructuring to reason about: every index stays exactly where it started,
// regardless of recursion order. Doing this for every cell in the *same* atomic open as
// `current_gen`'s own `update(new_value)` (see `writer_put`) is what keeps
// `cell_gen[i]@ == current_gen@` unconditionally true at every other open's entry, with no gap
// while cells are still `Empty`. Recursive on `n` (not a `while`/`loop`) because the caller needs
// to call this from *inside* a single `open_atomic_invariant!` block, which Verus disallows
// containing a loop.
proof fn update_all_cell_gen(
    tracked cell_gen: &mut Seq<FracGhost<Loc>>,
    tracked witnesses: &mut Seq<FracGhost<Loc>>,
    n: int,
    new_value: Loc,
)
    requires
        0 <= n <= old(cell_gen).len(),
        n <= old(witnesses).len(),
        forall|k: int|
            0 <= k < n ==> {
                &&& #[trigger] old(cell_gen)[k].id() == old(witnesses)[k].id()
                &&& (old(cell_gen)[k].frac() == 1 as real / 2 as real || old(cell_gen)[k].frac()
                    == 1 as real)
                &&& old(witnesses)[k].frac() == 1 as real / 2 as real
            },
    ensures
        final(cell_gen).len() == old(cell_gen).len(),
        final(witnesses).len() == old(witnesses).len(),
        forall|k: int|
            n <= k < old(cell_gen).len() ==> #[trigger] final(cell_gen)[k] == old(cell_gen)[k],
        forall|k: int|
            n <= k < old(witnesses).len() ==> #[trigger] final(witnesses)[k] == old(witnesses)[k],
        // Deliberately two quantifiers, not one conjoined pair: the caller consumes the
        // `witnesses` half *outside* the `open_atomic_invariant!` block that calls this, where
        // `cell_gen` (living inside the invariant's tracked payload) is out of scope. A single
        // `forall` triggered on `final(cell_gen)[k].id()` leaves the `witnesses` facts
        // uninstantiable there, because the trigger term itself cannot be written.
        forall|k: int|
            0 <= k < n ==> {
                &&& #[trigger] final(cell_gen)[k].id() == old(cell_gen)[k].id()
                &&& final(cell_gen)[k].frac() == 1 as real / 2 as real
                &&& final(cell_gen)[k]@ == new_value
            },
        forall|k: int|
            0 <= k < n ==> {
                &&& #[trigger] final(witnesses)[k].id() == old(witnesses)[k].id()
                &&& final(witnesses)[k].frac() == 1 as real / 2 as real
                &&& final(witnesses)[k]@ == new_value
            },
    decreases n,
{
    broadcast use vstd::seq::group_seq_lemmas;

    if n == 0 {
    } else {
        let ghost cell_gen_before: Seq<FracGhost<Loc>> = *cell_gen;
        let ghost witnesses_before: Seq<FracGhost<Loc>> = *witnesses;
        assert(cell_gen_before == *old(cell_gen));
        assert(witnesses_before == *old(witnesses));
        update_all_cell_gen(cell_gen, witnesses, n - 1, new_value);
        assert(cell_gen[n - 1] == cell_gen_before[n - 1]);
        assert(witnesses[n - 1] == witnesses_before[n - 1]);
        assert(cell_gen[n - 1].id() == witnesses[n - 1].id());
        assert(cell_gen[n - 1].frac() == 1 as real / 2 as real || cell_gen[n - 1].frac()
            == 1 as real);
        assert(witnesses[n - 1].frac() == 1 as real / 2 as real);
        {
            let tracked cell_gen_ref = cell_gen.tracked_borrow_mut(n - 1);
            let tracked witness_ref = witnesses.tracked_borrow(n - 1);
            assert(cell_gen_ref.frac() == 1 as real / 2 as real || cell_gen_ref.frac()
                == 1 as real);
            // `witness_ref` is a live `1/2`-fraction, same-id copy -- were `cell_gen_ref.frac()`
            // currently `1` (the other disjunct), the two would sum past `1`, contradicting
            // `bounded_with`'s own conservation. So it must be `1/2` here -- established, not
            // assumed.
            cell_gen_ref.bounded_with(witness_ref);
            assert(cell_gen_ref.frac() == 1 as real / 2 as real);
        }
        let tracked cell_gen_ref = cell_gen.tracked_borrow_mut(n - 1);
        let tracked witness_ref = witnesses.tracked_borrow_mut(n - 1);
        cell_gen_ref.update_with(witness_ref, new_value);
    }
}

// `dead_code`: `inv` is a ghost field, so it is erased in a plain (non-Verus) build and looks
// unread there -- same reason as `abd::server::register`'s own structs carry this allow.
#[allow(dead_code)]
pub struct Slot<T> {
    gate: PAtomicPtr<T>,
    stash: Vec<PAtomicPtr<T>>,
    claimed: PAtomicBool,
    installed_flag: PAtomicBool,
    inv: Tracked<AtomicInvariant<SlotKey, SlotBig<T>, SlotBigPred<T>>>,
}

impl<T> Slot<T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.inv@.constant().gate_id == self.gate.id()
        &&& self.inv@.constant().stash_ids.len() == self.stash@.len()
        &&& forall|i: int|
            0 <= i < self.stash@.len() ==> #[trigger] self.inv@.constant().stash_ids[i]
                == self.stash@[i].id()
        &&& self.inv@.constant().claimed_id == self.claimed.id()
        &&& self.inv@.constant().installed_flag_id == self.installed_flag.id()
        &&& self.inv@.constant().cell_gen_ids.len() == self.stash@.len()
    }

    pub closed spec fn num_readers(self) -> nat {
        self.stash@.len()
    }

    pub closed spec fn current_gen_id(self) -> Loc {
        self.inv@.constant().current_gen_id
    }

    pub closed spec fn cell_gen_id(self, reader_idx: int) -> Loc {
        self.inv@.constant().cell_gen_ids[reader_idx]
    }

    pub fn new_vacant(num_readers: usize) -> (result: Self)
        ensures
            result.num_readers() == num_readers,
    {
        let (gate, Tracked(gate_perm)) = PAtomicPtr::<T>::new(core::ptr::null_mut());
        let tracked placeholder_gen = Frac::new(());
        let ghost gen0 = placeholder_gen.id();
        let mut stash: Vec<PAtomicPtr<T>> = Vec::new();
        let tracked mut stash_perms: Seq<PermissionPtr<T>> = Seq::tracked_empty();
        let tracked mut stash_states: Seq<StashSlot<T>> = Seq::tracked_empty();
        let tracked mut cell_gen: Seq<FracGhost<Loc>> = Seq::tracked_empty();
        let mut i: usize = 0;
        while i < num_readers
            invariant
        // Needed for `i == num_readers` at exit: the loop condition alone only gives
        // `i >= num_readers`, which is not enough to match the `SlotKey` sequences'
        // `num_readers` lengths against the accumulated `Seq`s' `i` lengths below.

                i <= num_readers,
                stash.len() == i,
                stash_perms.len() == i,
                stash_states.len() == i,
                cell_gen.len() == i,
                forall|j: int|
                    0 <= j < i ==> {
                        &&& #[trigger] stash_perms[j].id() == stash@[j].id()
                        &&& stash_perms[j].value().addr() == 0
                        &&& stash_states[j] is Empty
                        &&& cell_gen[j].frac() == 1 as real
                        &&& cell_gen[j]@ == gen0
                    },
            decreases num_readers - i,
        {
            let ghost old_stash_view: Seq<PAtomicPtr<T>> = stash@;
            let (cell, Tracked(perm)) = PAtomicPtr::<T>::new(core::ptr::null_mut());
            stash.push(cell);
            proof {
                broadcast use vstd::seq::group_seq_lemmas;

                let ghost old_len = stash_perms.len();
                let ghost old_stash_perms: Seq<PermissionPtr<T>> = stash_perms;
                let ghost old_cell_gen: Seq<FracGhost<Loc>> = cell_gen;
                stash_perms.tracked_push(perm);
                stash_states.tracked_push(StashSlot::Empty);
                let tracked this_cell_gen = FracGhost::new(gen0);
                cell_gen.tracked_push(this_cell_gen);
                assert forall|j: int| 0 <= j < old_len + 1 implies {
                    &&& #[trigger] stash_perms[j].id() == stash@[j].id()
                    &&& stash_perms[j].value().addr() == 0
                    &&& stash_states[j] is Empty
                    &&& cell_gen[j].frac() == 1 as real
                    &&& cell_gen[j]@ == gen0
                } by {
                    assert(stash@ == old_stash_view.push(cell));
                    assert(stash_perms == old_stash_perms.push(perm));
                    assert(cell_gen == old_cell_gen.push(this_cell_gen));
                    if j < old_len {
                        assert(stash@[j] == old_stash_view.push(cell)[j]);
                        assert(old_stash_view.push(cell)[j] == old_stash_view[j]);
                        assert(stash_perms[j] == old_stash_perms.push(perm)[j]);
                        assert(old_stash_perms.push(perm)[j] == old_stash_perms[j]);
                        assert(cell_gen[j] == old_cell_gen.push(this_cell_gen)[j]);
                        assert(old_cell_gen.push(this_cell_gen)[j] == old_cell_gen[j]);
                    } else {
                        assert(stash@[j] == old_stash_view.push(cell)[j]);
                        assert(old_stash_view.push(cell)[j] == cell);
                        assert(stash_perms[j] == old_stash_perms.push(perm)[j]);
                        assert(old_stash_perms.push(perm)[j] == perm);
                        assert(cell_gen[j] == old_cell_gen.push(this_cell_gen)[j]);
                        assert(old_cell_gen.push(this_cell_gen)[j] == this_cell_gen);
                    }
                }
            }
            i += 1;
        }
        let (claimed, Tracked(claimed_perm)) = PAtomicBool::new(false);
        let (installed_flag, Tracked(installed_perm)) = PAtomicBool::new(false);
        let tracked current_gen = FracGhost::new(gen0);
        let ghost stash_ids = Seq::new(num_readers as nat, |j: int| stash@[j].id());
        let ghost cell_gen_ids = Seq::new(num_readers as nat, |j: int| cell_gen[j].id());
        let ghost key = SlotKey {
            gate_id: gate.id(),
            stash_ids,
            claimed_id: claimed.id(),
            current_gen_id: current_gen.id(),
            cell_gen_ids,
            installed_flag_id: installed_flag.id(),
        };
        proof {
            broadcast use vstd::seq::group_seq_lemmas;

            assert forall|j: int|
                #![trigger stash_ids[j]]
                0 <= j < stash_ids.len() implies stash_ids[j] == stash@[j].id() by {
                assert(stash_perms[j].id() == stash@[j].id());
            }
            assert forall|j: int| 0 <= j < cell_gen.len() implies #[trigger] cell_gen[j]@
                == gen0 by {
                assert(stash_perms[j].id() == stash@[j].id());
            }
            // Restate each of `SlotBigPred::inv`'s quantified clauses in the shape (and with the
            // trigger) the predicate itself uses. The loop above proves everything in terms of
            // `stash@[j].id()` under a single `stash_perms[j].id()` trigger; the predicate reads
            // it back per-clause against the `SlotKey` sequences.
            assert forall|i: int| 0 <= i < stash_ids.len() implies #[trigger] stash_perms[i].id()
                == stash_ids[i] by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
            assert forall|i: int| 0 <= i < cell_gen_ids.len() implies #[trigger] cell_gen[i].id()
                == cell_gen_ids[i] by {}
            assert forall|i: int| 0 <= i < cell_gen.len() implies #[trigger] cell_gen[i]@
                == current_gen@ by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
            assert forall|i: int| 0 <= i < stash_states.len() implies {
                &&& #[trigger] stash_states[i] is Empty
                &&& stash_perms[i].value().addr() == 0
                &&& cell_gen[i].frac() == 1 as real
            } by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
        }
        let tracked big = SlotBig {
            gate_perm,
            gate_state: SlotState::Vacant,
            stash_perms,
            stash_states,
            claimed_perm,
            current_gen,
            cell_gen,
            installed_perm,
        };
        let tracked inv = AtomicInvariant::new(key, big, 0);
        Slot { gate, stash, claimed, installed_flag, inv: Tracked(inv) }
    }

    // Convenience for the very first install, avoiding an awkward `new_vacant` + `writer_put`
    // dance. Safe to populate everything directly (no atomics-as-such needed) since this runs
    // single-threaded, before any reader/writer could possibly observe this `Slot`.
    // Constructs an already-claimed slot (matching `EpochAtomicPtr`'s invariant that whichever
    // slot is `current` is always claimed) and hands back a witness fragment of its `current_gen`
    // -- the same shape `writer_put` itself hands back -- so the caller (`EpochAtomicPtr::new`)
    // can install it into `current`'s own ghost payload, exactly mirroring how a later `write`
    // threads a fresh witness through `current`'s swap.
    pub fn new_occupied(v: T, num_readers: usize) -> (result: (Self, Tracked<FracGhost<Loc>>))
        requires
            core::mem::size_of::<T>() != 0,
        ensures
            result.0.num_readers() == num_readers,
            result.1@.id() == result.0.current_gen_id(),
            result.1@.frac() == 1 as real / 2 as real,
    {
        let (ptr, Tracked(points_to), Tracked(dealloc)) = frac_ptr::epoch_alloc(v);
        let tracked mut frac = Frac::new(points_to);
        let ghost gen_id = frac.id();
        let ghost piece_frac: real = 1 as real / (num_readers as real + 1 as real);
        let (gate, Tracked(gate_perm)) = PAtomicPtr::<T>::new(ptr);
        let mut stash: Vec<PAtomicPtr<T>> = Vec::new();
        let tracked mut stash_perms: Seq<PermissionPtr<T>> = Seq::tracked_empty();
        let tracked mut stash_states: Seq<StashSlot<T>> = Seq::tracked_empty();
        let tracked mut cell_gen: Seq<FracGhost<Loc>> = Seq::tracked_empty();
        proof {
            assert(piece_frac * (num_readers as real + 1 as real) == 1 as real) by (nonlinear_arith)
                requires
                    piece_frac == 1 as real / (num_readers as real + 1 as real),
            ;
            assert(frac.frac() == 1 as real - (0 as real) * piece_frac) by (nonlinear_arith)
                requires
                    frac.frac() == 1 as real,
            ;
        }
        let mut i: usize = 0;
        while i < num_readers
            invariant
        // As in `new_vacant`: without this, exit only gives `i >= num_readers`, so
        // neither the `SlotKey` length matching nor the post-loop
        // `frac.frac() == 1 - num_readers * piece_frac` step below is provable.

                i <= num_readers,
                stash.len() == i,
                stash_perms.len() == i,
                stash_states.len() == i,
                cell_gen.len() == i,
                frac.resource().ptr() == ptr,
                frac.resource().is_init(),
                frac.id() == gen_id,
                ptr.addr() != 0,
                frac.frac() == 1 as real - (i as real) * piece_frac,
                piece_frac * (num_readers as real + 1 as real) == 1 as real,
                forall|j: int|
                    0 <= j < i ==> {
                        &&& #[trigger] stash_perms[j].id() == stash@[j].id()
                        &&& stash_perms[j].value() == ptr
                        &&& stash_states[j] is Present
                        &&& stash_states[j]->Present_0.resource().ptr() == ptr
                        &&& stash_states[j]->Present_0.resource().is_init()
                        &&& stash_states[j]->Present_0.id() == gen_id
                        &&& stash_states[j]->Present_0.frac() == piece_frac
                        &&& cell_gen[j].frac() == 1 as real
                        &&& cell_gen[j]@ == gen_id
                    },
            decreases num_readers - i,
        {
            proof {
                assert((0 as real) < piece_frac) by (nonlinear_arith)
                    requires
                        piece_frac * (num_readers as real + 1 as real) == 1 as real,
                        (num_readers as real + 1 as real) > 0 as real,
                ;
                assert(piece_frac < frac.frac()) by (nonlinear_arith)
                    requires
                        i < num_readers,
                        piece_frac * (num_readers as real + 1 as real) == 1 as real,
                        piece_frac > 0 as real,
                        frac.frac() == 1 as real - (i as real) * piece_frac,
                ;
            }
            let tracked piece = frac.split_to(piece_frac);
            let ghost old_stash_view: Seq<PAtomicPtr<T>> = stash@;
            let (cell, Tracked(perm)) = PAtomicPtr::<T>::new(ptr);
            stash.push(cell);
            proof {
                broadcast use vstd::seq::group_seq_lemmas;

                let ghost old_len = stash_perms.len();
                let ghost old_stash_perms: Seq<PermissionPtr<T>> = stash_perms;
                let ghost old_stash_states: Seq<StashSlot<T>> = stash_states;
                let ghost old_cell_gen: Seq<FracGhost<Loc>> = cell_gen;
                stash_perms.tracked_push(perm);
                stash_states.tracked_push(StashSlot::Present(piece));
                let tracked this_cell_gen = FracGhost::new(gen_id);
                cell_gen.tracked_push(this_cell_gen);
                assert(frac.frac() == 1 as real - (i as real + 1 as real) * piece_frac)
                    by (nonlinear_arith)
                    requires
                        frac.frac() == (1 as real - (i as real) * piece_frac) - piece_frac,
                ;
                assert(stash@ == old_stash_view.push(cell));
                assert(stash_perms == old_stash_perms.push(perm));
                assert(stash_states == old_stash_states.push(StashSlot::Present(piece)));
                assert(cell_gen == old_cell_gen.push(this_cell_gen));
                assert forall|j: int| 0 <= j < old_len + 1 implies {
                    &&& #[trigger] stash_perms[j].id() == stash@[j].id()
                    &&& stash_perms[j].value() == ptr
                    &&& stash_states[j] is Present
                    &&& stash_states[j]->Present_0.resource().ptr() == ptr
                    &&& stash_states[j]->Present_0.resource().is_init()
                    &&& stash_states[j]->Present_0.id() == gen_id
                    &&& stash_states[j]->Present_0.frac() == piece_frac
                    &&& cell_gen[j].frac() == 1 as real
                    &&& cell_gen[j]@ == gen_id
                } by {
                    if j < old_len {
                        assert(stash@[j] == old_stash_view.push(cell)[j]);
                        assert(old_stash_view.push(cell)[j] == old_stash_view[j]);
                        assert(stash_perms[j] == old_stash_perms.push(perm)[j]);
                        assert(old_stash_perms.push(perm)[j] == old_stash_perms[j]);
                        assert(stash_states[j] == old_stash_states.push(
                            StashSlot::Present(piece),
                        )[j]);
                        assert(old_stash_states.push(StashSlot::Present(piece))[j]
                            == old_stash_states[j]);
                        assert(cell_gen[j] == old_cell_gen.push(this_cell_gen)[j]);
                        assert(old_cell_gen.push(this_cell_gen)[j] == old_cell_gen[j]);
                    } else {
                        assert(stash@[j] == old_stash_view.push(cell)[j]);
                        assert(old_stash_view.push(cell)[j] == cell);
                        assert(stash_perms[j] == old_stash_perms.push(perm)[j]);
                        assert(old_stash_perms.push(perm)[j] == perm);
                        assert(stash_states[j] == old_stash_states.push(
                            StashSlot::Present(piece),
                        )[j]);
                        assert(old_stash_states.push(StashSlot::Present(piece))[j]
                            == StashSlot::Present(piece));
                        assert(cell_gen[j] == old_cell_gen.push(this_cell_gen)[j]);
                        assert(old_cell_gen.push(this_cell_gen)[j] == this_cell_gen);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(frac.frac() == piece_frac) by (nonlinear_arith)
                requires
                    frac.frac() == 1 as real - (num_readers as real) * piece_frac,
                    piece_frac * (num_readers as real + 1 as real) == 1 as real,
            ;
        }
        let (claimed, Tracked(claimed_perm)) = PAtomicBool::new(true);
        let (installed_flag, Tracked(installed_perm)) = PAtomicBool::new(true);
        let tracked mut current_gen = FracGhost::new(gen_id);
        let tracked witness = current_gen.split();
        let ghost stash_ids = Seq::new(num_readers as nat, |j: int| stash@[j].id());
        let ghost cell_gen_ids = Seq::new(num_readers as nat, |j: int| cell_gen[j].id());
        let ghost key = SlotKey {
            gate_id: gate.id(),
            stash_ids,
            claimed_id: claimed.id(),
            current_gen_id: current_gen.id(),
            cell_gen_ids,
            installed_flag_id: installed_flag.id(),
        };
        proof {
            broadcast use vstd::seq::group_seq_lemmas;

            assert forall|j: int|
                #![trigger stash_ids[j]]
                0 <= j < stash_ids.len() implies stash_ids[j] == stash@[j].id() by {
                assert(stash_perms[j].id() == stash@[j].id());
            }
            // Same per-clause restatement as `new_vacant`'s, but for the already-installed shape:
            // every cell `Present`, `claimed`/`installed` both `true`, and `current_gen` already
            // split once (so it sits at `1/2`, matching the `claimed` clause).
            assert forall|i: int| 0 <= i < stash_ids.len() implies #[trigger] stash_perms[i].id()
                == stash_ids[i] by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
            assert forall|i: int| 0 <= i < cell_gen_ids.len() implies #[trigger] cell_gen[i].id()
                == cell_gen_ids[i] by {}
            assert forall|i: int| 0 <= i < cell_gen.len() implies #[trigger] cell_gen[i]@
                == current_gen@ by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
            assert forall|i: int| 0 <= i < stash_states.len() implies {
                &&& #[trigger] stash_states[i] is Present
                &&& stash_perms[i].value().addr() != 0
                &&& stash_states[i]->Present_0.resource().ptr() == stash_perms[i].value()
                &&& stash_states[i]->Present_0.resource().is_init()
                &&& stash_states[i]->Present_0.id() == cell_gen[i]@
                &&& stash_states[i]->Present_0.frac() == piece_frac
                &&& cell_gen[i].frac() == 1 as real
            } by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
        }
        let tracked big = SlotBig {
            gate_perm,
            gate_state: SlotState::Occupied { frac, dealloc },
            stash_perms,
            stash_states,
            claimed_perm,
            current_gen,
            cell_gen,
            installed_perm,
        };
        let tracked inv = AtomicInvariant::new(key, big, 0);
        (Slot { gate, stash, claimed, installed_flag, inv: Tracked(inv) }, Tracked(witness))
    }

    // Cheap, non-mutating peek: is something currently installed?
    pub fn is_occupied(&self) -> (result: bool) {
        proof {
            use_type_invariant(self);
        }
        let ptr;
        open_atomic_invariant!(self.inv.borrow() => big => {
            ptr = self.gate.load(Tracked(&big.gate_perm));
        });
        ptr.addr() != 0
    }

    // Cheap, non-mutating peek: does reader `reader_idx`'s stash cell currently hold its
    // fragment (i.e. is it *not* checked out)? Advisory only.
    pub fn stash_has_piece(&self, reader_idx: usize) -> (result: bool)
        requires
            reader_idx < self.num_readers(),
    {
        proof {
            use_type_invariant(self);
        }
        let cell = &self.stash[reader_idx];
        let ptr;
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = big.stash_perms.tracked_borrow(reader_idx as int);
            ptr = cell.load(Tracked(perm_ref));
        });
        ptr.addr() != 0
    }

    pub fn stash_len(&self) -> (result: usize)
        ensures
            result == self.num_readers(),
    {
        self.stash.len()
    }

    // A reader checks its own pre-allocated piece out, together with a witness fragment of this
    // cell's own `cell_gen[reader_idx]` -- split off *because* the cell being `Present` (checked
    // fresh, right here) guarantees, per the invariant's own clause, that `cell_gen[reader_idx]`
    // was at `frac() == 1` the instant before this open, making the split a real, checked step.
    // The reader must hold onto this witness and hand it back, unmodified, to `checkin` -- it is
    // what lets `checkin` prove the checked-out piece's id still matches the *current* generation
    // without assuming anything survived unchanged in between (see `checkin`'s doc comment).
    // `None` (signaled by a null returned pointer) only if this cell wasn't actually holding a
    // piece (already checked out, or the generation hasn't been installed yet) -- callers retry
    // (liveness only).
    pub fn checkout(&self, reader_idx: usize) -> (result: (
        *mut T,
        Tracked<Option<StashedPiece<T>>>,
    ))
        requires
            reader_idx < self.num_readers(),
        ensures
            result.0.addr() != 0 ==> result.1@ is Some,
            result.1@ is Some ==> {
                &&& result.1@->Some_0.0.resource().ptr() == result.0
                &&& result.1@->Some_0.0.resource().is_init()
                &&& result.1@->Some_0.0.frac() == 1 as real / (self.num_readers() as real
                    + 1 as real)
                &&& result.1@->Some_0.1.id() == self.cell_gen_id(reader_idx as int)
                &&& result.1@->Some_0.1.frac() == 1 as real / 2 as real
                &&& result.1@->Some_0.0.id() == result.1@->Some_0.1@
            },
    {
        proof {
            use_type_invariant(self);
        }
        let cell = &self.stash[reader_idx];
        let null_ptr: *mut T = core::ptr::null_mut();
        let tracked mut out: Option<StashedPiece<T>> = None;
        let ptr;
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = big.stash_perms.tracked_borrow_mut(reader_idx as int);
            ptr = cell.swap(Tracked(perm_ref), null_ptr);
            let tracked state_ref = big.stash_states.tracked_borrow_mut(reader_idx as int);
            let tracked mut placeholder = StashSlot::Empty;
            proof {
                vstd::modes::tracked_swap(state_ref, &mut placeholder);
                match placeholder {
                    StashSlot::Present(piece) => {
                        let tracked cell_gen_ref = big.cell_gen.tracked_borrow_mut(reader_idx as int);
                        let tracked gen_witness = cell_gen_ref.split();
                        out = Some((piece, gen_witness));
                    },
                    StashSlot::Empty => {},
                }
            }
        });
        (ptr, Tracked(out))
    }

    // A reader hands its piece back, together with the witness fragment of `cell_gen[reader_idx]`
    // it got from the matching `checkout`. `checkin` combines that witness back into
    // `cell_gen[reader_idx]` -- restoring `frac() == 1`, established fresh, within this same
    // open, right before installing `Present(piece)`, which is exactly what the invariant's
    // gating clause then needs. No trust escape: the combine's `id()`-equality precondition
    // holds because `gen_witness` is statically tied to this exact cell via `cell_gen_id()`, and
    // the fact that it's still a *live*, unconsumed fragment (not assumed, but a real resource
    // the caller is handing back) is what proves -- via the resource algebra's own conservation,
    // not by assuming anything survived unchanged -- that no `writer_put` could have updated
    // `cell_gen[reader_idx]`'s value in the meantime (that update requires full ownership, which
    // is impossible while this fragment is elsewhere). `ptr` must match the piece's own pointer
    // (always true for a piece obtained from `checkout` and returned unmodified).
    pub fn checkin(
        &self,
        reader_idx: usize,
        ptr: *mut T,
        Tracked(piece): Tracked<Frac<PointsTo<T>>>,
        Tracked(gen_witness): Tracked<FracGhost<Loc>>,
    )
        requires
            reader_idx < self.num_readers(),
            piece.resource().ptr() == ptr,
            piece.resource().is_init(),
            // Exactly the fraction `SlotBigPred::inv`'s `Present` arm demands -- without this the
            // invariant is genuinely unprovable at this block's end, not merely hard to prove.
            // Supplied by `checkout`/`drain_and_extract`'s own postconditions, so callers already
            // have it.
            piece.frac() == 1 as real / (self.num_readers() as real + 1 as real),
            ptr.addr() != 0,
            gen_witness.id() == self.cell_gen_id(reader_idx as int),
            gen_witness.frac() == 1 as real / 2 as real,
            piece.id() == gen_witness@,
    {
        proof {
            use_type_invariant(self);
        }
        let cell = &self.stash[reader_idx];
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = big.stash_perms.tracked_borrow_mut(reader_idx as int);
            cell.store(Tracked(perm_ref), ptr);
            let tracked state_ref = big.stash_states.tracked_borrow_mut(reader_idx as int);
            let tracked mut placeholder = StashSlot::Present(piece);
            proof {
                let tracked cell_gen_ref = big.cell_gen.tracked_borrow_mut(reader_idx as int);
                // `gen_witness` is a live `1/2`-fraction, same-id copy of `cell_gen[reader_idx]`
                // -- were its frac currently `1` (the never-checked-out-again disjunct),
                // the two would sum past `1`, contradicting `bounded_with`'s own soundness. So
                // it must be `1/2` -- established here, not assumed.
                cell_gen_ref.bounded_with(&gen_witness);
                assert(cell_gen_ref.frac() == 1 as real / 2 as real);
                // The invariant's `Empty` clause reads `if installed_perm.value() {1/2} else
                // {1}` for this exact cell (still `Empty`, pre-swap); the `1/2` just derived
                // above rules out the `else` branch, so `installed_perm.value()` must be `true`
                // here -- established, not assumed, and needed to keep the invariant's separate
                // `!installed_perm.value() ==> every cell Empty` clause satisfied once this cell
                // becomes `Present` below.
                assert(big.installed_perm.value());
                cell_gen_ref.combine(gen_witness);
                vstd::modes::tracked_swap(state_ref, &mut placeholder);
            }
        });
    }

    // Tries to become the exclusive claim-holder of this slot. On success, also splits off a
    // small witness fragment of `current_gen` -- sound *unconditionally* within the `r is Ok`
    // branch, because success means the CAS observed `claimed == false`, which (per
    // `SlotBigPred`'s own clause, holding fresh at this exact open) guarantees
    // `current_gen.frac() == 1` right then -- no separate flag or cross-open persistence
    // assumption needed. The witness is handed back so the caller can carry proof of the current
    // generation's id across the many separate opens its reclaim sequence needs (see
    // `drain_and_extract`), and must eventually be handed back via `writer_put`.
    pub fn try_claim(&self) -> (result: (bool, Tracked<Option<FracGhost<Loc>>>))
        ensures
            result.0 ==> result.1@ is Some,
            result.1@ is Some ==> {
                &&& result.1@->Some_0.id() == self.current_gen_id()
                &&& result.1@->Some_0.frac() == 1 as real / 2 as real
            },
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut out: Option<FracGhost<Loc>> = None;
        let r;
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = &mut big.claimed_perm;
            r = self.claimed.compare_exchange(Tracked(perm_ref), false, true);
            proof {
                if r is Ok {
                    let tracked witness = big.current_gen.split();
                    out = Some(witness);
                }
            }
        });
        (r.is_ok(), Tracked(out))
    }

    // Releases the exclusive claim on this slot, allowing a future `try_claim` to succeed. Takes
    // a witness fragment of `current_gen` -- freshly split off by `writer_put` (for a slot that
    // was just claimed and reclaimed) or by `EpochAtomicPtr::new`/a prior `write`'s own
    // `current`-swap (for a slot that was `current`, now being displaced) -- and combines it
    // back, restoring `frac() == 1` fresh, within this same open, right before storing
    // `claimed = false`, which is exactly what the gating clause then needs. No trust escape:
    // the combine's `id()`-equality precondition holds because `witness` is statically tied to
    // this exact slot via `current_gen_id()`, not because anything is assumed to have survived
    // unchanged since it was split off.
    pub fn release(&self, Tracked(witness): Tracked<FracGhost<Loc>>)
        requires
            witness.id() == self.current_gen_id(),
            witness.frac() == 1 as real / 2 as real,
    {
        proof {
            use_type_invariant(self);
        }
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = &mut big.claimed_perm;
            proof {
                // Same reasoning as `writer_put`: `witness` being a live `1/2` fraction of
                // `current_gen` rules out the unclaimed (`frac() == 1`) case via
                // `bounded_with`'s own conservation, so `frac() == 1/2` here is established,
                // not assumed.
                big.current_gen.bounded_with(&witness);
                assert(big.current_gen.frac() == 1 as real / 2 as real);
                big.current_gen.combine(witness);
            }
            self.claimed.store(Tracked(perm_ref), false);
        });
    }

    // Extracts the managed fragment entirely, swapping the gate to `Vacant`. Sound regardless of
    // occupancy (a never-occupied slot is already `Vacant`, so this is a no-op swap). Takes
    // `witness` (the caller's own witness fragment, from `try_claim`) purely to expose, via
    // `Frac::agree` against `current_gen` at this exact open, that the extracted frac's id
    // matches it -- the same relational technique `drain_and_extract` uses.
    pub fn writer_extract_gate(&self, Tracked(witness): Tracked<&FracGhost<Loc>>) -> (result: (
        *mut T,
        Tracked<SlotState<T>>,
    ))
        requires
            witness.id() == self.current_gen_id(),
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
                &&& result.1@->Occupied_frac.id()
                    == witness@
                // The managed remainder's own share, straight from `SlotBigPred::inv`'s
                // `Occupied` arm. The caller's drain loop needs it as the base case of its
                // `frac() == (i+1)/(n+1)` accumulator, so it has to be exposed here.
                &&& result.1@->Occupied_frac.frac() == 1 as real / (self.num_readers() as real
                    + 1 as real)
            },
    {
        proof {
            use_type_invariant(self);
        }
        let null_ptr: *mut T = core::ptr::null_mut();
        let tracked mut out: Option<SlotState<T>> = None;
        let ptr;
        open_atomic_invariant!(self.inv.borrow() => big => {
            ptr = self.gate.swap(Tracked(&mut big.gate_perm), null_ptr);
            let tracked mut placeholder = SlotState::Vacant;
            proof {
                witness.agree(&big.current_gen);
                vstd::modes::tracked_swap(&mut big.gate_state, &mut placeholder);
                out = Some(placeholder);
            }
        });
        (ptr, Tracked(out.tracked_unwrap()))
    }

    // For a slot that has *never* been installed: atomically (via a single `compare_exchange`,
    // false -> true) claims that fact *and* extracts every cell's `cell_gen` witness in the same
    // step -- exactly mirroring how `try_claim`'s own CAS and its `current_gen` split happen
    // together. This pairing is what keeps the invariant satisfied throughout: the moment
    // `installed_perm.value()` flips to `true`, every `cell_gen[i]` must already be at exactly
    // `1/2` (the `Empty` clause's `if installed {1/2} else {1}`), which is precisely what the
    // split, done in the same atomic step, establishes -- not two separate facts that could ever
    // be observed out of sync. The facts justifying the split itself (`!installed_perm.value() ==>
    // every stash_states[i] is Empty` together with the `Empty` clause's `else {1}` branch) are
    // read from `big`'s state as it stood at this open's *start*, before the CAS's own mutation.
    // The returned `bool` is `false` when this slot had already been installed before -- the
    // caller falls back to the ordinary drain sequence in that case (whose witnesses come from
    // `checkin`/`drain_and_extract` instead).
    pub fn extract_fresh_cell_gen_witnesses(&self) -> (result: (bool, Tracked<Seq<FracGhost<Loc>>>))
        ensures
            result.0 ==> result.1@.len() == self.num_readers(),
            result.0 ==> forall|k: int|
                0 <= k < result.1@.len() ==> {
                    &&& #[trigger] result.1@[k].id() == self.cell_gen_id(k)
                    &&& result.1@[k].frac() == 1 as real / 2 as real
                },
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut fresh_witnesses: Seq<FracGhost<Loc>> = Seq::tracked_empty();
        let r;
        open_atomic_invariant!(self.inv.borrow() => big => {
            let ghost ids: Seq<Loc> = Seq::new(self.num_readers(), |k: int| self.cell_gen_id(k));
            let ghost was_installed_before = big.installed_perm.value();
            let ghost cell_gen_before: Seq<FracGhost<Loc>> = big.cell_gen;
            proof {
                broadcast use vstd::seq::group_seq_lemmas;
                // Capture the (already-holding, ambient) unconditional invariant clause about
                // every `cell_gen[i]`'s value, fresh, before anything below mutates `cell_gen` --
                // so it can be chained back to afterward via `cell_gen_before`.
                assert forall|k: int| 0 <= k < big.cell_gen.len() implies
                    #[trigger] big.cell_gen[k]@ == big.current_gen@ by {}
                if !was_installed_before {
                    assert forall|k: int| 0 <= k < big.cell_gen.len() implies {
                        &&& big.cell_gen[k].id() == ids[k]
                        &&& #[trigger] big.cell_gen[k].frac() == 1 as real
                    } by {
                        assert(big.stash_states[k] is Empty);
                    }
                }
            }
            let tracked perm_ref = &mut big.installed_perm;
            r = self.installed_flag.compare_exchange(Tracked(perm_ref), false, true);
            proof {
                if r is Ok {
                    fresh_witnesses = split_all_cell_gen(&mut big.cell_gen, ids.len() as int, ids);
                    assert forall|k: int| 0 <= k < fresh_witnesses.len() implies {
                        &&& #[trigger] fresh_witnesses[k].id() == self.cell_gen_id(k)
                        &&& fresh_witnesses[k].frac() == 1 as real / 2 as real
                    } by {
                        assert(big.cell_gen[k].id() == ids[k]);
                    }
                    assert forall|k: int| 0 <= k < big.cell_gen.len() implies
                        #[trigger] big.cell_gen[k]@ == big.current_gen@ by {
                        assert(big.cell_gen[k].id() == ids[k]);
                        assert(big.cell_gen[k]@ == cell_gen_before[k]@);
                    }
                    assert(big.installed_perm.value());
                    assert forall|k: int| 0 <= k < big.stash_states.len() implies {
                        &&& #[trigger] big.stash_states[k] is Empty
                        &&& big.cell_gen[k].frac() == 1 as real / 2 as real
                    } by {
                        assert(big.cell_gen[k].id() == ids[k]);
                    }
                }
            }
        });
        (r.is_ok(), Tracked(fresh_witnesses))
    }

    // Drains reader `reader_idx`'s stash cell. Returns the drained pointer (non-null iff a piece
    // was found -- executable liveness signal for the caller) together with the piece itself and
    // a witness fragment of `cell_gen[reader_idx]` (split off for exactly the same reason, and by
    // exactly the same reasoning, as `checkout`'s own witness -- this transition also moves
    // `stash_states[reader_idx]` from `Present` to `Empty`, so it must maintain the same gating
    // clause `checkout`/`checkin` rely on). The caller must hand this witness to the matching
    // `writer_put` call, which combines it back. If present, the piece is guaranteed (not
    // assumed) to match `witness`'s wrapped value, via `Frac::agree` against `current_gen`,
    // freshly re-derived at this exact open, chained through the invariant's own
    // `cell_gen[i]@ == current_gen@` clause.
    pub fn drain_and_extract(
        &self,
        reader_idx: usize,
        Tracked(witness): Tracked<&FracGhost<Loc>>,
    ) -> (result: (*mut T, Tracked<Option<StashedPiece<T>>>))
        requires
            reader_idx < self.num_readers(),
            witness.id() == self.current_gen_id(),
        ensures
            result.0.addr() != 0 ==> result.1@ is Some,
            result.1@ is Some ==> {
                &&& result.1@->Some_0.0.resource().ptr() == result.0
                &&& result.1@->Some_0.0.resource().is_init()
                &&& result.1@->Some_0.0.id() == witness@
                &&& result.1@->Some_0.0.frac() == 1 as real / (self.num_readers() as real
                    + 1 as real)
                &&& result.1@->Some_0.1.id() == self.cell_gen_id(reader_idx as int)
                &&& result.1@->Some_0.1.frac() == 1 as real / 2 as real
            },
    {
        proof {
            use_type_invariant(self);
        }
        let cell = &self.stash[reader_idx];
        let null_ptr: *mut T = core::ptr::null_mut();
        let tracked mut out: Option<StashedPiece<T>> = None;
        let ptr;
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = big.stash_perms.tracked_borrow_mut(reader_idx as int);
            ptr = cell.swap(Tracked(perm_ref), null_ptr);
            let tracked state_ref = big.stash_states.tracked_borrow_mut(reader_idx as int);
            let tracked mut placeholder = StashSlot::Empty;
            proof {
                vstd::modes::tracked_swap(state_ref, &mut placeholder);
                witness.agree(&big.current_gen);
                match placeholder {
                    StashSlot::Present(piece) => {
                        let tracked cell_gen_ref = big.cell_gen.tracked_borrow_mut(reader_idx as int);
                        let tracked cell_gen_witness = cell_gen_ref.split();
                        out = Some((piece, cell_gen_witness));
                    },
                    StashSlot::Empty => {},
                }
            }
        });
        (ptr, Tracked(out))
    }

    // Given a live `1/2`-fraction witness for every `cell_gen[0..n]`, derives -- does not
    // assume -- that every one of those cells is currently `Empty` and that this slot is
    // `installed`. Sound because the invariant's `Present` arm always forces `frac() == 1`
    // exactly; a live external `1/2` witness rules that out via `bounded_with`'s own
    // conservation, leaving only `Empty`, whose own `else` branch (the `!installed` disjunct)
    // would *also* force `frac() == 1`, so `installed_perm.value()` must hold too. Must run
    // *before* the caller mutates `cell_gen` (e.g. via `update_all_cell_gen`) -- the invariant
    // this reasoning leans on is only guaranteed to hold at this open's *start*, not
    // mid-mutation. Recursive on `n` (not a `while`/`loop`) because the caller needs to call this
    // from inside a single `open_atomic_invariant!` block, which Verus disallows containing a loop.
    //
    // The `n <= old(big).stash_states.len()` precondition is load-bearing, not defensive: the
    // facts being derived are indexed into `stash_states`, but `n`'s other bound is against
    // `cell_gen.len()`, and only `Slot::inv` (the *type* invariant, not reachable from here --
    // `&self` is ghost-mode in a `proof fn`, so `use_type_invariant` can't be called on it) ties
    // those two lengths together, both to `self.stash@.len()`. Without this clause
    // `big.stash_states[n - 1]` is an out-of-bounds index, so the invariant's per-cell `match`
    // clause has no instantiation whose own `0 <= i < big.stash_states.len()` guard is provable
    // and every derivation below fails -- which Verus reports as `recommendation not met` on the
    // `stash_states[n - 1]` index, *not* as a trigger problem. The caller discharges it from its
    // own `use_type_invariant(self)` plus the ambient `SlotBigPred::inv`.
    proof fn derive_empty_and_installed(
        &self,
        tracked big: &mut SlotBig<T>,
        tracked witnesses: &Seq<FracGhost<Loc>>,
        n: int,
    )
        requires
            SlotBigPred::<T>::inv(self.inv@.constant(), *old(big)),
            0 <= n <= old(big).cell_gen.len(),
            n <= old(big).stash_states.len(),
            n <= witnesses.len(),
            forall|k: int|
                0 <= k < n ==> {
                    &&& #[trigger] old(big).cell_gen[k].id() == witnesses[k].id()
                    &&& witnesses[k].frac() == 1 as real / 2 as real
                },
        ensures
            *final(big) == *old(big),
            forall|k: int| 0 <= k < n ==> #[trigger] final(big).stash_states[k] is Empty,
            n > 0 ==> final(big).installed_perm.value(),
        decreases n,
    {
        if n == 0 {
        } else {
            self.derive_empty_and_installed(big, witnesses, n - 1);
            assert(*big == *old(big));
            assert(SlotBigPred::<T>::inv(self.inv@.constant(), *big));
            assert(big.cell_gen[n - 1].id() == witnesses[n - 1].id());
            // Case-split on the shape (a proof-mode `if`, not just an assertion) is what
            // actually forces the SMT solver to explore the invariant's `Present` arm and
            // notice the contradiction below -- a bare `assert` of the disjunction, without the
            // case split, did not fire the per-cell match clause reliably in earlier attempts.
            if big.stash_states[n - 1] is Present {
                assert(big.cell_gen[n - 1].frac() == 1 as real);
            }
            assert(big.cell_gen[n - 1].frac() == 1 as real / 2 as real || big.cell_gen[n - 1].frac()
                == 1 as real);
            let ghost cell_gen_before: Seq<FracGhost<Loc>> = big.cell_gen;
            let tracked cell_gen_ref = big.cell_gen.tracked_borrow_mut(n - 1);
            let tracked witness_ref = witnesses.tracked_borrow(n - 1);
            cell_gen_ref.bounded_with(witness_ref);
            assert(cell_gen_ref.frac() == 1 as real / 2 as real);
            assert(*cell_gen_ref == cell_gen_before[n - 1]);
            assert(big.cell_gen == cell_gen_before.update(n - 1, *cell_gen_ref));
            assert forall|j: int|
                0 <= j < big.cell_gen.len() implies #[trigger] cell_gen_before.update(
                n - 1,
                *cell_gen_ref,
            )[j] == cell_gen_before[j] by {}
            assert(big.cell_gen =~= cell_gen_before);
            assert(big.cell_gen == cell_gen_before);
            assert(*big == *old(big));
            // Now `cell_gen[n-1].frac() == 1/2` is known exactly (just established above via
            // `bounded_with`). Case-split again: if `Present`, the invariant forces `frac() ==
            // 1`, contradicting the known `1/2` -- so it must be `Empty`.
            if big.stash_states[n - 1] is Present {
                assert(big.cell_gen[n - 1].frac() == 1 as real);
                assert(false);
            }
            assert(big.stash_states[n - 1] is Empty);
            if !big.installed_perm.value() {
                assert(big.cell_gen[n - 1].frac() == 1 as real);
                assert(false);
            }
            assert(big.installed_perm.value());
        }
    }

    // Installs a fresh value, splitting it into one piece per reader, installed directly into
    // the (already-allocated, persistent) `stash` cells. Combines `witness` back into
    // `current_gen` (restoring `frac() == 1`, sound regardless of the claim flag's value since
    // the gating clause only ever *requires* this when unclaimed, never forbids it) and then
    // updates `current_gen`'s wrapped value to the new generation's id, all within the same open
    // as the gate publish -- so the cross-cell id-matching clause holds vacuously (every stash
    // cell is still `Empty` at that point) regardless of the new value.
    // `cell_witnesses`: one `1/2`-fraction witness per reader, from that call's own drain
    // sequence (or, for a slot's very first install, from `extract_fresh_cell_gen_witnesses`).
    pub fn writer_put(
        &self,
        v: T,
        Tracked(witness): Tracked<FracGhost<Loc>>,
        Tracked(cell_witnesses): Tracked<Seq<FracGhost<Loc>>>,
    ) -> (result: Tracked<FracGhost<Loc>>)
        requires
            core::mem::size_of::<T>() != 0,
            witness.id() == self.current_gen_id(),
            witness.frac() == 1 as real / 2 as real,
            cell_witnesses.len() == self.num_readers(),
            forall|j: int|
                0 <= j < cell_witnesses.len() ==> {
                    &&& #[trigger] cell_witnesses[j].id() == self.cell_gen_id(j)
                    &&& cell_witnesses[j].frac() == 1 as real / 2 as real
                },
        ensures
            result@.id() == self.current_gen_id(),
            result@.frac() == 1 as real / 2 as real,
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut cell_witnesses = cell_witnesses;
        let (ptr, Tracked(points_to), Tracked(dealloc)) = frac_ptr::epoch_alloc(v);
        let tracked mut frac = Frac::new(points_to);
        let ghost gen_id = frac.id();
        let n = self.stash.len();
        let ghost piece_frac: real = 1 as real / (n as real + 1 as real);
        // Split locally first -- ordinary, single-threaded proof reasoning, no shared invariant
        // involved yet -- so every piece provably shares `gen_id` with the eventual managed
        // remainder, established once, all at once.
        let tracked mut pieces: Seq<Frac<PointsTo<T>>> = Seq::tracked_empty();
        proof {
            assert(piece_frac * (n as real + 1 as real) == 1 as real) by (nonlinear_arith)
                requires
                    piece_frac == 1 as real / (n as real + 1 as real),
            ;
            assert(frac.frac() == 1 as real - (0 as real) * piece_frac) by (nonlinear_arith)
                requires
                    frac.frac() == 1 as real,
            ;
        }
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                pieces.len() == i,
                frac.resource().ptr() == ptr,
                frac.resource().is_init(),
                frac.id() == gen_id,
                ptr.addr() != 0,
                frac.frac() == 1 as real - (i as real) * piece_frac,
                piece_frac * (n as real + 1 as real) == 1 as real,
                // Without these, the pieces reach the publish loop as opaque values and
                // `SlotBigPred::inv`'s `Present` arm (which pins each piece's id, fraction,
                // pointer and initialisation) cannot be re-established there.
                forall|k: int|
                    0 <= k < pieces.len() ==> {
                        &&& #[trigger] pieces[k].id() == gen_id
                        &&& pieces[k].frac() == piece_frac
                        &&& pieces[k].resource().ptr() == ptr
                        &&& pieces[k].resource().is_init()
                    },
            decreases n - i,
        {
            proof {
                assert((0 as real) < piece_frac) by (nonlinear_arith)
                    requires
                        piece_frac * (n as real + 1 as real) == 1 as real,
                        (n as real + 1 as real) > 0 as real,
                ;
                assert(piece_frac < frac.frac()) by (nonlinear_arith)
                    requires
                        i < n,
                        piece_frac * (n as real + 1 as real) == 1 as real,
                        piece_frac > 0 as real,
                        frac.frac() == 1 as real - (i as real) * piece_frac,
                ;
            }
            let tracked piece = frac.split_to(piece_frac);
            proof {
                broadcast use vstd::seq::group_seq_lemmas;

                let ghost old_pieces: Seq<Frac<PointsTo<T>>> = pieces;
                let ghost old_len = pieces.len();
                pieces.tracked_push(piece);
                assert(pieces == old_pieces.push(piece));
                assert forall|k: int| 0 <= k < old_len + 1 implies {
                    &&& #[trigger] pieces[k].id() == gen_id
                    &&& pieces[k].frac() == piece_frac
                    &&& pieces[k].resource().ptr() == ptr
                    &&& pieces[k].resource().is_init()
                } by {
                    assert(pieces[k] == old_pieces.push(piece)[k]);
                    if k < old_len {
                        assert(old_pieces.push(piece)[k] == old_pieces[k]);
                        assert(old_pieces[k].id() == gen_id);
                    } else {
                        assert(old_pieces.push(piece)[k] == piece);
                    }
                }
                assert(frac.frac() == 1 as real - (i as real + 1 as real) * piece_frac)
                    by (nonlinear_arith)
                    requires
                        frac.frac() == (1 as real - (i as real) * piece_frac) - piece_frac,
                ;
            }
            i += 1;
        }
        proof {
            assert(frac.frac() == piece_frac) by (nonlinear_arith)
                requires
                    frac.frac() == 1 as real - (n as real) * piece_frac,
                    piece_frac * (n as real + 1 as real) == 1 as real,
            ;
        }
        let ghost n_int: int = n as int;
        let tracked mut new_witness_out: Option<FracGhost<Loc>> = None;
        open_atomic_invariant!(self.inv.borrow() => big => {
            proof {
                // Bridge `n` (an exec length, `self.stash.len()`) to the invariant constant's own
                // lengths. `SlotBigPred::inv` states the gate's fraction and the per-cell clauses
                // in terms of `k.stash_ids.len()`/`k.cell_gen_ids.len()`, while everything this
                // function computes is in terms of `n`; only `Slot::inv` ties them together.
                assert(n_int == self.inv@.constant().stash_ids.len());
                assert(n_int == self.inv@.constant().cell_gen_ids.len());
                assert(big.stash_states.len() == n_int);
                assert(big.cell_gen.len() == n_int);
                // `witness` is a live, `1/2`-fraction, same-id copy of `current_gen` -- were
                // `current_gen.frac()` currently `1` (the unclaimed case), the two would sum
                // past `1`, contradicting `bounded_with`'s own soundness. So it must be `1/2`
                // (the claimed case) -- established here, not assumed, from the resource
                // algebra's own conservation, not from directly observing `claimed`'s value.
                big.current_gen.bounded_with(&witness);
                assert(big.current_gen.frac() == 1 as real / 2 as real);
                // Establish the fraction disjunction for every cell this call is about to touch,
                // while `SlotBigPred::inv` is the invariant macro's own ambient fact. The `by`
                // block mentions `big.stash_states[k]` to fire the per-cell match clause's
                // trigger; that clause's *guard* needs `k < big.stash_states.len()`, which comes
                // from `use_type_invariant(self)` at the top of this function bridging
                // `stash_ids.len()` and `cell_gen_ids.len()` (both to `self.stash@.len()`).
                assert forall|k: int| 0 <= k < cell_witnesses.len() implies {
                    &&& #[trigger] big.cell_gen[k].id() == cell_witnesses[k].id()
                    &&& (big.cell_gen[k].frac() == 1 as real / 2 as real
                        || big.cell_gen[k].frac() == 1 as real)
                } by {
                    assert(big.cell_gen[k].id() == self.cell_gen_id(k));
                    assert(cell_witnesses[k].id() == self.cell_gen_id(k));
                    assert(big.stash_states[k] is Empty || big.stash_states[k] is Present);
                }
                // Derive "every touched cell is Empty" and "this slot is installed" now, while
                // the ambient invariant is still guaranteed to hold (mid-block, after mutating
                // `cell_gen`/`current_gen`, it transiently isn't) -- see
                // `derive_empty_and_installed`'s doc comment.
                self.derive_empty_and_installed(&mut big, &cell_witnesses, n_int);
            }
            self.gate.store(Tracked(&mut big.gate_perm), ptr);
            proof {
                big.gate_state = SlotState::Occupied { frac, dealloc };
                big.current_gen.combine(witness);
                big.current_gen.update(gen_id);
                let tracked new_witness = big.current_gen.split();
                new_witness_out = Some(new_witness);
                // Update every `cell_gen[i]`'s (and every `cell_witnesses[i]`'s) wrapped value to
                // `gen_id` in this *same* open, so `cell_gen[i]@ == current_gen@` never has a gap
                // (see `SlotBigPred::inv`'s unconditional clause) -- not deferred to the per-cell
                // loop below, which only needs `combine` from here on (the value is already
                // right). `update_all_cell_gen`'s precondition is exactly the disjunction just
                // established above.
                update_all_cell_gen(&mut big.cell_gen, &mut cell_witnesses, n_int, gen_id);
                assert(big.current_gen@ == gen_id);
                assert forall|k: int| 0 <= k < big.cell_gen.len() implies
                    #[trigger] big.cell_gen[k]@ == big.current_gen@ by {
                    assert(big.cell_gen[k].id() == self.cell_gen_id(k));
                    assert(big.cell_gen[k]@ == gen_id);
                }
                // `stash_states[k] is Empty` and `installed_perm.value()` were already derived
                // above, *before* the mutations in this block -- neither `stash_states` nor
                // `installed_perm` is touched by anything since, so those facts are still
                // exactly what the invariant's `Empty` match arm needs here.
            }
            proof {
                // As in the publish block below: establish the predicate here, with `Seq`'s
                // lemmas in scope, rather than leaving it to the macro's own end-of-block check.
                broadcast use vstd::seq::group_seq_lemmas;

                let ghost kk = self.inv@.constant();
                // `derive_empty_and_installed` only promises `installed` when there is at least
                // one cell to derive it from -- which is exactly when the `Empty` arm below is
                // non-vacuous, so the guard costs nothing.
                if n_int > 0 {
                    assert(big.installed_perm.value());
                }
                // `update_all_cell_gen`'s per-cell ensures is triggered on
                // `big.cell_gen[i].id()`, so the fraction it also guarantees is unavailable until
                // that term is mentioned.
                assert forall|i: int| 0 <= i < big.cell_gen.len() implies
                    #[trigger] big.cell_gen[i].frac() == 1 as real / 2 as real by {
                    assert(big.cell_gen[i].id() == self.cell_gen_id(i));
                }
                assert(SlotBigPred::<T>::inv(kk, big));
            }
        });
        // Publish each reader's already-split, already-id-matching piece, combining its
        // `cell_gen` witness back (restoring `frac() == 1`, the same `bounded_with` way as
        // `current_gen` above). Its value is already `gen_id` (updated above, in the same open
        // as `current_gen`'s own update), so no further `.update()` is needed here. A witness is
        // *always* supplied here now -- either from the drain loop (an occupied slot's readers)
        // or from `writer_extract_gate` itself (a never-installed slot's fresh `frac() == 1`
        // cells, pre-split via `bounded_with`'s own `1/2` convention) -- so there's no unprovable
        // "no witness" case left to handle.
        let tracked mut cell_witnesses_seq = cell_witnesses;
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                self.inv(),
                n == self.num_readers(),
                pieces.len() == n - j,
                cell_witnesses_seq.len() == n - j,
                ptr.addr() != 0,
                piece_frac == 1 as real / (n as real + 1 as real),
                forall|k: int|
                    0 <= k < cell_witnesses_seq.len() ==> {
                        &&& #[trigger] cell_witnesses_seq[k].id() == self.cell_gen_id(k + j)
                        &&& cell_witnesses_seq[k].frac() == 1 as real
                            / 2 as real
                        // Carried so the `Present` arm's `piece.id() == cell_gen[j]@` clause is
                        // provable after `combine` (which forces `cell_gen[j]@ == cell_witness@`).
                        &&& cell_witnesses_seq[k]@ == gen_id
                    },
                forall|k: int|
                    0 <= k < pieces.len() ==> {
                        &&& #[trigger] pieces[k].id() == gen_id
                        &&& pieces[k].frac() == piece_frac
                        &&& pieces[k].resource().ptr() == ptr
                        &&& pieces[k].resource().is_init()
                    },
            decreases n - j,
        {
            let tracked piece;
            let tracked cell_witness: FracGhost<Loc>;
            proof {
                broadcast use vstd::seq::group_seq_lemmas;

                let ghost old_pieces: Seq<Frac<PointsTo<T>>> = pieces;
                piece = pieces.tracked_remove(0);
                assert(piece == old_pieces[0]);
                // Instantiate the loop invariant at `k == 0` by its own trigger term, so the
                // removed piece's fraction, pointer and initialisation -- everything the
                // `Present` arm demands of it -- are known to the publish block below.
                assert(old_pieces[0].id() == gen_id);
                assert(piece.frac() == piece_frac);
                assert(piece.resource().ptr() == ptr);
                assert(piece.resource().is_init());
                // `Seq::remove`'s index lemma is *not* in `group_seq_lemmas` (unlike `push`'s),
                // so shifting a per-index fact across a `tracked_remove` needs it called by hand.
                old_pieces.remove_ensures(0);
                assert forall|k: int| 0 <= k < pieces.len() implies {
                    &&& #[trigger] pieces[k].id() == gen_id
                    &&& pieces[k].frac() == piece_frac
                    &&& pieces[k].resource().ptr() == ptr
                    &&& pieces[k].resource().is_init()
                } by {
                    // Mentions the loop invariant's own trigger term (`old_pieces[k + 1].id()`),
                    // not just `old_pieces[k + 1]` -- otherwise the invariant is never
                    // instantiated at `k + 1` and the shifted fact is unavailable.
                    assert(old_pieces[k + 1].id() == gen_id);
                    assert(pieces[k] == old_pieces[k + 1]);
                }
                let ghost old_seq: Seq<FracGhost<Loc>> = cell_witnesses_seq;
                let tracked w = cell_witnesses_seq.tracked_remove(0);
                assert(w == old_seq[0]);
                // Instantiate the loop invariant at `k == 0` -- by its own trigger term -- so the
                // removed witness's fraction and wrapped value (not just its identity) are known
                // to the publish block below.
                assert(old_seq[0].id() == self.cell_gen_id(0 + j));
                assert(w.frac() == 1 as real / 2 as real);
                assert(w@ == gen_id);
                old_seq.remove_ensures(0);
                assert forall|k: int| 0 <= k < cell_witnesses_seq.len() implies {
                    &&& #[trigger] cell_witnesses_seq[k].id() == self.cell_gen_id(k + j + 1)
                    &&& cell_witnesses_seq[k].frac() == 1 as real / 2 as real
                    &&& cell_witnesses_seq[k]@ == gen_id
                } by {
                    assert(old_seq[k + 1].id() == self.cell_gen_id(k + 1 + j));
                    assert(cell_witnesses_seq[k] == old_seq[k + 1]);
                }
                cell_witness = w;
            }
            let cell = &self.stash[j];
            open_atomic_invariant!(self.inv.borrow() => big => {
                // Block-level snapshots: the three per-index borrows below each rewrite their own
                // `Seq`, and re-establishing the invariant needs every *other* index framed as
                // unchanged against these.
                let ghost states_before: Seq<StashSlot<T>> = big.stash_states;
                let ghost perms_before: Seq<PermissionPtr<T>> = big.stash_perms;
                let ghost cg_before: Seq<FracGhost<Loc>> = big.cell_gen;
                proof {
                    // Same bridge as the gate-store block: `SlotBigPred::inv`'s `Present` arm
                    // states the piece's share as `1/(k.stash_ids.len()+1)`, this function
                    // computes it as `1/(n+1)`.
                    // Stated via `n`, not the pre-loop ghost `n_int`: only `n` is tied into this
                    // loop's own `invariant` clause, so `n_int == n as int` is not available here.
                    assert(n as int == self.inv@.constant().stash_ids.len());
                    // The whole derivation has to sit in *one* block, with no mutation of `big`
                    // in between: the disjunction (from the per-cell match clause, fired by
                    // mentioning `big.stash_states[j]`) is what turns `bounded_with`'s `<= 1/2`
                    // into an exact `== 1/2`, and a `cell.store` between the two loses it.
                    // Snapshot the pre-borrow sequence: it is what gives `cell_gen_ref` a stable
                    // name to be linked back to (`bounded_with` is non-mutating), so the
                    // disjunction survives the borrow. Same shape as
                    // `derive_empty_and_installed`'s.
                    assert(big.stash_states[j as int] is Empty
                        || big.stash_states[j as int] is Present);
                    assert(cg_before[j as int].frac() == 1 as real / 2 as real
                        || cg_before[j as int].frac() == 1 as real);
                    let tracked cell_gen_ref = big.cell_gen.tracked_borrow_mut(j as int);
                    cell_gen_ref.bounded_with(&cell_witness);
                    assert(*cell_gen_ref == cg_before[j as int]);
                    assert(cell_gen_ref.frac() == 1 as real / 2 as real);
                    // Same derivation as `checkin`'s: `!installed` would force every cell `Empty`
                    // *and* at `frac() == 1`, contradicting the `1/2` just established. Needed to
                    // keep the `!installed ==> every cell Empty` clause satisfied once this cell
                    // becomes `Present` below.
                    assert(big.installed_perm.value());
                    cell_gen_ref.combine(cell_witness);
                }
                let tracked perm_ref = big.stash_perms.tracked_borrow_mut(j as int);
                cell.store(Tracked(perm_ref), ptr);
                proof {
                    let tracked state_ref = big.stash_states.tracked_borrow_mut(j as int);
                    let tracked mut placeholder = StashSlot::Present(piece);
                    vstd::modes::tracked_swap(state_ref, &mut placeholder);
                }
                proof {
                    // The per-cell borrows above leave every *other* index untouched, but showing
                    // that needs `Seq`'s update-index lemmas, which are not in scope for the
                    // macro's own end-of-block check -- so establish the predicate here, where
                    // they are, and let that check consume it.
                    broadcast use vstd::seq::group_seq_lemmas;

                    let ghost kk = self.inv@.constant();
                    assert(big.stash_states[j as int] is Present);
                    assert(big.cell_gen[j as int].frac() == 1 as real);
                    assert(big.cell_gen[j as int]@ == gen_id);
                    assert(big.stash_perms[j as int].value() == ptr);
                    assert(big.stash_states.len() == states_before.len());
                    assert(big.stash_perms.len() == perms_before.len());
                    assert(big.cell_gen.len() == cg_before.len());
                    // Framing: only index `j` was touched.
                    assert forall|i: int| 0 <= i < big.stash_states.len() && i != j implies {
                        &&& #[trigger] big.stash_states[i] == states_before[i]
                        &&& big.stash_perms[i] == perms_before[i]
                        &&& big.cell_gen[i] == cg_before[i]
                    } by {}
                    assert(forall|i: int|
                        0 <= i < kk.cell_gen_ids.len() ==> #[trigger] big.cell_gen[i].id()
                            == kk.cell_gen_ids[i]);
                    assert(forall|i: int|
                        0 <= i < big.cell_gen.len() ==> #[trigger] big.cell_gen[i]@
                            == big.current_gen@);
                    assert(SlotBigPred::<T>::inv(kk, big));
                }
            });
            j += 1;
        }
        // No `installed_flag` store here: it is already `true` by the time any `writer_put` runs.
        // `extract_fresh_cell_gen_witnesses` flips it, once and forever, with the very
        // `compare_exchange` that mints a never-installed slot's `cell_gen` witnesses, and this
        // function's own precondition (live `1/2`-fraction witnesses for every cell) is
        // unsatisfiable before that -- which is exactly what the gate-store block's
        // `derive_empty_and_installed` call re-derives. A redundant store here would also be
        // *unprovable* in its own open: nothing carries "every cell is now `Present`" across
        // opens, so the invariant's `Empty` arm could not be re-established for a cell the solver
        // still believes is empty.
        Tracked(new_witness_out.tracked_unwrap())
    }
}

// Actually frees a fully-drained occupant's backing memory. Only sound once `frac() == 1` --
// i.e. once every reader's stash cell has been drained and combined back in. Takes the
// `SlotState<T>` obtained from `Slot::writer_extract_gate` directly, so there's no way to call
// this without having first taken the slot to `Vacant`.
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
