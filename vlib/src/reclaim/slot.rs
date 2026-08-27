//! `Slot<T>`: a heap-address-stable, *reusable* holder for a lock-free-published value, together
//! with one pre-split fractional reader fragment per reader (the "stash"), all governed by a
//! single, hand-rolled `AtomicInvariant` spanning the slot's own pointer, every stash cell's
//! pointer, *and* the slot's own exclusive-claim flag (raw `vstd::invariant`/`PAtomicPtr`, not the
//! `atomic_ghost` convenience wrapper, and not any state-machine macro).
//!
//! This follows the CSL "hazard pointer" proof of Jung et al., *Modular Verification of Safe
//! Memory Reclamation in Concurrent Separation Logic* (OOPSLA 2023), on both of the axes that
//! matter:
//!
//!   - **Fig. 9's "split once, up front, one fragment per reader"**: the published value's
//!     `Frac<PointsTo<T>>` is split into `num_readers + 1` fixed `1/(n+1)` shares at
//!     `writer_put`/`new_occupied` time -- never dynamically per pin. Reclaim reassembles
//!     `frac() == 1` by combining every share back, which is what makes the deallocation sound.
//!   - **Fig. 9's ownership *ledger*, and §5's BlockId.** The paper tracks *where each fragment
//!     currently lives* with per-thread half/half ghost variables, and reads that state back by
//!     value agreement (`Ghost-Var-Agree`) -- it never infers state by refuting a fraction. Here
//!     that is one `GhostMapAuth<int, Loc>` (`gen_auth`) whose domain is fixed forever at `-1`
//!     (the paper's `★` -- the retirer's own key) plus one key per reader, together with the
//!     `GhostSubmap` of exactly those fragments the invariant itself currently holds
//!     (`stashed_frags`). *Which side holds key `i`* is the state: held by the invariant means
//!     reader `i`'s share is checked in, held by a caller means it is checked out. Each key's
//!     *value* is the generation id -- §5's BlockId, the ABA guard that stops a share checked out
//!     under one generation from being checked back in under a later one.
//!
//! Everything a caller needs to know about slot state therefore follows from one `agree` or one
//! disjointness step on a resource it *holds*, with no cross-open persistence assumption: a live
//! `GhostPointsTo` for key `i` proves, freshly at any later atomic open, both what generation `i`
//! belongs to (`agree` against `gen_auth`) and that the invariant cannot also be holding key `i`
//! (fragments for a key are exclusive) -- and the latter, read through the ledger clause below,
//! *is* "reader `i`'s cell is currently empty".
//!
//! Ghost state:
//!   - `SlotState`: `Vacant`, or `Occupied { frac, dealloc }` where `frac` is the "managed"
//!     remainder kept after splitting off one piece per reader into `stash`.
//!   - `StashSlot`: `Empty`, or `Present(piece)` -- one per reader, tied to the *same* physical
//!     cell (bidirectional: `Empty` iff the physical pointer is null).
//!   - `gen_auth` / `stashed_frags`: the ledger described above.
//!
//! Exclusivity, formalized: the two flags each gate one ledger key. `claimed` is true exactly
//! when the retirer's key `-1` is checked out (so `try_claim`'s CAS *is* what hands out the
//! retirer's fragment, and `release` hands it back); `vacant_flag` is true exactly when the
//! invariant holds every reader's fragment despite every cell being empty -- true at
//! construction (nothing has ever been published), and true again once a fully-drained,
//! already-published slot's fragments are all handed back at once via `release_to_idle`, rather
//! than being re-published. It is *not* a one-way latch: `writer_put` sets it back to `false` in
//! the same atomic step it installs a value, and `release_to_idle` sets it back to `true` in the
//! same atomic step it recombines everything -- letting `write` (and, later, an idle-slot
//! reclaimer, and a failed-CAS abandon path) tell "nothing to drain" from "needs draining" with
//! an ordinary atomic read instead of inferring it from ghost state across separate opens.
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
use vstd::resource::frac_opt::Frac;
use vstd::resource::map::GhostMapAuth;
use vstd::resource::map::GhostPointsTo;
use vstd::resource::map::GhostSubmap;
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
/// the `PointsTo` share itself, plus the ledger fragment for that reader's key. The two always
/// travel together -- the fragment is what lets `checkin` re-derive, by agreement at its own
/// atomic open, which generation the share belongs to, with no cross-open persistence assumption.
pub type StashedPiece<T> = (Frac<PointsTo<T>>, GhostPointsTo<int, Loc>);

/// The ledger key standing for the retirer -- the `★` of the paper's `℘(ThreadId ∪ {★})`. Reader
/// keys are `0..num_readers`, so `-1` cannot collide with one.
pub open spec fn retirer_key() -> int {
    -1
}

// The invariant's constant: which physical atomics (by id) this instance governs, plus the fixed
// identity of the ledger resource. Fixed forever once the `Slot` is constructed.
#[verifier::reject_recursive_types(T)]  // T occurs in argument position of spec_fn
pub struct SlotKey<T> {
    pub gate_id: int,
    pub stash_ids: Seq<int>,
    pub claimed_id: int,
    pub gen_id: Loc,
    pub vacant_flag_id: int,
    /// Content invariant: every value ever installed here satisfies it. Established once at
    /// install, assumable at every `checkout`.
    pub content: spec_fn(T) -> bool,
}

// The invariant's tracked payload: everything needed to describe the current state of the gate
// atomic, every stash atomic, both flags, and the ledger together.
pub tracked struct SlotBig<T> {
    pub gate_perm: PermissionPtr<T>,
    pub gate_state: SlotState<T>,
    pub stash_perms: Seq<PermissionPtr<T>>,
    pub stash_states: Seq<StashSlot<T>>,
    pub claimed_perm: PermissionBool,
    // `true` exactly when the invariant holds every reader's ledger key despite every cell being
    // Empty -- toggled `false` by `writer_put`'s `compare_exchange` (via
    // `extract_idle_reader_frags`, which hands that call its reader fragments in the same step),
    // toggled back `true` by `release_to_idle` (which hands them all back in the same step it
    // sets this). Being physical is the point: `write` (exec code) branches on "nothing to drain"
    // with an ordinary atomic op rather than inferring it from ghost state across separate opens.
    pub vacant_perm: PermissionBool,
    // The ledger authority. Domain is fixed forever at `{retirer_key()} ∪ 0..num_readers`; each
    // key's value is the generation id of whichever value is (or was last) published here.
    pub gen_auth: GhostMapAuth<int, Loc>,
    // Exactly those ledger fragments the invariant itself currently holds. Which side holds a key
    // *is* that key's state -- see `SlotBigPred::inv`'s two `contains` clauses, which are the only
    // place slot state and ledger state are tied together, and are therefore the only thing any
    // caller has to appeal to.
    pub stashed_frags: GhostSubmap<int, Loc>,
}

pub struct SlotBigPred<T> {
    dummy: core::marker::PhantomData<T>,
}

impl<T> InvariantPredicate<SlotKey<T>, SlotBig<T>> for SlotBigPred<T> {
    open spec fn inv(k: SlotKey<T>, big: SlotBig<T>) -> bool {
        &&& big.gate_perm.id() == k.gate_id
        &&& big.stash_perms.len() == k.stash_ids.len()
        &&& big.stash_states.len() == k.stash_ids.len()
        &&& forall|i: int|
            0 <= i < k.stash_ids.len() ==> #[trigger] big.stash_perms[i].id() == k.stash_ids[i]
        &&& big.claimed_perm.id() == k.claimed_id
        &&& big.vacant_perm.id() == k.vacant_flag_id
        &&& big.gen_auth.id() == k.gen_id
        &&& big.stashed_frags.id()
            == k.gen_id
        // The authority's domain never changes: the retirer's key plus one per reader. Nothing
        // ever calls `insert`/`delete` on it after construction, only `update`. Stated pointwise
        // rather than as a set equation -- `vstd`'s `Set` is finite-by-construction (`Set::new`
        // returns an `Option`), so membership is the cheaper and more directly usable form.
        &&& forall|key: int| #[trigger]
            big.gen_auth@.contains_key(key) <==> (retirer_key() <= key
                < k.stash_ids.len())
            // Every key agrees on the generation, so the retirer's key names it for the whole slot.
            // `writer_put` re-establishes this with a *single* `GhostSubmap::update` covering the
            // entire domain, in the same atomic open as the gate store -- so it never has a window
            // where it is transiently false.
        &&& forall|key: int|
            retirer_key() <= key < k.stash_ids.len() ==> #[trigger] big.gen_auth@[key]
                == big.gen_auth@[retirer_key()]
        // The ledger clauses. These two, and only these two, tie fragment location to slot state;
        // every derivation elsewhere in this module goes through one of them.
        &&& (big.stashed_frags@.contains_key(retirer_key()) <==> !big.claimed_perm.value())
        &&& forall|i: int|
            0 <= i < k.stash_ids.len() ==> (#[trigger] big.stashed_frags@.contains_key(i) <==> (
            big.stash_states[i] is Present
                || big.vacant_perm.value()))
            // Whenever `vacant`, every cell is empty -- which is what makes the `vacant` disjunct
            // above a description of "invariant holds every reader key despite nothing being
            // Present" (true both before the first install, and again after a full drain handed
            // everything back via `release_to_idle`) rather than an escape hatch, and gives
            // `Present ==> !vacant` everywhere.
        &&& (big.vacant_perm.value() ==> forall|i: int|
            0 <= i < big.stash_states.len() ==> #[trigger] big.stash_states[i] is Empty)
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
                &&& frac.id() == big.gen_auth@[retirer_key()]
                &&& frac.frac() == 1 as real / (k.stash_ids.len() as real
                    + 1 as real)
                // Content invariant: the currently-published value satisfies it. Needed on this
                // arm (not just `Present`) because `checkout` and `checkin` read/write through
                // `stash_states`, but a fresh `writer_put`/`new_occupied` install first
                // establishes the fact here, against the gate's own managed remainder.
                &&& (k.content)(frac.resource().value())
            },
        })
        &&& forall|i: int|
            0 <= i < big.stash_states.len() ==> (match #[trigger] big.stash_states[i] {
                StashSlot::Empty => big.stash_perms[i].value().addr() == 0,
                StashSlot::Present(piece) => {
                    &&& big.stash_perms[i].value().addr() != 0
                    &&& piece.resource().ptr() == big.stash_perms[i].value()
                    &&& piece.resource().is_init()
                    &&& piece.id() == big.gen_auth@[retirer_key()]
                    &&& piece.frac() == 1 as real / (k.stash_ids.len() as real
                        + 1 as real)
                    // Content invariant, restated here (not derived from the `Occupied` arm)
                    // because a reader can legally `checkout` from a slot whose gate share has
                    // already been extracted by a drain -- `Present` must carry the fact on its
                    // own rather than deriving it by `Frac` agreement against `gate_state`.
                    &&& (k.content)(piece.resource().value())
                },
            })
    }
}

// `dead_code`: `inv` is a ghost field, so it is erased in a plain (non-Verus) build and looks
// unread there -- same reason as `abd::server::register`'s own structs carry this allow.
//
// `reject_recursive_types(T)`: propagated up from `SlotKey<T>` (see its own doc comment) --
// `T` occurs in `SlotKey<T>`'s `content: spec_fn(T) -> bool` field, which is embedded here via
// `inv`'s `AtomicInvariant<SlotKey<T>, ..>`, so `T`'s non-positive position is transitive.
#[allow(dead_code)]
#[verifier::reject_recursive_types(T)]
pub struct Slot<T> {
    gate: PAtomicPtr<T>,
    stash: Vec<PAtomicPtr<T>>,
    claimed: PAtomicBool,
    vacant_flag: PAtomicBool,
    inv: Tracked<AtomicInvariant<SlotKey<T>, SlotBig<T>, SlotBigPred<T>>>,
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
        &&& self.inv@.constant().vacant_flag_id == self.vacant_flag.id()
    }

    pub closed spec fn num_readers(self) -> nat {
        self.stash@.len()
    }

    /// The `Loc` of this slot's ledger (`gen_auth`/`stashed_frags` share it). One id for the whole
    /// slot now: a single authority keyed by reader index replaced what used to be an array of
    /// separate per-cell fractional resources, each with its own `Loc`.
    pub closed spec fn gen_loc(self) -> Loc {
        self.inv@.constant().gen_id
    }

    /// The content invariant every value ever installed into this slot satisfies -- fixed at
    /// construction (`new_vacant`/`new_occupied`), never changed afterwards.
    pub closed spec fn content(self) -> spec_fn(T) -> bool {
        self.inv@.constant().content
    }

    pub fn new_vacant(num_readers: usize, Ghost(content): Ghost<spec_fn(T) -> bool>) -> (result:
        Self)
        ensures
            result.num_readers() == num_readers,
            result.content() == content,
    {
        let (gate, Tracked(gate_perm)) = PAtomicPtr::<T>::new(core::ptr::null_mut());
        // A vacant slot has no published value, so no real generation either -- any `Loc` will do
        // as the ledger's initial value. Minting a throwaway `Frac` is just a cheap way to get
        // one; nothing ever compares against it, because nothing can hold a share yet.
        let tracked placeholder_gen = Frac::new(());
        let ghost gen0 = placeholder_gen.id();
        let mut stash: Vec<PAtomicPtr<T>> = Vec::new();
        let tracked mut stash_perms: Seq<PermissionPtr<T>> = Seq::tracked_empty();
        let tracked mut stash_states: Seq<StashSlot<T>> = Seq::tracked_empty();
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
                forall|j: int|
                    0 <= j < i ==> {
                        &&& #[trigger] stash_perms[j].id() == stash@[j].id()
                        &&& stash_perms[j].value().addr() == 0
                        &&& stash_states[j] is Empty
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
                stash_perms.tracked_push(perm);
                stash_states.tracked_push(StashSlot::Empty);
                assert forall|j: int| 0 <= j < old_len + 1 implies {
                    &&& #[trigger] stash_perms[j].id() == stash@[j].id()
                    &&& stash_perms[j].value().addr() == 0
                    &&& stash_states[j] is Empty
                } by {
                    assert(stash@ == old_stash_view.push(cell));
                    assert(stash_perms == old_stash_perms.push(perm));
                    if j < old_len {
                        assert(stash@[j] == old_stash_view.push(cell)[j]);
                        assert(old_stash_view.push(cell)[j] == old_stash_view[j]);
                        assert(stash_perms[j] == old_stash_perms.push(perm)[j]);
                        assert(old_stash_perms.push(perm)[j] == old_stash_perms[j]);
                    } else {
                        assert(stash@[j] == old_stash_view.push(cell)[j]);
                        assert(old_stash_view.push(cell)[j] == cell);
                        assert(stash_perms[j] == old_stash_perms.push(perm)[j]);
                        assert(old_stash_perms.push(perm)[j] == perm);
                    }
                }
            }
            i += 1;
        }
        let (claimed, Tracked(claimed_perm)) = PAtomicBool::new(false);
        let (vacant_flag, Tracked(vacant_perm)) = PAtomicBool::new(true);
        let ghost stash_ids = Seq::new(num_readers as nat, |j: int| stash@[j].id());
        // One `GhostMapAuth` for the whole ledger, minted with its full and final domain. The
        // returned submap holds *every* key, which is exactly right for a never-claimed,
        // vacant slot: unclaimed means the invariant holds the retirer's key, and vacant means
        // it holds every reader's key too.
        let ghost initial_gens: Map<int, Loc> = Map::new(
            vstd::set_lib::set_int_range(retirer_key(), num_readers as int),
            |key: int| gen0,
        );
        let tracked (gen_auth, stashed_frags) = GhostMapAuth::<int, Loc>::new(initial_gens);
        let ghost key = SlotKey {
            gate_id: gate.id(),
            stash_ids,
            claimed_id: claimed.id(),
            gen_id: gen_auth.id(),
            vacant_flag_id: vacant_flag.id(),
            content,
        };
        proof {
            broadcast use vstd::seq::group_seq_lemmas, vstd::set_lib::group_set_lib_default;

            assert forall|j: int|
                #![trigger stash_ids[j]]
                0 <= j < stash_ids.len() implies stash_ids[j] == stash@[j].id() by {
                assert(stash_perms[j].id() == stash@[j].id());
            }
            assert forall|i: int| 0 <= i < stash_ids.len() implies #[trigger] stash_perms[i].id()
                == stash_ids[i] by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
            assert(gen_auth@ == initial_gens);
            assert(stashed_frags@ == initial_gens);
            assert forall|key: int| #[trigger]
                gen_auth@.contains_key(key) <==> (retirer_key() <= key < stash_ids.len()) by {}
            // Every key was minted with the same value, so the "all keys agree" clause holds by
            // construction rather than needing any per-key reasoning.
            assert forall|key: int|
                retirer_key() <= key < stash_ids.len() implies #[trigger] gen_auth@[key]
                == gen_auth@[retirer_key()] by {}
            assert(stashed_frags@.contains_key(retirer_key()));
            assert forall|i: int|
                0 <= i < stash_ids.len() implies #[trigger] stashed_frags@.contains_key(i) by {}
            assert forall|i: int| 0 <= i < stash_states.len() implies {
                &&& #[trigger] stash_states[i] is Empty
                &&& stash_perms[i].value().addr() == 0
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
            vacant_perm,
            gen_auth,
            stashed_frags,
        };
        let tracked inv = AtomicInvariant::new(key, big, 0);
        Slot { gate, stash, claimed, vacant_flag, inv: Tracked(inv) }
    }

    // Convenience for the very first install, avoiding an awkward `new_vacant` + `writer_put`
    // dance. Safe to populate everything directly (no atomics-as-such needed) since this runs
    // single-threaded, before any reader/writer could possibly observe this `Slot`.
    // Constructs an already-claimed slot (matching `EpochAtomicPtr`'s invariant that whichever
    // slot is `current` is always claimed) and hands back the retirer's ledger fragment -- the
    // same thing `writer_put` itself hands back -- so the caller (`EpochAtomicPtr::new`) can
    // install it into `current`'s own ghost payload, exactly mirroring how a later `write` threads
    // a fresh one through `current`'s swap.
    pub fn new_occupied(
        v: T,
        num_readers: usize,
        Ghost(content): Ghost<spec_fn(T) -> bool>,
    ) -> (result: (Self, Tracked<GhostPointsTo<int, Loc>>))
        requires
            core::mem::size_of::<T>() != 0,
            content(v),
        ensures
            result.0.num_readers() == num_readers,
            result.0.content() == content,
            result.1@.id() == result.0.gen_loc(),
            result.1@.key() == retirer_key(),
    {
        let (ptr, Tracked(points_to), Tracked(dealloc)) = frac_ptr::epoch_alloc(v);
        let tracked mut frac = Frac::new(points_to);
        let ghost gen_id = frac.id();
        let ghost piece_frac: real = 1 as real / (num_readers as real + 1 as real);
        let (gate, Tracked(gate_perm)) = PAtomicPtr::<T>::new(ptr);
        let mut stash: Vec<PAtomicPtr<T>> = Vec::new();
        let tracked mut stash_perms: Seq<PermissionPtr<T>> = Seq::tracked_empty();
        let tracked mut stash_states: Seq<StashSlot<T>> = Seq::tracked_empty();
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
                frac.resource().ptr() == ptr,
                frac.resource().is_init(),
                frac.resource().value() == v,
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
                        &&& stash_states[j]->Present_0.resource().value() == v
                        &&& stash_states[j]->Present_0.id() == gen_id
                        &&& stash_states[j]->Present_0.frac() == piece_frac
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
                stash_perms.tracked_push(perm);
                stash_states.tracked_push(StashSlot::Present(piece));
                assert(frac.frac() == 1 as real - (i as real + 1 as real) * piece_frac)
                    by (nonlinear_arith)
                    requires
                        frac.frac() == (1 as real - (i as real) * piece_frac) - piece_frac,
                ;
                assert(stash@ == old_stash_view.push(cell));
                assert(stash_perms == old_stash_perms.push(perm));
                assert(stash_states == old_stash_states.push(StashSlot::Present(piece)));
                assert forall|j: int| 0 <= j < old_len + 1 implies {
                    &&& #[trigger] stash_perms[j].id() == stash@[j].id()
                    &&& stash_perms[j].value() == ptr
                    &&& stash_states[j] is Present
                    &&& stash_states[j]->Present_0.resource().ptr() == ptr
                    &&& stash_states[j]->Present_0.resource().is_init()
                    &&& stash_states[j]->Present_0.resource().value() == v
                    &&& stash_states[j]->Present_0.id() == gen_id
                    &&& stash_states[j]->Present_0.frac() == piece_frac
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
        let (vacant_flag, Tracked(vacant_perm)) = PAtomicBool::new(false);
        let ghost stash_ids = Seq::new(num_readers as nat, |j: int| stash@[j].id());
        // Mint the ledger with its full and final domain, every key already naming this
        // generation, then hand the retirer's key straight out: the slot is born claimed (it is
        // `EpochAtomicPtr`'s initial `current`), and claimed means exactly "the retirer's fragment
        // is checked out". Every reader's key stays with the invariant, matching every cell being
        // `Present`.
        let ghost initial_gens: Map<int, Loc> = Map::new(
            vstd::set_lib::set_int_range(retirer_key(), num_readers as int),
            |key: int| gen_id,
        );
        let tracked (gen_auth, mut stashed_frags) = GhostMapAuth::<int, Loc>::new(initial_gens);
        let tracked retirer_frag = stashed_frags.split_points_to(retirer_key());
        let ghost key = SlotKey {
            gate_id: gate.id(),
            stash_ids,
            claimed_id: claimed.id(),
            gen_id: gen_auth.id(),
            vacant_flag_id: vacant_flag.id(),
            content,
        };
        proof {
            broadcast use vstd::seq::group_seq_lemmas;

            assert forall|j: int|
                #![trigger stash_ids[j]]
                0 <= j < stash_ids.len() implies stash_ids[j] == stash@[j].id() by {
                assert(stash_perms[j].id() == stash@[j].id());
            }
            assert forall|i: int| 0 <= i < stash_ids.len() implies #[trigger] stash_perms[i].id()
                == stash_ids[i] by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
            assert(gen_auth@ == initial_gens);
            assert forall|key: int| #[trigger]
                gen_auth@.contains_key(key) <==> (retirer_key() <= key < stash_ids.len()) by {}
            assert forall|key: int|
                retirer_key() <= key < stash_ids.len() implies #[trigger] gen_auth@[key]
                == gen_auth@[retirer_key()] by {}
            // `split_points_to` removed exactly the retirer's key, so the invariant now holds
            // precisely the reader keys -- which is what "claimed, and every cell Present" means.
            assert(stashed_frags@ =~= initial_gens.remove(retirer_key()));
            assert(!stashed_frags@.contains_key(retirer_key()));
            assert forall|i: int|
                0 <= i < stash_ids.len() implies #[trigger] stashed_frags@.contains_key(i) by {}
            assert forall|i: int| 0 <= i < stash_states.len() implies {
                &&& #[trigger] stash_states[i] is Present
                &&& stash_perms[i].value().addr() != 0
                &&& stash_states[i]->Present_0.resource().ptr() == stash_perms[i].value()
                &&& stash_states[i]->Present_0.resource().is_init()
                &&& stash_states[i]->Present_0.resource().value() == v
                &&& stash_states[i]->Present_0.id() == gen_auth@[retirer_key()]
                &&& stash_states[i]->Present_0.frac() == piece_frac
            } by {
                assert(stash_perms[i].id() == stash@[i].id());
            }
            // Content invariant: `frac`'s (and hence every split-off piece's) resource is
            // exactly the one `epoch_alloc`/`Frac::new` installed `v` into above, so `content(v)`
            // (this function's own `requires`) discharges both `SlotBigPred::inv`'s `Occupied`
            // and `Present` arms in one step.
            assert(frac.resource().value() == v);
            assert(content(v));
        }
        let tracked big = SlotBig {
            gate_perm,
            gate_state: SlotState::Occupied { frac, dealloc },
            stash_perms,
            stash_states,
            claimed_perm,
            vacant_perm,
            gen_auth,
            stashed_frags,
        };
        let tracked inv = AtomicInvariant::new(key, big, 0);
        (Slot { gate, stash, claimed, vacant_flag, inv: Tracked(inv) }, Tracked(retirer_frag))
    }

    // Cheap, non-mutating peek: does the gate currently hold a published value?
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

    // A reader checks its own pre-allocated piece out, together with the ledger fragment for its
    // own key -- taken out of the invariant's `stashed_frags` *because* the cell being `Present`
    // (established fresh, right here, from the physical pointer being non-null) is, by the
    // invariant's ledger clause, exactly what says the invariant is currently holding that key.
    // The reader must hold onto the fragment and hand it back, unmodified, to `checkin`: it is
    // what lets `checkin` prove the piece still belongs to the *current* generation, by agreement
    // against the authority at that later open, rather than assuming anything survived unchanged.
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
                &&& result.1@->Some_0.1.id() == self.gen_loc()
                &&& result.1@->Some_0.1.key() == reader_idx as int
                &&& result.1@->Some_0.0.id() == result.1@->Some_0.1.value()
                &&& self.content()(result.1@->Some_0.0.resource().value())
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
                        // `Present` (just observed) gives `contains_key(reader_idx)` straight from
                        // the ledger clause, which is `split_points_to`'s whole precondition. The
                        // cell is now `Empty` and its key is checked out -- the same clause, read
                        // the other way, so the invariant is maintained by construction.
                        let tracked gen_frag = big.stashed_frags.split_points_to(
                            reader_idx as int,
                        );
                        // Ties the piece's generation to the fragment's own value -- the fact the
                        // reader carries away, and that `checkin` reads back the same way.
                        gen_frag.agree(&big.gen_auth);
                        assert(big.gen_auth@[reader_idx as int] == gen_frag.value());
                        assert(piece.id() == gen_frag.value());
                        out = Some((piece, gen_frag));
                    },
                    StashSlot::Empty => {},
                }
            }
        });
        (ptr, Tracked(out))
    }

    // A reader hands its piece back, together with the ledger fragment for its key that it got
    // from the matching `checkout`. Two things fall out of that fragment being a *live,
    // unconsumed* resource, both established freshly at this open with no persistence assumption:
    // `agree` against the authority says which generation the piece belongs to (so the
    // invariant's `Present` arm can be re-established), and `combine_points_to`'s own
    // `!old(self)@.contains_key(..)` postcondition says the invariant was *not* holding this key
    // -- which, through the ledger clause, is precisely "this cell was empty and this slot is
    // installed". No fraction is refuted anywhere; this is the paper's `Ghost-Var-Agree` step.
    // `ptr` must match the piece's own pointer (always true for a piece obtained from `checkout`
    // and returned unmodified).
    pub fn checkin(
        &self,
        reader_idx: usize,
        ptr: *mut T,
        Tracked(piece): Tracked<Frac<PointsTo<T>>>,
        Tracked(gen_frag): Tracked<GhostPointsTo<int, Loc>>,
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
            gen_frag.id() == self.gen_loc(),
            gen_frag.key() == reader_idx as int,
            piece.id() == gen_frag.value(),
            // Exactly what `SlotBigPred::inv`'s `Present` arm demands, same reasoning as the
            // fraction above -- callers already have it from `checkout`'s own postcondition.
            self.content()(piece.resource().value()),
    {
        proof {
            use_type_invariant(self);
        }
        let cell = &self.stash[reader_idx];
        open_atomic_invariant!(self.inv.borrow() => big => {
            proof {
                // Agreement, not refutation: this pins `gen_auth@[reader_idx]` to the fragment's
                // own value, and the invariant's "all keys agree" clause carries that to the
                // retirer's key, which is what the `Present` arm is stated against.
                gen_frag.agree(&big.gen_auth);
                assert(big.gen_auth@[reader_idx as int] == gen_frag.value());
                assert(piece.id() == big.gen_auth@[retirer_key()]);
            }
            let tracked perm_ref = big.stash_perms.tracked_borrow_mut(reader_idx as int);
            cell.store(Tracked(perm_ref), ptr);
            proof {
                let tracked state_ref = big.stash_states.tracked_borrow_mut(reader_idx as int);
                let tracked mut placeholder = StashSlot::Present(piece);
                big.stashed_frags.combine_points_to(gen_frag);
                vstd::modes::tracked_swap(state_ref, &mut placeholder);
            }
        });
    }

    // Tries to become the exclusive claim-holder of this slot. On success, hands out the retirer's
    // ledger fragment -- the paper's `★` key. Sound *unconditionally* within the `r is Ok` branch:
    // success means the CAS observed `claimed == false`, and the invariant's own ledger clause
    // says unclaimed is exactly "the invariant is holding the retirer's key", which is
    // `split_points_to`'s whole precondition. No separate flag, no cross-open persistence
    // assumption, no fraction. The fragment is what lets the caller carry proof of the current
    // generation across the many separate opens its reclaim sequence needs (see
    // `drain_and_extract`), and must eventually be handed back via `writer_put`.
    pub fn try_claim(&self) -> (result: (bool, Tracked<Option<GhostPointsTo<int, Loc>>>))
        ensures
            result.0 ==> result.1@ is Some,
            result.1@ is Some ==> {
                &&& result.1@->Some_0.id() == self.gen_loc()
                &&& result.1@->Some_0.key() == retirer_key()
            },
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut out: Option<GhostPointsTo<int, Loc>> = None;
        let r;
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = &mut big.claimed_perm;
            r = self.claimed.compare_exchange(Tracked(perm_ref), false, true);
            proof {
                if r is Ok {
                    let tracked frag = big.stashed_frags.split_points_to(retirer_key());
                    out = Some(frag);
                }
            }
        });
        (r.is_ok(), Tracked(out))
    }

    // Releases the exclusive claim on this slot, allowing a future `try_claim` to succeed. Takes
    // the retirer's ledger fragment -- minted by `writer_put` (for a slot that was just claimed
    // and reclaimed) or by `EpochAtomicPtr::new`/a prior `write`'s own `current`-swap (for a slot
    // that was `current`, now being displaced) -- and hands it back to the invariant, which is
    // exactly what the ledger clause needs before storing `claimed = false`. No trust escape: the
    // combine's `id()`-equality precondition holds because the fragment is statically tied to this
    // slot's ledger via `gen_loc()`, not because anything is assumed to have survived unchanged.
    pub fn release(&self, Tracked(retirer_frag): Tracked<GhostPointsTo<int, Loc>>)
        requires
            retirer_frag.id() == self.gen_loc(),
            retirer_frag.key() == retirer_key(),
    {
        proof {
            use_type_invariant(self);
        }
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = &mut big.claimed_perm;
            proof {
                big.stashed_frags.combine_points_to(retirer_frag);
            }
            self.claimed.store(Tracked(perm_ref), false);
        });
    }

    // Generalizes `release` to *also* return every reader's ledger fragment at once, marking the
    // slot genuinely idle (`vacant_flag = true`) rather than just unclaimed. Two call sites, both
    // already holding exactly this shape of input: (1) `EpochAtomicPtr::write`'s existing reclaim
    // path, after a real drain waited out reader quiescence on a slot that really was `current`;
    // (2) `EpochAtomicPtr::try_write`'s CAS-failure path, abandoning a slot that was claimed and
    // `writer_put`-installed but never made `current` -- since only the `current` slot is ever
    // reachable via `pin`, no real reader could have touched it, so that path never needs to wait
    // for anything, just drain (instantly) and call this.
    //
    // Callers must have already reduced the gate to `Vacant` (via `writer_extract_gate`) and
    // reclaimed whatever it held -- this function's own proof does not depend on `gate_state`
    // (that clause is independent of the ledger, exactly as for `writer_put`'s unconditional
    // `gate.store`), but calling it before doing so would leave that occupant's resources
    // unreachable rather than actually freed.
    //
    // Two physical atomics, two opens (the macro allows only one atomic op per open): the first
    // combines every reader key back and flips `vacant_flag`, using the *same* "holding every key
    // proves every cell Empty" derivation `writer_put`'s gate-store block uses (read before
    // mutating, since the fact needed is about the state *before* this call, not after); the
    // second mirrors `release` exactly, for the retirer key.
    pub fn release_to_idle(
        &self,
        Tracked(retirer_frag): Tracked<GhostPointsTo<int, Loc>>,
        Tracked(reader_frags): Tracked<GhostSubmap<int, Loc>>,
    )
        requires
            retirer_frag.id() == self.gen_loc(),
            retirer_frag.key() == retirer_key(),
            reader_frags.id() == self.gen_loc(),
            forall|k: int| #[trigger]
                reader_frags@.contains_key(k) <==> (0 <= k < self.num_readers()),
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut reader_frags = reader_frags;
        open_atomic_invariant!(self.inv.borrow() => big => {
            proof {
                assert(self.num_readers() as int == self.inv@.constant().stash_ids.len());
                reader_frags.disjoint(&big.stashed_frags);
                assert forall|i: int| 0 <= i < self.num_readers() implies
                    #[trigger] big.stash_states[i] is Empty by {
                    assert(reader_frags@.dom().contains(i));
                    assert(!big.stashed_frags@.contains_key(i));
                }
                big.stashed_frags.combine(reader_frags);
            }
            let tracked vacant_ref = &mut big.vacant_perm;
            self.vacant_flag.store(Tracked(vacant_ref), true);
            proof {
                let ghost kk = self.inv@.constant();
                assert(SlotBigPred::<T>::inv(kk, big));
            }
        });
        open_atomic_invariant!(self.inv.borrow() => big => {
            let tracked perm_ref = &mut big.claimed_perm;
            proof {
                big.stashed_frags.combine_points_to(retirer_frag);
            }
            self.claimed.store(Tracked(perm_ref), false);
        });
    }

    // Extracts the managed fragment entirely, swapping the gate to `Vacant`. Sound regardless of
    // occupancy (a never-occupied slot is already `Vacant`, so this is a no-op swap). Takes the
    // caller's own retirer fragment (from `try_claim`) purely to expose, via `agree` against the
    // authority at this exact open, that the extracted frac's id is the generation the caller
    // names -- the same relational technique `drain_and_extract` uses.
    pub fn writer_extract_gate(
        &self,
        Tracked(retirer_frag): Tracked<&GhostPointsTo<int, Loc>>,
    ) -> (result: (*mut T, Tracked<SlotState<T>>))
        requires
            retirer_frag.id() == self.gen_loc(),
            retirer_frag.key() == retirer_key(),
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
                    == retirer_frag.value()
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
                retirer_frag.agree(&big.gen_auth);
                vstd::modes::tracked_swap(&mut big.gate_state, &mut placeholder);
                out = Some(placeholder);
            }
        });
        (ptr, Tracked(out.tracked_unwrap()))
    }

    // For a slot that is currently *vacant* -- either never installed, or fully drained and
    // returned to idle by `release_to_idle` -- atomically (via a single `compare_exchange`,
    // `true -> false`) claims that fact *and* takes every reader's ledger fragment out of the
    // invariant in the same step -- exactly mirroring how `try_claim`'s own CAS and its retirer
    // fragment come out together. The pairing is what keeps the invariant satisfied throughout:
    // the ledger clause reads `contains_key(i) <==> (Present || vacant)`, so flipping `vacant` to
    // `false` while every cell is still `Empty` is *only* consistent if the reader keys leave the
    // invariant in the very same step. The justifying fact (`vacant ==> every cell Empty`) is
    // read from `big` as it stood at this open's start, before the CAS mutated it.
    //
    // This is where the ledger encoding pays off most visibly: what used to be a loop-free
    // recursive proof fn splitting `n` separate fractional resources one at a time is now a single
    // `GhostSubmap::split` over the whole reader key range.
    //
    // The returned `bool` is `false` when this slot was occupied (not vacant) -- the caller falls
    // back to the ordinary drain sequence in that case (whose fragments come from
    // `drain_and_extract` instead).
    pub fn extract_idle_reader_frags(&self) -> (result: (bool, Tracked<GhostSubmap<int, Loc>>))
        ensures
            result.1@.id() == self.gen_loc(),
            result.0 ==> forall|k: int| #[trigger]
                result.1@@.contains_key(k) <==> (0 <= k < self.num_readers()),
            // The not-vacant case matters to the caller too: an empty submap of this ledger is
            // exactly the right seed for its drain-loop accumulator.
            !result.0 ==> forall|k: int| !(#[trigger] result.1@@.contains_key(k)),
    {
        proof {
            use_type_invariant(self);
        }
        let ghost reader_keys: Set<int> = vstd::set_lib::set_int_range(
            0,
            self.num_readers() as int,
        );
        let tracked mut idle_frags: Option<GhostSubmap<int, Loc>> = None;
        let r;
        open_atomic_invariant!(self.inv.borrow() => big => {
            proof {
                // Read the justifying clause *before* the CAS mutates `vacant_perm`.
                if big.vacant_perm.value() {
                    assert forall|k: int| reader_keys.contains(k) implies
                        #[trigger] big.stashed_frags@.dom().contains(k) by {
                        assert(big.stash_states[k] is Empty);
                    }
                    assert(reader_keys <= big.stashed_frags@.dom());
                }
            }
            let tracked perm_ref = &mut big.vacant_perm;
            r = self.vacant_flag.compare_exchange(Tracked(perm_ref), true, false);
            proof {
                if r is Ok {
                    idle_frags = Some(big.stashed_frags.split(reader_keys));
                } else {
                    // Not vacant: hand back an empty submap of the right ledger, so the return
                    // type needs no `Option` and the caller's `id()` fact holds unconditionally.
                    idle_frags = Some(big.stashed_frags.empty());
                }
            }
        });
        (r.is_ok(), Tracked(idle_frags.tracked_unwrap()))
    }

    // Drains reader `reader_idx`'s stash cell. Returns the drained pointer (non-null iff a piece
    // was found -- executable liveness signal for the caller) together with the piece itself and
    // that reader's ledger fragment. Identical in shape to `checkout`: the cell being `Present`
    // (observed fresh, here) is by the ledger clause exactly "the invariant holds this key", which
    // is what lets the key be taken out; and the cell is left `Empty` with its key checked out, so
    // the same clause is maintained. The caller must hand the fragment to the matching
    // `writer_put`, which is what puts the key back. If present, the piece's generation is
    // *proven* to be the one `retirer_frag` names -- by `agree` against the authority at this
    // exact open, chained through the invariant's "all keys agree" clause -- not assumed.
    pub fn drain_and_extract(
        &self,
        reader_idx: usize,
        Tracked(retirer_frag): Tracked<&GhostPointsTo<int, Loc>>,
    ) -> (result: (*mut T, Tracked<Option<StashedPiece<T>>>))
        requires
            reader_idx < self.num_readers(),
            retirer_frag.id() == self.gen_loc(),
            retirer_frag.key() == retirer_key(),
        ensures
            result.0.addr() != 0 ==> result.1@ is Some,
            result.1@ is Some ==> {
                &&& result.1@->Some_0.0.resource().ptr() == result.0
                &&& result.1@->Some_0.0.resource().is_init()
                &&& result.1@->Some_0.0.id() == retirer_frag.value()
                &&& result.1@->Some_0.0.frac() == 1 as real / (self.num_readers() as real
                    + 1 as real)
                &&& result.1@->Some_0.1.id() == self.gen_loc()
                &&& result.1@->Some_0.1.key() == reader_idx as int
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
                retirer_frag.agree(&big.gen_auth);
                match placeholder {
                    StashSlot::Present(piece) => {
                        let tracked gen_frag = big.stashed_frags.split_points_to(reader_idx as int);
                        out = Some((piece, gen_frag));
                    },
                    StashSlot::Empty => {},
                }
            }
        });
        (ptr, Tracked(out))
    }

    // Installs a fresh value, splitting it into one piece per reader, installed directly into
    // the (already-allocated, persistent) `stash` cells.
    //
    // The ledger work is one step, not `n`: the caller hands over the retirer's fragment plus a
    // `GhostSubmap` covering *every* reader key, so this call momentarily holds the ledger's whole
    // domain and can retag it to the new generation with a single `GhostSubmap::update`, in the
    // same atomic open as the gate store. Because the authority and the caller's own copy move
    // together in that one step, the invariant's "all keys agree" clause never has a window where
    // it is transiently false -- which is what the old fraction-based ledger needed a recursive
    // per-cell proof fn (and a matching per-cell disjunction refutation) to arrange.
    //
    // Holding all the reader keys is also, by the ledger clause alone, the proof that every cell
    // is currently `Empty` and this slot is no longer vacant: `GhostSubmap::disjoint` against the
    // invariant's own `stashed_frags` says the invariant cannot be holding any of them.
    //
    // `reader_frags`: every reader key, from this call's own drain sequence (or, for a vacant
    // slot, from `extract_idle_reader_frags`).
    pub fn writer_put(
        &self,
        v: T,
        Tracked(retirer_frag): Tracked<GhostPointsTo<int, Loc>>,
        Tracked(reader_frags): Tracked<GhostSubmap<int, Loc>>,
    ) -> (result: Tracked<GhostPointsTo<int, Loc>>)
        requires
            core::mem::size_of::<T>() != 0,
            retirer_frag.id() == self.gen_loc(),
            retirer_frag.key() == retirer_key(),
            reader_frags.id() == self.gen_loc(),
            forall|k: int| #[trigger]
                reader_frags@.contains_key(k) <==> (0 <= k < self.num_readers()),
            self.content()(v),
        ensures
            result@.id() == self.gen_loc(),
            result@.key() == retirer_key(),
    {
        proof {
            use_type_invariant(self);
        }
        let (ptr, Tracked(points_to), Tracked(dealloc)) = frac_ptr::epoch_alloc(v);
        let tracked mut frac = Frac::new(points_to);
        let ghost gen_id = frac.id();
        let n = self.stash.len();
        let ghost piece_frac: real = 1 as real / (n as real + 1 as real);
        // The whole ledger domain, held locally for the duration of this call.
        let tracked mut all_frags = reader_frags;
        proof {
            all_frags.combine_points_to(retirer_frag);
        }
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
                frac.resource().value() == v,
                frac.id() == gen_id,
                ptr.addr() != 0,
                frac.frac() == 1 as real - (i as real) * piece_frac,
                piece_frac * (n as real + 1 as real) == 1 as real,
                // Without these, the pieces reach the publish loop as opaque values and
                // `SlotBigPred::inv`'s `Present` arm (which pins each piece's id, fraction,
                // pointer, initialisation and content) cannot be re-established there.
                forall|k: int|
                    0 <= k < pieces.len() ==> {
                        &&& #[trigger] pieces[k].id() == gen_id
                        &&& pieces[k].frac() == piece_frac
                        &&& pieces[k].resource().ptr() == ptr
                        &&& pieces[k].resource().is_init()
                        &&& pieces[k].resource().value() == v
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
                    &&& pieces[k].resource().value() == v
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
        let ghost all_keys: Set<int> = vstd::set_lib::set_int_range(retirer_key(), n_int);
        let ghost reader_keys: Set<int> = vstd::set_lib::set_int_range(0, n_int);
        let ghost new_gens: Map<int, Loc> = Map::new(all_keys, |k: int| gen_id);
        let tracked mut retirer_out: Option<GhostPointsTo<int, Loc>> = None;
        open_atomic_invariant!(self.inv.borrow() => big => {
            proof {
                // Bridge `n` (an exec length, `self.stash.len()`) to the invariant constant's own
                // length. `SlotBigPred::inv` states the gate's and each piece's share in terms of
                // `k.stash_ids.len()`, while everything this function computes is in terms of `n`;
                // only `Slot::inv` ties them together.
                assert(n_int == self.inv@.constant().stash_ids.len());
                assert forall|k: int| #[trigger] all_frags@.contains_key(k) <==> (retirer_key()
                    <= k < n_int) by {}
                // The one derivation that used to need a recursive proof fn and a per-cell
                // fraction refutation: holding every key means the invariant holds none of them,
                // and the ledger clause turns that directly into "every cell is Empty, and this
                // slot is no longer vacant" (and, for the retirer's key, "this slot is claimed").
                all_frags.disjoint(&big.stashed_frags);
                assert forall|i: int| 0 <= i < n_int implies {
                    &&& #[trigger] big.stash_states[i] is Empty
                    &&& !big.vacant_perm.value()
                } by {
                    assert(all_frags@.dom().contains(i));
                    assert(!big.stashed_frags@.contains_key(i));
                }
                assert(!big.stashed_frags@.contains_key(retirer_key())) by {
                    assert(all_frags@.dom().contains(retirer_key()));
                }
                assert(big.claimed_perm.value());
            }
            self.gate.store(Tracked(&mut big.gate_perm), ptr);
            proof {
                big.gate_state = SlotState::Occupied { frac, dealloc };
                // Retag the entire ledger domain to the new generation -- authority and local copy
                // together, in one step, in this same open. That simultaneity is exactly what
                // keeps the "all keys agree" clause gap-free.
                all_frags.update(&mut big.gen_auth, new_gens);
                assert(big.gen_auth@ =~= new_gens);
                assert(all_frags@ =~= new_gens);
                assert(new_gens.dom() =~= all_keys);
                assert(big.gen_auth@[retirer_key()] == gen_id);
                // Keep the retirer's key; the reader keys go back one at a time below, each in the
                // same open as its own cell's physical store.
                let tracked frag = all_frags.split_points_to(retirer_key());
                retirer_out = Some(frag);
                assert forall|k: int| #[trigger] all_frags@.contains_key(k) <==> (0 <= k < n_int)
                    by {}
            }
            proof {
                let ghost kk = self.inv@.constant();
                assert forall|key: int| #[trigger] big.gen_auth@.contains_key(key) <==> (
                retirer_key() <= key < kk.stash_ids.len()) by {}
                assert forall|key: int| retirer_key() <= key < kk.stash_ids.len() implies
                    #[trigger] big.gen_auth@[key] == big.gen_auth@[retirer_key()] by {}
                // Content invariant for the `Occupied` arm: `frac`'s resource is exactly what
                // `epoch_alloc`/`Frac::new` installed `v` into above, and `self.content()(v)` is
                // this function's own `requires`.
                assert(big.gate_state->Occupied_frac.resource().value() == v);
                assert(self.content()(v));
                assert(SlotBigPred::<T>::inv(kk, big));
            }
        });
        // Publish each reader's already-split piece, handing that reader's ledger key back to the
        // invariant in the same open as its own cell's physical store. Every key's value is
        // already `gen_id` (retagged above, in the gate-store open), so nothing here touches the
        // authority -- a `combine_points_to` is the whole ghost step, and its own
        // `!old(self)@.contains_key(..)` postcondition is what re-proves this cell was empty and
        // this slot no longer vacant.
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                self.inv(),
                n == self.num_readers(),
                pieces.len() == n - j,
                ptr.addr() != 0,
                piece_frac == 1 as real / (n as real + 1 as real),
                // `requires`-level facts about unchanging parameters don't carry into a loop body
                // on their own -- a `while` loop's body is checked against its own `invariant`
                // clause alone, so this (needed to re-establish `SlotBigPred::inv`'s `Present`
                // arm below) has to be restated here.
                self.content()(v),
                all_frags.id() == self.gen_loc(),
                forall|k: int| #[trigger] all_frags@.contains_key(k) <==> (j <= k < n as int),
                forall|k: int| j <= k < n as int ==> #[trigger] all_frags@[k] == gen_id,
                forall|k: int|
                    0 <= k < pieces.len() ==> {
                        &&& #[trigger] pieces[k].id() == gen_id
                        &&& pieces[k].frac() == piece_frac
                        &&& pieces[k].resource().ptr() == ptr
                        &&& pieces[k].resource().is_init()
                        &&& pieces[k].resource().value() == v
                    },
            decreases n - j,
        {
            let tracked piece;
            let tracked gen_frag: GhostPointsTo<int, Loc>;
            proof {
                broadcast use vstd::seq::group_seq_lemmas;

                let ghost old_pieces: Seq<Frac<PointsTo<T>>> = pieces;
                piece = pieces.tracked_remove(0);
                assert(piece == old_pieces[0]);
                // Instantiate the loop invariant at `k == 0` by its own trigger term, so the
                // removed piece's fraction, pointer, initialisation and content -- everything the
                // `Present` arm demands of it -- are known to the publish block below.
                assert(old_pieces[0].id() == gen_id);
                assert(piece.frac() == piece_frac);
                assert(piece.resource().ptr() == ptr);
                assert(piece.resource().is_init());
                assert(piece.resource().value() == v);
                // `Seq::remove`'s index lemma is *not* in `group_seq_lemmas` (unlike `push`'s),
                // so shifting a per-index fact across a `tracked_remove` needs it called by hand.
                old_pieces.remove_ensures(0);
                assert forall|k: int| 0 <= k < pieces.len() implies {
                    &&& #[trigger] pieces[k].id() == gen_id
                    &&& pieces[k].frac() == piece_frac
                    &&& pieces[k].resource().ptr() == ptr
                    &&& pieces[k].resource().is_init()
                    &&& pieces[k].resource().value() == v
                } by {
                    // Mentions the loop invariant's own trigger term (`old_pieces[k + 1].id()`),
                    // not just `old_pieces[k + 1]` -- otherwise the invariant is never
                    // instantiated at `k + 1` and the shifted fact is unavailable.
                    assert(old_pieces[k + 1].id() == gen_id);
                    assert(pieces[k] == old_pieces[k + 1]);
                }
                assert(all_frags@.contains_key(j as int));
                let ghost af_before: Map<int, Loc> = all_frags@;
                assert(af_before[j as int] == gen_id);
                gen_frag = all_frags.split_points_to(j as int);
                // `split_points_to` relates the two maps by an `insert`, so reading the pre-split
                // map at this key is what recovers the fragment's value.
                assert(af_before == all_frags@.insert(gen_frag.key(), gen_frag.value()));
                assert(af_before[j as int] == gen_frag.value());
                assert(gen_frag.value() == gen_id);
                assert forall|k: int| #[trigger]
                    all_frags@.contains_key(k) <==> ((j + 1) as int <= k < n as int) by {}
            }
            let cell = &self.stash[j];
            open_atomic_invariant!(self.inv.borrow() => big => {
                let ghost states_before: Seq<StashSlot<T>> = big.stash_states;
                let ghost perms_before: Seq<PermissionPtr<T>> = big.stash_perms;
                proof {
                    // Same bridge as the gate-store block: `SlotBigPred::inv`'s `Present` arm
                    // states the piece's share as `1/(k.stash_ids.len()+1)`, this function
                    // computes it as `1/(n+1)`. Stated via `n`, not the pre-loop ghost `n_int`:
                    // only `n` is tied into this loop's own `invariant` clause.
                    assert(n as int == self.inv@.constant().stash_ids.len());
                    gen_frag.agree(&big.gen_auth);
                    assert(big.gen_auth@[j as int] == gen_id);
                    assert(big.gen_auth@[retirer_key()] == gen_id);
                }
                let tracked perm_ref = big.stash_perms.tracked_borrow_mut(j as int);
                cell.store(Tracked(perm_ref), ptr);
                proof {
                    let tracked state_ref = big.stash_states.tracked_borrow_mut(j as int);
                    let tracked mut placeholder = StashSlot::Present(piece);
                    big.stashed_frags.combine_points_to(gen_frag);
                    vstd::modes::tracked_swap(state_ref, &mut placeholder);
                }
                proof {
                    // The per-index borrows above leave every *other* index untouched, but showing
                    // that needs `Seq`'s update-index lemmas, which are not in scope for the
                    // macro's own end-of-block check -- so establish the predicate here, where
                    // they are, and let that check consume it.
                    broadcast use vstd::seq::group_seq_lemmas;

                    let ghost kk = self.inv@.constant();
                    assert(big.stash_states[j as int] is Present);
                    assert(big.stash_perms[j as int].value() == ptr);
                    assert(big.stashed_frags@.contains_key(j as int));
                    assert forall|i: int| 0 <= i < big.stash_states.len() && i != j implies {
                        &&& #[trigger] big.stash_states[i] == states_before[i]
                        &&& big.stash_perms[i] == perms_before[i]
                    } by {}
                    // Content invariant for this cell's `Present` arm -- `piece`'s resource is the
                    // one split off `frac` above, which the splitting loop already tied to `v`.
                    assert(big.stash_states[j as int]->Present_0.resource().value() == v);
                    assert(self.content()(v));
                    assert(SlotBigPred::<T>::inv(kk, big));
                }
            });
            j += 1;
        }
        Tracked(retirer_out.tracked_unwrap())
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
// `Slot<T>`'s only fields with any actual runtime bytes are the physical atomics (`gate`,
// `stash`, `claimed`, `vacant_flag` -- all `core::sync::atomic` wrappers, already `Send`/`Sync`
// unconditionally). `inv: Tracked<AtomicInvariant<..>>` is `PhantomData`-backed (see
// `verus_builtin::Tracked`'s definition) and holds *zero* bytes in any build that actually runs
// (i.e. one not compiled through the Verus frontend) -- but Rust's auto-trait inference for
// `PhantomData<A>` conservatively mirrors `A`'s own bounds regardless, and `A` here
// (`AtomicInvariant<SlotKey<T>, SlotBig<T>, SlotBigPred<T>>`) contains a `*mut T`-typed ghost
// permission token deep inside `SlotBig<T>`, which is enough to make raw auto-derivation fail
// even though no such pointer is ever actually stored. These impls correct that false negative;
// they do not change what is actually shared. The bounds mirror `Arc<T>`'s own
// (`T: Send + Sync` for both): a `T` published through a `Slot` can be read via `&T` from any
// reader thread (needs `Sync`) and may be moved to a different thread when it is deallocated by
// whichever writer's `reclaim()` call happens to observe quiescence, which need not be the thread
// that allocated it (needs `Send`).
unsafe impl<T: Send + Sync> Send for Slot<T> {}
unsafe impl<T: Send + Sync> Sync for Slot<T> {}
