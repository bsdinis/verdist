//! Lock-free (hazard-pointer/epoch-reclamation) backend for the ABD register, replacing
//! `register.rs`'s `RwLock`-guarded `MonotonicRegister` for the read/write paths that don't need
//! `&mut` (see `claude-files/monotonic_register_backend_switch.md`, sections 1-5). Structured as
//! three homes instead of one struct (design doc section 2):
//!
//!   - `data: EpochAtomicPtr<RegisterSnapshot>` -- the published version. Readers touch only this
//!     (a pin + one atomic cell exchange) and `pub_seq` below -- never a lock, never blocked by a
//!     writer.
//!   - `pub_seq: AtomicU64<..>` -- the AUTHORITY: this server's `MonotonicTimestampResource` half
//!     plus a seq -> timestamp ledger (`PubState`/`PubPred`). A plain atomic load of this,
//!     compared against the `seq` a reader pinned, is the seqlock-style linearization point (see
//!     `validate` below and design doc section 3): if they match, the pinned snapshot's ghost
//!     content was authoritative at the instant of that load.
//!   - `gate: AtomicBool<..>` -- writer serialization only. It carries **no ghost payload** and
//!     proves nothing: the CAS on `pub_seq` (see the future `write` in `validate`'s sibling) is
//!     the actual mutual-exclusion argument. The gate exists purely so publication order agrees
//!     with advance order (a liveness property -- without it, two writers could publish out of
//!     order and leave `pub_seq` naming a *newer* generation than `data`, starving readers).
//!
//! `MonotonicRegister`/`MonotonicRegisterInner`/`MonotonicRegisterInv` in `register.rs` are not
//! touched by this module -- see `RegisterStore` (a later phase) for the runtime switch between
//! the two backends.
//!
//! This file implements design doc sections 5.1-5.4: the snapshot + content predicate, the
//! authority (`PubState`/`PubPred`), the register's own type invariant, `new`, the private
//! `observe`/`validate` helpers, and both halves of section 5.4's two protocols: `read`/
//! `read_timestamp` (the observe-validate retry loop) and `write` (the same loop, plus the
//! nested-open CAS on `pub_seq` that does the actual advance).
#[cfg(verus_only)]
use crate::invariants;
use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::ServerToken;
use crate::invariants::StateInvariant;
use crate::proto::GetRequest;
use crate::proto::GetResponse;
use crate::proto::GetTimestampRequest;
use crate::proto::GetTimestampResponse;
use crate::proto::WriteRequest;
use crate::proto::WriteResponse;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use vlib::monotonic::map::GhostMonotonicMap;
use vlib::reclaim::atomic_ptr::EpochAtomicPtr;

use std::sync::Arc;

use vstd::atomic::PAtomicU64;
#[cfg(verus_only)]
use vstd::atomic::PermissionU64;
use vstd::atomic_ghost::atomic_with_ghost;
use vstd::atomic_ghost::AtomicBool;
use vstd::atomic_ghost::AtomicInvariantPredicate;
#[cfg(verus_only)]
use vstd::atomic_ghost::AtomicPredU64;
use vstd::atomic_ghost::AtomicU64;
#[cfg(verus_only)]
use vstd::invariant::AtomicInvariant;
#[cfg(verus_only)]
use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::resource::map::GhostPersistentPointsTo;
use vstd::resource::Loc;

verus! {

// ---------------------------------------------------------------------------------------------
// 5.1: snapshot + content predicate
// ---------------------------------------------------------------------------------------------
/// Identity fields shared by every part of an `EpochMonotonicRegister` (the published snapshot,
/// the authority, and the register itself). Bundled into one `Ghost<LockfreeIds>` so the content
/// invariant threaded through `EpochAtomicPtr`/`Slot` (see `vlib::reclaim::slot`'s `content:
/// spec_fn(T) -> bool`) can pin a `RegisterSnapshot`'s ghost fields to *this* register instance,
/// not merely to "some register or other" -- see `snapshot_content` below.
pub struct LockfreeIds {
    pub resource_loc: Loc,
    pub commitment_id: Loc,
    pub server_token_id: Loc,
    pub ledger_id: Loc,
    pub id: u64,
}

/// One published version of the register: a value/timestamp pair plus the publish sequence
/// number that ties it to `pub_seq`'s ledger (design doc section 3), and duplicable ghost
/// witnesses a reader can carry out of the pin without holding a guard.
///
/// `#[repr(C)]` + the `global layout` declaration below fix this struct's runtime layout so
/// `EpochAtomicPtr::new`/`vlib::reclaim::frac_ptr::epoch_alloc`'s `core::mem::size_of::<T>() !=
/// 0` precondition is dischargeable: `size_of` is `uninterp` in `vstd` (see `vstd::layout`), so
/// Verus has no way to compute it for a user struct on its own. `global layout` is not a trust
/// escape -- it is checked by the real Rust compiler wherever this crate is actually compiled
/// (including under `cargo verus verify`, which still type-checks/const-evaluates the erased exec
/// code): a wrong size/align here is a hard `E0080 evaluation panicked: does not have the
/// expected size` compile error, not a silently-accepted assumption. (Verified empirically before
/// writing this: a deliberately-wrong `global size_of` value fails `cargo verus verify -p abd`
/// with exactly that error, without needing `--compile`.) The value is exec fields only --
/// `value: Option<u64>` (16 bytes) + `timestamp: Timestamp` (24 bytes, 3x u64) + `seq: u64` (8
/// bytes) = 48 bytes total, align 8; the three `Tracked<_>` fields are zero-sized regardless of
/// their type parameter (`PhantomData`'s auto-trait/layout behavior).
#[repr(C)]
pub struct RegisterSnapshot {
    pub value: Option<u64>,
    pub timestamp: Timestamp,
    pub seq: u64,
    /// `LowerBound{timestamp}` -- a duplicate peeled off the authority's half at publish time.
    pub lb: Tracked<MonotonicTimestampResource>,
    /// `key == timestamp, value == value` -- this write's commitment.
    pub commitment: Tracked<WriteCommitment>,
    /// `key == seq, value == timestamp` -- this snapshot's entry in `pub_seq`'s ledger.
    pub ledger_frag: Tracked<GhostPersistentPointsTo<u64, Timestamp>>,
}

global layout RegisterSnapshot is size == 48, align == 8;

pub open spec fn snapshot_inv(ids: LockfreeIds, s: RegisterSnapshot) -> bool {
    &&& s.lb@@ is LowerBound
    &&& s.lb@@.timestamp() == s.timestamp
    &&& s.lb@.loc() == ids.resource_loc
    &&& s.commitment@.id() == ids.commitment_id
    &&& s.commitment@.key() == s.timestamp
    &&& s.commitment@.value() == s.value
    &&& s.ledger_frag@.id() == ids.ledger_id
    &&& s.ledger_frag@.key() == s.seq
    &&& s.ledger_frag@.value() == s.timestamp
}

/// The content invariant handed to `EpochAtomicPtr::new`/`Slot` (see `vlib::reclaim::slot`'s
/// module docs): every value ever published through `data` satisfies `snapshot_inv` against
/// *this* register's `ids`. The first five clauses of `snapshot_inv` are exactly `GetResponse::inv`
/// (`proto/get.rs`), so `GetResponse::new`'s `requires` discharge straight off a pinned snapshot.
pub open spec fn snapshot_content(ids: LockfreeIds) -> spec_fn(RegisterSnapshot) -> bool {
    |s: RegisterSnapshot| snapshot_inv(ids, s)
}

// ---------------------------------------------------------------------------------------------
// 5.2: the authority
// ---------------------------------------------------------------------------------------------
/// `pub_seq`'s ghost payload: this server's `HalfRightToAdvance` plus the seq -> timestamp
/// ledger. Holding the half here (not in the published snapshot) is exactly what makes
/// `resource` writer-exclusive again -- see design doc section 1a/1b.
pub tracked struct PubState {
    pub half: MonotonicTimestampResource,
    pub ledger: GhostMonotonicMap<u64, Timestamp>,
}

pub struct PubPred;

impl AtomicInvariantPredicate<LockfreeIds, u64, PubState> for PubPred {
    open spec fn atomic_inv(k: LockfreeIds, v: u64, g: PubState) -> bool {
        &&& g.half.loc() == k.resource_loc
        &&& g.half@ is HalfRightToAdvance
        &&& g.ledger.id() == k.ledger_id
        &&& g.ledger@.contains_key(v)
        &&& g.ledger@[v]
            == g.half@.timestamp()
        // What makes `GhostMonotonicMap::insert`'s `!contains(seq + 1)` precondition
        // dischargeable at write time: the current exec value `v` is always the ledger's
        // greatest allocated key.
        &&& forall|s: u64| #[trigger] g.ledger@.contains_key(s) ==> s <= v
    }
}

/// Trivial predicate for the writer-serialization gate: no ghost payload, always `true` -- see
/// this module's top-of-file docs and design doc section 5.4 item 2 for why the gate must not
/// carry any ghost state (that would reintroduce an `RwLock`-shaped exclusive-transfer argument).
/// `vlib::reclaim::atomic_ptr::TrivialPred` is the same idea but only implemented for `usize`
/// (it backs that module's own `write_seq` nonce counter); this is the `bool` sibling, kept local
/// to `abd` rather than added to `vlib` since nothing else needs it there.
pub struct GateTrivialPred;

impl AtomicInvariantPredicate<(), bool, ()> for GateTrivialPred {
    open spec fn atomic_inv(k: (), v: bool, g: ()) -> bool {
        true
    }
}

/// A copy of one pinned snapshot's exec fields plus duplicated ghost witnesses, taken outside
/// any guard -- `observe` never returns while still holding a pin (see its own doc comment).
/// Private carrier, not part of the public protocol.
#[allow(dead_code)]
struct Observed {
    value: Option<u64>,
    timestamp: Timestamp,
    seq: u64,
    lb: Tracked<MonotonicTimestampResource>,
    commitment: Tracked<WriteCommitment>,
    ledger_frag: Tracked<GhostPersistentPointsTo<u64, Timestamp>>,
}

impl Observed {
    #[allow(dead_code)]
    spec fn inv(self, ids: LockfreeIds) -> bool {
        &&& self.lb@@ is LowerBound
        &&& self.lb@@.timestamp() == self.timestamp
        &&& self.lb@.loc() == ids.resource_loc
        &&& self.commitment@.id() == ids.commitment_id
        &&& self.commitment@.key() == self.timestamp
        &&& self.commitment@.value() == self.value
        &&& self.ledger_frag@.id() == ids.ledger_id
        &&& self.ledger_frag@.key() == self.seq
        &&& self.ledger_frag@.value() == self.timestamp
    }
}

// ---------------------------------------------------------------------------------------------
// 5.3: the register
// ---------------------------------------------------------------------------------------------
#[allow(dead_code)]
pub struct EpochMonotonicRegister<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    ids: Ghost<LockfreeIds>,
    // Plain exec copy of `ids@.id`, tied back to it by `inv()` below -- needed because `write`
    // must pass this server's id as a real runtime `u64` to `WriteRequest::destruct` (an exec
    // `u64` parameter, not a `Ghost`/`Tracked` one, unlike `server_lower_bound`'s `Ghost<u64>`
    // that `read`/`read_timestamp` get away with). Mirrors `MonotonicRegisterInner`'s own `id:
    // u64` field + `id()` spec fn split (`register.rs`).
    id: u64,
    data: EpochAtomicPtr<RegisterSnapshot>,
    // `EpochAtomicPtr::num_readers` is a `closed spec fn` (`vlib/src/reclaim/atomic_ptr.rs`) --
    // there is no exec-callable way to ask `data` how many reader slots it has. `read` /
    // `read_timestamp` need an actual runtime `usize` to reduce `shard_idx` into range (design
    // doc section 5.3), so this is a plain exec copy of the same `num_readers` passed to `new`,
    // tied back to `data.num_readers()` by `inv()` below.
    num_readers: usize,
    pub_seq: AtomicU64<LockfreeIds, PubState, PubPred>,
    gate: AtomicBool<(), (), GateTrivialPred>,
    server_token: Tracked<ServerToken>,
    state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
}

impl<ML, RL> EpochMonotonicRegister<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.id == self.id()
        &&& self.pub_seq.well_formed()
        &&& self.pub_seq.constant()
            == self.ids@
        // See `new`'s construction comment: needed to discharge Verus's nested-invariant-open
        // check in `write` (`self.state_inv`, namespace `invariants::state_inv_id()`, vs.
        // `self.pub_seq`, namespace `0`).
        &&& self.pub_seq.atomic_inv@.namespace() == 0
        &&& self.gate.well_formed()
        &&& self.data.content() == snapshot_content(self.ids@)
        &&& self.data.num_readers() > 0
        &&& self.num_readers as nat == self.data.num_readers()
        &&& self.server_token@.id() == self.ids@.server_token_id
        &&& self.server_token@.key() == self.ids@.id
        &&& self.server_token@.value() == self.ids@.resource_loc
        &&& self.state_inv@.namespace() == invariants::state_inv_id()
        &&& self.state_inv@.constant().commitments_ids.commitment_id == self.ids@.commitment_id
        &&& self.state_inv@.constant().server_tokens_id == self.ids@.server_token_id
        &&& self.state_inv@.constant().server_locs.contains_key(self.ids@.id)
        &&& self.state_inv@.constant().server_locs[self.ids@.id] == self.ids@.resource_loc
    }

    // Matching `MonotonicRegister`'s shapes (`register.rs:435-449`) so the `RegisterStore` enum
    // (a later phase) can forward to either backend without a spec-level tie between them.
    pub closed spec fn resource_loc(self) -> Loc {
        self.ids@.resource_loc
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.ids@.commitment_id
    }

    pub closed spec fn server_token_id(self) -> Loc {
        self.ids@.server_token_id
    }

    pub closed spec fn id(self) -> u64 {
        self.ids@.id
    }

    pub fn new(
        server_id: u64,
        state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
        num_readers: usize,
        num_slots: usize,
    ) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
            state_inv@.constant().server_locs.contains_key(server_id),
            num_readers >= 1,
            num_slots >= 1,
            num_slots <= vlib::reclaim::atomic_ptr::INDEX_SPACE,
        ensures
            r.id() == server_id,
            r.commitment_id() == state_inv@.constant().commitments_ids.commitment_id,
            r.server_token_id() == state_inv@.constant().server_tokens_id,
            r.resource_loc() == state_inv@.constant().server_locs[server_id],
    {
        // Claim this server's slot in the universe and mint its server token -- shared with
        // `MonotonicRegisterInner::new` (`register.rs`) via `invariants::claim_server`, since
        // both are establishing the exact same facts (a fresh `HalfRightToAdvance` for
        // `server_id`, a token for it, and `state.inv()` re-established before the invariant
        // closes). Only what gets built from the results differs.
        let tracked zero_commitment;
        let tracked resource;
        let tracked server_token;
        vstd::open_atomic_invariant!(&state_inv.borrow() => state => {
            proof {
                let tracked (r, tok, zc) = invariants::claim_server(&mut state, server_id);
                resource = r;
                server_token = tok;
                zero_commitment = zc;
            }
        });

        // `resource@ == HalfRightToAdvance{Timestamp::spec_default()}` (`split_auth`'s own
        // ensures): this server has just been claimed, so nothing has advanced its half yet.
        //
        // Ledger starts with exactly one entry, seq 0 -> the default timestamp, matching the
        // initial snapshot's `seq` and `pub_seq`'s initial exec value below.
        let tracked mut ledger = GhostMonotonicMap::<u64, Timestamp>::empty();
        let tracked ledger_frag0 = ledger.insert(0u64, Timestamp::spec_default());

        // Peel off the published `LowerBound` *before* moving `resource` into `pub_seq`'s
        // payload -- once it lives there, the only way to touch it again is through the atomic
        // invariant, and the initial snapshot needs its own duplicate up front.
        let tracked lb0 = resource.extract_lower_bound();

        let ghost ids = LockfreeIds {
            resource_loc: resource.loc(),
            commitment_id: zero_commitment.id(),
            server_token_id: server_token.id(),
            ledger_id: ledger.id(),
            id: server_id,
        };

        let tracked pub_state = PubState { half: resource, ledger };
        assert(<PubPred as AtomicInvariantPredicate<LockfreeIds, u64, PubState>>::atomic_inv(
            ids,
            0u64,
            pub_state,
        ));
        // Hand-construct the underlying `AtomicInvariant` -- rather than going through
        // `AtomicU64::new`, whose own `ensures` is only `well_formed() && constant() == k` and so
        // drops the namespace it passes internally -- so that this namespace (always `0`, by
        // `atomic_ghost`'s own construction, for *every* `AtomicU64`/`AtomicBool`; see
        // `vstd::atomic_ghost`'s `declare_atomic_type!`) becomes a real postcondition
        // (`AtomicInvariant::new`'s own `ensures` includes `namespace() == ns`) that `inv()`
        // below can carry forward. `write`'s nested `open_atomic_invariant!` (on `state_inv`,
        // namespace 1) / `atomic_with_ghost!` (on `pub_seq`) needs both namespaces as *known*
        // facts to discharge Verus's "possible invariant collision" check for nested opens, which
        // compares namespace *values*, not source-level integer literals -- confirmed against
        // `vstd`'s own `nested_good` test (`rust_verify_test/tests/open_invariant.rs`), which puts
        // exactly this pair of facts (`i.namespace() == 0, j.namespace() == 1`) in its own
        // `requires` for the identical reason. `AtomicU64::new` exposes no way to obtain this for
        // the atomic it builds, so there is no way to get this fact through it; this instead
        // reproduces that constructor's body field-for-field using only public `vstd` APIs
        // (`AtomicU64`'s own fields are `pub`, merely `#[doc(hidden)]`) -- no `vstd` change, no
        // trust escape. Flagged in `claude-files/backend_switch_questions.md`.
        let (pub_seq_patomic, Tracked(pub_seq_perm)) = PAtomicU64::new(0u64);
        let tracked pub_seq_pair = (pub_seq_perm, pub_state);
        assert(<AtomicPredU64<PubPred> as InvariantPredicate<
            (LockfreeIds, int),
            (PermissionU64, PubState),
        >>::inv((ids, pub_seq_patomic.id()), pub_seq_pair));
        let tracked pub_seq_atomic_inv = AtomicInvariant::<
            (LockfreeIds, int),
            (PermissionU64, PubState),
            AtomicPredU64<PubPred>,
        >::new((ids, pub_seq_patomic.id()), pub_seq_pair, 0);
        let pub_seq = AtomicU64::<LockfreeIds, PubState, PubPred> {
            patomic: pub_seq_patomic,
            atomic_inv: Tracked(pub_seq_atomic_inv),
        };
        assert(pub_seq.well_formed());
        assert(pub_seq.atomic_inv@.namespace() == 0);

        let gate = AtomicBool::<(), (), GateTrivialPred>::new(Ghost(()), false, Tracked(()));

        let initial_snapshot = RegisterSnapshot {
            value: None,
            timestamp: Timestamp::default(),
            seq: 0,
            lb: Tracked(lb0),
            commitment: Tracked(zero_commitment),
            ledger_frag: Tracked(ledger_frag0),
        };
        assert(snapshot_inv(ids, initial_snapshot));

        let data = EpochAtomicPtr::<RegisterSnapshot>::new(
            initial_snapshot,
            num_slots,
            num_readers,
            Ghost(snapshot_content(ids)),
        );

        let r = EpochMonotonicRegister {
            ids: Ghost(ids),
            id: server_id,
            data,
            num_readers,
            pub_seq,
            gate,
            server_token: Tracked(server_token),
            state_inv,
        };
        assert(r.inv());
        r
    }

    // -----------------------------------------------------------------------------------------
    // 5.4: the two protocols -- `observe` (no validation) and `validate` (the seqlock check)
    // -----------------------------------------------------------------------------------------
    /// Pins the current published snapshot, copies its `Copy` exec fields and duplicates its
    /// ghost witnesses, then **unpins before returning** -- a future reader/writer never holds an
    /// `EpochGuard` across the `pub_seq` load (`validate`) or a publish (`write`), matching design
    /// doc section 5.4's "never hold a guard across the CAS or the publish".
    #[allow(dead_code)]
    fn observe(&self, ridx: usize) -> (r: Observed)
        requires
            self.inv(),
            ridx < self.data.num_readers(),
        ensures
            r.inv(self.ids@),
    {
        proof {
            use_type_invariant(self);
        }
        let guard = self.data.pin(ridx);
        let snap = guard.get_ref();
        let value = snap.value;
        let timestamp = snap.timestamp;
        let seq = snap.seq;
        let tracked lb;
        let tracked commitment;
        let tracked ledger_frag;
        proof {
            assert(snapshot_inv(self.ids@, *snap));
            lb = snap.lb.borrow().extract_lower_bound();
            commitment = snap.commitment.borrow().duplicate();
            ledger_frag = snap.ledger_frag.borrow().duplicate();
        }
        guard.unpin();
        Observed {
            value,
            timestamp,
            seq,
            lb: Tracked(lb),
            commitment: Tracked(commitment),
            ledger_frag: Tracked(ledger_frag),
        }
    }

    /// The seqlock-style linearization check (design doc section 3): does the ledger's entry for
    /// `obs_seq` (carried in by the caller's snapshot fragment) still agree with `pub_seq`'s
    /// *current* exec value? If so, `obs_ts` was the authoritative timestamp at the instant of
    /// this load, and the caller's lower bound can be validated against it. On a `false` return
    /// the caller must retry (a fresh publish landed between its `observe` and this call) --
    /// nothing here is a safety violation, only a missed race.
    #[allow(dead_code)]
    #[allow(unused_variables)]
    fn validate(
        &self,
        obs_seq: u64,
        obs_ts: Timestamp,
        Tracked(frag): Tracked<&GhostPersistentPointsTo<u64, Timestamp>>,
        req_lb: &mut Tracked<MonotonicTimestampResource>,
    ) -> (r: bool)
        requires
            self.inv(),
            frag.id() == self.ids@.ledger_id,
            frag.key() == obs_seq,
            frag.value() == obs_ts,
            old(req_lb)@.loc() == self.ids@.resource_loc,
            old(req_lb)@@ is LowerBound,
        ensures
            final(req_lb)@ == old(req_lb)@,
            r ==> old(req_lb)@@.timestamp() <= obs_ts,
    {
        proof {
            use_type_invariant(self);
        }
        // Work on a throwaway duplicate of the caller's lower bound, never on `req_lb` itself:
        // mutating `*req_lb` from inside an `atomic_with_ghost!` block does not propagate to
        // this function's own `final(req_lb)` postcondition (confirmed by testing -- a real
        // limitation of `#[verifier::invariant_block]`'s effect tracking across a re-borrowed
        // `&mut` *parameter*), matching why every other invariant-block call site in this
        // codebase (e.g. `MonotonicRegisterInner::write`, `register.rs`) only ever mutates a
        // freshly-owned local captured into the block, never a `&mut` parameter directly.
        // `req_lb` itself is never touched, so `final(req_lb)@ == old(req_lb)@` holds trivially,
        // and `dup_lb`'s timestamp equals `old(req_lb)`'s by construction (`extract_lower_bound`
        // is a non-mutating `&self` duplicate).
        let tracked mut dup_lb = req_lb.borrow().extract_lower_bound();
        let s =
            atomic_with_ghost!(&self.pub_seq => load(); update prev -> next; returning ret; ghost g => {
            // `atomic_inv` gives `g.ledger@[ret] == g.half@.timestamp()`; combined with the
            // fragment's own agreement below, `ret == obs_seq` is exactly what's needed to
            // conclude `g.half@.timestamp() == obs_ts`.
            g.ledger.lemma_lb_points_to(frag);
            dup_lb.lemma_lower_bound(&g.half);
            assert(ret == obs_seq ==> dup_lb@.timestamp() <= obs_ts);
        });
        s == obs_seq
    }

    // -----------------------------------------------------------------------------------------
    // 5.4: the two protocols -- `read` / `read_timestamp` (observe-validate retry loop)
    // -----------------------------------------------------------------------------------------
    /// Exactly `MonotonicRegister::read`'s contract (`register.rs`) with a leading `shard_idx`,
    /// so `RegisterStore` (a later phase) can forward to either backend uniformly.
    ///
    /// Extracts the request's lower bound once, then spins `observe` -> `validate` until a
    /// publish is caught mid-flight (design doc section 3's seqlock check returns `true`),
    /// building the `GetResponse` straight from that iteration's duplicated ghost witnesses:
    /// `Observed::inv` is exactly `GetResponse::new`'s five-clause `requires` (plus the ledger
    /// clauses `GetResponse::new` doesn't need), so that call discharges directly off `obs` and
    /// `self.inv()` -- no `req`/`servers()` reasoning needed for it at all. `req`/`servers()`
    /// reasoning is only needed for this function's own last two `ensures`, exactly mirroring
    /// `MonotonicRegisterInner::read`'s two identical `lemma_dom_correspondence` blocks around
    /// `server_lower_bound`.
    #[allow(unused_variables)]
    // The observe-validate retry loop below is liveness-only (design doc section 7 item 2,
    // matching `vlib::reclaim`'s own spin loops): it only fails to terminate under a sustained
    // stream of publishes landing exactly between this reader's `observe` and its `pub_seq`
    // load, never a safety concern.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn read(&self, shard_idx: usize, mut req: GetRequest) -> (r: GetResponse)
        requires
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
        ensures
            r.loc() == self.resource_loc(),
            r.server_id() == self.id(),
            r.spec_commitment().id() == self.commitment_id(),
            r.server_token_id() == self.server_token_id(),
            req.servers().contains_key(r.server_id()),
            req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp(),
    {
        proof {
            use_type_invariant(self);
        }
        // `shard_idx` only ever selects a reader slot for liveness (two shards sharing one
        // `reader_idx` only spin against each other -- see `EpochGuard::inv`'s per-`(slot,
        // reader_idx)` stash cell -- never a safety concern). Reducing it here, rather than
        // tying `Server::spec_num_shards()` to `data.num_readers()` at the spec level, is what
        // lets `new` take a plain `usize` -- see `EpochMonotonicRegister::inv` and design doc
        // section 5.3. Construction passes the same thread count to both, so in practice every
        // shard gets its own reader slot.
        let ridx = shard_idx % self.num_readers;

        proof {
            req.servers().lemma_dom_correspondence();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
        }
        let lb = req.server_lower_bound(Ghost(self.id()));
        proof {
            req.servers().lemma_dom_correspondence();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
        }
        let Tracked(t_lb) = lb;
        let mut req_lb = Tracked(t_lb);

        // The response is built *inside* the loop (it needs that iteration's `obs`), but
        // `return`ing it directly from there would state this function's own `ensures` --
        // which mentions `req`, mutated *before* the loop by `server_lower_bound` above -- from
        // inside the loop's own spun-off verification context, where `req` (a "modified before
        // the loop" parameter) is deliberately re-havoced and reconstrained by the loop's own
        // `invariant` alone (see Verus's `loop_isolation`). The loop's own `ensures` clause
        // below is exactly the bridge for this: it is asserted at `break` time (inside that same
        // spun-off context, so it sees everything this iteration established) and then handed
        // back to *this* function's normal context after the loop, where `req` is unaffected by
        // the loop's isolation boundary at all. `resp_opt` itself carries no proof weight beyond
        // "was actually assigned"; all its content comes from the `ensures` clause.
        #[allow(unused_assignments)]
        let mut resp_opt: Option<GetResponse> = None;
        loop
            invariant
                ridx < self.data.num_readers(),
                req.servers().contains_key(self.id()),
                req_lb@.loc() == self.resource_loc(),
                req_lb@@ is LowerBound,
                req_lb@@.timestamp() == req.servers()[self.id()]@@.timestamp(),
            ensures
                resp_opt is Some,
                ({
                    let r = resp_opt->Some_0;
                    &&& r.loc() == self.resource_loc()
                    &&& r.server_id() == self.id()
                    &&& r.spec_commitment().id() == self.commitment_id()
                    &&& r.server_token_id() == self.server_token_id()
                    &&& req.servers().contains_key(r.server_id())
                    &&& req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp()
                }),
        {
            proof {
                use_type_invariant(self);
            }
            let obs = self.observe(ridx);
            let ok = self.validate(
                obs.seq,
                obs.timestamp,
                Tracked(obs.ledger_frag.borrow()),
                &mut req_lb,
            );
            if ok {
                proof {
                    use_type_invariant(self);
                    assert(req.servers().contains_key(self.id()));
                    assert(req.servers()[self.id()]@@.timestamp() <= obs.timestamp);
                }
                let tracked server_token = self.server_token.borrow().duplicate();
                proof {
                    assert(server_token.key() == self.id());
                }
                let resp = GetResponse::new(
                    obs.value,
                    obs.timestamp,
                    obs.lb,
                    obs.commitment,
                    Tracked(server_token),
                );
                resp_opt = Some(resp);
                break;
            }
        }
        resp_opt.unwrap()
    }

    /// Exactly `MonotonicRegister::read_timestamp`'s contract (`register.rs`) with a leading
    /// `shard_idx` -- see `read`'s doc comment above, which this mirrors verbatim minus the
    /// value/commitment fields `GetTimestampResponse` doesn't carry.
    #[allow(unused_variables)]
    // See `read`'s identical comment: liveness-only retry loop below.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn read_timestamp(&self, shard_idx: usize, mut req: GetTimestampRequest) -> (r:
        GetTimestampResponse)
        requires
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
        ensures
            r.loc() == self.resource_loc(),
            r.server_id() == self.id(),
            r.server_token_id() == self.server_token_id(),
            req.servers().contains_key(r.server_id()),
            req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp(),
    {
        proof {
            use_type_invariant(self);
        }
        // See `read`'s identical comment: liveness only, never a safety concern.
        let ridx = shard_idx % self.num_readers;

        proof {
            req.servers().lemma_dom_correspondence();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
        }
        let lb = req.server_lower_bound(Ghost(self.id()));
        proof {
            req.servers().lemma_dom_correspondence();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
        }
        let Tracked(t_lb) = lb;
        let mut req_lb = Tracked(t_lb);

        // See `read`'s identical comment: the response is built inside the loop but must not
        // be `return`ed from there directly, since this function's own `ensures` mentions
        // `req` -- mutated *before* the loop -- which the loop's own spun-off verification
        // context re-havocs per Verus's `loop_isolation`. The loop's own `ensures` bridges
        // this back into the normal (non-isolated) context after the loop.
        #[allow(unused_assignments)]
        let mut resp_opt: Option<GetTimestampResponse> = None;
        loop
            invariant
                ridx < self.data.num_readers(),
                req.servers().contains_key(self.id()),
                req_lb@.loc() == self.resource_loc(),
                req_lb@@ is LowerBound,
                req_lb@@.timestamp() == req.servers()[self.id()]@@.timestamp(),
            ensures
                resp_opt is Some,
                ({
                    let r = resp_opt->Some_0;
                    &&& r.loc() == self.resource_loc()
                    &&& r.server_id() == self.id()
                    &&& r.server_token_id() == self.server_token_id()
                    &&& req.servers().contains_key(r.server_id())
                    &&& req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp()
                }),
        {
            proof {
                use_type_invariant(self);
            }
            let obs = self.observe(ridx);
            let ok = self.validate(
                obs.seq,
                obs.timestamp,
                Tracked(obs.ledger_frag.borrow()),
                &mut req_lb,
            );
            if ok {
                proof {
                    use_type_invariant(self);
                    assert(req.servers().contains_key(self.id()));
                    assert(req.servers()[self.id()]@@.timestamp() <= obs.timestamp);
                }
                let tracked server_token = self.server_token.borrow().duplicate();
                let resp = GetTimestampResponse::new(obs.timestamp, obs.lb, Tracked(server_token));
                resp_opt = Some(resp);
                break;
            }
        }
        resp_opt.unwrap()
    }

    // -----------------------------------------------------------------------------------------
    // 5.4: the two protocols -- `write` (observe-validate, then the nested-open CAS on `pub_seq`)
    // -----------------------------------------------------------------------------------------
    /// Exactly `MonotonicRegister::write`'s contract (`register.rs`) with a leading `shard_idx`.
    ///
    /// `req.destruct(self.id)` consumes `req` once, up front -- unlike `read`/`read_timestamp`'s
    /// `mut req: GetRequest` (mutated in place via `&mut`, so it stays alive and referenceable
    /// through their retry loop), `req` here is fully moved-from and cannot be named again
    /// anywhere past that call, in *any* mode (a plain ownership fact, not a proof one). So
    /// everything this function's own `ensures` needs about `req` -- its timestamp and its
    /// per-server lower bound -- is pinned into plain locals (`req_ts`) and a ghost snapshot
    /// (`orig_lb_ts`) right there, in the same straight-line, non-isolated context
    /// `destruct`'s own postcondition is established in (exactly where `MonotonicRegisterInner
    /// ::write` itself relies on it, with no loop at all). The retry loop below is then stated,
    /// invariant *and* its own bridging `ensures`, purely in terms of those locals -- never
    /// `req` -- and built into `resp_opt`/`break` exactly like `read`/`read_timestamp`'s identical
    /// bridge (loop-isolation havocs params "modified" before a loop; see design doc section 10
    /// and `claude-files/backend_switch_questions.md` Q2). Only *after* the loop, back in the
    /// ordinary context, are `req_ts`/`orig_lb_ts` reconnected to `req` to discharge this
    /// function's real postcondition.
    ///
    /// Acquires the writer-serialization gate (design doc section 5.4 item 2) before the retry
    /// loop and releases it on every exit -- a plain CAS spin with **no** ghost payload (see
    /// `GateTrivialPred` and this module's top-of-file docs): it proves nothing about exclusivity,
    /// it only keeps publication order matching advance order. The CAS on `pub_seq` inside the
    /// loop is the actual mutual-exclusion argument (design doc section 5.4 item 2), and its ghost
    /// block lifts `MonotonicRegisterInner::write`'s existing proof (`register.rs`) verbatim, with
    /// `r := g.half` and `timestamp := req_ts`, preceded by one new step: connecting the
    /// observation's ledger fragment to `g.half`'s *current* timestamp (design doc section 5.4
    /// item 2's "ledger agreement").
    #[allow(unused_variables)]
    // Both loops below (the gate-acquire spin and the observe-validate-CAS retry) are
    // liveness-only, matching `read`/`read_timestamp` and `vlib::reclaim`'s own spin loops (design
    // doc section 7 items 1/2): the gate spin only fails to terminate if another writer holds it
    // forever, and the retry loop only fails to terminate under a sustained stream of publishes
    // landing exactly between this writer's `observe` and its CAS.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn write(&self, shard_idx: usize, req: WriteRequest) -> (r: WriteResponse)
        requires
            req.servers().locs().contains_key(self.id()),
            req.servers().locs()[self.id()] == self.resource_loc(),
            req.commitment_id() == self.commitment_id(),
        ensures
            r.loc() == self.resource_loc(),
            r.server_id() == self.id(),
            r.server_token_id() == self.server_token_id(),
            req.servers().contains_key(r.server_id()),
            req.servers()[r.server_id()]@@.timestamp() <= r.spec_timestamp(),
            req.spec_timestamp() <= r.spec_timestamp(),
    {
        proof {
            use_type_invariant(self);
        }
        // See `read`'s identical comment: liveness only.
        let ridx = shard_idx % self.num_readers;

        proof {
            req.servers().lemma_dom_correspondence();
            assert(req.servers().dom().contains(self.id()));
            assert(req.servers().contains_key(self.id()));
        }
        let (value, req_ts, commitment, mut req_lb) = req.destruct(self.id);

        // Pin everything the function's own `ensures` -- and the eventual published snapshot's
        // `snapshot_inv` -- needs about `req` *here* -- `req` is dead (moved-from) from this
        // point on; see this function's doc comment. `commitment`'s facts need the exact same
        // treatment as `req_ts`/`orig_lb_ts`: unlike `lb`/`ledger_frag` (whose `snapshot_inv`
        // clauses trace back only to `self`/`obs`/the CAS block's own reasoning), `commitment`'s
        // clauses trace back to `req` via `destruct`'s postcondition, so without pinning them
        // here the same "modified-before-the-loop" havoc that necessitated this pattern in the
        // first place (design doc section 10; `backend_switch_questions.md` Q2) erases them by
        // the time the success branch, deep inside the loop, needs them.
        let ghost orig_lb_ts = req_lb@@.timestamp();
        proof {
            assert(req_ts == req.spec_timestamp());
            assert(req_lb@@ == req.servers()[self.id()]@@);
            assert(orig_lb_ts == req.servers()[self.id()]@@.timestamp());
            assert(commitment@.id() == self.ids@.commitment_id);
            assert(commitment@.key() == req_ts);
            assert(commitment@.value() == value);
        }

        // Acquire the writer-serialization gate: a plain CAS spin, no ghost payload -- see this
        // function's doc comment and design doc section 5.4 item 2.
        loop {
            proof {
                use_type_invariant(self);
            }
            let got =
                atomic_with_ghost!(&self.gate => compare_exchange(false, true);
                update prev -> next; returning ret; ghost g => { });
            if got.is_ok() {
                break;
            }
        }

        // See `read`'s identical comment for why the response is built into `resp_opt` and
        // `break`-ed out of the loop rather than `return`-ed directly, and this function's own
        // doc comment for why the loop's `invariant`/`ensures` below name `req_ts`/`orig_lb_ts`
        // rather than `req` itself.
        #[allow(unused_assignments)]
        let mut resp_opt: Option<WriteResponse> = None;
        loop
            invariant
                ridx < self.data.num_readers(),
                req_lb@.loc() == self.resource_loc(),
                req_lb@@ is LowerBound,
                req_lb@@.timestamp() == orig_lb_ts,
                // `commitment` (a `tracked` value, unlike the plain `Ghost` locals above) needs
                // its own facts restated here for the same reason `req_lb`'s do: read purely
                // inside the success branch below otherwise isn't enough to carry them there --
                // confirmed empirically (the three asserts right after `snap` is built failed
                // without this, even with the identical facts already pinned right after
                // `destruct`, above).
                commitment@.id() == self.ids@.commitment_id,
                commitment@.key() == req_ts,
                commitment@.value() == value,
            ensures
                resp_opt is Some,
                ({
                    let r = resp_opt->Some_0;
                    &&& r.loc() == self.resource_loc()
                    &&& r.server_id() == self.id()
                    &&& r.server_token_id() == self.server_token_id()
                    &&& orig_lb_ts <= r.spec_timestamp()
                    &&& req_ts <= r.spec_timestamp()
                }),
        {
            proof {
                use_type_invariant(self);
            }
            let obs = self.observe(ridx);
            let ok = self.validate(
                obs.seq,
                obs.timestamp,
                Tracked(obs.ledger_frag.borrow()),
                &mut req_lb,
            );
            if !ok {
                continue;
            }
            if req_ts <= obs.timestamp {
                // No advance needed: `obs.lb` is `LowerBound{obs.timestamp}` and `validate` just
                // gave `orig_lb_ts <= obs.timestamp` -- both of `write`'s timestamp-facing
                // postconditions hold off the observation alone; nothing is published.
                proof {
                    use_type_invariant(self);
                }
                let tracked server_token = self.server_token.borrow().duplicate();
                resp_opt = Some(WriteResponse::new(obs.lb, Tracked(server_token)));
                break;
            }
            // `obs.seq + 1` must not overflow -- design doc section 7 item 1: the exec guard
            // degrades to an unproductive spin after 2^64 writes (~584 years at 10^9 writes/s)
            // rather than needing an `assume`. Not a trust escape; do not replace with one.

            if obs.seq == u64::MAX {
                continue;
            }
            // A plain exec local, not `obs.seq + 1` written out at each use site: referencing an
            // exec `u64` field in an arithmetic expression from *inside* a ghost/proof block (as
            // `g.ledger.insert` below needs) infers the literal `1`'s `int` type onto the whole
            // sum instead of `u64`, since nothing there pins it back down. Binding it once, here,
            // in plain exec code, fixes the type before any ghost code sees it.

            let next_seq = obs.seq + 1;

            // Fresh each iteration -- populated inside the CAS's ghost block below (only on the
            // `prev == obs.seq` branch) and `tracked_unwrap`ped outside, after the block closes,
            // never carried through a separate `match` on the macro's exec result (the E0382
            // hazard design doc section 5.4 item 3 warns about).

            let tracked mut new_frag: Option<GhostPersistentPointsTo<u64, Timestamp>> = None;
            let tracked mut new_lb: Option<MonotonicTimestampResource> = None;

            // Nesting is legal and load-bearing (design doc section 5.4 item 1): `state_inv`'s
            // namespace is 1, every `atomic_ghost` atomic (here, `pub_seq`) uses namespace 0, and
            // the outer open contains exactly one atomic op -- the CAS. All of the
            // `state.servers` bookkeeping below happens inside the CAS's own ghost block, on the
            // `prev == obs.seq` branch only, so the CAS-failure branch touches `state` not at all.
            let cas: Result<u64, u64>;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                cas = atomic_with_ghost!(&self.pub_seq => compare_exchange(obs.seq, next_seq);
                    update prev -> next; returning ret; ghost g => {
                        if prev == obs.seq {
                            // Ledger agreement: `atomic_inv` (assumed here, with `v := prev ==
                            // obs.seq`) gives `g.ledger@[obs.seq] == g.half@.timestamp()`;
                            // combined with the observation's own fragment (`obs.ledger_frag`),
                            // that pins `g.half@.timestamp() == obs.timestamp` -- the fact that
                            // makes `advance_halves`'s `new_value > old(self)@.timestamp()`
                            // precondition (with `new_value := req_ts`) exactly this iteration's
                            // own `req_ts > obs.timestamp` check above.
                            g.ledger.lemma_lb_points_to(obs.ledger_frag.borrow());
                            assert(g.half@.timestamp() == obs.timestamp);

                            // ---- lifted verbatim from `MonotonicRegisterInner::write`
                            // ---- (`register.rs`), with `r := g.half`, `timestamp := req_ts`.
                            let ghost old_servers = state.servers;
                            state.servers.lemma_inv();
                            assert(state.server_tokens@ <= old_servers.locs());
                            assert(old_servers.locs().dom() == old_servers.dom());

                            state.server_tokens.lemma_lb_points_to(self.server_token.borrow());
                            let ghost server_id = self.server_token@.key();
                            assert(old_servers.locs().contains_key(server_id));
                            assert(state.servers.locs().contains_key(server_id));
                            assert(old_servers.dom().contains(server_id));
                            assert(old_servers.contains_key(server_id));
                            assert(old_servers[server_id]@.loc() == old_servers.locs()[server_id]);
                            assert(g.half.loc() == old_servers.locs()[server_id]);

                            let tracked mut other_half =
                                state.servers.tracked_remove_auth(server_id);
                            let ghost unchanged_servers = state.servers;
                            state.servers.lemma_inv();
                            assert(!unchanged_servers.dom().contains(server_id));
                            g.half.lemma_halves_agree(&other_half);
                            g.half.advance_halves(&mut other_half, req_ts);
                            state.servers.tracked_insert_auth(server_id, other_half);
                            state.servers.lemma_inv();

                            assert(old_servers.leq(state.servers)) by {
                                assert(old_servers.locs() == state.servers.locs());
                                assert forall |id| #[trigger] old_servers.contains_key(id)
                                    implies state.servers[id]@@.timestamp()
                                        >= old_servers[id]@@.timestamp() by {
                                    if id != server_id {
                                        assert(old_servers.dom().contains(id));
                                        assert(unchanged_servers.dom().contains(id));
                                        assert(unchanged_servers.contains_key(id)); // TRIGGER
                                        assert(state.servers.dom().contains(id));
                                    }
                                }
                            }
                            assert forall |id: u64| #[trigger]
                                state.unclaimed_servers().contains(id)
                                implies state.servers[id]@@ is FullRightToAdvance by {
                                assert(state.servers.dom().contains(id));
                                if id != server_id {
                                    assert(unchanged_servers.dom().contains(id));
                                    assert(unchanged_servers.contains_key(id));
                                }
                            }
                            assert forall |id: u64| #[trigger]
                                state.server_tokens@.contains_key(id)
                                implies state.servers[id]@@ is HalfRightToAdvance by {
                                assert(old_servers.locs().contains_key(id));
                                assert(old_servers.dom().contains(id));
                                assert(state.servers.dom().contains(id));
                                if id != server_id {
                                    assert(unchanged_servers.dom().contains(id));
                                    assert(unchanged_servers.contains_key(id));
                                }
                            }
                            old_servers.lemma_leq_quorums(
                                state.servers,
                                state.linearization_queue.watermark(),
                            );
                            assert(state.inv());

                            new_frag = Some(g.ledger.insert(next_seq, req_ts));
                            new_lb = Some(g.half.extract_lower_bound());
                        }
                        // failure branch (`prev != obs.seq`): `state` untouched above, so
                        // `state.inv()` is trivially preserved, and `new_frag`/`new_lb` stay
                        // `None`.
                    });
            });

            match cas {
                Ok(_) => {
                    proof {
                        use_type_invariant(self);
                    }
                    assert(new_frag is Some);
                    assert(new_lb is Some);
                    let tracked frag = new_frag.tracked_unwrap();
                    let tracked lb_val = new_lb.tracked_unwrap();
                    let tracked snap_lb = lb_val.extract_lower_bound();
                    let tracked server_token = self.server_token.borrow().duplicate();
                    let tracked snap_commitment = commitment.borrow().duplicate();
                    let snap = RegisterSnapshot {
                        value,
                        timestamp: req_ts,
                        seq: next_seq,
                        lb: Tracked(snap_lb),
                        commitment: Tracked(snap_commitment),
                        ledger_frag: Tracked(frag),
                    };
                    assert(snapshot_inv(self.ids@, snap));
                    // Publish only after the invariant above has closed -- `EpochAtomicPtr::write`
                    // opens namespace-0 invariants itself, and no `EpochGuard` is held here (see
                    // `observe`'s doc comment: it always `unpin()`s before returning).
                    self.data.write(snap);
                    resp_opt = Some(WriteResponse::new(Tracked(lb_val), Tracked(server_token)));
                    break;
                },
                Err(_) => {
                    continue;
                },
            }
        }
        let resp = resp_opt.unwrap();
        atomic_with_ghost!(&self.gate => store(false); update prev -> next; ghost g => { });
        resp
    }

    /// Forwards to `EpochAtomicPtr::reclaim_pass` -- see its doc comment. Meant to be called
    /// periodically from a dedicated background thread (via `Service::background_tick`, wired up
    /// through `RegisterStore`/`RegisterService` in `server/mod.rs`), so that `write`'s own
    /// `claim_and_install` -- reached through `self.data.write` above -- finds slots already idle
    /// instead of having to drain+spin for one inline.
    pub fn reclaim_pass(&self) {
        self.data.reclaim_pass();
    }
}

} // verus!
