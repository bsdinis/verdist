//! Ghost resource for a monotonically-advancing epoch counter, used by epoch-based
//! reclamation (EBR). This mirrors `abd::resource::monotonic_timestamp::MonotonicTimestampResource`
//! exactly, generalized from a domain `Timestamp` to a plain `nat`, so that it can be reused
//! outside of `abd`.
//!
//! This module intentionally contains *only* the ghost/proof-only resource for now: the
//! physical `AtomicU64`-backed `EpochGlobal` wrapper that pairs a real counter with this
//! resource is deferred, because `vstd`'s verified `fetch_add` requires proving the counter
//! never overflows `u64::MAX` -- a bound that can't be discharged forever for an
//! unconditionally-incrementing counter. That's a real design decision (e.g. switch to
//! `fetch_add_wrapping` plus a "physical value == ghost epoch mod 2^64" invariant, at the cost
//! of needing wraparound-aware comparisons wherever epochs are compared) that should be made
//! explicitly rather than folded in here silently.
use vstd::resource::algebra::ResourceAlgebra;
#[cfg(verus_only)]
use vstd::resource::copy_duplicable_part;
use vstd::resource::pcm::Resource;
use vstd::resource::pcm::PCM;
#[cfg(verus_only)]
use vstd::resource::update_and_redistribute;
#[cfg(verus_only)]
use vstd::resource::update_mut;
use vstd::resource::Loc;

use vstd::prelude::*;

verus! {

// An epoch resource represents a resource with one of the following values:
//
// `LowerBound{ lower_bound }` -- knowledge that the epoch is at least `lower_bound`
//
// `FullRightToAdvance{ value }` -- knowledge that the epoch is exactly `value` and
// the authority to advance it past that value
#[allow(dead_code)]
pub tracked enum EpochResourceValue {
    LowerBound { lower_bound: nat },
    FullRightToAdvance { value: nat },
    HalfRightToAdvance { value: nat },
    Invalid,
}

impl ResourceAlgebra for EpochResourceValue {
    open spec fn valid(self) -> bool {
        !(self is Invalid)
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            // Two lower bounds can be combined into a lower bound
            // that's the maximum of the two lower bounds.
            (
                EpochResourceValue::LowerBound { lower_bound: lower_bound1 },
                EpochResourceValue::LowerBound { lower_bound: lower_bound2 },
            ) => {
                let max_lower_bound = if lower_bound1 > lower_bound2 {
                    lower_bound1
                } else {
                    lower_bound2
                };
                EpochResourceValue::LowerBound { lower_bound: max_lower_bound }
            },
            // A lower bound can be combined with a right to
            // advance as long as the lower bound doesn't exceed
            // the value in the right to advance.
            // full
            (
                EpochResourceValue::LowerBound { lower_bound },
                EpochResourceValue::FullRightToAdvance { value },
            ) => if lower_bound <= value {
                EpochResourceValue::FullRightToAdvance { value }
            } else {
                EpochResourceValue::Invalid {  }
            },
            (
                EpochResourceValue::FullRightToAdvance { value },
                EpochResourceValue::LowerBound { lower_bound },
            ) => if lower_bound <= value {
                EpochResourceValue::FullRightToAdvance { value }
            } else {
                EpochResourceValue::Invalid {  }
            },
            // half
            (
                EpochResourceValue::LowerBound { lower_bound },
                EpochResourceValue::HalfRightToAdvance { value },
            ) => if lower_bound <= value {
                EpochResourceValue::HalfRightToAdvance { value }
            } else {
                EpochResourceValue::Invalid {  }
            },
            (
                EpochResourceValue::HalfRightToAdvance { value },
                EpochResourceValue::LowerBound { lower_bound },
            ) => if lower_bound <= value {
                EpochResourceValue::HalfRightToAdvance { value }
            } else {
                EpochResourceValue::Invalid {  }
            },
            // Two half rights to advance can be combined into a full right to advance
            // iff they agree on the value
            (
                EpochResourceValue::HalfRightToAdvance { value: lvalue },
                EpochResourceValue::HalfRightToAdvance { value: rvalue },
            ) => if lvalue == rvalue {
                EpochResourceValue::FullRightToAdvance { value: lvalue }
            } else {
                EpochResourceValue::Invalid {  }
            },
            // Any other combination is invalid
            (_, _) => EpochResourceValue::Invalid {  },
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl PCM for EpochResourceValue {
    open spec fn unit() -> Self {
        EpochResourceValue::LowerBound { lower_bound: 0 }
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

impl EpochResourceValue {
    pub open spec fn epoch(self) -> nat {
        match self {
            EpochResourceValue::LowerBound { lower_bound } => lower_bound,
            EpochResourceValue::FullRightToAdvance { value } => value,
            EpochResourceValue::HalfRightToAdvance { value } => value,
            EpochResourceValue::Invalid => 0,
        }
    }
}

#[allow(dead_code)]
pub struct EpochResource {
    r: Resource<EpochResourceValue>,
}

impl EpochResource {
    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> EpochResourceValue {
        self.r.value()
    }

    // Creates a new epoch counter, returning full authority to advance it and
    // knowledge that its current value is 0.
    pub proof fn alloc() -> (tracked result: Self)
        ensures
            result@ == (EpochResourceValue::FullRightToAdvance { value: 0 }),
    {
        let v = EpochResourceValue::FullRightToAdvance { value: 0 };
        let tracked r = Resource::<EpochResourceValue>::alloc(v);
        Self { r }
    }

    // Join two resources
    pub proof fn join(tracked self: Self, tracked other: Self) -> (tracked r: Self)
        requires
            self.loc() == other.loc(),
            self@.epoch() == other@.epoch(),
        ensures
            r.loc() == self.loc(),
            r@.epoch() == EpochResourceValue::op(self@, other@).epoch(),
    {
        let tracked r = self.r.join(other.r);
        Self { r }
    }

    // Split a full authority into two halves
    pub proof fn split(tracked self) -> (tracked r: (Self, Self))
        requires
            self@ is FullRightToAdvance,
        ensures
            r.0.loc() == self.loc(),
            r.1.loc() == self.loc(),
            r.0@.epoch() == self@.epoch(),
            r.1@.epoch() == self@.epoch(),
            r.0@ is HalfRightToAdvance,
            r.1@ is HalfRightToAdvance,
    {
        let half = EpochResourceValue::HalfRightToAdvance {
            value: self@->FullRightToAdvance_value,
        };
        let tracked (left, right) = self.r.split(half, half);
        (EpochResource { r: left }, EpochResource { r: right })
    }

    // Uses a resource granting full authority to advance the epoch to advance it
    // to a strictly greater value.
    pub proof fn advance(tracked &mut self, new_value: nat)
        requires
            old(self)@ is FullRightToAdvance,
            new_value > old(self)@.epoch(),
        ensures
            final(self).loc() == old(self).loc(),
            final(self)@ == (EpochResourceValue::FullRightToAdvance { value: new_value }),
    {
        let r = EpochResourceValue::FullRightToAdvance { value: new_value };
        update_mut(&mut self.r, r);
    }

    // Synchronized advance for two owners of matching halves.
    pub proof fn advance_halves(tracked &mut self, tracked other: &mut Self, new_value: nat)
        requires
            old(self).loc() == old(other).loc(),
            old(self)@ is HalfRightToAdvance,
            old(other)@ is HalfRightToAdvance,
            new_value > old(self)@.epoch(),
        ensures
            final(self).loc() == old(self).loc(),
            final(other).loc() == old(other).loc(),
            final(self)@.epoch() == new_value,
            final(other)@.epoch() == new_value,
            final(self)@ is HalfRightToAdvance,
            final(other)@ is HalfRightToAdvance,
    {
        self.r.validate_2(&other.r);
        let updated = EpochResourceValue::HalfRightToAdvance { value: new_value };
        update_and_redistribute(&mut self.r, &mut other.r, updated, updated);
    }

    pub proof fn extract_lower_bound(tracked &self) -> (tracked out: Self)
        ensures
            out@ is LowerBound,
            out.loc() == self.loc(),
            out@ == (EpochResourceValue::LowerBound { lower_bound: self@.epoch() }),
    {
        self.r.validate();
        let v = EpochResourceValue::LowerBound { lower_bound: self@.epoch() };
        let tracked r = copy_duplicable_part(&self.r, v);
        Self { r }
    }

    pub proof fn lemma_lower_bound(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            final(self)@ == old(self)@,
            final(self).loc() == old(self).loc(),
            final(self)@ is LowerBound && other@ is FullRightToAdvance ==> final(self)@.epoch()
                <= other@.epoch(),
            other@ is LowerBound && final(self)@ is FullRightToAdvance ==> other@.epoch()
                <= final(self)@.epoch(),
            final(self)@ is LowerBound && other@ is HalfRightToAdvance ==> final(self)@.epoch()
                <= other@.epoch(),
            other@ is LowerBound && final(self)@ is HalfRightToAdvance ==> other@.epoch()
                <= final(self)@.epoch(),
    {
        self.r.validate_2(&other.r)
    }

    pub proof fn lemma_halves_agree(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
            old(self)@ is HalfRightToAdvance,
            other@ is HalfRightToAdvance,
        ensures
            final(self).loc() == old(self).loc(),
            final(self)@ == old(self)@,
            final(self)@.epoch() == other@.epoch(),
    {
        self.r.validate_2(&other.r)
    }

    pub proof fn weaken(tracked &self, target: nat) -> (tracked out: Self)
        requires
            self@ is LowerBound,
            self@.epoch() >= target,
        ensures
            out.loc() == self.loc(),
            out@ is LowerBound,
            out@.epoch() == target,
    {
        let r_target = EpochResourceValue::LowerBound { lower_bound: target };
        assert(EpochResourceValue::op(r_target, self@) == self@);
        let tracked r = self.r.duplicate_previous(r_target);
        EpochResource { r }
    }
}

// The physical epoch counter wraps at 2^64. The ghost `EpochResource` epoch is an
// unbounded `nat` that never wraps; the invariant ties the two together as
// `ghost epoch mod 2^64 == physical value`, so the ghost side can keep advancing
// forever while the physical `AtomicU64` wraps normally (exactly like a TCP sequence
// number or `jiffies`). Comparing epochs across a wraparound needs wraparound-aware
// (serial-number-style) comparison wherever that happens -- deferred to the reader-slot /
// collector design (steps 2-3), which is the reason this file stops at a bare counter.
pub open spec fn epoch_modulus() -> nat {
    (u64::MAX as nat) + 1
}

pub struct EpochGlobalPred;

// `K = Loc` (the resource's own location) rather than `()`: this lets a `ReaderSlot`
// (added in a later step) statically pin itself to *this specific* `EpochGlobal` instance
// via `EpochGlobal::loc()`, rather than being tied to an arbitrary/unrelated counter.
impl vstd::atomic_ghost::AtomicInvariantPredicate<Loc, u64, EpochResource> for EpochGlobalPred {
    open spec fn atomic_inv(k: Loc, v: u64, g: EpochResource) -> bool {
        &&& g@ is FullRightToAdvance
        &&& g@.epoch() % epoch_modulus() == v as nat
        &&& g.loc() == k
    }
}

pub struct EpochGlobal {
    counter: vstd::atomic_ghost::AtomicU64<Loc, EpochResource, EpochGlobalPred>,
}

impl EpochGlobal {
    pub closed spec fn well_formed(&self) -> bool {
        self.counter.well_formed()
    }

    pub closed spec fn loc(&self) -> Loc {
        self.counter.constant()
    }

    pub fn new() -> (result: Self)
        ensures
            result.well_formed(),
    {
        let tracked r = EpochResource::alloc();
        let loc = Ghost(r.loc());
        proof {
            vstd::arithmetic::div_mod::lemma_small_mod(0, epoch_modulus());
        }
        let counter = vstd::atomic_ghost::AtomicU64::new(loc, 0, Tracked(r));
        EpochGlobal { counter }
    }

    // Returns the physical (wrapped) counter value. Only meaningful modulo 2^64 --
    // not a total order on its own once wraparound is in play.
    pub fn load(&self) -> (v: u64)
        requires
            self.well_formed(),
    {
        vstd::atomic_ghost::atomic_with_ghost!(&self.counter => load(); ghost g => {})
    }

    // Advances the logical epoch by 1 and returns the new physical (wrapped) value.
    pub fn advance(&self) -> (new_val: u64)
        requires
            self.well_formed(),
    {
        vstd::atomic_ghost::atomic_with_ghost!(&self.counter => fetch_add_wrapping(1); ghost g => {
            vstd::arithmetic::div_mod::lemma_mod_adds(g@.epoch() as int, 1, epoch_modulus() as int);
            g.advance(g@.epoch() + 1);
        })
    }

    // Reads the current (wrapped) epoch together with a durable "epoch was >= this value at
    // some point" witness for that *exact* value, atomically -- so callers (e.g. `ReaderSlot::pin`)
    // don't race between a plain `load()` and a separate ghost extraction.
    pub fn current(&self) -> (result: (u64, Tracked<EpochResource>))
        requires
            self.well_formed(),
        ensures
            result.1@@ is LowerBound,
            result.1@@.epoch() % epoch_modulus() == result.0 as nat,
            result.1@.loc() == self.loc(),
    {
        let tracked mut lb_out = EpochResource::alloc();
        let v =
            vstd::atomic_ghost::atomic_with_ghost!(&self.counter => load(); ghost g => {
            lb_out = g.extract_lower_bound();
        });
        (v, Tracked(lb_out))
    }
}

impl Default for EpochGlobal {
    fn default() -> Self {
        Self::new()
    }
}

} // verus!
