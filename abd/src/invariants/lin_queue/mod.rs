#[cfg(verus_only)]
use crate::invariants::committed_to::WriteAllocation;
#[cfg(verus_only)]
use crate::invariants::committed_to::WriteCommitment;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

#[cfg(verus_only)]
use vstd::assert_by_contradiction;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::ghost_var::GhostVarAuth;
use vstd::resource::map::GhostMapAuth;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::map::GhostPointsTo;
use vstd::resource::Loc;
#[cfg(verus_only)]
use vstd::set_lib::*;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

mod completed;
mod maybe_lin;
mod pending;

pub use completed::CompletedRead;
pub use completed::CompletedWrite;
pub use maybe_lin::MaybeReadLinearized;
pub use maybe_lin::MaybeWriteLinearized;
pub use pending::PendingRead;
pub use pending::PendingWrite;

verus! {

pub tracked enum InsertError<ML, RL> {
    WriteWatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked w_watermark_lb: MonotonicTimestampResource,
        // Linearizer to return to user on error
        tracked w_lin: ML,
    },
    ReadWatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked r_watermark_lb: MonotonicTimestampResource,
        // Linearizer to return to user on error
        tracked r_lin: RL,
    },
}

impl<ML, RL> InsertError<ML, RL> {
    pub proof fn tracked_write_destruct(tracked self) -> (tracked r: ML)
        requires
            self is WriteWatermarkContradiction,
        ensures
            self->w_lin == r,
    {
        match self {
            InsertError::WriteWatermarkContradiction { w_lin, .. } => w_lin,
            _ => vstd::pervasive::proof_from_false(),
        }
    }

    pub proof fn tracked_read_destruct(tracked self) -> (tracked r: RL)
        requires
            self is ReadWatermarkContradiction,
        ensures
            self->r_lin == r,
    {
        match self {
            InsertError::ReadWatermarkContradiction { r_lin, .. } => r_lin,
            _ => vstd::pervasive::proof_from_false(),
        }
    }

    pub proof fn lower_bound(tracked self) -> (tracked r: MonotonicTimestampResource)
        requires
            ({
                ||| self is WriteWatermarkContradiction
                ||| self is ReadWatermarkContradiction
            }),
        ensures
            self is WriteWatermarkContradiction ==> r == self->w_watermark_lb,
            self is ReadWatermarkContradiction ==> r == self->r_watermark_lb,
    {
        match self {
            InsertError::WriteWatermarkContradiction { w_watermark_lb, .. } => w_watermark_lb,
            InsertError::ReadWatermarkContradiction { r_watermark_lb, .. } => r_watermark_lb,
        }
    }
}

#[allow(dead_code)]
pub struct LinearizationQueue<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    // commitment to values
    committed_to: GhostPersistentSubmap<Timestamp, Option<u64>>,
    // completed operations
    completed_writes: Map<Timestamp, CompletedWrite<ML>>,
    // completed operations
    completed_reads: Map<(Option<u64>, nat), CompletedRead<RL>>,
    // pending operations
    pending_writes: Map<Timestamp, PendingWrite<ML>>,
    // completed operations
    pending_reads: Map<(Option<u64>, nat), PendingRead<RL>>,
    // Why we need a token maps in addition to the completed + pending operations
    //
    // The values in the completed + pending are possibly all changed with apply_linearizer
    // This would require all Tokens to be passed, which is impossible
    write_token_map: GhostMapAuth<Timestamp, WriteTokenVal<ML>>,
    read_token_map: GhostMapAuth<(Option<u64>, nat), ReadTokenVal<RL>>,
    // counter for next read op
    next_read_op: nat,
    // everything up to the watermark is guaranteed to be applied
    watermark: MonotonicTimestampResource,
    // This is the register this lin queue refers to
    ghost register_id: Loc,
}

pub type LinWriteToken<ML> = GhostPointsTo<Timestamp, WriteTokenVal<ML>>;

pub type LinReadToken<RL> = GhostPointsTo<(Option<u64>, nat), ReadTokenVal<RL>>;

pub struct ReadTokenVal<RL> {
    pub ghost lin: RL,
    pub ghost op: RegisterRead,
    pub tracked min_ts: MonotonicTimestampResource,
}

pub struct WriteTokenVal<ML> {
    pub ghost lin: ML,
    pub ghost op: RegisterWrite,
    pub ghost committed: bool,
}

pub struct LinQueueIds {
    pub committed_to_id: Loc,
    pub write_token_map_id: Loc,
    pub read_token_map_id: Loc,
    pub watermark_id: Loc,
    pub register_id: Loc,
}

// Specs
impl<ML, RL> LinearizationQueue<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    // basic invariant
    // - always true, asserts facts that are always true
    pub closed spec fn basic_inv(&self) -> bool {
        &&& self.watermark@ is FullRightToAdvance
        &&& self.committed_to@.contains_key(self.watermark@.timestamp())
        &&& forall|ts: Timestamp| #[trigger]
            self.committed_to@.contains_key(ts) ==> ts <= self.watermark@.timestamp()
        &&& forall|ts: Timestamp| #[trigger]
            self.write_token_map@.contains_key(ts) && ts <= self.watermark@.timestamp()
                ==> self.committed_to@.contains_key(ts)
    }

    // full invariant over the write domain:
    //  1. the completed_writes + pending_writes match the write token domain
    //  2. everything below the watermark is completed, and matches the correct ids
    //  3. completed writes match the history
    //  4. everything above the watermark is pending and matches the correct ids
    pub closed spec fn write_dom_inv(&self) -> bool {
        &&& self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        )
        &&& self.completed_writes.dom() <= self.committed_to@.dom()
        &&& self.completed_writes.dom().disjoint(self.pending_writes.dom())
        &&& self.committed_to@.dom().disjoint(self.pending_writes.dom())
        &&& forall|ts: Timestamp| #[trigger]
            self.completed_writes.contains_key(ts) ==> {
                let comp = self.completed_writes[ts];
                &&& ts <= self.watermark@.timestamp()
                &&& self.committed_to@.contains_key(ts)
                &&& comp.timestamp() == ts
                &&& comp.value() == self.committed_to@[ts]
                &&& comp.lin() == self.write_token_map@[ts].lin
                &&& comp.op() == self.write_token_map@[ts].op
                &&& comp.commitment_id() == self.committed_to.id()
                &&& comp.register_id() == self.register_id
            }
        &&& forall|ts: Timestamp| #[trigger]
            self.pending_writes.contains_key(ts) ==> {
                let pending = self.pending_writes[ts];
                &&& ts > self.watermark@.timestamp()
                &&& pending.timestamp() == ts
                &&& pending.register_id() == self.register_id
                &&& pending.commitment_id() == self.committed_to.id()
                &&& pending.lin() == self.write_token_map@[ts].lin
                &&& pending.op() == self.write_token_map@[ts].op
                &&& pending.write_status() is Committed == self.write_token_map@[ts].committed
                &&& !pending.namespaces().contains(super::state_inv_id())
            }
    }

    pub closed spec fn read_dom_composition(&self) -> bool {
        &&& self.read_token_map@.dom() == self.completed_reads.dom().union(self.pending_reads.dom())
        &&& self.completed_reads.dom().disjoint(self.pending_reads.dom())
    }

    pub closed spec fn read_tok_inv(&self) -> bool {
        forall|key: (Option<u64>, nat)| #[trigger]
            self.read_token_map@.contains_key(key) ==> {
                let tok = self.read_token_map@[key];
                &&& key.1 < self.next_read_op
                &&& tok.min_ts.loc() == self.watermark.loc()
                &&& tok.min_ts@ is LowerBound
                &&& tok.min_ts@.timestamp() <= self.watermark@.timestamp()
            }
    }

    pub closed spec fn read_completed_inv(&self) -> bool {
        forall|key: (Option<u64>, nat)| #[trigger]
            self.completed_reads.contains_key(key) ==> {
                let comp = self.completed_reads[key];
                let token = self.read_token_map@[key];
                &&& self.committed_to@.contains_key(comp.timestamp())
                &&& comp.value() == key.0
                &&& comp.register_id() == self.register_id
                &&& comp.lin() == token.lin
                &&& comp.op() == token.op
                &&& token.min_ts@.timestamp() <= comp.timestamp()
                &&& comp.timestamp() <= self.watermark@.timestamp()
                &&& comp.value() == self.committed_to@[comp.timestamp()]
            }
    }

    // full invariant over the read domain:
    //  1. the completed_reads + pending_reads match the read token domain
    //  2. every read that has had the opportunity to linearize (i.e., there has appeared a write
    //     with the target value) has
    //  3. everything pending matches the correct ids
    pub closed spec fn read_dom_inv(&self) -> bool {
        self.read_dom_inv_param(false  /* weak */ )
    }

    // weak invariant over the read domain:
    //  1. the completed_reads + pending_reads match the read token domain
    //  2. every read that has had the opportunity to linearize strictly below the watermark (i.e., there has appeared a write
    //     with the target value) has
    //  3. everything pending matches the correct ids
    pub closed spec fn weak_read_dom_inv(&self) -> bool {
        self.read_dom_inv_param(true  /* weak */ )
    }

    pub closed spec fn read_dom_inv_param(&self, weak: bool) -> bool {
        &&& self.read_dom_composition()
        &&& self.read_tok_inv()
        &&& self.read_completed_inv()
        &&& forall|key: (Option<u64>, nat)| #[trigger]
            self.pending_reads.contains_key(key) ==> {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                &&& pending.value() == key.0
                &&& pending.lin() == token.lin
                &&& pending.op() == token.op
                &&& pending.register_id() == self.register_id
                &&& forall|ts: Timestamp|
                    {
                        &&& #[trigger] self.committed_to@.contains_key(ts)
                        &&& token.min_ts@.timestamp() <= ts
                        &&& (ts < self.watermark@.timestamp() || (!weak && ts
                            == self.watermark@.timestamp()))
                    } ==> { self.committed_to@[ts] != pending.value() }
                &&& !pending.namespaces().contains(super::state_inv_id())
            }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.basic_inv()
        &&& self.write_dom_inv()
        &&& self.read_dom_inv()
    }

    pub open spec fn ids(self) -> LinQueueIds {
        LinQueueIds {
            committed_to_id: self.committed_to_id(),
            write_token_map_id: self.write_token_id(),
            read_token_map_id: self.read_token_id(),
            watermark_id: self.watermark_id(),
            register_id: self.register_id(),
        }
    }

    pub closed spec fn committed_to_id(self) -> Loc {
        self.committed_to.id()
    }

    pub closed spec fn write_token_id(self) -> Loc {
        self.write_token_map.id()
    }

    pub closed spec fn read_token_id(self) -> Loc {
        self.read_token_map.id()
    }

    pub closed spec fn watermark_id(self) -> Loc {
        self.watermark.loc()
    }

    pub closed spec fn register_id(self) -> Loc {
        self.register_id
    }

    pub closed spec fn watermark(self) -> Timestamp
        recommends
            self.basic_inv(),
    {
        self.watermark@.timestamp()
    }

    pub closed spec fn current_value(self) -> Option<u64>
        recommends
            self.basic_inv(),
    {
        self.committed_to@[self.watermark@.timestamp()]
    }

    pub open spec fn known_timestamps(self) -> Set<Timestamp>
        recommends
            self.basic_inv(),
    {
        self.committed_values().dom().union(self.pending_writes().dom())
    }

    pub closed spec fn committed_values(self) -> Map<Timestamp, Option<u64>>
        recommends
            self.inv(),
    {
        self.committed_to@
    }

    pub closed spec fn outstanding_writes(self) -> Map<Timestamp, WriteTokenVal<ML>>
        recommends
            self.inv(),
    {
        self.write_token_map@
    }

    pub closed spec fn outstanding_reads(self) -> Map<(Option<u64>, nat), ReadTokenVal<RL>>
        recommends
            self.inv(),
    {
        self.read_token_map@
    }

    pub closed spec fn pending_writes(self) -> Map<Timestamp, PendingWrite<ML>>
        recommends
            self.inv(),
    {
        self.pending_writes
    }

    pub closed spec fn completed_writes(self) -> Map<Timestamp, CompletedWrite<ML>>
        recommends
            self.inv(),
    {
        self.completed_writes
    }

    pub closed spec fn pending_reads(self) -> Map<(Option<u64>, nat), PendingRead<RL>>
        recommends
            self.inv(),
    {
        self.pending_reads
    }

    pub closed spec fn completed_reads(self) -> Map<(Option<u64>, nat), CompletedRead<RL>>
        recommends
            self.inv(),
    {
        self.completed_reads
    }

    /// Show that if there is a lowerbound with the same id as the watermark it is <= the watermark
    pub proof fn lemma_watermark_lb(tracked &self, tracked lb: &mut MonotonicTimestampResource)
        requires
            self.inv(),
            old(lb)@ is LowerBound,
            old(lb).loc() == self.watermark_id(),
        ensures
            final(lb).loc() == old(lb).loc(),
            final(lb)@ == old(lb)@,
            final(lb)@.timestamp() <= self.watermark(),
    {
        lb.lemma_lower_bound(&self.watermark);
    }

    /// Show that if we have a write token for a key, then it exists
    pub proof fn lemma_write_token(tracked &self, tracked token: &LinWriteToken<ML>)
        requires
            self.inv(),
            token.id() == self.write_token_id(),
        ensures
            self.outstanding_writes().contains_pair(token.key(), token.value()),
            ({
                ||| self.pending_writes().contains_key(token.key())
                ||| self.completed_writes().contains_key(token.key())
            }),
    {
        token.agree(&self.write_token_map);
    }

    /// Show that if we have a read token for a key, then it exists
    pub proof fn lemma_read_token(tracked &self, tracked token: &LinReadToken<RL>)
        requires
            self.inv(),
            token.id() == self.read_token_id(),
        ensures
            self.outstanding_reads().contains_pair(token.key(), token.value()),
            ({
                ||| self.pending_reads().contains_key(token.key())
                ||| self.completed_reads().contains_key(token.key())
            }),
    {
        token.agree(&self.read_token_map);
    }

    /// Get the tracked submap that corresponds to the committed_values
    pub proof fn tracked_committed_values(tracked &self) -> (tracked r: &GhostPersistentSubmap<
        Timestamp,
        Option<u64>,
    >)
        requires
            self.inv(),
        ensures
            r.id() == self.committed_to_id(),
            r@ == self.committed_values(),
    {
        &self.committed_to
    }

    pub proof fn lemma_known_timestamps(self)
        requires
            self.inv(),
        ensures
            self.committed_values().dom() <= self.known_timestamps(),
            self.outstanding_writes().dom() <= self.known_timestamps(),
            self.pending_writes().dom() <= self.known_timestamps(),
            self.completed_writes().dom() <= self.known_timestamps(),
    {
    }
}

impl<ML, RL> LinearizationQueue<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub proof fn new(register_id: Loc, tracked zero_commitment: WriteCommitment) -> (tracked result:
        Self)
        requires
            zero_commitment.key() == Timestamp::spec_default(),
            zero_commitment.value() == None::<u64>,
        ensures
            result.inv(),
            result.register_id() == register_id,
            result.committed_to_id() == zero_commitment.id(),
            result.watermark() == Timestamp::spec_default(),
            result.committed_values() == map![Timestamp::spec_default() => None::<u64>],
            result.current_value() == None::<u64>,
            result.outstanding_reads().is_empty(),
            result.outstanding_writes().is_empty(),
            result.pending_reads().is_empty(),
            result.pending_writes().is_empty(),
            result.completed_reads().is_empty(),
            result.completed_writes().is_empty(),
    {
        let tracked completed_writes = Map::tracked_empty();
        let tracked completed_reads = Map::tracked_empty();
        let tracked pending_writes = Map::tracked_empty();
        let tracked pending_reads = Map::tracked_empty();
        let tracked write_token_map = GhostMapAuth::new(Map::empty()).0;
        let tracked read_token_map = GhostMapAuth::new(Map::empty()).0;
        assert(write_token_map@.dom() == completed_writes.dom().union(pending_writes.dom()));
        assert(read_token_map@.dom() == completed_reads.dom().union(pending_reads.dom()));
        let tracked watermark = MonotonicTimestampResource::alloc();
        LinearizationQueue {
            committed_to: zero_commitment.submap(),
            completed_writes,
            completed_reads,
            pending_writes,
            pending_reads,
            write_token_map,
            read_token_map,
            next_read_op: 0,
            watermark,
            register_id,
        }
    }

    /// Inserts the mut linearizer into the linearization queue
    pub proof fn insert_write_linearizer(
        tracked &mut self,
        tracked lin: ML,
        tracked op: RegisterWrite,
        timestamp: Timestamp,
        tracked allocation_opt: Option<WriteAllocation>,
    ) -> (tracked r: Result<LinWriteToken<ML>, InsertError<ML, RL>>)
        requires
            old(self).inv(),
            lin.pre(op),
            lin.namespaces().finite(),
            !lin.namespaces().contains(super::state_inv_id()),
            op.id == old(self).register_id(),
            allocation_opt is Some <==> timestamp > old(self).watermark(),
            allocation_opt is Some ==> ({
                let allocation = allocation_opt->Some_0;
                &&& allocation.key() == timestamp
                &&& allocation.value() == op.new_value
                &&& allocation.id() == old(self).committed_to_id()
                &&& !old(self).outstanding_writes().contains_key(timestamp)
            }),
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).current_value() == old(self).current_value(),
            final(self).watermark() == old(self).watermark(),
            final(self).committed_values() == old(self).committed_values(),
            final(self).outstanding_reads() == old(self).outstanding_reads(),
            r is Ok <==> timestamp > old(self).watermark(),
            r is Ok ==> ({
                let token = r->Ok_0;
                &&& token.id() == final(self).write_token_id()
                &&& token.key() == timestamp
                &&& token.value().lin == lin
                &&& token.value().op == op
                &&& !token.value().committed
                &&& final(self).outstanding_writes() == old(self).outstanding_writes().insert(
                    token.key(),
                    token.value(),
                )
                &&& final(self).pending_writes().dom() == old(self).pending_writes().dom().insert(
                    token.key(),
                )
            }),
            r is Err ==> ({
                let err = r->Err_0;
                let watermark_lb = r->Err_0->w_watermark_lb;
                &&& *final(self) == *old(self)
                &&& err is WriteWatermarkContradiction
                &&& err->w_lin == lin
                &&& watermark_lb@.timestamp() == final(self).watermark()
                &&& watermark_lb@.timestamp() >= timestamp
                &&& watermark_lb.loc() == final(self).watermark_id()
                &&& watermark_lb@ is LowerBound
            }),
    {
        if timestamp <= self.watermark@.timestamp() {
            return Err(
                InsertError::WriteWatermarkContradiction {
                    w_watermark_lb: self.watermark.extract_lower_bound(),
                    w_lin: lin,
                },
            );
        }
        let tracked allocation = allocation_opt.tracked_unwrap();
        let tracked v = WriteTokenVal { lin, op, committed: false };
        let tracked pending = PendingWrite::new(lin, op, allocation, timestamp);

        self.pending_writes.tracked_insert(timestamp, pending);
        let tracked lin_token = self.write_token_map.insert(timestamp, v);
        // load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));

        lin_token.lemma_view();

        assert(self.write_dom_inv());
        Ok(lin_token)
    }

    /// Inserts the read linearizer into the linearization queue
    pub proof fn insert_read_linearizer(
        tracked &mut self,
        tracked lin: RL,
        tracked op: RegisterRead,
        value: Option<u64>,
        tracked register: &GhostVarAuth<Option<u64>>,
    ) -> (tracked token: LinReadToken<RL>)
        requires
            old(self).inv(),
            lin.pre(op),
            lin.namespaces().finite(),
            !lin.namespaces().contains(super::state_inv_id()),
            op.id == old(self).register_id(),
            register.id() == old(self).register_id(),
            register@ == old(self).current_value(),
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).current_value() == old(self).current_value(),
            final(self).watermark() == old(self).watermark(),
            final(self).committed_values() == old(self).committed_values(),
            final(self).outstanding_writes() == old(self).outstanding_writes(),
            final(self).outstanding_reads() == old(self).outstanding_reads().insert(
                token.key(),
                token.value(),
            ),
            final(self).pending_writes() == old(self).pending_writes(),
            value == final(self).current_value() ==> final(self).completed_reads().contains_key(
                token.key(),
            ),
            value != final(self).current_value() ==> final(self).pending_reads().contains_key(
                token.key(),
            ),
            token.id() == final(self).read_token_id(),
            token.key().0 == value,
            token.value().lin == lin,
            token.value().op == op,
            token.value().min_ts.loc() == final(self).watermark_id(),
            token.value().min_ts@.timestamp() == final(self).watermark(),
        opens_invariants ISet::new(|id: int| id != super::state_inv_id())
    {
        let key = (value, self.next_read_op);
        let tracked v = ReadTokenVal { lin, op, min_ts: self.watermark.extract_lower_bound() };
        self.watermark.lemma_lower_bound(&v.min_ts);

        assert(!self.read_token_map@.contains_key(key));
        assert(!self.pending_reads.contains_key(key));
        assert(!self.completed_reads.contains_key(key));

        let tracked token = self.read_token_map.insert((value, self.next_read_op), v);
        token.lemma_view();
        self.next_read_op = self.next_read_op + 1;

        let tracked mut pending = PendingRead::new(lin, op, value);
        if value == self.current_value() {
            let tracked completed = pending.apply_linearizer(register, self.watermark@.timestamp());
            self.completed_reads.tracked_insert(token.key(), completed);
        } else {
            self.pending_reads.tracked_insert(token.key(), pending);
        }

        // load bearing assert
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(
            self.pending_reads.dom(),
        ));

        token
    }

    pub proof fn commit_value(
        tracked &mut self,
        tracked write_token: &mut LinWriteToken<ML>,
    ) -> (tracked r: WriteCommitment)
        requires
            old(self).inv(),
            old(write_token).id() == old(self).write_token_id(),
            !old(write_token).value().committed,
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).current_value() == old(self).current_value(),
            final(self).watermark() == old(self).watermark(),
            final(self).committed_values() == old(self).committed_values(),
            final(self).outstanding_writes().dom() == old(self).outstanding_writes().dom(),
            final(self).outstanding_reads() == old(self).outstanding_reads(),
            final(self).pending_writes().dom() == old(self).pending_writes().dom(),
            final(write_token).id() == old(write_token).id(),
            final(write_token).key() == old(write_token).key(),
            final(write_token).value().lin == old(write_token).value().lin,
            final(write_token).value().op == old(write_token).value().op,
            final(write_token).value().committed == true,
            r.id() == final(self).committed_to_id(),
            r.key() == final(write_token).key(),
            r.value() == final(write_token).value().op.new_value,
    {
        write_token.agree(&self.write_token_map);
        let tracked commitment = if write_token.key() <= self.watermark@.timestamp() {
            let tracked mut completed = self.completed_writes.tracked_remove(write_token.key());
            let tracked commitment = completed.duplicate_commitment();
            self.completed_writes.tracked_insert(write_token.key(), completed);
            commitment
        } else {
            let tracked pending = self.pending_writes.tracked_remove(write_token.key());
            let tracked (pending, commitment) = pending.commit();
            pending.lemma_pending_inv();
            self.pending_writes.tracked_insert(write_token.key(), pending);
            commitment
        };

        let new_write_val = WriteTokenVal {
            lin: write_token.value().lin,
            op: write_token.value().op,
            committed: true,
        };
        write_token.update(&mut self.write_token_map, new_write_val);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));
        commitment
    }

    pub open spec fn pending_writes_up_to(self, max_timestamp: Timestamp) -> (r: Set<Timestamp>)
        recommends
            self.inv(),
    {
        self.pending_writes().dom().filter(|ts: Timestamp| ts <= max_timestamp)
    }

    proof fn lemma_pending_writes(self, max_timestamp: Timestamp)
        requires
            self.inv(),
        ensures
            self.pending_writes_up_to(max_timestamp) <= self.pending_writes.dom(),
            self.pending_writes_up_to(max_timestamp).len() <= self.pending_writes.dom().len(),
    {
        self.pending_writes.dom().lemma_len_filter(|ts: Timestamp| ts <= max_timestamp);
    }

    pub open spec fn pending_reads_with_value(self, value: Option<u64>) -> (r: Set<
        (Option<u64>, nat),
    >)
        recommends
            self.inv() || self.current_value() == value,
    {
        self.pending_reads().dom().filter(|k: (Option<u64>, nat)| k.0 == value)
    }

    proof fn lemma_pending_reads(self, value: Option<u64>)
        requires
            self.inv() || self.current_value() == value,
        ensures
            self.pending_reads_with_value(value) <= self.pending_reads.dom(),
            self.pending_reads_with_value(value).len() <= self.pending_reads.dom().len(),
            forall|x: (Option<u64>, nat)| #[trigger]
                self.pending_reads_with_value(value).contains(x) ==> x.0 == value,
    {
        self.pending_reads.dom().lemma_len_filter(|k: (Option<u64>, nat)| k.0 == value);
        lemma_len_subset(self.pending_reads_with_value(value), self.pending_reads.dom());
    }

    /// Applies the linearizer for all operations prophecized to <= timestamp
    pub proof fn apply_linearizers_up_to(
        tracked &mut self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        max_timestamp: Timestamp,
    ) -> (tracked r: MonotonicTimestampResource)
        requires
            old(self).inv(),
            old(register).id() == old(self).register_id(),
            old(self).current_value() == old(register)@,
            old(self).known_timestamps().contains(max_timestamp),
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).current_value() == final(register)@,
            final(register).id() == old(register).id(),
            final(self).outstanding_writes() == old(self).outstanding_writes(),
            final(self).outstanding_reads() == old(self).outstanding_reads(),
            max_timestamp > old(self).watermark() ==> final(self).watermark() == max_timestamp,
            max_timestamp <= old(self).watermark() ==> final(self).watermark() == old(
                self,
            ).watermark(),
            final(self).committed_values().dom() == old(self).committed_values().dom().union(
                old(self).pending_writes_up_to(max_timestamp),
            ),
            final(self).pending_writes() == old(self).pending_writes().remove_keys(
                old(self).pending_writes_up_to(max_timestamp),
            ),
            final(self).pending_writes_up_to(max_timestamp).len() == 0,
            r.loc() == final(self).watermark_id(),
            r@.timestamp() == final(self).watermark(),
            r@ is LowerBound,
        decreases old(self).pending_writes_up_to(max_timestamp).len(),
        opens_invariants ISet::new(|id: int| id != super::state_inv_id())
    {
        let pending_writes = self.pending_writes_up_to(max_timestamp);
        self.lemma_pending_writes(max_timestamp);

        if pending_writes.len() == 0 {
            if self.pending_writes.contains_key(max_timestamp) {
                assert_by_contradiction!(max_timestamp <= self.watermark@.timestamp(),
                {
                    assert(self.pending_writes_up_to(max_timestamp).contains(max_timestamp)); // trigger
                });
            }
            return self.watermark.extract_lower_bound();
        }
        let ts_leq = |a: Timestamp, b: Timestamp| a <= b;
        let next_ts = pending_writes.find_unique_minimal(ts_leq);
        pending_writes.find_unique_minimal_ensures(ts_leq);

        // take linearizer, apply, move watermark, place in completed
        let tracked (pending, cur_commitment) = self.pending_writes.tracked_remove(
            next_ts,
        ).commit();
        let tracked mut completed = pending.apply_linearizer(register, next_ts);

        let ghost old_committed = self.committed_to@;
        self.committed_to.intersection_agrees_points_to(&cur_commitment);
        self.committed_to.combine_points_to(cur_commitment);
        assert(self.committed_to@ == old_committed.insert(
            cur_commitment.key(),
            cur_commitment.value(),
        ));
        assert(old_committed <= self.committed_to@);

        let ghost old_watermark = self.watermark@.timestamp();
        self.watermark.advance(next_ts);
        self.completed_writes.tracked_insert(completed.timestamp(), completed);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));

        assert forall|ts: Timestamp| #[trigger] self.pending_writes.contains_key(ts) implies ts
            > self.watermark@.timestamp() by {
            assert_by_contradiction!(ts > self.watermark@.timestamp(), {
                if ts > old_watermark && ts < next_ts {
                    pending_writes.lemma_minimal_equivalent_least(ts_leq, next_ts);
                    assert(ts_leq(next_ts, ts)); // CONTRADICTION
                }
            });
        }

        // linearize any reads at the current value
        self.apply_read_linearizers_at_value(&*register, self.current_value());

        // XXX: load bearing assert
        assert(self.pending_writes_up_to(max_timestamp) == old(self).pending_writes_up_to(
            max_timestamp,
        ).remove(next_ts));
        self.apply_linearizers_up_to(register, max_timestamp)
    }

    proof fn apply_read_linearizers_at_value(
        tracked &mut self,
        tracked register: &GhostVarAuth<Option<u64>>,
        value: Option<u64>,
    )
        requires
            register.id() == old(self).register_id,
            old(self).basic_inv(),
            old(self).write_dom_inv(),
            old(self).weak_read_dom_inv(),
            old(self).current_value() == register@,
            register@ == value,
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).watermark() == old(self).watermark(),
            final(self).current_value() == old(self).current_value(),
            final(self).outstanding_writes() == old(self).outstanding_writes(),
            final(self).outstanding_reads() == old(self).outstanding_reads(),
            final(self).completed_writes() == old(self).completed_writes(),
            final(self).pending_writes() == old(self).pending_writes(),
            final(self).committed_values() == old(self).committed_values(),
            final(self).pending_reads().dom() == old(self).pending_reads().dom().difference(
                old(self).pending_reads_with_value(value),
            ),
            final(self).completed_reads().dom() == old(self).completed_reads().dom().union(
                old(self).pending_reads_with_value(value),
            ),
        decreases old(self).pending_reads_with_value(value).len(),
        opens_invariants ISet::new(|id: int| id != super::state_inv_id())
    {
        let ghost old_watermark = self.watermark@.timestamp();
        let pending_reads = self.pending_reads_with_value(value);
        self.lemma_pending_reads(value);
        if pending_reads.len() == 0 {
            assert forall|key: (Option<u64>, nat)| #[trigger]
                self.pending_reads.contains_key(key) implies {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                forall|ts: Timestamp|
                    {
                        &&& token.min_ts@.timestamp() <= ts
                        &&& ts <= self.watermark@.timestamp()
                        &&& #[trigger] self.committed_to@.contains_key(ts)
                    } ==> { self.committed_to@[ts] != pending.value() }
            } by {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                assert forall|ts: Timestamp|
                    {
                        &&& token.min_ts@.timestamp() <= ts
                        &&& ts <= self.watermark@.timestamp()
                        &&& #[trigger] self.committed_to@.contains_key(ts)
                    } implies self.committed_to@[ts] != pending.value() by {
                    if ts == self.watermark@.timestamp() {
                        assert_by_contradiction!(self.committed_to@[ts] != pending.value(), {
                            assert(self.pending_reads_with_value(pending.value()).contains(key)); // trigger
                        });
                    }
                }
            };
            return;
        }
        assert(!pending_reads.is_empty());

        let next_key = choose|k: (Option<u64>, nat)| pending_reads.contains(k);

        // take linearizer, apply, move watermark, place in completed
        let tracked pending = self.pending_reads.tracked_remove(next_key);
        let tracked completed = pending.apply_linearizer(register, self.watermark@.timestamp());
        self.completed_reads.tracked_insert(next_key, completed);

        // XXX: load bearing asserts
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(
            self.pending_reads.dom(),
        ));
        assert(self.completed_reads.dom() <= self.read_token_map@.dom());
        assert(self.pending_reads_with_value(value) == old(self).pending_reads_with_value(
            value,
        ).remove(next_key));

        assert(self.read_completed_inv());
        self.apply_read_linearizers_at_value(register, value)
    }

    /// Return the completion of the write at timestamp - removing it from the sequence
    pub proof fn extract_write_completion(
        tracked &mut self,
        tracked token: LinWriteToken<ML>,
        tracked resource: MonotonicTimestampResource,
    ) -> (tracked r: ML::Completion)
        requires
            old(self).inv(),
            token.id() == old(self).write_token_id(),
            resource.loc() == old(self).watermark_id(),
            resource@ is LowerBound,
            resource@.timestamp() >= token.key(),
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).watermark() == old(self).watermark(),
            final(self).current_value() == old(self).current_value(),
            final(self).committed_values() == old(self).committed_values(),
            final(self).outstanding_writes() == old(self).outstanding_writes().remove(token.key()),
            final(self).completed_writes() == old(self).completed_writes().remove(token.key()),
            final(self).pending_writes() == old(self).pending_writes(),
            ({
                let WriteTokenVal { lin, op, .. } = token.value();
                lin.post(op, (), r)
            }),
    {
        token.agree(&self.write_token_map);
        self.watermark.lemma_lower_bound(&resource);

        let tracked completed = self.completed_writes.tracked_remove(token.key());
        self.write_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));

        completed.tracked_completion()
    }

    /// Return the completion of a read at the timestamp - removing it from the sequence
    pub proof fn extract_read_completion(
        tracked &mut self,
        tracked token: LinReadToken<RL>,
        exec_timestamp: Timestamp,
        tracked resource: MonotonicTimestampResource,
        tracked mut commitment: WriteCommitment,
    ) -> (tracked r: RL::Completion)
        requires
            old(self).inv(),
            token.id() == old(self).read_token_id(),
            resource.loc() == old(self).watermark_id(),
            resource@ is LowerBound,
            resource@.timestamp() >= exec_timestamp,
            exec_timestamp >= token.value().min_ts@.timestamp(),
            commitment.id() == old(self).committed_to_id(),
            commitment.key() == exec_timestamp,
            commitment.value() == token.key().0,
            old(self).committed_values().contains_key(exec_timestamp),
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).watermark() == old(self).watermark(),
            final(self).current_value() == old(self).current_value(),
            final(self).committed_values() == old(self).committed_values(),
            final(self).outstanding_writes() == old(self).outstanding_writes(),
            final(self).outstanding_reads() == old(self).outstanding_reads().remove(token.key()),
            final(self).completed_reads() == old(self).completed_reads().remove(token.key()),
            final(self).completed_writes() == old(self).completed_writes(),
            final(self).pending_writes() == old(self).pending_writes(),
            token.value().lin.post(token.value().op, token.key().0, r),
    {
        token.agree(&self.read_token_map);
        self.watermark.lemma_lower_bound(&resource);
        commitment.intersection_agrees_submap(&self.committed_to);

        let tracked completed = self.completed_reads.tracked_remove(token.key());
        self.read_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(
            self.pending_reads.dom(),
        ));

        assert(self.inv());
        completed.tracked_completion()
    }

    /// Remove the linearizer/completion from the queue (for error cases)
    pub proof fn remove_write_lin(
        tracked &mut self,
        tracked token: LinWriteToken<ML>,
    ) -> (tracked r: (MaybeWriteLinearized<ML, ML::Completion>, Option<WriteAllocation>))
        requires
            old(self).inv(),
            token.id() == old(self).write_token_id(),
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).watermark() == old(self).watermark(),
            final(self).current_value() == old(self).current_value(),
            final(self).committed_values() == old(self).committed_values(),
            final(self).outstanding_writes() == old(self).outstanding_writes().remove(token.key()),
            final(self).completed_writes() == old(self).completed_writes().remove(token.key()),
            token.value().lin == r.0.lin(),
            token.value().op == r.0.op(),
            !token.value().committed && r.1 is Some ==> {
                let allocation = r.1->Some_0;
                &&& allocation.id() == final(self).committed_to_id()
                &&& allocation.key() == token.key()
                &&& allocation.value() == token.value().op.new_value
                &&& final(self).pending_writes() == old(self).pending_writes().remove(token.key())
                &&& final(self).known_timestamps() == old(self).known_timestamps().remove(
                    token.key(),
                )
                &&& old(self).pending_writes().contains_key(token.key())
            },
            !token.value().committed && r.1 is None ==> {
                final(self).pending_writes() == old(self).pending_writes()
            },
            r.0.inv(),
    {
        token.agree(&self.write_token_map);

        let tracked (lincomp, allocation_opt) = if token.key() <= self.watermark@.timestamp() {
            (self.completed_writes.tracked_remove(token.key()).maybe(), None)
        } else {
            let tracked pending = self.pending_writes.tracked_remove(token.key());
            pending.lemma_pending_inv();
            if token.value().committed {
                pending.maybe()
            } else {
                pending.maybe()
            }
        };
        self.write_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));

        (lincomp, allocation_opt)
    }

    /// Remove the linearizer/completion from the queue (for error cases)
    pub proof fn remove_read_lin(tracked &mut self, tracked token: LinReadToken<RL>) -> (tracked r:
        MaybeReadLinearized<RL, RL::Completion>)
        requires
            old(self).inv(),
            token.id() == old(self).read_token_id(),
        ensures
            final(self).inv(),
            final(self).ids() == old(self).ids(),
            final(self).watermark() == old(self).watermark(),
            final(self).current_value() == old(self).current_value(),
            final(self).committed_values() == old(self).committed_values(),
            final(self).outstanding_writes() == old(self).outstanding_writes(),
            final(self).outstanding_reads() == old(self).outstanding_reads().remove(token.key()),
            final(self).pending_writes() == old(self).pending_writes(),
            final(self).completed_writes() == old(self).completed_writes(),
            token.value().lin == r.lin(),
            token.value().op == r.op(),
    {
        token.agree(&self.read_token_map);

        let completed = exists|ts: Timestamp|
            {
                &&& token.value().min_ts@.timestamp() <= ts
                &&& ts <= self.watermark@.timestamp()
                &&& #[trigger] self.committed_to@.contains_key(ts)
                &&& self.committed_to@[ts] == token.key().0
            };

        let tracked lincomp = if completed {
            self.completed_reads.tracked_remove(token.key()).maybe()
        } else {
            self.pending_reads.tracked_remove(token.key()).maybe()
        };
        self.read_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(
            self.pending_reads.dom(),
        ));

        lincomp
    }
}

} // verus!
impl<ML, RL> std::fmt::Debug for InsertError<ML, RL> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::WriteWatermarkContradiction { .. } => {
                f.write_str("WriteWatermarkContradiction")
            }
            InsertError::ReadWatermarkContradiction { .. } => {
                f.write_str("ReadWatermarkContradiction")
            }
        }
    }
}
