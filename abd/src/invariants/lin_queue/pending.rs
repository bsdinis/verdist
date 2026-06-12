use crate::invariants::committed_to::WriteAllocation;
use crate::invariants::committed_to::WriteCommitment;
#[cfg(verus_only)]
use crate::invariants::lin_queue::CompletedRead;
#[cfg(verus_only)]
use crate::invariants::lin_queue::CompletedWrite;
#[cfg(verus_only)]
use crate::invariants::lin_queue::MaybeReadLinearized;
#[cfg(verus_only)]
use crate::invariants::lin_queue::MaybeWriteLinearized;
use crate::timestamp::Timestamp;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::ghost_var::GhostVarAuth;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

#[allow(dead_code)]
pub enum WriteStatus {
    Allocated { allocation: WriteAllocation },
    Committed { commitment: WriteCommitment },
}

impl WriteStatus {
    pub open spec fn id(self) -> Loc {
        match self {
            WriteStatus::Allocated { allocation } => allocation.id(),
            WriteStatus::Committed { commitment } => commitment.id(),
        }
    }

    pub open spec fn timestamp(self) -> Timestamp {
        match self {
            WriteStatus::Allocated { allocation } => allocation.key(),
            WriteStatus::Committed { commitment } => commitment.key(),
        }
    }

    pub open spec fn value(self) -> Option<u64> {
        match self {
            WriteStatus::Allocated { allocation } => allocation.value(),
            WriteStatus::Committed { commitment } => commitment.value(),
        }
    }

    proof fn allocated(tracked allocation: WriteAllocation) -> (tracked r: WriteStatus)
        ensures
            r is Allocated,
            r->allocation == allocation,
    {
        WriteStatus::Allocated { allocation }
    }

    proof fn commit(tracked self) -> (tracked r: Self)
        ensures
            r is Committed,
            self is Committed ==> r == self,
            self is Allocated ==> {
                &&& r.id() == self.id()
                &&& r.timestamp() == self.timestamp()
                &&& r.value() == self.value()
            },
    {
        let tracked commitment = match self {
            WriteStatus::Allocated { allocation } => allocation.persist(),
            WriteStatus::Committed { commitment } => commitment,
        };

        WriteStatus::Committed { commitment }
    }

    proof fn duplicate(tracked self) -> (tracked r: (Self, WriteCommitment))
        requires
            self is Committed,
        ensures
            r.0.id() == self.id(),
            r.0.timestamp() == self.timestamp(),
            r.0.value() == self.value(),
            r.0 is Committed,
            r.1.id() == r.0.id(),
            r.1.key() == r.0.timestamp(),
            r.1.value() == r.0.value(),
    {
        match self {
            WriteStatus::Committed { mut commitment } => {
                let tracked dup = commitment.duplicate();
                let tracked new_self = WriteStatus::Committed { commitment };
                (new_self, dup)
            },
            WriteStatus::Allocated { .. } => vstd::pervasive::proof_from_false(),
        }
    }

    proof fn tracked_destruct_commitment(tracked self) -> (tracked r: WriteCommitment)
        requires
            self is Committed,
        ensures
            r.id() == self->commitment.id(),
            r@ == self->commitment@,
    {
        match self {
            WriteStatus::Committed { commitment } => commitment,
            WriteStatus::Allocated { .. } => vstd::pervasive::proof_from_false(),
        }
    }

    proof fn tracked_destruct_allocation(tracked self) -> (tracked r: WriteAllocation)
        requires
            self is Allocated,
        ensures
            r.id() == self->allocation.id(),
            r@ == self->allocation@,
    {
        match self {
            WriteStatus::Committed { .. } => vstd::pervasive::proof_from_false(),
            WriteStatus::Allocated { allocation } => allocation,
        }
    }
}

#[allow(dead_code)]
pub struct PendingWrite<ML: MutLinearizer<RegisterWrite>> {
    lin: ML,
    op: RegisterWrite,
    write_status: WriteStatus,
    ghost timestamp: Timestamp,
}

#[allow(dead_code)]
pub struct PendingRead<RL: ReadLinearizer<RegisterRead>> {
    lin: RL,
    op: RegisterRead,
    ghost value: Option<u64>,
}

impl<ML: MutLinearizer<RegisterWrite>> PendingWrite<ML> {
    pub proof fn new(
        tracked lin: ML,
        tracked op: RegisterWrite,
        tracked allocation: WriteAllocation,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
            allocation.key() == timestamp,
            allocation.value() == op.new_value,
        ensures
            result.lin() == lin,
            result.op() == op,
            result.value() == op.new_value,
            result.timestamp() == timestamp,
            result.write_status() == (WriteStatus::Allocated { allocation }),
    {
        PendingWrite { lin, op, write_status: WriteStatus::Allocated { allocation }, timestamp }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
        &&& self.timestamp() == self.write_status().timestamp()
        &&& self.value() == self.write_status().value()
        &&& self.value() == self.op.new_value
    }

    pub proof fn lemma_pending_inv(tracked &self)
        ensures
            self.lin().namespaces().finite(),
            self.lin().pre(self.op()),
            self.timestamp() == self.write_status().timestamp(),
            self.value() == self.write_status().value(),
            self.value() == self.op().new_value,
    {
        use_type_invariant(self);
    }

    pub closed spec fn lin(self) -> ML {
        self.lin
    }

    pub closed spec fn op(self) -> RegisterWrite {
        self.op
    }

    pub closed spec fn timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub open spec fn value(self) -> Option<u64> {
        self.op().new_value
    }

    pub closed spec fn write_status(self) -> WriteStatus {
        self.write_status
    }

    pub open spec fn commitment_id(self) -> Loc {
        self.write_status().id()
    }

    pub open spec fn register_id(self) -> Loc {
        self.op().id@
    }

    pub open spec fn namespaces(self) -> ISet<int> {
        self.lin().namespaces()
    }

    pub proof fn commit(tracked self) -> (tracked r: (Self, WriteCommitment))
        ensures
            r.0.lin() == self.lin(),
            r.0.op() == self.op(),
            r.0.timestamp() == self.timestamp(),
            r.0.commitment_id() == self.commitment_id(),
            r.0.write_status() is Committed,
            r.1.id() == r.0.commitment_id(),
            r.1.key() == r.0.timestamp(),
            r.1.value() == r.0.value(),
    {
        use_type_invariant(&self);
        let tracked PendingWrite { lin, op, write_status, timestamp } = self;
        let tracked (write_status, dup) = write_status.commit().duplicate();
        let tracked pending = PendingWrite { lin, op, write_status, timestamp };
        (pending, dup)
    }

    pub proof fn apply_linearizer(
        tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        timestamp: Timestamp,
    ) -> (tracked r: CompletedWrite<ML>)
        requires
            self.write_status() is Committed,
            self.register_id() == old(register).id(),
            timestamp >= self.timestamp(),
        ensures
            r.op() == self.op(),
            r.timestamp() == self.timestamp(),
            r.value() == self.value(),
            r.lin() == self.lin(),
            r.commitment_id() == self.commitment_id(),
            final(register).id() == old(register).id(),
            final(register)@ == r.value(),
        opens_invariants self.namespaces()
    {
        use_type_invariant(&self);
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, (), &());
        CompletedWrite::new(
            completion,
            self.op,
            self.write_status.tracked_destruct_commitment(),
            lin_copy,
            self.timestamp,
        )
    }

    pub proof fn maybe(tracked self) -> (tracked r: (
        MaybeWriteLinearized<ML, ML::Completion>,
        Option<WriteAllocation>,
    ))
        ensures
            r.0 == (MaybeWriteLinearized::<ML, ML::Completion>::Linearizer {
                lin: self.lin(),
                op: self.op(),
                timestamp: self.timestamp(),
            }),
            r.1 is Some <==> self.write_status() is Allocated,
            r.1 is Some ==> {
                let allocation = r.1->Some_0;
                &&& allocation.id() == self.commitment_id()
                &&& allocation.key() == self.timestamp()
                &&& allocation.value() == self.value()
            },
    {
        use_type_invariant(&self);
        let tracked maybe = MaybeWriteLinearized::Linearizer {
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        };

        let tracked allocation_opt = if &self.write_status is Allocated {
            let tracked allocation = self.write_status.tracked_destruct_allocation();
            Some(allocation)
        } else {
            None
        };

        (maybe, allocation_opt)
    }
}

impl<RL: ReadLinearizer<RegisterRead>> PendingRead<RL> {
    pub proof fn new(
        tracked lin: RL,
        tracked op: RegisterRead,
        value: Option<u64>,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result.lin() == lin,
            result.op() == op,
            result.value() == value,
            result.register_id() == op.id,
    {
        PendingRead { lin, op, value }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
    }

    pub proof fn lemma_pending_inv(tracked &self)
        ensures
            self.lin().pre(self.op()),
    {
        use_type_invariant(self);
    }

    pub closed spec fn lin(self) -> RL {
        self.lin
    }

    pub closed spec fn op(self) -> RegisterRead {
        self.op
    }

    pub closed spec fn value(self) -> Option<u64> {
        self.value
    }

    pub open spec fn register_id(self) -> Loc {
        self.op().id@
    }

    pub open spec fn namespaces(self) -> ISet<int> {
        self.lin().namespaces()
    }

    pub proof fn apply_linearizer(
        tracked self,
        tracked register: &GhostVarAuth<Option<u64>>,
        timestamp: Timestamp,
    ) -> (tracked r: CompletedRead<RL>)
        requires
            self.register_id() == register.id(),
            self.value() == register@,
        ensures
            r.lin() == self.lin(),
            r.op() == self.op(),
            r.value() == self.value(),
            r.timestamp() == timestamp,
        opens_invariants self.namespaces()
    {
        use_type_invariant(&self);
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, &self.value);
        CompletedRead::new(completion, self.op, lin_copy, self.value, timestamp)
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeReadLinearized<RL, RL::Completion>)
        ensures
            r.inv(),
            r == (MaybeReadLinearized::<RL, RL::Completion>::Linearizer {
                lin: self.lin(),
                op: self.op(),
                value: self.value(),
            }),
    {
        use_type_invariant(&self);
        MaybeReadLinearized::Linearizer { lin: self.lin, op: self.op, value: self.value }
    }
}

} // verus!
