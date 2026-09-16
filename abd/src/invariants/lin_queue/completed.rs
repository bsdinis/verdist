use crate::invariants::committed_to::WriteCommitment;
#[cfg(verus_only)]
use crate::invariants::lin_queue::maybe_lin::MaybeReadLinearized;
#[cfg(verus_only)]
use crate::invariants::lin_queue::maybe_lin::MaybeWriteLinearized;
use crate::timestamp::Timestamp;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use vstd::logatom::{MutLinearizer, ReadLinearizer};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::ghost_var::GhostVarAuth;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

#[allow(dead_code)]
#[verifier::reject_recursive_types(N)]
pub struct CompletedWrite<const N: usize, ML: MutLinearizer<RegisterWrite<N>>> {
    completion: ML::Completion,
    op: RegisterWrite<N>,
    commitment: WriteCommitment<N>,
    ghost lin: ML,
    ghost timestamp: Timestamp,
}

#[allow(dead_code)]
#[verifier::reject_recursive_types(N)]
pub struct CompletedRead<const N: usize, RL: ReadLinearizer<RegisterRead<N>>> {
    completion: RL::Completion,
    op: RegisterRead<N>,
    ghost lin: RL,
    ghost value: Option<[u8; N]>,
    ghost timestamp: Timestamp,
}

impl<const N: usize, ML: MutLinearizer<RegisterWrite<N>>> CompletedWrite<N, ML> {
    pub proof fn new(
        tracked completion: ML::Completion,
        tracked op: RegisterWrite<N>,
        tracked commitment: WriteCommitment<N>,
        lin: ML,
        timestamp: Timestamp,
    ) -> (tracked r: Self)
        requires
            lin.post(op, (), completion),
            commitment.key() == timestamp,
            commitment.value() == op.new_value,
        ensures
            r.lin() == lin,
            r.completion() == completion,
            r.op() == op,
            r.timestamp() == timestamp,
            r.commitment() == commitment,
    {
        CompletedWrite { completion, op, commitment, lin, timestamp }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, (), self.completion)
        &&& self.commitment.key() == self.timestamp
        &&& self.commitment.value() == self.op.new_value
    }

    pub closed spec fn lin(self) -> ML {
        self.lin
    }

    pub closed spec fn completion(self) -> ML::Completion {
        self.completion
    }

    pub closed spec fn op(self) -> RegisterWrite<N> {
        self.op
    }

    pub closed spec fn timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub open spec fn value(self) -> Option<[u8; N]> {
        self.op().new_value
    }

    pub closed spec fn commitment(self) -> WriteCommitment<N> {
        self.commitment
    }

    pub open spec fn register_id(self) -> Loc {
        self.op().id@
    }

    pub open spec fn commitment_id(self) -> Loc {
        self.commitment().id()
    }

    pub proof fn duplicate_commitment(tracked &mut self) -> (tracked r: WriteCommitment<N>)
        ensures
            final(self).timestamp() == old(self).timestamp(),
            final(self).value() == old(self).value(),
            final(self).lin() == old(self).lin(),
            final(self).op() == old(self).op(),
            final(self).commitment()@ == old(self).commitment()@,
            final(self).commitment().id() == old(self).commitment().id(),
            final(self).completion() == old(self).completion(),
            r.id() == final(self).commitment_id(),
            r.key() == final(self).timestamp(),
            r.value() == final(self).value(),
    {
        use_type_invariant(&*self);
        self.commitment.duplicate()
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeWriteLinearized<N, ML, ML::Completion>)
        ensures
            r.inv(),
            r == (MaybeWriteLinearized::Completion {
                completion: self.completion(),
                lin: self.lin(),
                op: self.op(),
                timestamp: self.timestamp(),
            }),
    {
        use_type_invariant(&self);
        MaybeWriteLinearized::Completion {
            completion: self.completion,
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }
    }

    pub proof fn tracked_completion(tracked self) -> (tracked r: ML::Completion)
        ensures
            r == self.completion(),
            self.lin().post(self.op(), (), self.completion()),
    {
        use_type_invariant(&self);
        self.completion
    }
}

impl<const N: usize, RL: ReadLinearizer<RegisterRead<N>>> CompletedRead<N, RL> {
    pub proof fn new(
        tracked completion: RL::Completion,
        tracked op: RegisterRead<N>,
        lin: RL,
        value: Option<[u8; N]>,
        timestamp: Timestamp,
    ) -> (tracked r: Self)
        requires
            lin.post(op, value, completion),
        ensures
            r.lin() == lin,
            r.completion() == completion,
            r.op() == op,
            r.timestamp() == timestamp,
            r.value() == value,
    {
        CompletedRead { completion, value, lin, op, timestamp }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, self.value, self.completion)
    }

    pub closed spec fn lin(self) -> RL {
        self.lin
    }

    pub closed spec fn completion(self) -> RL::Completion {
        self.completion
    }

    pub closed spec fn op(self) -> RegisterRead<N> {
        self.op
    }

    pub closed spec fn timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn value(self) -> Option<[u8; N]> {
        self.value
    }

    pub open spec fn register_id(self) -> Loc {
        self.op().id@
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeReadLinearized<N, RL, RL::Completion>)
        ensures
            r.inv(),
            r == (MaybeReadLinearized::<N, RL, RL::Completion>::Completion {
                completion: self.completion(),
                op: self.op(),
                lin: self.lin(),
                value: self.value(),
            }),
    {
        use_type_invariant(&self);
        MaybeReadLinearized::Completion {
            completion: self.completion,
            op: self.op,
            lin: self.lin,
            value: self.value,
        }
    }

    pub proof fn tracked_completion(tracked self) -> (tracked r: RL::Completion)
        ensures
            r == self.completion(),
            self.lin().post(self.op(), self.value(), self.completion()),
    {
        use_type_invariant(&self);
        self.completion
    }
}

} // verus!
