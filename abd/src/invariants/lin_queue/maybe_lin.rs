use crate::timestamp::Timestamp;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use vstd::logatom::{MutLinearizer, ReadLinearizer};
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::resource::ghost_var::GhostVarAuth;

verus! {

pub enum MaybeWriteLinearized<const N: usize, ML, MC> {
    Linearizer { lin: ML, ghost op: RegisterWrite<N>, ghost timestamp: Timestamp },
    Completion {
        completion: MC,
        ghost op: RegisterWrite<N>,
        ghost timestamp: Timestamp,
        ghost lin: ML,
    },
}

pub enum MaybeReadLinearized<const N: usize, RL, RC> {
    Linearizer { lin: RL, ghost op: RegisterRead<N>, ghost value: Option<[u8; N]> },
    Completion { completion: RC, ghost op: RegisterRead<N>, ghost value: Option<[u8; N]>, ghost lin: RL },
}

impl<const N: usize, ML: MutLinearizer<RegisterWrite<N>>> MaybeWriteLinearized<N, ML, ML::Completion> {
    pub proof fn linearizer(
        tracked lin: ML,
        op: RegisterWrite<N>,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (MaybeWriteLinearized::<N, ML, ML::Completion>::Linearizer {
                lin,
                op,
                timestamp,
            }),
            result.inv(),
    {
        MaybeWriteLinearized::Linearizer { lin, op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.namespaces().finite()
        &&& self is Linearizer ==> self.lin().pre(self.op())
        &&& self is Completion ==> self.lin().post(self.op(), (), self->completion)
    }

    pub open spec fn lin(self) -> ML {
        match self {
            MaybeWriteLinearized::Linearizer { lin, .. } => lin,
            MaybeWriteLinearized::Completion { lin, .. } => lin,
        }
    }

    pub open spec fn op(self) -> RegisterWrite<N> {
        match self {
            MaybeWriteLinearized::Linearizer { op, .. } => op,
            MaybeWriteLinearized::Completion { op, .. } => op,
        }
    }

    pub open spec fn timestamp(self) -> Timestamp {
        match self {
            MaybeWriteLinearized::Linearizer { timestamp, .. } => timestamp,
            MaybeWriteLinearized::Completion { timestamp, .. } => timestamp,
        }
    }

    pub open spec fn namespaces(self) -> ISet<int> {
        match self {
            MaybeWriteLinearized::Linearizer { lin, .. } => lin.namespaces(),
            MaybeWriteLinearized::Completion { .. } => ISet::empty(),
        }
    }

    pub proof fn tracked_extract_completion(tracked self) -> (tracked r: ML::Completion)
        requires
            self is Completion,
            self.inv(),
        ensures
            self->completion == r,
    {
        match self {
            MaybeWriteLinearized::Completion { completion, .. } => completion,
            _ => proof_from_false(),
        }
    }
}

impl<const N: usize, RL: ReadLinearizer<RegisterRead<N>>> MaybeReadLinearized<N, RL, RL::Completion> {
    pub proof fn linearizer(
        tracked lin: RL,
        op: RegisterRead<N>,
        value: Option<[u8; N]>,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (MaybeReadLinearized::<N, RL, RL::Completion>::Linearizer { lin, op, value }),
            result.inv(),
    {
        MaybeReadLinearized::Linearizer { lin, op, value }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.namespaces().finite()
        &&& self is Linearizer ==> self.lin().pre(self.op())
        &&& self is Completion ==> self.lin().post(
            self.op(),
            self->Completion_value,
            self->completion,
        )
    }

    pub open spec fn lin(self) -> RL {
        match self {
            MaybeReadLinearized::Linearizer { lin, .. } => lin,
            MaybeReadLinearized::Completion { lin, .. } => lin,
        }
    }

    pub open spec fn op(self) -> RegisterRead<N> {
        match self {
            MaybeReadLinearized::Linearizer { op, .. } => op,
            MaybeReadLinearized::Completion { op, .. } => op,
        }
    }

    pub open spec fn value(self) -> Option<[u8; N]> {
        match self {
            MaybeReadLinearized::Linearizer { value, .. } => value,
            MaybeReadLinearized::Completion { value, .. } => value,
        }
    }

    pub open spec fn namespaces(self) -> ISet<int> {
        match self {
            MaybeReadLinearized::Linearizer { lin, .. } => lin.namespaces(),
            MaybeReadLinearized::Completion { .. } => ISet::empty(),
        }
    }

    pub proof fn tracked_extract_completion(tracked self) -> (tracked r: RL::Completion)
        requires
            self is Completion,
            self.inv(),
        ensures
            self->completion == r,
    {
        match self {
            MaybeReadLinearized::Completion { completion, .. } => completion,
            _ => proof_from_false(),
        }
    }
}

} // verus!
