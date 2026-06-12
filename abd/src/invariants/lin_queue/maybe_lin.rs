use crate::timestamp::Timestamp;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use vstd::logatom::{MutLinearizer, ReadLinearizer};
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::resource::ghost_var::GhostVarAuth;

verus! {

pub enum MaybeWriteLinearized<ML, MC> {
    Linearizer { lin: ML, ghost op: RegisterWrite, ghost timestamp: Timestamp },
    Completion {
        completion: MC,
        ghost op: RegisterWrite,
        ghost timestamp: Timestamp,
        ghost lin: ML,
    },
}

pub enum MaybeReadLinearized<RL, RC> {
    Linearizer { lin: RL, ghost op: RegisterRead, ghost value: Option<u64> },
    Completion { completion: RC, ghost op: RegisterRead, ghost value: Option<u64>, ghost lin: RL },
}

impl<ML: MutLinearizer<RegisterWrite>> MaybeWriteLinearized<ML, ML::Completion> {
    pub proof fn linearizer(
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (MaybeWriteLinearized::<ML, ML::Completion>::Linearizer {
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

    pub open spec fn op(self) -> RegisterWrite {
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

impl<RL: ReadLinearizer<RegisterRead>> MaybeReadLinearized<RL, RL::Completion> {
    pub proof fn linearizer(
        tracked lin: RL,
        op: RegisterRead,
        value: Option<u64>,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (MaybeReadLinearized::<RL, RL::Completion>::Linearizer { lin, op, value }),
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

    pub open spec fn op(self) -> RegisterRead {
        match self {
            MaybeReadLinearized::Linearizer { op, .. } => op,
            MaybeReadLinearized::Completion { op, .. } => op,
        }
    }

    pub open spec fn value(self) -> Option<u64> {
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
