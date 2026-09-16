use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::lin_queue::LinWriteToken;
use crate::invariants::lin_queue::MaybeReadLinearized;
use crate::invariants::lin_queue::MaybeWriteLinearized;
use crate::timestamp::Timestamp;

use specs::register::RegisterError;
use specs::register::RegisterRead;
use specs::register::RegisterWrite;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;

verus! {

/// ABD read related errors
///
/// The only way an ABD read fails is when a quorum is known to be unatainable
/// This happens when a connection reset happens
/// In this case, the error is exposed to the client
#[verifier::reject_recursive_types(N)]
pub enum ReadError<const N: usize, RL, RC> {
    // The first read quorum failed
    FailedFirstQuorum {
        obtained: usize,
        required: usize,
        lincomp: Tracked<MaybeReadLinearized<N, RL, RC>>,
    },
    // The writeback phase of the read failed
    FailedSecondQuorum {
        obtained: usize,
        required: usize,
        lincomp: Tracked<MaybeReadLinearized<N, RL, RC>>,
    },
}

/// ABD write related errors
///
/// The only way an ABD write fails is when a quorum is known to be unatainable
/// This happens when a connection reset happens
/// In this case, the error is exposed to the client
#[verifier::reject_recursive_types(N)]
pub enum WriteError<const N: usize, ML, MC> {
    // The first phase of the write failed
    // In this case the write never physicially started, so we can get the MaybeLinearized
    FailedFirstQuorum {
        obtained: usize,
        required: usize,
        lincomp: Tracked<MaybeWriteLinearized<N, ML, MC>>,
    },
    // The second phase of the write failed
    // In this case the write is physically ongoing, so we can only return a token into the queue
    FailedSecondQuorum {
        obtained: usize,
        required: usize,
        timestamp: Timestamp,
        token: Tracked<LinWriteToken<N, ML>>,
        commitment: Tracked<WriteCommitment<N>>,
    },
}

impl<const N: usize, ML> WriteError<N, ML, ML::Completion> where ML: MutLinearizer<RegisterWrite<N>> {
    pub open spec fn inv(self) -> bool {
        match self {
            WriteError::FailedFirstQuorum { lincomp, .. } => { lincomp@.inv() },
            WriteError::FailedSecondQuorum { token, commitment, timestamp, .. } => {
                &&& token@.key() == timestamp
                &&& commitment@.key() == timestamp
                &&& commitment@.value() == token@.value().op.new_value
            },
        }
    }
}

impl<const N: usize, RL, RC> std::error::Error for ReadError<N, RL, RC> {

}

impl<const N: usize, ML, MC> std::error::Error for WriteError<N, ML, MC> {

}

impl<const N: usize, RL> RegisterError<RL, RegisterRead<N>> for ReadError<N, RL, RL::Completion> where
    RL: ReadLinearizer<RegisterRead<N>>,
 {
    open spec fn err_ensures(self, op: RegisterRead<N>, lin: RL) -> bool {
        &&& self is FailedFirstQuorum ==> ({
            &&& self->FailedFirstQuorum_lincomp@.lin() == lin
            &&& self->FailedFirstQuorum_lincomp@.op() == op
        })
        &&& self is FailedSecondQuorum ==> ({
            &&& self->FailedSecondQuorum_lincomp@.lin() == lin
            &&& self->FailedSecondQuorum_lincomp@.op() == op
        })
    }
}

impl<const N: usize, ML> RegisterError<ML, RegisterWrite<N>> for WriteError<N, ML, ML::Completion> where
    ML: MutLinearizer<RegisterWrite<N>>,
 {
    open spec fn err_ensures(self, op: RegisterWrite<N>, lin: ML) -> bool {
        &&& self.inv()
        &&& self is FailedFirstQuorum ==> ({
            &&& self->lincomp@.lin() == lin
            &&& self->lincomp@.op() == op
        })
        &&& self is FailedSecondQuorum ==> ({
            &&& self->token@.value().lin == lin
            &&& self->token@.value().op == op
        })
    }
}

} // verus!
impl<const N: usize, RL, RC> std::fmt::Debug for ReadError<N, RL, RC> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReadError::FailedFirstQuorum {
                obtained, required, ..
            } => f
                .debug_struct("FailedFirstQuorum")
                .field("obtained", &obtained)
                .field("required", &required)
                .finish(),
            ReadError::FailedSecondQuorum {
                obtained, required, ..
            } => f
                .debug_struct("FailedSecondQuorum")
                .field("obtained", &obtained)
                .field("required", &required)
                .finish(),
        }
    }
}

impl<const N: usize, RL, RC> std::fmt::Display for ReadError<N, RL, RC> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReadError::FailedFirstQuorum { obtained, required, .. } => {
                f.write_fmt(format_args!("failed to obtain a quorum for the read; got {obtained} of {required} required responses"))
            },
            ReadError::FailedSecondQuorum { obtained, required, .. } => {
                f.write_fmt(format_args!("failed to obtain a quorum for the writeback phase of the read; got {obtained} of {required} required responses"))
            },
        }
    }
}

impl<const N: usize, ML, MC> std::fmt::Debug for WriteError<N, ML, MC> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WriteError::FailedFirstQuorum {
                obtained, required, ..
            } => f
                .debug_struct("FailedFirstQuorum")
                .field("obtained", &obtained)
                .field("required", &required)
                .finish(),
            WriteError::FailedSecondQuorum {
                obtained, required, ..
            } => f
                .debug_struct("FailedSecondQuorum")
                .field("obtained", &obtained)
                .field("required", &required)
                .finish(),
        }
    }
}

impl<const N: usize, ML, MC> std::fmt::Display for WriteError<N, ML, MC> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WriteError::FailedFirstQuorum { obtained, required, .. } => {
                f.write_fmt(format_args!("failed to obtain a quorum for the first phase of the write; got {obtained} of {required} required responses"))
            },
            WriteError::FailedSecondQuorum { obtained, required, .. } => {
                f.write_fmt(format_args!("failed to obtain a quorum for the second phase of the write; got {obtained} of {required} required responses"))
            },
        }
    }
}
