use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;

use verdist::network::error::ConnectError;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;

impl<ML, RL> From<ConnectError> for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn from(value: ConnectError) -> Self {
        Error::Connection(value)
    }
}

impl<ML, RL> From<abd::client::error::ReadError<RL, RL::Completion>>
    for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn from(value: abd::client::error::ReadError<RL, RL::Completion>) -> Self {
        Error::AbdRead(value)
    }
}

impl<ML, RL> From<abd::client::error::WriteError<ML, ML::Completion>>
    for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn from(value: abd::client::error::WriteError<ML, ML::Completion>) -> Self {
        Error::AbdWrite(value)
    }
}

impl<ML, RL> std::error::Error for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match self {
            Error::Connection(e) => Some(e),
            Error::AbdRead(e) => Some(e),
            Error::AbdWrite(e) => Some(e),
            _ => None,
        }
    }
}

impl<ML, RL> std::fmt::Display for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::AbdRead(e) => e.fmt(f),
            Error::AbdWrite(e) => e.fmt(f),
            _ => Ok(()),
        }
    }
}

impl<ML, RL> std::fmt::Debug for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::AbdRead(e) => e.fmt(f),
            Error::AbdWrite(e) => e.fmt(f),
            _ => Ok(()),
        }
    }
}

verus! {

pub(crate) enum Error<ML, MC, RL, RC> {
    Empty,
    Connection(ConnectError),
    AbdRead(abd::client::error::ReadError<RL, RC>),
    AbdWrite(abd::client::error::WriteError<ML, MC>),
}

} // verus!
