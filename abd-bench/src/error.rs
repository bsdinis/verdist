use verdist::network::error::ConnectError;

use specs::register::RegisterRead;
use specs::register::RegisterWrite;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;

impl<const N: usize, ML, RL> From<ConnectError> for Error<N, ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite<N>>,
    RL: ReadLinearizer<RegisterRead<N>>,
{
    fn from(value: ConnectError) -> Self {
        Error::Connection(value)
    }
}

impl<const N: usize, ML, RL> From<abd::client::error::ReadError<N, RL, RL::Completion>>
    for Error<N, ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite<N>>,
    RL: ReadLinearizer<RegisterRead<N>>,
{
    fn from(value: abd::client::error::ReadError<N, RL, RL::Completion>) -> Self {
        Error::AbdRead(value)
    }
}

impl<const N: usize, ML, RL> From<abd::client::error::WriteError<N, ML, ML::Completion>>
    for Error<N, ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite<N>>,
    RL: ReadLinearizer<RegisterRead<N>>,
{
    fn from(value: abd::client::error::WriteError<N, ML, ML::Completion>) -> Self {
        Error::AbdWrite(value)
    }
}

impl<const N: usize, ML, RL> std::error::Error for Error<N, ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite<N>>,
    RL: ReadLinearizer<RegisterRead<N>>,
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

impl<const N: usize, ML, RL> std::fmt::Display for Error<N, ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite<N>>,
    RL: ReadLinearizer<RegisterRead<N>>,
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

impl<const N: usize, ML, RL> std::fmt::Debug for Error<N, ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite<N>>,
    RL: ReadLinearizer<RegisterRead<N>>,
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

pub enum Error<const N: usize, ML, MC, RL, RC> {
    Empty,
    Connection(ConnectError),
    AbdRead(abd::client::error::ReadError<N, RL, RC>),
    AbdWrite(abd::client::error::WriteError<N, ML, MC>),
}
