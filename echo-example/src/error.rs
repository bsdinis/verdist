use vstd::prelude::*;

use verdist::network::error::ConnectError;

impl From<ConnectError> for Error {
    fn from(value: ConnectError) -> Self {
        Error::Connection(value)
    }
}

impl From<echo::client::error::EchoError> for Error {
    fn from(value: echo::client::error::EchoError) -> Self {
        Error::EchoError(value)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Connection(e) => Some(e),
            Error::EchoError(e) => Some(e),
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::EchoError(e) => e.fmt(f),
        }
    }
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::EchoError(e) => e.fmt(f),
        }
    }
}

verus! {

pub(crate) enum Error {
    Connection(ConnectError),
    EchoError(echo::client::error::EchoError),
}

} // verus!
