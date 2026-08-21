use std::error::Error;
use std::fmt::Debug;
use std::fmt::Display;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::convert::FromSpecImpl;

verus! {

#[derive(Debug)]
pub enum TryListenError {
    Empty,
    Disconnected,
    NoFreePorts,
    Io(std::io::Error),
}

#[derive(Debug)]
pub enum TryRecvError {
    Empty,
    Disconnected,
    Io(std::io::Error),
}

#[derive(Debug)]
pub enum SendError {
    Failed,
    Io(std::io::Error),
}

#[derive(Debug)]
pub enum InvokeError {
    Io(std::io::Error),
    FailedToSend,
    Disconnected,
    Empty,
}

#[derive(Debug)]
pub enum ConnectError {
    Failed,
    NoFreePorts,
    Io(std::io::Error),
}

// TryListenError
//
impl Error for TryListenError {
    /* TODO(verus): verus bug
    Uncommenting this `source()` impl (returning `Option<&(dyn Error + 'static)>`) makes
    `cargo verus verify -p verdist` fail during Verus's internal "Trait-Conflict-Checker" pass
    (rust_verify/src/trait_check.rs, which re-emits a synthetic `dummyrs.rs` using placeholder
    types like `struct Dyn<const N: usize, A>(Box<A>, [bool])` to check that the axioms Verus
    generates for trait impls don't conflict). The checker fails to also derive that its `Dyn<N, ()>`
    placeholder for the `dyn Error` trait object satisfies `Error`'s supertrait bounds (`Debug`,
    `Display`), and emits:

        error[E0277]: the trait bound `Dyn<0, ()>: T151_Display` is not satisfied
        error[E0277]: the trait bound `Dyn<0, ()>: T152_Debug` is not satisfied
        note: This error was found in Verus's Trait-Conflict-Checker
        error: could not compile `verdist` (lib) due to 2 previous errors

    Reproduced against Verus 0.2026.08.13 (commit 8fe3542, dirty checkout at ../verus). This
    reproduces with a single `source()` impl uncommented (i.e. it isn't specific to having several
    at once), and is independent of the pre-existing unrelated "field expression for an opaque
    datatype" errors in network/impls/{tcp,udp,modelled}.rs that also currently break
    `cargo verus verify -p verdist` (those abort compilation earlier, before this pass runs, so
    that bug was masked until those are also fixed).

    Searched https://github.com/verus-lang/verus/issues for a matching tracked issue (checked
    #1310 "[Trait-conflict-checker] Trait bound is not satisfied (external impl of a trait)",
    #1519, #1547, #1601, #1172, and discussion #1047 "Supporting dyn soundly") but none matches
    this exact "Dyn<N, A> doesn't satisfy the impl's supertrait bounds" shape closely enough to
    link with confidence. #1310 is the closest analog (same Trait-Conflict-Checker component,
    same "synthetic placeholder type doesn't satisfy trait bound" pattern, just via a different
    placeholder family `C<N, A>` instead of `Dyn<N, A>`, and a different trait). If filing a new
    issue, this comment plus the error above should be enough for a minimal repro.

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TryListenError::Io(io) => Some(io),
            _ => None,
        }
    }
    */

}

impl From<std::io::Error> for TryListenError {
    fn from(value: std::io::Error) -> TryListenError {
        TryListenError::Io(value)
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<std::io::Error> for TryListenError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: std::io::Error) -> TryListenError {
        TryListenError::Io(value)
    }
}

impl From<crossbeam_channel::TryRecvError> for TryListenError {
    fn from(value: crossbeam_channel::TryRecvError) -> TryListenError {
        if value.is_empty() {
            TryListenError::Empty
        } else {
            TryListenError::Disconnected
        }
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<crossbeam_channel::TryRecvError> for TryListenError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: crossbeam_channel::TryRecvError) -> TryListenError {
        if value is Empty {
            TryListenError::Empty
        } else {
            TryListenError::Disconnected
        }
    }
}

// TryRecvError
//
impl Error for TryRecvError {
    /* TODO(verus): verus bug -- same as TryListenError's `Error` impl above, see its comment
    for the full repro/error and the upstream-issue search notes.

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TryRecvError::Io(io) => Some(io),
            _ => None,
        }
    }
    */

}

impl From<std::io::Error> for TryRecvError {
    fn from(value: std::io::Error) -> TryRecvError {
        TryRecvError::Io(value)
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<std::io::Error> for TryRecvError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: std::io::Error) -> TryRecvError {
        TryRecvError::Io(value)
    }
}

impl From<crossbeam_channel::TryRecvError> for TryRecvError {
    fn from(value: crossbeam_channel::TryRecvError) -> TryRecvError {
        if value.is_empty() {
            TryRecvError::Empty
        } else {
            TryRecvError::Disconnected
        }
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<crossbeam_channel::TryRecvError> for TryRecvError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: crossbeam_channel::TryRecvError) -> TryRecvError {
        if value is Empty {
            TryRecvError::Empty
        } else {
            TryRecvError::Disconnected
        }
    }
}

// SendError
//
impl Error for SendError {
    /* TODO(verus): verus bug -- same as TryListenError's `Error` impl above, see its comment
    for the full repro/error and the upstream-issue search notes.

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            SendError::Io(io) => Some(io),
            _ => None,
        }
    }
    */

}

impl<S> From<crossbeam_channel::SendError<S>> for SendError {
    fn from(_value: crossbeam_channel::SendError<S>) -> SendError {
        SendError::Failed
    }
}

#[cfg(verus_only)]
impl<S> FromSpecImpl<crossbeam_channel::SendError<S>> for SendError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: crossbeam_channel::SendError<S>) -> SendError {
        SendError::Failed
    }
}

impl From<std::io::Error> for SendError {
    fn from(value: std::io::Error) -> SendError {
        SendError::Io(value)
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<std::io::Error> for SendError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: std::io::Error) -> SendError {
        SendError::Io(value)
    }
}

// InvokeError
//
impl Error for InvokeError {
    /* TODO(verus): verus bug -- same as TryListenError's `Error` impl above, see its comment
    for the full repro/error and the upstream-issue search notes.

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            InvokeError::Io(io) => Some(io),
            _ => None,
        }
    }
    */

}

impl From<SendError> for InvokeError {
    fn from(value: SendError) -> InvokeError {
        match value {
            SendError::Failed => InvokeError::FailedToSend,
            SendError::Io(io) => InvokeError::Io(io),
        }
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<SendError> for InvokeError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: SendError) -> InvokeError {
        match value {
            SendError::Failed => InvokeError::FailedToSend,
            SendError::Io(io) => InvokeError::Io(io),
        }
    }
}

impl From<TryRecvError> for InvokeError {
    fn from(value: TryRecvError) -> InvokeError {
        match value {
            TryRecvError::Empty => InvokeError::Empty,
            TryRecvError::Disconnected => InvokeError::Disconnected,
            TryRecvError::Io(io) => InvokeError::Io(io),
        }
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<TryRecvError> for InvokeError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: TryRecvError) -> InvokeError {
        match value {
            TryRecvError::Empty => InvokeError::Empty,
            TryRecvError::Disconnected => InvokeError::Disconnected,
            TryRecvError::Io(io) => InvokeError::Io(io),
        }
    }
}

// ConnectError
//
impl Error for ConnectError {
    /* TODO(verus): verus bug -- same as TryListenError's `Error` impl above, see its comment
    for the full repro/error and the upstream-issue search notes.

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ConnectError::Io(io) => Some(io),
            _ => None,
        }
    }
    */

}

impl From<std::io::Error> for ConnectError {
    fn from(value: std::io::Error) -> ConnectError {
        ConnectError::Io(value)
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<std::io::Error> for ConnectError {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: std::io::Error) -> ConnectError {
        ConnectError::Io(value)
    }
}

} // verus!
//=======
// Display impls (unverified)
impl Display for TryListenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TryListenError::Empty => f.write_str("TryListenError: no message came"),
            TryListenError::Disconnected => f.write_str("TryListenError: listenning channel broke"),
            TryListenError::NoFreePorts => f.write_str("TryListenError: no free ports"),
            TryListenError::Io(_) => f.write_str("TryListenError: io error"),
        }
    }
}

impl Display for TryRecvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TryRecvError::Empty => f.write_str("TryRecvError: no message came"),
            TryRecvError::Disconnected => f.write_str("TryRecvError: channel broke"),
            TryRecvError::Io(_) => f.write_str("TryRecvError: io error"),
        }
    }
}

impl Display for SendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SendError::Failed => f.write_str("SendError: unknown error"),
            SendError::Io(_) => f.write_str("SendError: io error"),
        }
    }
}

impl Display for ConnectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConnectError::Failed => f.write_str("ConnectError: unknown error"),
            ConnectError::NoFreePorts => f.write_str("ConnectError: no free ports on the server"),
            ConnectError::Io(_) => f.write_str("ConnectError: io error"),
        }
    }
}

impl Display for InvokeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InvokeError::FailedToSend => f.write_str("InvokeError: failed to send"),
            InvokeError::Empty => f.write_str("InvokeError: no reply came"),
            InvokeError::Disconnected => f.write_str("InvokeError: channel broke"),
            InvokeError::Io(_) => f.write_str("InvokeError: io error"),
        }
    }
}
