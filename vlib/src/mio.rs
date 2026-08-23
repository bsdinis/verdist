//! Minimal trusted surface for `mio`'s epoll/kqueue/IOCP abstraction, used by
//! `verdist::service::Server::run_epoll` to block a thread on real fd readiness instead of
//! spinning or sleeping-with-backoff.
//!
//! Follows this codebase's existing convention for foreign crates (see `crossbeam.rs`,
//! `serde.rs`, `flexbuffers.rs`, `std/net.rs`): an `external_type_specification` shim makes each
//! foreign type nameable inside `verus! {}`, and a tight set of `assume_specification`s gives
//! trusted signatures to the handful of functions actually called. Everything built on top of
//! these (in `verdist::service`) is ordinary verified Verus code -- these are the only new
//! trusted primitives this rewrite introduces.
//!
//! `mio::Token`/`SourceFd`/`Interest` are deliberately *not* given their own shims: they carry no
//! proof-relevant content (nothing about correctness ever depends on which token value labels a
//! registration), so exposing them as separate Verus-visible types would just be more surface
//! for no benefit. Instead, "register/deregister one fd for read-readiness" is collapsed into two
//! minimal named leaf functions below, each given a single `assume_specification` -- a tighter
//! trust boundary than assembling `Token`/`SourceFd`/`Interest` from verified code would be.

use vstd::prelude::*;

/// Registers `fd` on `registry` for read-readiness notifications, keyed by `fd` itself (raw fds
/// are unique among a process's open files while open, so no separate token allocator is
/// needed). Real `mio::Token`/`SourceFd`/`Interest` construction lives entirely in this one
/// plain function's body rather than being reconstructed by verified callers.
pub fn mio_register_readable(registry: &mio::Registry, fd: i32, token: usize) -> std::io::Result<
    (),
> {
    registry.register(&mut mio::unix::SourceFd(&fd), mio::Token(token), mio::Interest::READABLE)
}

/// Drops the readiness registration for `fd`.
pub fn mio_deregister(registry: &mio::Registry, fd: i32) -> std::io::Result<()> {
    registry.deregister(&mut mio::unix::SourceFd(&fd))
}

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExPoll(mio::Poll);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExRegistry(mio::Registry);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExEvents(mio::Events);

pub assume_specification[ mio::Poll::new ]() -> (r: std::io::Result<mio::Poll>)
    no_unwind
;

pub assume_specification[ mio::Poll::registry ](p: &mio::Poll) -> (r: &mio::Registry)
    no_unwind
;

pub assume_specification[ mio::Poll::poll ](
    p: &mut mio::Poll,
    events: &mut mio::Events,
    timeout: Option<std::time::Duration>,
) -> (r: std::io::Result<()>)
    no_unwind
;

pub assume_specification[ mio::Registry::try_clone ](r: &mio::Registry) -> (r2: std::io::Result<
    mio::Registry,
>)
    no_unwind
;

pub assume_specification[ mio::Events::with_capacity ](capacity: usize) -> (r: mio::Events)
    no_unwind
;

pub assume_specification[ mio_register_readable ](
    registry: &mio::Registry,
    fd: i32,
    token: usize,
) -> (res: std::io::Result<()>)
    no_unwind
;

pub assume_specification[ mio_deregister ](registry: &mio::Registry, fd: i32) -> (res: std::io::Result<
    (),
>)
    no_unwind
;

} // verus!
