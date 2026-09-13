//! `vinfo!`/`vdebug!` -- `tracing`-backed analogues of `print::vprintln!`/`veprintln!`, meant as a
//! drop-in replacement wherever per-request/per-op debug output is wanted without paying
//! `vprintln!`'s unconditional cost. `vdebug!` wraps `tracing::debug!`; `vinfo!` wraps
//! `tracing::info!`, for coarser, still-diagnostic events one step up from `vdebug!`'s
//! per-request detail.
//!
//! `vprintln!`/`veprintln!` always run `format!(...)` and always write to stdout/stderr, no matter
//! whether anything is watching -- confirmed (via `perf record -g`) to cost real CPU
//! (`core::fmt::write`, `Debug::fmt`) *and* real cross-thread contention (all worker threads
//! serialize on Rust's single global stderr lock) on every call, every request, unconditionally
//! (see `claude-docs/PROFILING.md` §7.7).
//!
//! `tracing`'s macros check whether the target level is enabled *before* evaluating their
//! arguments (a cached atomic load per callsite, via `Callsite::interest`) -- with no global
//! `Subscriber` installed (the default: nothing calls `tracing_subscriber::fmt().init()` or
//! similar), every level is reported disabled and the call is just that cached check, no
//! `format!`, no write, no lock. A binary that wants to see the output opts in explicitly (e.g.
//! `echo_server`'s `main` installing an `EnvFilter`-driven subscriber, gated by `RUST_LOG`) --
//! everyone else, including every benchmark run in this codebase, pays nothing by default.
use vstd::prelude::*;

verus! {

#[macro_export]
macro_rules! vinfo {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
            tracing::info!($($arg)*);
        }
        #[cfg(verus_only)]
        {
        }
    };
}

#[macro_export]
macro_rules! vdebug {
    ($($arg:tt)*) => {
        #[cfg(not(verus_only))]
        {
            tracing::debug!($($arg)*);
        }
        #[cfg(verus_only)]
        {
        }
    };
}

} // verus!
