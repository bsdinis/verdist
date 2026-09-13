//! `IoUringTcp*` -- a new, additive `Channel`/`Listener`/`Connector` variant for TCP built on
//! `io_uring` instead of blocking `read`/`write` syscalls (see `network::impls::tcp` for the
//! existing, unmodified blocking-syscall version this sits alongside; nothing in that file was
//! touched to build this one).
//!
//! # UNVERIFIED IN THIS SANDBOX -- read before trusting this code
//!
//! `io_uring_setup` returns `EPERM` in the sandbox this was written in (confirmed via a minimal
//! standalone probe: `IoUring::new(8)` fails immediately, before any op is ever submitted). That
//! means **none of the code in this file has ever actually been run**, let alone benchmarked --
//! it was written by reading the `io-uring` crate's source (`opcode::{Read,Write}`'s builder
//! shapes, `IoUring::{submission,completion,submit_and_wait}`'s signatures) and reasoning by
//! analogy with `network::impls::tcp`'s already-working blocking implementation, not by testing.
//!
//! In particular, the *one thing this whole exercise's own design doc
//! (`claude-files/io_uring_design.md`) said must be measured, not assumed*, is still unmeasured:
//! whether an `io_uring` `Read`/`Recv` op on a socket with `SO_RCVTIMEO` set actually honors that
//! timeout the way a direct blocking `read(2)`/`recv(2)` call does. This file assumes it does (see
//! `is_recv_timeout_errno`'s use in `read_exact_or_none`) -- exactly the kind of assumption that
//! turned out to be wrong for `recvmmsg` earlier this session. **Before relying on this in
//! production: build it somewhere `io_uring_setup` actually works, and directly confirm that
//! assumption** (a pre-queued read completing near-instantly vs. an empty socket actually waiting
//! out the ~2ms timeout) before trusting the liveness/backoff behavior at all.
//!
//! # Scope (Phase A only)
//!
//! Deliberately the simplest correct thing, not the fast thing: one `io_uring` ring per
//! connection, one op submitted and waited on at a time (`submit_and_wait(1)`) -- semantically a
//! drop-in for `Channel`'s existing `&self`-based `send`/`try_recv` contract, so
//! `Server::poll_shard`/`poll_shard_epoll` need no changes to use it. No `SQPOLL`, no linked
//! timeouts, no cross-connection batching (`Server`'s shard-level dispatch loop still visits one
//! connection at a time) -- those are exactly the follow-ups the design doc calls "Phase B" and
//! explicitly defers until Phase A has real, measured numbers to justify them.
use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::net::SocketAddr;
use std::net::TcpStream;
use std::net::ToSocketAddrs;
use std::os::fd::AsRawFd;

use io_uring::opcode;
use io_uring::types;
use io_uring::IoUring;

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::network::channel::Connector;
use crate::network::channel::Listener;
use crate::network::channel::RawFdChannel;
use crate::network::channel::RawFdListener;
use crate::network::error::ConnectError;
use crate::network::error::TryListenError;

#[cfg(verus_only)]
use vlib::serde::ExDeserialize;
#[cfg(verus_only)]
use vlib::serde::ExSerialize;

use vstd::prelude::*;

/// `submit_and_wait(1)`, retrying if the underlying `io_uring_enter` syscall is interrupted by a
/// signal. This matters more than an ordinary EINTR retry: submission and the wait happen in the
/// *same* syscall, so by the time `io_uring_enter` can return `EINTR` the SQE has already been
/// accepted by the kernel and is in flight -- bailing out here without retrying would abandon a
/// live op whose buffer the caller is about to drop/reuse (a real use-after-free), and would leave
/// its eventual completion sitting in the CQ ring to be wrongly reaped by the *next*, unrelated
/// call. Caught by review before this ever shipped anywhere it could run.
///
/// Lives outside `verus! {}` (unlike this file's other helpers): `IoUring`/`squeue::Entry`/
/// `cqueue::Entry` have no `external_type_specification` shim, so a fn *signature* mentioning
/// `&mut IoUring` directly (not hidden behind an already-opaque `external_body` struct's `&self`)
/// isn't representable even with `#[verifier::external_body]` -- that annotation skips checking a
/// function's *body*, but its signature still has to type-check in Verus's model.
fn submit_and_wait_1(ring: &mut IoUring) -> std::io::Result<()> {
    loop {
        match ring.submit_and_wait(1) {
            Ok(_) => return Ok(()),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
}

/// Like `submit_and_wait_1`, but never waits: flushes queued SQEs to the kernel
/// (`io_uring_enter` with no `GETEVENTS` flag) and returns as soon as the kernel has accepted
/// them, regardless of whether any have completed yet. Used by the receive path instead of
/// `submit_and_wait_1` -- see `poll_read`'s doc for why.
fn submit_now(ring: &mut IoUring) -> std::io::Result<()> {
    loop {
        match ring.submit() {
            Ok(_) => return Ok(()),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
}

/// Submits a `Read` op for `dst` if `*op_in_flight` is `false`, then does a **non-blocking** peek
/// of the completion queue -- never `submit_and_wait`. Returns `Ok(None)` if nothing has completed
/// yet (and sets `*op_in_flight = true`, so the caller knows not to submit a second op for the
/// same memory -- doing so while one is still in flight would violate `SubmissionQueue::push`'s
/// own safety contract, see this file's other `unsafe` docs); `Ok(Some(result))` with the raw
/// `cqe.result()` once a completion has been reaped (resetting `*op_in_flight = false`).
///
/// This is the fix for the io_uring "wakeup bug" (`claude-docs/PROFILING.md` §7.4 item 2). The
/// original design submitted one `Read` op and `submit_and_wait`ed on it, assuming
/// `SO_RCVTIMEO`/`O_NONBLOCK` would make that wait return quickly with "no data yet" on an empty
/// socket, the same way a direct blocking `recv(2)` with a receive timeout does. Directly testing
/// this against a real empty socket (both blocking- and non-blocking-mode) showed io_uring's
/// `Read` op honors **neither**: it simply waits until real data arrives, with no timeout and no
/// `EAGAIN`-on-empty behavior at all. `submit_and_wait`ing on it therefore blocked the whole
/// shard-scan loop on whichever connection it visited first that had nothing to read yet, instead
/// of bailing out after ~2ms the way the plain TCP/UDP backends do -- serializing per-connection
/// turnaround and producing the missed-wakeup-shaped context-switch cost this session's benchmark
/// saw. The fix has to live on the completion-queue side, not the socket: submit once, then only
/// ever *peek* for it, exactly as this function does. Lives outside `verus! {}` for the same
/// reason as `submit_and_wait_1`: `&mut IoUring` isn't representable in a signature Verus has to
/// check, even under `#[verifier::external_body]`.
fn poll_read(
    ring: &mut IoUring,
    fd: i32,
    op_in_flight: &mut bool,
    dst: &mut [u8],
) -> std::io::Result<Option<i32>> {
    if !*op_in_flight {
        let entry = opcode::Read::new(types::Fd(fd), dst.as_mut_ptr(), dst.len() as u32).build()
            .user_data(0);
        // SAFETY: same contract as `writev_once_raw`'s (see its doc): `dst`'s memory must stay
        // valid and unaliased until this op's completion is reaped. It does: `dst` is borrowed
        // from the caller's persistent per-stream state (not a transient local), which is never
        // touched again -- by this connection's single owner thread, per this file's own
        // single-owner-thread invariant -- until `*op_in_flight` is observed `false` again, which
        // only happens once the completion below has actually been reaped.
        unsafe {
            ring.submission().push(&entry).map_err(
                |e| std::io::Error::other(format!("io_uring submission queue full: {e}")),
            )?;
        }
        submit_now(ring)?;
        *op_in_flight = true;
    }
    match ring.completion().next() {
        None => Ok(None),
        Some(cqe) => {
            *op_in_flight = false;
            Ok(Some(cqe.result()))
        }
    }
}

/// Submits one `Writev` op for `iovecs` (built by `writev_all` below), waits for its single
/// completion, and returns the raw result (negative errno, or bytes written). Same split as
/// `submit_and_wait_1`: `libc::iovec` -- like `IoUring` itself -- has no `external_type_specification`
/// shim, so a fn *signature* naming `&[libc::iovec]` isn't representable even under
/// `#[verifier::external_body]` (which only skips body-checking, not signature-checking), so this
/// lives outside `verus! {}` entirely rather than as a method inside it.
fn writev_once_raw(ring: &mut IoUring, fd: i32, iovecs: &[libc::iovec]) -> std::io::Result<i32> {
    let entry = opcode::Writev::new(types::Fd(fd), iovecs.as_ptr(), iovecs.len() as u32).build()
        .user_data(0);
    // SAFETY: same contract as `IoUringTcpStream::read_once`/`writev_once_raw` (see their doc):
    // `SubmissionQueue::push` requires the memory named by every `iovec` -- including the
    // `iovec` array itself, which the kernel also reads -- to stay valid and unaliased until
    // the op's completion is reaped. `iovecs` here is a caller-owned local on the stack, and this
    // function submits and immediately `submit_and_wait_1`s for exactly that one completion
    // before returning, so nothing named by `iovecs` is ever touched again after that point.
    unsafe {
        ring.submission().push(&entry).map_err(
            |e| std::io::Error::other(format!("io_uring submission queue full: {e}")),
        )?;
    }
    submit_and_wait_1(ring)?;
    let cqe = ring.completion().next().expect(
        "submit_and_wait_1 returned Ok, so at least one completion must be present",
    );
    Ok(cqe.result())
}

/// `writev(2)`-shaped send of `prefix` followed by `payload` as two `iovec`s in a single SQE per
/// attempt, instead of copying both into one contiguous buffer first (which is what `send`, below,
/// used to do). Mirrors `tcp.rs`'s vectored-write `send` (one `write_vectored` call, no copy) --
/// see that function's doc for the atomicity discussion, which applies verbatim here. Lives outside
/// `verus! {}` for the same reason as `writev_once_raw`: it builds `libc::iovec` values directly.
fn writev_all(ring: &mut IoUring, fd: i32, mut prefix: &[u8], mut payload: &[u8]) -> std::io::Result<
    (),
> {
    loop {
        if prefix.is_empty() && payload.is_empty() {
            return Ok(());
        }
        let iovecs_storage = [
            libc::iovec { iov_base: prefix.as_ptr() as *mut libc::c_void, iov_len: prefix.len() },
            libc::iovec { iov_base: payload.as_ptr() as *mut libc::c_void, iov_len: payload.len() },
        ];
        let iovecs: &[libc::iovec] = if prefix.is_empty() {
            &iovecs_storage[1..]
        } else {
            &iovecs_storage[..]
        };
        let res = writev_once_raw(ring, fd, iovecs)?;
        if res < 0 {
            let errno = res.wrapping_neg();
            if errno == libc::EINTR {
                continue;
            }
            vlib::veprintln!("warning: non-atomic write of len + payload failed");
            return Err(std::io::Error::from_raw_os_error(errno));
        }
        if res == 0 {
            vlib::veprintln!("warning: non-atomic write of len + payload failed");
            return Err(
                std::io::Error::new(std::io::ErrorKind::WriteZero, "failed to write whole buffer"),
            );
        }
        let mut n = res as usize;
        if !prefix.is_empty() {
            let take = n.min(prefix.len());
            prefix = &prefix[take..];
            n -= take;
        }
        if n > 0 {
            let take = n.min(payload.len());
            payload = &payload[take..];
        }
    }
}

verus! {

/// Submission/completion ring size. 8 is generous for this file's one-op-at-a-time usage (never
/// more than one op in flight per connection); picked, not measured -- see the file's top doc.
const RING_ENTRIES: u32 = 8;

/// Kept only as a defensive fallback inside `try_recv`'s loop (a completed op reporting this errno
/// would previously have driven the old `SO_RCVTIMEO`-based bail-out): direct testing (see
/// `poll_read`'s doc) showed io_uring's `Read` op never actually completes with it in practice, so
/// this is not load-bearing for correctness, just a "treat it as not-ready-yet rather than a hard
/// error" safety net should some kernel/path ever surface it.
#[verifier::external_body]
fn is_recv_timeout_errno(errno: i32) -> bool {
    errno == libc::EAGAIN || errno == libc::EWOULDBLOCK || errno == libc::ETIMEDOUT
}

/// Per-connection receive state, resumed across calls to `try_recv` since a `Read` op may
/// complete on one call and be picked up (or still be in flight) on a later one -- unlike the old
/// design, which submitted and fully waited out one op per call. `external_body`: a plain
/// state-holder with no spec surface of its own, held only inside `IoUringTcpStream`'s own
/// already-opaque cell (same treatment as that struct's `ring` field).
#[verifier::external_body]
struct TcpRecvState {
    op_in_flight: bool,
    reading_payload: bool,
    len_buf: [u8; 4],
    filled: usize,
    payload_buf: Vec<u8>,
}

impl TcpRecvState {
    #[verifier::external_body]
    fn new() -> Self {
        TcpRecvState {
            op_in_flight: false,
            reading_payload: false,
            len_buf: [0u8; 4],
            filled: 0,
            payload_buf: Vec::new(),
        }
    }
}

/// `io_uring`-backed analogue of `network::impls::tcp::TypedTcpStream`. See this file's top doc
/// for what's unverified and why interior mutability (not `&mut self`) is needed here: `send`/
/// `try_recv` take `&self` (required by the `Channel` trait, whose signature this file does not
/// change), but submitting into and reaping from an `io_uring` ring is inherently a mutating
/// operation on the ring's own submission/completion cursors.
// `#[verifier::external_body]`: same reason as `TypedTcpStream` before it dropped its own cell
// (see tcp.rs's history) -- an `UnsafeCell` field has no Verus spec surface, which makes every
// field opaque to Verus even from this type's own impl block, so every method touching a field
// directly needs the annotation too. Additionally opaque here regardless: `io_uring::IoUring`
// itself is an external (non-Verus-aware) type with no `external_type_specification` shim.
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct IoUringTcpStream<R, S> {
    inner: TcpStream,
    // SAFETY (single-owner-thread invariant): only the single thread that owns this channel's
    // connection ever calls `send`/`try_recv` (server side: `ServerOwnershipTransferPlan.md`;
    // client side: one thread per channel) -- exactly the same caller invariant
    // `TypedTcpStream`/`TypedUdpSocket` used to rely on for their own (since-removed) `UnsafeCell`
    // fields, and for the same reason: `Channel::send`/`try_recv` take `&self`, not `&mut self`,
    // so nothing here is enforced by the type system, only by that documented discipline. Unlike
    // those types' old cells, this one is *not* `Sync` (no `unsafe impl` anywhere in this file) --
    // nothing requires it to be (see `Server::_marker`'s `PhantomData<C::Id>` doc in
    // `service/mod.rs` for why `Channel` impls no longer need `Sync` at all).
    ring: UnsafeCell<IoUring>,
    recv_state: UnsafeCell<TcpRecvState>,
    _marker: PhantomData<(R, S)>,
}

impl<R, S> IoUringTcpStream<R, S> where for <'de>R: serde::Deserialize<'de>, S: serde::Serialize {
    #[verifier::external_body]
    pub fn new(stream: TcpStream) -> std::io::Result<Self> {
        stream.set_nonblocking(false)?;
        stream.set_nodelay(true)?;
        let ring = IoUring::new(RING_ENTRIES)?;
        Ok(
            IoUringTcpStream {
                inner: stream,
                ring: UnsafeCell::new(ring),
                recv_state: UnsafeCell::new(TcpRecvState::new()),
                _marker: PhantomData,
            },
        )
    }

    /// `#[verifier::external_body]` (rather than a new `assume_specification` for `postcard`,
    /// which Verus's error otherwise suggests): this is a small, self-contained helper with no
    /// `requires`/`ensures` of its own, so trusting its body -- the same treatment every other
    /// I/O-touching function in this `impl` already gets -- is a strictly smaller trust
    /// addition than registering a spec for `postcard`'s own API surface, and needs no new axiom
    /// category (`external_body` is already used throughout this file).
    #[verifier::external_body]
    fn deserialize(buf: &[u8]) -> Result<R, std::io::Error> {
        let value = postcard::from_bytes::<R>(buf).map_err(
            |e|
                {
                    #[cfg(not(verus_only))]
                    { std::io::Error::other(format!("failed to deserialize: {e:?}")) }
                    #[cfg(verus_only)]
                    { std::io::Error::from_raw_os_error(-1) }
                },
        )?;
        Ok(value)
    }

    /// Unlike `tcp.rs`/`udp.rs`, this allocates a fresh `Vec` per call rather than reusing a
    /// thread-local buffer -- that reuse optimization was applied to `tcp.rs`/`udp.rs` earlier
    /// this session but never extended to the io_uring paths; left as-is here (out of scope for
    /// the flexbuffers->postcard swap this function is otherwise part of). `external_body` for
    /// the same reason as `deserialize` above.
    #[verifier::external_body]
    fn serialize(v: &S) -> Result<Vec<u8>, std::io::Error> {
        postcard::to_allocvec(v).map_err(
            |e|
                {
                    #[cfg(not(verus_only))]
                    { std::io::Error::other(format!("failed to serialize: {e:?}")) }
                    #[cfg(verus_only)]
                    { std::io::Error::from_raw_os_error(-1) }
                },
        )
    }

    /// Drives this connection's persistent `TcpRecvState` forward using `poll_read` (never
    /// `submit_and_wait` -- see its doc for why) until either a full message has been read
    /// (`Ok(Some(_))`), no more progress is available right now (`Ok(None)`, leaving whatever was
    /// read so far intact in `recv_state` for the next call), or a real error/EOF occurs.
    #[verifier::external_body]
    pub fn try_recv(&self) -> Result<Option<R>, std::io::Error> {
        let ring = unsafe { &mut *self.ring.get() };
        let state = unsafe { &mut *self.recv_state.get() };
        let fd = self.inner.as_raw_fd();
        loop {
            let dst: &mut [u8] = if state.reading_payload {
                &mut state.payload_buf[state.filled..]
            } else {
                &mut state.len_buf[state.filled..]
            };
            let res = match poll_read(ring, fd, &mut state.op_in_flight, dst)? {
                None => return Ok(None),
                Some(res) => res,
            };
            if res < 0 {
                let errno = res.wrapping_neg();
                if is_recv_timeout_errno(errno) {
                    continue;
                }
                return Err(std::io::Error::from_raw_os_error(errno));
            }
            if res == 0 {
                return Err(
                    std::io::Error::new(
                        std::io::ErrorKind::UnexpectedEof,
                        "peer closed connection mid-message",
                    ),
                );
            }
            state.filled += res as usize;
            if !state.reading_payload {
                if state.filled < state.len_buf.len() {
                    continue;
                }
                let len = u32::from_ne_bytes(state.len_buf) as usize;
                state.filled = 0;
                if len == 0 {
                    // Empty payload: nothing left to read, matches the old
                    // `read_exact_or_none`'s no-op-on-empty-buffer behavior (its `while filled <
                    // buf.len()` loop never issued a read at all when `buf.len() == 0`).
                    let result = Self::deserialize(&[])?;
                    return Ok(Some(result));
                }
                state.payload_buf = vec![0u8; len];
                state.reading_payload = true;
                continue;
            }
            if state.filled < state.payload_buf.len() {
                continue;
            }
            let result = Self::deserialize(&state.payload_buf)?;
            state.filled = 0;
            state.reading_payload = false;
            return Ok(Some(result));
        }
    }

    /// Same `writev(2)`-shaped send as `tcp.rs`'s vectored-write `send` (one op per attempt for
    /// the length-prefix + payload together, no copy to combine them into one buffer first --
    /// unlike this function's own previous version). The actual `iovec` construction/partial-write
    /// retry loop lives in the free function `writev_all`, above this file's `verus! {}` block:
    /// `libc::iovec` has no `external_type_specification` shim, so it can't appear in a signature
    /// Verus has to check, even under `#[verifier::external_body]` (see `writev_all`'s doc) -- but
    /// this method's own signature only ever mentions `&S`/`std::io::Error`, so it keeps its
    /// `#[verifier::external_body]` like every other method here and just delegates.
    #[verifier::external_body]
    pub fn send(&self, v: &S) -> Result<(), std::io::Error> {
        let s = Self::serialize(v)?;
        let len = s.len() as u32;
        let len_bytes = len.to_ne_bytes();
        let ring = unsafe { &mut *self.ring.get() };
        writev_all(ring, self.inner.as_raw_fd(), &len_bytes, &s)
    }

    #[verifier::external_body]
    pub fn local_addr(&self) -> SocketAddr {
        self.inner.local_addr().expect("local addr should be set")
    }

    #[verifier::external_body]
    pub fn peer_addr(&self) -> SocketAddr {
        self.inner.peer_addr().expect("peer addr should be set")
    }

    /// The underlying stream's raw fd, for `Server::run_epoll` to register with an `mio::Poll`
    /// instance (see `crate::network::channel::RawFdChannel`). NOT the ring's own fd -- `mio`
    /// polls readiness on the TCP socket itself, same as the blocking-syscall transport; the ring
    /// is this file's own private implementation detail underneath `send`/`try_recv`.
    #[verifier::external_body]
    pub fn raw_fd(&self) -> i32 {
        self.inner.as_raw_fd()
    }
}

/// Listens for and hands off raw `TcpStream`s exactly like `tcp.rs`'s `TcpListener` (same
/// bind/accept/handshake shape -- duplicated, not shared, so this file never has to reach into
/// `tcp.rs`'s private fields or modify it at all, per this variant's whole point: existing
/// TCP/UDP code stays untouched).
#[verifier::external_body]
pub struct IoUringTcpListener {
    listener: std::net::TcpListener,
    id: u64,
}

impl IoUringTcpListener {
    #[verifier::external_body]
    pub fn listen<A: ToSocketAddrs>(addr: A, id: u64) -> std::io::Result<Self> {
        let listener = std::net::TcpListener::bind(addr)?;
        listener.set_nonblocking(true).expect("this should never fail");
        Ok(IoUringTcpListener { listener, id })
    }
}

#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct IoUringTcpConnector<A: ToSocketAddrs> {
    listening_addr: A,
    #[allow(dead_code)]
    server_id: u64,
}

impl<A: ToSocketAddrs> IoUringTcpConnector<A> {
    #[verifier::external_body]
    pub fn new(listening_addr: A, server_id: u64) -> std::io::Result<Self> {
        Ok(IoUringTcpConnector { listening_addr, server_id })
    }
}

/// Channel TO Client
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct IoUringClientChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    stream: IoUringTcpStream<R, S>,
    server_id: u64,
    client_id: u64,
}

/// Channel TO Server
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct IoUringServerChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    stream: IoUringTcpStream<R, S>,
    server_id: u64,
    client_id: u64,
}

impl<K, R, S> IoUringClientChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        stream: IoUringTcpStream<R, S>,
    ) -> Self {
        IoUringClientChannel { pred, stream, server_id, client_id }
    }
}

impl<K, R, S> IoUringServerChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        stream: IoUringTcpStream<R, S>,
    ) -> Self {
        IoUringServerChannel { pred, stream, server_id, client_id }
    }
}

impl<K, R, S> Channel for IoUringClientChannel<K, R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    type R = R;

    type S = S;

    type Id = (u64, u64);

    type K = K;

    #[verifier::external_body]
    closed spec fn constant(self) -> Self::K {
        self.pred@
    }

    #[verifier::external_body]
    fn try_recv(&self) -> Result<R, crate::network::error::TryRecvError> {
        match self.stream.try_recv() {
            Ok(Some(x)) => Ok(x),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        self.stream.send(v).map_err(|e| e.into())
    }

    #[verifier::external_body]
    fn id(&self) -> Self::Id {
        (self.server_id, self.client_id)
    }

    #[verifier::external_body]
    closed spec fn spec_id(self) -> Self::Id {
        (self.server_id, self.client_id)
    }
}

impl<K, R, S> RawFdChannel for IoUringClientChannel<K, R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    fn raw_fd(&self) -> i32 {
        self.stream.raw_fd()
    }
}

impl<K, R, S> Channel for IoUringServerChannel<K, R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    type R = R;

    type S = S;

    type Id = (u64, u64);

    type K = K;

    #[verifier::external_body]
    closed spec fn constant(self) -> Self::K {
        self.pred@
    }

    #[verifier::external_body]
    fn try_recv(&self) -> Result<R, crate::network::error::TryRecvError> {
        match self.stream.try_recv() {
            Ok(Some(x)) => Ok(x),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        self.stream.send(v).map_err(|e| e.into())
    }

    #[verifier::external_body]
    fn id(&self) -> Self::Id {
        (self.client_id, self.server_id)
    }

    #[verifier::external_body]
    closed spec fn spec_id(self) -> Self::Id {
        (self.client_id, self.server_id)
    }
}

// Same trust-boundary note as `tcp.rs`'s identical `try_accept_raw`/`wrap_raw` pair: the real work
// here is a blocking accept + client-id handshake over a raw socket, which Verus cannot reason
// about, so `r.constant() == gen_pred(self)` is assumed rather than checked -- it holds by
// construction since the body does nothing to `pred` other than store the given ghost value
// verbatim.
impl<K, R, S> Listener<IoUringClientChannel<K, R, S>> for IoUringTcpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.id
    }

    type Raw = (TcpStream, u64);

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn try_accept_raw(&self) -> Result<(u64, Self::Raw), TryListenError> {
        let (mut stream, addr) = match self.listener.accept() {
            Ok(res) => res,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                return Err(TryListenError::Empty);
            },
            Err(e) => {
                return Err(e.into());
            },
        };

        let mut client_id_buf = [0u8;8];
        stream.set_nonblocking(false).expect("this should never fail");
        std::io::Read::read_exact(&mut stream, &mut client_id_buf)?;
        std::io::Write::write_all(&mut stream, &self.id.to_ne_bytes())?;
        let client_id = u64::from_ne_bytes(client_id_buf);
        stream.set_nonblocking(true).expect("this should never fail");

        Ok((client_id, (stream, client_id)))
    }

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn wrap_raw(&self, raw: Self::Raw, gen_pred: Ghost<spec_fn(&Self) -> K>) -> (r: Result<
        IoUringClientChannel<K, R, S>,
        TryListenError,
    >) {
        let (stream, client_id) = raw;
        let pred = Ghost(gen_pred@(self));
        let tstream = IoUringTcpStream::new(stream)?;
        let chan = IoUringClientChannel::new(pred, self.id, client_id, tstream);

        vlib::veprintln!("[server|{:>3}]: accepted connection from client {client_id} (channel_id: {:?}) [io_uring]", self.id, chan.id());

        Ok(chan)
    }
}

impl<K, R, S> RawFdListener<IoUringClientChannel<K, R, S>> for IoUringTcpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    fn raw_fd(&self) -> i32 {
        self.listener.as_raw_fd()
    }
}

impl<K, R, S, A> Connector<IoUringServerChannel<K, R, S>> for IoUringTcpConnector<A> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
    A: ToSocketAddrs + Clone,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.server_id
    }

    #[verifier::external_body]
    fn connect<F>(&self, local_id: u64, gen_pred: F) -> (r: Result<
        IoUringServerChannel<K, R, S>,
        ConnectError,
    >) where F: FnOnce(&Self, u64) -> Ghost<K> {
        vlib::veprintln!(
            "[client|{:>3}]: connecting to server [io_uring]", local_id,
        );
        let mut stream = TcpStream::connect(self.listening_addr.clone())?;
        stream.set_nonblocking(false).expect("this should never fail");
        std::io::Write::write_all(&mut stream, &local_id.to_ne_bytes())?;
        let mut server_id_buf = [0u8;8];
        std::io::Read::read_exact(&mut stream, &mut server_id_buf)?;
        let server_id = u64::from_ne_bytes(server_id_buf);
        stream.set_nonblocking(true).expect("this should never fail");

        let tstream = IoUringTcpStream::new(stream)?;
        let pred = gen_pred(self, local_id);

        let peer_addr = tstream.peer_addr();
        let chan = IoUringServerChannel::new(pred, server_id, local_id, tstream);
        vlib::veprintln!(
            "[client|{:>3}]: connected to server {server_id} (channel_id: {:?}, server addr: {:?}) [io_uring]", local_id, chan.id(),
            peer_addr
        );
        Ok(chan)
    }
}

} // verus!
