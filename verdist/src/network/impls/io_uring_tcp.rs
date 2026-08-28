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
use std::time::Duration;

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

verus! {

/// Same value as `network::impls::tcp::RECV_TIMEOUT_MILLIS` -- kept as a literal, separate
/// constant (not re-exported from `tcp.rs`) so this file has zero dependency on that one beyond
/// the plain, already-`pub` `TcpStream`/std types every transport shares.
const RECV_TIMEOUT_MILLIS: u64 = 2;

/// Submission/completion ring size. 8 is generous for this file's one-op-at-a-time usage (never
/// more than one op in flight per connection); picked, not measured -- see the file's top doc.
const RING_ENTRIES: u32 = 8;

#[verifier::external_body]
fn is_recv_timeout_errno(errno: i32) -> bool {
    errno == libc::EAGAIN || errno == libc::EWOULDBLOCK || errno == libc::ETIMEDOUT
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
    _marker: PhantomData<(R, S)>,
}

impl<R, S> IoUringTcpStream<R, S> where for <'de>R: serde::Deserialize<'de>, S: serde::Serialize {
    #[verifier::external_body]
    pub fn new(stream: TcpStream) -> std::io::Result<Self> {
        stream.set_nonblocking(false)?;
        stream.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS)))?;
        stream.set_nodelay(true)?;
        let ring = IoUring::new(RING_ENTRIES)?;
        Ok(IoUringTcpStream { inner: stream, ring: UnsafeCell::new(ring), _marker: PhantomData })
    }

    fn deserialize(buf: &[u8]) -> Result<R, std::io::Error> {
        let root = flexbuffers::Reader::get_root(buf).map_err(
            |e|
                {
                    #[cfg(not(verus_only))]
                    { std::io::Error::other(format!("failed to deserialize: {e:?}")) }
                    #[cfg(verus_only)]
                    { std::io::Error::from_raw_os_error(-1) }
                },
        )?;
        let value = R::deserialize(root).map_err(
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

    fn serialize(v: &S) -> Result<flexbuffers::FlexbufferSerializer, std::io::Error> {
        let mut s = flexbuffers::FlexbufferSerializer::new();
        v.serialize(&mut s).map_err(
            |e|
                {
                    #[cfg(not(verus_only))]
                    { std::io::Error::other(format!("failed to serialize: {e:?}")) }
                    #[cfg(verus_only)]
                    { std::io::Error::from_raw_os_error(-1) }
                },
        )?;
        Ok(s)
    }

    /// Submits one `Read` op for `buf[filled..]`, waits for its single completion, and returns
    /// how many bytes it reported (`Ok(0)` means EOF, matching `Read::read`'s own convention).
    /// `unsafe`: (a) the cell access, justified by this struct's single-owner-thread invariant
    /// (see `ring`'s field doc); (b) `SubmissionQueue::push`, which is `unsafe` in the `io-uring`
    /// crate itself -- its safety contract is that `buf`'s memory must stay valid and unaliased
    /// until the op's completion is reaped, which holds here because this function submits and
    /// immediately `submit_and_wait`s for exactly that one completion before returning, never
    /// leaving an op in flight past this call.
    #[verifier::external_body]
    fn read_once(&self, buf: &mut [u8]) -> Result<i32, std::io::Error> {
        let ring = unsafe { &mut *self.ring.get() };
        let entry = opcode::Read::new(
            types::Fd(self.inner.as_raw_fd()),
            buf.as_mut_ptr(),
            buf.len() as u32,
        ).build().user_data(0);
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

    /// Same write-side `unsafe` contract as `read_once`, for `Write` instead of `Read`.
    #[verifier::external_body]
    fn write_once(&self, buf: &[u8]) -> Result<i32, std::io::Error> {
        let ring = unsafe { &mut *self.ring.get() };
        let entry = opcode::Write::new(
            types::Fd(self.inner.as_raw_fd()),
            buf.as_ptr(),
            buf.len() as u32,
        ).build().user_data(0);
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

    /// Same shape/contract as `tcp.rs`'s `TypedTcpStream::read_exact_or_none` (see its doc):
    /// fills `buf` completely, retrying through recv-timeouts and resuming from where the
    /// previous attempt left off. If `bail_if_empty`, returns `Ok(false)` (consuming nothing) the
    /// first time a timeout occurs with zero bytes of *this* field read so far.
    #[verifier::external_body]
    fn read_exact_or_none(&self, buf: &mut [u8], bail_if_empty: bool) -> Result<
        bool,
        std::io::Error,
    > {
        let mut filled = 0usize;
        while filled < buf.len() {
            let res = self.read_once(&mut buf[filled..])?;
            if res < 0 {
                let errno = res.wrapping_neg();
                if is_recv_timeout_errno(errno) {
                    if bail_if_empty && filled == 0 {
                        return Ok(false);
                    }
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
            filled += res as usize;
        }
        Ok(true)
    }

    #[verifier::external_body]
    pub fn try_recv(&self) -> Result<Option<R>, std::io::Error> {
        let mut len_bytes = [0u8;4];
        if !self.read_exact_or_none(&mut len_bytes, true)? {
            return Ok(None);
        }
        let len = u32::from_ne_bytes(len_bytes) as usize;
        let mut buf = vec![0u8; len];
        self.read_exact_or_none(&mut buf, false)?;
        let res = Self::deserialize(&buf)?;
        Ok(Some(res))
    }

    /// Unlike `tcp.rs`'s vectored-write send (one `writev(2)` for prefix + payload, no copy),
    /// this combines them into one buffer before the single `Write` op -- `io_uring` has a
    /// vectored `Writev` opcode too, but combining is simpler for a Phase A prototype and this
    /// file isn't chasing that optimization yet (see the top doc's scope note).
    #[verifier::external_body]
    pub fn send(&self, v: &S) -> Result<(), std::io::Error> {
        let s = Self::serialize(v)?;
        let len = s.view().len() as u32;
        let mut combined = Vec::with_capacity(4 + s.view().len());
        combined.extend_from_slice(&len.to_ne_bytes());
        combined.extend_from_slice(s.view());
        let mut filled = 0usize;
        while filled < combined.len() {
            let res = self.write_once(&combined[filled..])?;
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
                    std::io::Error::new(
                        std::io::ErrorKind::WriteZero,
                        "failed to write whole buffer",
                    ),
                );
            }
            filled += res as usize;
        }
        Ok(())
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
