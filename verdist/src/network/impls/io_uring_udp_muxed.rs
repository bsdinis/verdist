//! io_uring-backed router threads for `network::impls::udp_muxed::MuxedListener`.
//!
//! `network::impls::io_uring_udp`'s `Recv` opcode assumes a *connected* socket -- the completion
//! carries only a byte count, no source address, since the kernel already knows who the one peer
//! is. A muxed listener's router thread has no such peer: its socket receives from many clients at
//! once, so recovering *which* peer a given completion came from needs `opcode::RecvMsg` instead
//! (the io_uring analogue of `recvmsg(2)`), which fills in a caller-supplied `msghdr`'s `msg_name`
//! with the sender's address.
//!
//! This file adds exactly one thing: an alternate router-thread body (`router_thread_body_io_uring`,
//! below) using `RecvMsg` in place of `udp_muxed.rs::router_thread_body`'s blocking `recv_from`,
//! plus `MuxedListener::listen_io_uring`/`listen_io_uring_reuseport` constructors that spawn it.
//! Everything else -- the demux table, `MuxedRaw`, `MuxedClientChannel`, the `Listener`/`Channel`
//! impls, the `--epoll` driver -- is reused completely unchanged from `udp_muxed.rs`: io_uring only
//! changes *how a router thread learns of a new datagram*, nothing about what happens once it has
//! one (that's `udp_muxed::handle_datagram`, called identically from both router-thread flavors).
//!
//! Sending stays a plain blocking `send_to`/`send` syscall in both flavors (see
//! `MuxedClientChannel::send`/`MuxedServerChannel::send` in `udp_muxed.rs`) -- deliberately not
//! io_uring-based, for a reason specific to the *shared* socket this backend uses: an `IoUring`
//! ring is single-owner (see `io_uring_udp.rs`'s `IoUringUdpSocket`, guarded by that invariant),
//! but a muxed channel's socket is shared across every worker thread that might send a reply on
//! it, and reused across every future channel that socket's router thread will ever accept. Only
//! the router thread itself has the single-owner property this session's io_uring code relies on
//! throughout, so only its *receive* path gets an io_uring ring; a plain `send_to` is already safe
//! for concurrent callers at the OS level (see `udp_muxed.rs`'s top doc) and needs no such ring.
//!
//! The client side needs no new code at all: a client's channel talks to one, connected, privately
//! owned socket (see `MuxedServerChannel`) -- exactly the shape `io_uring_udp.rs`'s
//! `IoUringUdpSocket<R, S>` already handles. `MuxedConnector::listen_io_uring`-analogue below just
//! builds an `IoUringUdpSocket<Resp, MuxedEnvelope<Req>>` directly and reuses its `send`/`try_recv`
//! verbatim, wrapping/unwrapping the envelope at the one point that needs it.

use std::marker::PhantomData;
use std::net::SocketAddr;
use std::net::ToSocketAddrs;
use std::net::UdpSocket;
use std::os::fd::AsRawFd;
use std::sync::Arc;

use io_uring::opcode;
use io_uring::types;
use io_uring::IoUring;

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::network::channel::Connector;
use crate::network::error::ConnectError;
use crate::network::impls::io_uring_udp::IoUringUdpSocket;
use crate::network::impls::udp_muxed::handle_datagram;
use crate::network::impls::udp_muxed::MuxedConnector;
use crate::network::impls::udp_muxed::MuxedEnvelope;
use crate::network::impls::udp_muxed::MuxedListener;
use crate::network::impls::udp_muxed::BUF_SIZE;

use vstd::prelude::*;

/// See `io_uring_udp::submit_and_wait_1`'s identical doc -- same rationale (submission and wait
/// happen in the same `io_uring_enter` syscall, so an un-retried `EINTR` would abandon an
/// already-in-flight op) and same reason for living outside `verus! {}` (a `&mut IoUring`
/// parameter isn't representable even under `#[verifier::external_body]`). Duplicated rather than
/// shared, matching this crate's existing convention of keeping each network impl file
/// self-contained (see `io_uring_udp.rs`'s own top doc on why it duplicates rather than reaches
/// into `udp.rs`).
fn submit_now(ring: &mut IoUring) -> std::io::Result<()> {
    loop {
        match ring.submit() {
            Ok(_) => return Ok(()),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
}

/// One heap-allocated (`Box`, so its address is stable for the router thread's whole lifetime --
/// see `poll_recvmsg`'s doc for why that stability matters) scratch area for one in-flight
/// `RecvMsg` op: the receive buffer, the `iovec`/`sockaddr_storage`/`msghdr` triple `RecvMsg`
/// needs, and the in-flight flag. Exactly one of these per router thread, never touched by any
/// other thread -- same single-owner rationale as `io_uring_udp.rs::UdpRecvState`.
struct RecvMsgState {
    op_in_flight: bool,
    buf: [u8; BUF_SIZE],
    iov: libc::iovec,
    name: libc::sockaddr_storage,
    msghdr: libc::msghdr,
}

impl RecvMsgState {
    fn new() -> Box<Self> {
        Box::new(RecvMsgState {
            op_in_flight: false,
            buf: [0u8; BUF_SIZE],
            // SAFETY: all-zero is a valid bit pattern for `iovec`/`sockaddr_storage`/`msghdr` --
            // every field is either an integer or a raw pointer, and a null pointer is a valid
            // (if not yet meaningful) value for `iov_base`/`msg_name`/`msg_iov` here; every field
            // is (re-)populated by `poll_recvmsg` before ever being submitted.
            iov: unsafe { std::mem::zeroed() },
            name: unsafe { std::mem::zeroed() },
            msghdr: unsafe { std::mem::zeroed() },
        })
    }
}

/// `io_uring`-backed analogue of `io_uring_udp.rs::poll_recv`, for a *shared, unconnected* socket:
/// submits a `RecvMsg` op if none is in flight, then does a non-blocking peek of the completion
/// queue (never `submit_and_wait` -- see `poll_recv`'s doc for why: a blocking wait here would
/// stall this router thread's *only* receive path indefinitely whenever no client is currently
/// sending, exactly the bug that doc already found and fixed for the connected-socket case).
///
/// Re-points `state`'s `iovec`/`msghdr` raw pointers at its own sibling fields fresh on every
/// submission (never reuses a pointer computed on a previous call): `state` is passed in as `&mut`
/// already at its final, stable heap address (owned by a `Box` the caller never moves once
/// constructed -- see `RecvMsgState::new`'s doc), so computing `&mut state.iov`/`&mut state.name`
/// here, immediately before the one `submission().push` call that hands their addresses to the
/// kernel, is sound for exactly the same reason `io_uring_udp.rs::poll_recv` passing
/// `dst.as_mut_ptr()` fresh each call is: the pointed-to memory doesn't move between this
/// submission and the eventual reap, because nothing ever moves `*state` while an op is in flight.
fn poll_recvmsg(
    ring: &mut IoUring,
    fd: i32,
    state: &mut RecvMsgState,
) -> std::io::Result<Option<i32>> {
    if !state.op_in_flight {
        state.iov.iov_base = state.buf.as_mut_ptr() as *mut libc::c_void;
        state.iov.iov_len = state.buf.len();
        state.msghdr.msg_name = &mut state.name as *mut _ as *mut libc::c_void;
        state.msghdr.msg_namelen = std::mem::size_of::<libc::sockaddr_storage>() as u32;
        state.msghdr.msg_iov = &mut state.iov as *mut _;
        state.msghdr.msg_iovlen = 1;
        state.msghdr.msg_control = std::ptr::null_mut();
        state.msghdr.msg_controllen = 0;
        state.msghdr.msg_flags = 0;
        let entry = opcode::RecvMsg::new(types::Fd(fd), &mut state.msghdr as *mut _).build()
            .user_data(0);
        // SAFETY: `state.buf`/`state.iov`/`state.name`/`state.msghdr` are all fields of the same
        // heap-allocated `RecvMsgState`, whose address is stable until this op completes (see this
        // fn's doc) -- the raw pointers stored into the SQE above stay valid for exactly as long
        // as the kernel needs them.
        unsafe {
            ring.submission().push(&entry).map_err(
                |e| std::io::Error::other(format!("io_uring submission queue full: {e}")),
            )?;
        }
        submit_now(ring)?;
        state.op_in_flight = true;
    }
    match ring.completion().next() {
        None => Ok(None),
        Some(cqe) => {
            state.op_in_flight = false;
            Ok(Some(cqe.result()))
        },
    }
}

/// Same value as `io_uring_udp.rs::RING_ENTRIES` -- see that constant's "picked, not measured"
/// caveat, which applies identically here.
const RING_ENTRIES: u32 = 8;

fn is_recv_timeout_errno(errno: i32) -> bool {
    errno == libc::EAGAIN || errno == libc::EWOULDBLOCK || errno == libc::ETIMEDOUT
}

/// io_uring/`RecvMsg`-based analogue of `udp_muxed::router_thread_body` -- identical demux logic
/// (delegated to the shared `handle_datagram` helper), different receive mechanism. Owns its own
/// `IoUring` ring and `RecvMsgState` for its whole lifetime, exactly as single-owner as every other
/// per-thread `IoUring` in this crate.
fn router_thread_body_io_uring<R>(
    socket: Arc<UdpSocket>,
    new_conns_tx: crossbeam_channel::Sender<(u64, crate::network::impls::udp_muxed::MuxedRaw<R>)>,
) where for <'de>R: serde::Deserialize<'de> {
    let mut demux = std::collections::HashMap::new();
    let mut ring = match IoUring::new(RING_ENTRIES) {
        Ok(r) => r,
        Err(e) => {
            vlib::veprintln!("[io_uring_udp_muxed]: router thread failed to create io_uring instance: {e:?}; this router thread is now permanently inert");
            return;
        },
    };
    let mut state = RecvMsgState::new();
    let fd = socket.as_raw_fd();
    loop {
        let res = match poll_recvmsg(&mut ring, fd, &mut state) {
            // Unlike `router_thread_body`'s blocking `recv_from` (which sleeps for free, inside
            // the kernel, via its socket read timeout), `poll_recvmsg` never blocks -- it only
            // ever peeks (see that fn's doc). Without a backoff here, this would be a genuine,
            // unconditional 100%-CPU busy-spin on every router thread for the entire process
            // lifetime, not just an inefficiency: confirmed by this exact symptom during testing
            // (client processes intermittently timing out under load once >=2 router threads were
            // spinning, worse with more router threads/concurrent clients -- classic CPU
            // starvation, not a demux correctness bug). Same backoff value as
            // `RECV_TIMEOUT_MILLIS` elsewhere in this crate's UDP backends.
            Ok(None) => {
                std::thread::sleep(std::time::Duration::from_millis(
                    crate::network::impls::udp_muxed::RECV_TIMEOUT_MILLIS,
                ));
                continue;
            },
            Ok(Some(res)) => res,
            Err(e) => {
                vlib::veprintln!("[io_uring_udp_muxed]: router thread poll_recvmsg error: {e:?}");
                continue;
            },
        };
        if res < 0 {
            let errno = res.wrapping_neg();
            if !is_recv_timeout_errno(errno) {
                vlib::veprintln!("[io_uring_udp_muxed]: router thread recv error: errno {errno}");
            }
            continue;
        }
        let n = res as usize;
        // SAFETY/correctness: `poll_recvmsg` always fully (re)populates `state.name`/
        // `state.msghdr.msg_namelen` as part of the completed op before returning `Ok(Some(_))`
        // (the kernel writes both), so this is exactly the same "trust the kernel's own
        // getsockname/recvfrom-style output" pattern `socket2::SockAddr::new`'s own doc describes.
        let addr = match unsafe { socket2::SockAddr::new(state.name, state.msghdr.msg_namelen) }
            .as_socket()
        {
            Some(addr) => addr,
            None => {
                vlib::veprintln!("[io_uring_udp_muxed]: warning: RecvMsg completion carried an unrecognized peer address family; dropping datagram");
                continue;
            },
        };
        if n == BUF_SIZE {
            vlib::veprintln!("[io_uring_udp_muxed]: warning: receiving {BUF_SIZE:x} bytes from {addr:?} may have exhausted the buffer, message may have been truncated");
        }
        if !handle_datagram(&mut demux, addr, &state.buf[..n], &socket, &new_conns_tx) {
            return;
        }
    }
}

verus! {

impl<R, S> MuxedListener<R, S> where for <'de>R: serde::Deserialize<'de>, R: Send + 'static {
    /// io_uring/`RecvMsg`-based analogue of `MuxedListener::listen` -- same single-socket, no
    /// `SO_REUSEPORT` shape, different (io_uring) router thread. See this file's top doc.
    #[verifier::external_body]
    pub fn listen_io_uring<A: ToSocketAddrs>(addr: A, id: u64) -> std::io::Result<Self> {
        let socket = Arc::new(UdpSocket::bind(addr)?);
        // No read timeout here (unlike `listen`'s blocking-`recv_from` router thread): the
        // io_uring router thread never blocks in a syscall at all, it only ever peeks the
        // completion queue (see `poll_recvmsg`'s doc) -- a socket-level read timeout would be
        // meaningless for an op it never blockingly waits on.
        let (tx, rx) = crossbeam_channel::unbounded();
        std::thread::spawn(move || router_thread_body_io_uring::<R>(socket, tx));
        Ok(MuxedListener { id, new_conns: rx, _marker: PhantomData })
    }

    /// io_uring/`RecvMsg`-based analogue of `MuxedListener::listen_reuseport` -- same
    /// `SO_REUSEPORT`-before-`bind()`-via-`socket2` shape (see `listen_reuseport`'s doc), different
    /// (io_uring) router thread per socket.
    #[verifier::external_body]
    pub fn listen_io_uring_reuseport<A: ToSocketAddrs>(
        addr: A,
        id: u64,
        num_router_threads: usize,
    ) -> std::io::Result<Self> {
        assert!(num_router_threads > 0, "num_router_threads must be at least 1");
        let addr: SocketAddr = addr
            .to_socket_addrs()?
            .next()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidInput, "no address"))?;
        let (tx, rx) = crossbeam_channel::unbounded();
        for _ in 0..num_router_threads {
            let socket = Arc::new(crate::network::impls::udp_muxed::bind_reuseport(addr)?);
            let tx = tx.clone();
            std::thread::spawn(move || router_thread_body_io_uring::<R>(socket, tx));
        }
        Ok(MuxedListener { id, new_conns: rx, _marker: PhantomData })
    }
}

} // verus!

verus! {

/// `MuxedConnector`'s io_uring-based client-side channel, reusing `io_uring_udp.rs`'s
/// `IoUringUdpSocket<R, S>` verbatim rather than any new socket machinery (see this file's top
/// doc: the client side already owns a single, private, connected socket -- exactly
/// `IoUringUdpSocket`'s own design, no ambiguity about "which peer" the way the server's shared
/// socket has). `R` (`Resp`) is received plain, no envelope, matching
/// `udp_muxed::MuxedServerChannel::try_recv`; `S` (`Req`) is sent wrapped in a `MuxedEnvelope`,
/// matching `MuxedServerChannel::send` -- both via `IoUringUdpSocket<R, MuxedEnvelope<S>>`'s own,
/// unmodified `try_recv`/`send`.
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct IoUringMuxedServerChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    server_id: u64,
    client_id: u64,
    socket: IoUringUdpSocket<R, MuxedEnvelope<S>>,
}

impl<K, R, S> crate::network::channel::Channel for IoUringMuxedServerChannel<K, R, S> where
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
        match self.socket.try_recv() {
            Ok(Some(v)) => Ok(v),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        let envelope = MuxedEnvelope { client_id: self.client_id, body: v.clone() };
        self.socket.send(&envelope).map_err(|e| e.into())
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

// Same permanent-trust-boundary rationale as `udp_muxed.rs`'s identical `Connector` impl -- a
// second, non-overlapping impl of the same trait for the same `MuxedConnector<A>`, targeting a
// different produced channel type, is ordinary Rust (not a conflicting/duplicate impl).
impl<K, R, S, A> Connector<IoUringMuxedServerChannel<K, R, S>> for MuxedConnector<A> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
    A: ToSocketAddrs,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.server_id
    }

    #[verifier::external_body]
    fn connect<F>(&self, local_id: u64, gen_pred: F) -> (r: Result<
        IoUringMuxedServerChannel<K, R, S>,
        ConnectError,
    >) where F: FnOnce(&Self, u64) -> Ghost<K> {
        vlib::veprintln!(
            "[client|{:>3}]: connecting to server (io_uring_udp_muxed: no handshake, purely local)", local_id,
        );
        let addr = SocketAddr::new(self.local_ip, 0);
        let socket = UdpSocket::bind(addr)?;
        socket.connect(&self.listening_addr)?;
        let io_socket = IoUringUdpSocket::new(socket)?;
        let pred = gen_pred(self, local_id);
        let chan = IoUringMuxedServerChannel {
            pred,
            server_id: self.server_id,
            client_id: local_id,
            socket: io_socket,
        };
        vlib::veprintln!(
            "[client|{:>3}]: connected to server {} (channel_id: {:?})",
            local_id, self.server_id, chan.id()
        );
        Ok(chan)
    }
}

} // verus!
