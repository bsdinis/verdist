//! `IoUringUdp*` -- a new, additive `Channel`/`Listener`/`Connector` variant for UDP built on
//! `io_uring` instead of blocking `recv`/`send` syscalls (see `network::impls::udp` for the
//! existing, unmodified blocking-syscall version this sits alongside; nothing in that file was
//! touched to build this one). Same shape and same caveats as `io_uring_tcp.rs` -- see that
//! file's top doc for the full "UNVERIFIED IN THIS SANDBOX" explanation and the Phase-A-only
//! scope note; both apply here verbatim.
//!
//! One difference from TCP: the listening socket's role (demultiplexing arbitrary peers via
//! `recv_from`/`send_to`, never a single connected peer) stays on plain blocking syscalls here
//! too, exactly like `udp.rs`'s own `RawUdpSocket`/`TypedUdpSocket` split (see that file's
//! `RawUdpSocket` doc) -- there is no `io_uring`-specific listener type in this file at all,
//! because the listener never benefits from the per-connection optimization this file is
//! prototyping (one accept-thread-only socket, not per-shard-thread contended).
use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::net::IpAddr;
use std::net::SocketAddr;
use std::net::ToSocketAddrs;
use std::net::UdpSocket;
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

/// See `io_uring_tcp::submit_and_wait_1`'s doc -- identical rationale (submission and wait happen
/// in the same `io_uring_enter` syscall, so an un-retried `EINTR` here would abandon an
/// already-in-flight op, a use-after-free risk once the caller's buffer is dropped/reused) and
/// identical reason for living outside `verus! {}` (a `&mut IoUring` parameter isn't representable
/// even under `#[verifier::external_body]`, which only skips body-checking, not signature-checking).
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

/// Same value as `network::impls::udp::RECV_TIMEOUT_MILLIS`.
const RECV_TIMEOUT_MILLIS: u64 = 2;

/// See `io_uring_tcp.rs::RING_ENTRIES` -- same rationale, same "picked, not measured" caveat.
const RING_ENTRIES: u32 = 8;

const BUF_SIZE: usize = 1 << 12;

fn is_recv_timeout(e: &std::io::Error) -> bool {
    e.kind() == std::io::ErrorKind::WouldBlock || e.kind() == std::io::ErrorKind::TimedOut
}

#[verifier::external_body]
fn is_recv_timeout_errno(errno: i32) -> bool {
    errno == libc::EAGAIN || errno == libc::EWOULDBLOCK || errno == libc::ETIMEDOUT
}

fn udp_deserialize<R>(buf: &[u8]) -> Result<R, std::io::Error> where
    for <'de>R: serde::Deserialize<'de>,
 {
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

fn udp_serialize<S: serde::Serialize>(v: &S) -> Result<
    flexbuffers::FlexbufferSerializer,
    std::io::Error,
> {
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

/// `io_uring`-backed analogue of `network::impls::udp::TypedUdpSocket`, for the per-connection
/// (always-`connect`ed) role only -- see this file's top doc for why the listener stays on plain
/// syscalls. Same interior-mutability rationale as `io_uring_tcp::IoUringTcpStream` (see its doc).
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct IoUringUdpSocket<R, S> {
    inner: UdpSocket,
    ring: UnsafeCell<IoUring>,
    _marker: PhantomData<(R, S)>,
}

impl<R, S> IoUringUdpSocket<R, S> where for <'de>R: serde::Deserialize<'de>, S: serde::Serialize {
    #[verifier::external_body]
    pub fn new(socket: UdpSocket) -> std::io::Result<Self> {
        socket.set_nonblocking(false)?;
        socket.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS)))?;
        let ring = IoUring::new(RING_ENTRIES)?;
        Ok(IoUringUdpSocket { inner: socket, ring: UnsafeCell::new(ring), _marker: PhantomData })
    }

    /// Same `unsafe` contract as `io_uring_tcp::IoUringTcpStream::read_once`/`write_once`: cell
    /// access justified by the single-owner-thread invariant (see this struct's field doc via
    /// `io_uring_tcp.rs`'s identical one); `SubmissionQueue::push` is `unsafe` in the `io-uring`
    /// crate itself, whose safety contract (buffer stays valid+unaliased until the completion is
    /// reaped) holds here because this function submits and immediately waits for that exact one
    /// completion, never leaving an op in flight past the call.
    #[verifier::external_body]
    fn recv_once(&self, buf: &mut [u8]) -> Result<i32, std::io::Error> {
        let ring = unsafe { &mut *self.ring.get() };
        let entry = opcode::Recv::new(
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

    #[verifier::external_body]
    fn send_once(&self, buf: &[u8]) -> Result<i32, std::io::Error> {
        let ring = unsafe { &mut *self.ring.get() };
        let entry = opcode::Send::new(
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

    #[verifier::external_body]
    pub fn try_recv(&self) -> Result<Option<R>, std::io::Error> {
        let mut buf = [0;BUF_SIZE];
        let res = self.recv_once(&mut buf)?;
        if res < 0 {
            let errno = res.wrapping_neg();
            if is_recv_timeout_errno(errno) {
                return Ok(None);
            }
            return Err(std::io::Error::from_raw_os_error(errno));
        }
        let r = res as usize;
        if r == BUF_SIZE {
            vlib::veprintln!("[io_uring_udp:{:?}]: warning: receiving {:x} bytes from {:?} may have exhausted the buffer, message may have been truncated",
                self.local_addr(), BUF_SIZE, self.peer_addr());
        }
        let res = udp_deserialize(&buf[..r])?;
        Ok(Some(res))
    }

    /// One `Send` op, one datagram -- matching `udp.rs`'s original `send`/`send_to` exactly (see
    /// their doc): a UDP `send` is atomic-or-fails at the socket layer, unlike a TCP stream write,
    /// so there is no such thing as "resuming" a short send with another op. Doing that (an
    /// earlier version of this function did, in a loop) would emit the remainder as a *second,
    /// independent datagram* -- corrupting the wire protocol into two malformed messages instead
    /// of logging a warning, exactly the bug this doc is now warning the next editor away from.
    /// `EINTR` retries the *same* full datagram (never partial), since nothing has been sent yet.
    #[verifier::external_body]
    pub fn send(&self, v: &S) -> Result<(), std::io::Error> {
        let s = udp_serialize(v)?;
        let view = s.view();
        loop {
            let res = self.send_once(view)?;
            if res < 0 {
                let errno = res.wrapping_neg();
                if errno == libc::EINTR {
                    continue;
                }
                return Err(std::io::Error::from_raw_os_error(errno));
            }
            let sent_len = res as usize;
            if sent_len != view.len() {
                vlib::veprintln!("warning: partial write (only 0x{:x}B / 0x{:x}B sent). partial writes should be impossible for sizes <= 0x{:x}",
                sent_len, view.len(), i32::MAX);
            }
            return Ok(());
        }
    }

    #[verifier::external_body]
    pub fn local_addr(&self) -> SocketAddr {
        self.inner.local_addr().expect("local addr should be set")
    }

    #[verifier::external_body]
    pub fn peer_addr(&self) -> SocketAddr {
        self.inner.peer_addr().expect("peer addr should be set")
    }

    /// See `io_uring_tcp::IoUringTcpStream::raw_fd`'s doc -- same "NOT the ring's own fd" note.
    #[verifier::external_body]
    pub fn raw_fd(&self) -> i32 {
        self.inner.as_raw_fd()
    }
}

/// Listens for and hands off raw, per-client `UdpSocket`s exactly like `udp.rs`'s `UdpListener` --
/// same bind/rendezvous-handshake shape, duplicated (not shared) so this file never reaches into
/// `udp.rs`'s private fields or modifies it. Stays on plain blocking `recv_from`/`send_to` (see
/// this file's top doc for why).
#[verifier::external_body]
pub struct IoUringUdpListener {
    listening_socket: UdpSocket,
    id: u64,
}

impl IoUringUdpListener {
    #[verifier::external_body]
    pub fn listen<A: ToSocketAddrs>(addr: A, id: u64) -> std::io::Result<Self> {
        let listening_socket = UdpSocket::bind(addr)?;
        listening_socket.set_nonblocking(false)?;
        listening_socket.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS)))?;
        Ok(IoUringUdpListener { listening_socket, id })
    }
}

#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct IoUringUdpConnector<A: ToSocketAddrs> {
    listening_addr: A,
    local_ip: IpAddr,
    #[allow(dead_code)]
    server_id: u64,
}

impl<A: ToSocketAddrs> IoUringUdpConnector<A> {
    #[verifier::external_body]
    pub fn new(listening_addr: A, local_ip: IpAddr, server_id: u64) -> std::io::Result<Self> {
        Ok(IoUringUdpConnector { listening_addr, local_ip, server_id })
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
    socket: IoUringUdpSocket<R, S>,
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
    socket: IoUringUdpSocket<R, S>,
    server_id: u64,
    client_id: u64,
}

impl<K, R, S> IoUringClientChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        socket: IoUringUdpSocket<R, S>,
    ) -> Self {
        IoUringClientChannel { pred, socket, server_id, client_id }
    }
}

impl<K, R, S> IoUringServerChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        socket: IoUringUdpSocket<R, S>,
    ) -> Self {
        IoUringServerChannel { pred, socket, server_id, client_id }
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
        match self.socket.try_recv() {
            Ok(Some(x)) => Ok(x),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        self.socket.send(v).map_err(|e| e.into())
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
        self.socket.raw_fd()
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
        match self.socket.try_recv() {
            Ok(Some(x)) => Ok(x),
            Ok(None) => Err(crate::network::error::TryRecvError::Empty),
            Err(e) => Err(e.into()),
        }
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), crate::network::error::SendError> {
        self.socket.send(v).map_err(|e| e.into())
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

// Same trust-boundary note as `udp.rs`'s identical `try_accept_raw`/`wrap_raw` pair.
impl<K, R, S> Listener<IoUringClientChannel<K, R, S>> for IoUringUdpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.id
    }

    type Raw = (UdpSocket, u64);

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn try_accept_raw(&self) -> Result<(u64, Self::Raw), TryListenError> {
        let mut buf = [0;BUF_SIZE];
        let (r, addr) = match self.listening_socket.recv_from(&mut buf) {
            Ok(x) => x,
            Err(e) if is_recv_timeout(&e) => {
                return Err(TryListenError::Empty);
            },
            Err(e) => {
                return Err(e.into());
            },
        };
        let (client_id, connect_addr): (u64, SocketAddr) = udp_deserialize(&buf[..r])?;

        let local_ip = self.listening_socket.local_addr().expect("local addr should be set").ip();
        let socket = UdpSocket::bind((local_ip, 0))?;

        vlib::veprintln!(
            "[server|{:>3}]: accepting a connection from client {} id={client_id}, local addr is {:?} [io_uring]", self.id, &addr, socket.local_addr().unwrap()
        );

        let reply = udp_serialize(&(self.id, socket.local_addr().unwrap()))?;
        let sent_len = self.listening_socket.send_to(reply.view(), addr)?;
        if sent_len != reply.view().len() {
            vlib::veprintln!("warning: partial write (only 0x{:x}B / 0x{:x}B sent). partial writes should be impossible for sizes <= 0x{:x}",
            sent_len, reply.view().len(), i32::MAX);
        }
        socket.connect(connect_addr)?;

        Ok((client_id, (socket, client_id)))
    }

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn wrap_raw(&self, raw: Self::Raw, gen_pred: Ghost<spec_fn(&Self) -> K>) -> (r: Result<
        IoUringClientChannel<K, R, S>,
        TryListenError,
    >) {
        let (socket, client_id) = raw;
        let pred = Ghost(gen_pred@(self));
        let tsocket = IoUringUdpSocket::new(socket)?;

        let chan = IoUringClientChannel::new(pred, self.id, client_id, tsocket);

        vlib::veprintln!("[server|{:>3}]: accepted connection from client {client_id} (channel_id: {:?}) [io_uring]", self.id, chan.id());

        Ok(chan)
    }
}

impl<K, R, S> RawFdListener<IoUringClientChannel<K, R, S>> for IoUringUdpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[verifier::external_body]
    fn raw_fd(&self) -> i32 {
        self.listening_socket.as_raw_fd()
    }
}

impl<K, R, S, A> Connector<IoUringServerChannel<K, R, S>> for IoUringUdpConnector<A> where
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
        IoUringServerChannel<K, R, S>,
        ConnectError,
    >) where F: FnOnce(&Self, u64) -> Ghost<K> {
        vlib::veprintln!(
            "[client|{:>3}]: connecting to server [io_uring]", local_id,
        );
        let addr = SocketAddr::new(self.local_ip, 0);
        let connect_socket = UdpSocket::bind(addr)?;
        connect_socket.set_read_timeout(Some(Duration::from_millis(RECV_TIMEOUT_MILLIS)))?;
        let channel_socket = UdpSocket::bind(addr)?;
        connect_socket.connect(&self.listening_addr)?;

        let req = udp_serialize(&(local_id, channel_socket.local_addr().unwrap()))?;
        connect_socket.send(req.view())?;
        // Tolerant-of-noise loop matching `udp.rs`'s original `connect` exactly: a stray/malformed
        // datagram landing on this ephemeral rendezvous socket (plausible: a retransmit from a
        // previous failed attempt reusing a nearby port, or just line noise) is *not* a fatal
        // error here -- only a recognized (server_id, addr) reply ends the loop. An earlier
        // version of this function treated a recv error or a bad deserialize as fatal, aborting
        // the whole connection attempt on the first anomaly instead of tolerating it like the
        // blocking-syscall transport does; fixed after review.
        loop {
            let mut buf = [0;BUF_SIZE];
            let reply: Option<(u64, SocketAddr)> = connect_socket.recv(&mut buf).ok().and_then(
                |r| udp_deserialize(&buf[..r]).ok(),
            );
            if let Some((server_id, addr)) = reply {
                channel_socket.connect(addr)?;
                let tsocket = IoUringUdpSocket::new(channel_socket)?;
                let pred = gen_pred(self, local_id);

                let chan = IoUringServerChannel::new(pred, server_id, local_id, tsocket);
                vlib::veprintln!(
                        "[client|{:>3}]: connected to server {server_id} (channel_id: {:?}, server addr: {addr:?}) [io_uring]", local_id, chan.id()
                    );
                return Ok(chan);
            }
        }
    }
}

} // verus!
