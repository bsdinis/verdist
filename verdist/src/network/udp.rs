use std::collections::HashSet;
use std::marker::PhantomData;
use std::net::SocketAddr;
use std::net::ToSocketAddrs;
use std::net::UdpSocket;
use std::sync::Mutex;

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::network::channel::Connector;
use crate::network::channel::Listener;
use crate::network::error::ConnectError;
use crate::network::error::TryListenError;

#[cfg(verus_only)]
use vlib::serde::ExDeserialize;
#[cfg(verus_only)]
use vlib::serde::ExSerialize;
// #[cfg(verus_only)]
// use vlib::std::error::ExError;

use vstd::prelude::*;

verus! {

const BUF_SIZE: usize = 1 << 12;

/// Udp Socket that unmarshals receiving types (R) and marshals sending types (S)
pub struct TypedUdpSocket<R, S> {
    inner: UdpSocket,
    _marker: PhantomData<(R, S)>,
}

impl<R, S> TypedUdpSocket<R, S> where for <'de>R: serde::Deserialize<'de>, S: serde::Serialize {
    pub fn new(socket: UdpSocket) -> Self {
        TypedUdpSocket { inner: socket, _marker: PhantomData }
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

    #[verifier::external_body]
    pub fn try_recv(&self) -> Result<R, std::io::Error> {
        let mut buf = [0;BUF_SIZE];
        let r = self.inner.recv(&mut buf)?;
        if r == BUF_SIZE {
            vlib::veprintln!("[udp:{:?}]: warning: receiving {:x} bytes from {:?} may have exhausted the buffer, message may have been truncated",
                self.inner.local_addr(), BUF_SIZE, self.inner.peer_addr());
        }
        Self::deserialize(&buf)
    }

    #[verifier::external_body]
    pub fn try_recv_from(&self) -> Result<(R, SocketAddr), std::io::Error> {
        let mut buf = [0;BUF_SIZE];
        let (r, addr) = self.inner.recv_from(&mut buf)?;
        if r == BUF_SIZE {
            vlib::veprintln!("[udp:{:?}]: warning: receiving {:x} bytes from {:?} may have exhausted the buffer, message may have been truncated",
                self.inner.local_addr(), BUF_SIZE, self.inner.peer_addr());
        }
        let v = Self::deserialize(&buf)?;
        Ok((v, addr))
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

    #[verifier::external_body]
    pub fn send(&self, v: &S) -> Result<(), std::io::Error> {
        let s = Self::serialize(v)?;
        let sent_len = self.inner.send(s.view())?;
        if sent_len != s.view().len() {
            vlib::veprintln!("warning: partial write (only 0x{:x}B / 0x{:x}B sent). partial writes should be impossible for sizes <= 0x{:x}",
            sent_len, s.view().len(), i32::MAX);
        }
        Ok(())
    }

    #[verifier::external_body]
    pub fn send_to<A: ToSocketAddrs>(&self, v: &S, addr: A) -> Result<(), std::io::Error> {
        let s = Self::serialize(v)?;
        let sent_len = self.inner.send_to(s.view(), addr)?;
        if sent_len != s.view().len() {
            vlib::veprintln!("warning: partial write (only 0x{:x}B / 0x{:x}B sent). partial writes should be impossible for sizes <= 0x{:x}",
            sent_len, s.view().len(), i32::MAX);
        }
        Ok(())
    }

    pub fn local_addr(&self) -> std::io::Result<SocketAddr> {
        self.inner.local_addr()
    }

    pub fn peer_addr(&self) -> std::io::Result<SocketAddr> {
        self.inner.peer_addr()
    }
}

#[verifier::external_body]
pub struct UdpListener {
    listening_socket: TypedUdpSocket<u64, (u64, SocketAddr)>,
    port_range: (u16, u16),
    used_ports: Mutex<HashSet<u16>>,
    id: u64,
}

impl UdpListener {
    #[verifier::external_body]
    pub fn listen<A: ToSocketAddrs>(
        addr: A,
        id: u64,
        start_port: u16,
        end_port: u16,
    ) -> std::io::Result<Self> {
        let listening_socket = TypedUdpSocket::new(UdpSocket::bind(addr)?);
        Ok(
            UdpListener {
                listening_socket,
                port_range: (start_port, end_port),
                used_ports: Mutex::new(HashSet::new()),
                id,
            },
        )
    }

    #[verifier::external_body]
    pub fn allocate_port(&self) -> Option<u16> {
        let mut guard = self.used_ports.lock().unwrap();
        for port in self.port_range.0..self.port_range.1 {
            if !guard.contains(&port) {
                guard.insert(port);
                return Some(port);
            }
        }
        None
    }
}

#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct UdpConnector<A: ToSocketAddrs> {
    listening_addr: A,
    local_addr: SocketAddr,
}

impl<A: ToSocketAddrs> UdpConnector<A> {
    #[verifier::external_body]
    pub fn new<A2: ToSocketAddrs>(listening_addr: A, local_addr: A2) -> std::io::Result<Self> {
        let local_addr = local_addr.to_socket_addrs()?.next().ok_or_else(
            || std::io::Error::other("no address found"),
        )?;
        Ok(UdpConnector { listening_addr, local_addr })
    }
}

/// Channel TO Client
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct ClientChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    socket: TypedUdpSocket<R, S>,
    server_id: u64,
    client_id: u64,
}

/// Channel TO Server
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct ServerChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    socket: TypedUdpSocket<R, S>,
    server_id: u64,
    client_id: u64,
}

impl<K, R, S> ClientChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        socket: TypedUdpSocket<R, S>,
    ) -> Self {
        ClientChannel { pred, socket, server_id, client_id }
    }
}

impl<K, R, S> ServerChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        socket: TypedUdpSocket<R, S>,
    ) -> Self {
        ServerChannel { pred, socket, server_id, client_id }
    }
}

pub struct EmptyChanInv;

impl<Id, R, S> ChannelInvariant<EmptyChanInv, Id, R, S> for EmptyChanInv {
    open spec fn recv_inv(k: Self, id: Id, r: R) -> bool {
        true
    }

    open spec fn send_inv(k: Self, id: Id, s: S) -> bool {
        true
    }
}

impl<K, R, S> Channel for ClientChannel<K, R, S> where
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
        self.socket.try_recv().map_err(|e| e.into())
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

impl<K, R, S> Channel for ServerChannel<K, R, S> where
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
        self.socket.try_recv().map_err(|e| e.into())
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

// TODO: this is where we create the ghost map and the channel invariant
impl<K, R, S> Listener<ClientChannel<K, R, S>> for UdpListener where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
 {
    #[allow(unused_variables)]
    #[verifier::external_body]
    fn try_accept(&self, gen_pred: Ghost<spec_fn(&Self) -> K>) -> (r: Result<
        ClientChannel<K, R, S>,
        TryListenError,
    >) {
        let (client_id, addr) = self.listening_socket.try_recv_from()?;
        vlib::veprintln!(
            "[server|{:>3}]: accepting a connection from client {} id={client_id}", self.id, &addr,
        );

        let Some(port) = self.allocate_port() else {
            return Err(TryListenError::Empty);  // TODO: change to full ports
        };

        let local_ip = self.listening_socket.local_addr().unwrap().ip();
        self.listening_socket.send_to(&(self.id, SocketAddr::new(local_ip, port)), addr)?;

        let pred = Ghost(gen_pred@(self));
        let socket = UdpSocket::bind((local_ip, port))?;
        socket.connect(addr)?;
        let tsocket = TypedUdpSocket::new(socket);

        let chan = ClientChannel::new(pred, self.id, client_id, tsocket);

        vlib::veprintln!("[server|{:>3}]: accepted connection from client {client_id} (channel_id: {:?})", self.id, chan.id());

        Ok(chan)
    }
}

impl<K, R, S, A> Connector<ServerChannel<K, R, S>> for UdpConnector<A> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
    A: ToSocketAddrs,
 {
    #[verifier::external_body]
    fn connect<F>(&self, local_id: u64, gen_pred: F) -> Result<
        ServerChannel<K, R, S>,
        ConnectError,
    > where F: FnOnce(&Self, u64) -> Ghost<K> {
        vlib::veprintln!(
            "[client|{:>3}]: connecting to server", local_id,
        );
        let socket = UdpSocket::bind(&self.local_addr)?;
        socket.connect(&self.listening_addr)?;
        let tsocket = TypedUdpSocket::<(u64, SocketAddr), u64>::new(socket);

        tsocket.send(&local_id)?;
        loop {
            match tsocket.try_recv() {
                Ok((server_id, addr)) => {
                    let socket = UdpSocket::bind(self.local_addr)?;
                    socket.connect(addr)?;
                    let tsocket = TypedUdpSocket::new(socket);
                    let pred = gen_pred(self, local_id);

                    let chan = ServerChannel::new(pred, server_id, local_id, tsocket);
                    vlib::veprintln!(
                        "[client|{:>3}]: connected to server {server_id}  (channel_id: {:?})", local_id, chan.id()
                    );
                    return Ok(chan);
                },
                Err(_) => {},
            }
        }
    }
}

} // verus!
