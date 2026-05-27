use std::io::Read;
use std::io::Write;
use std::marker::PhantomData;
use std::net::SocketAddr;
use std::net::TcpStream;
use std::net::ToSocketAddrs;

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

use vstd::prelude::*;

verus! {

/// Tcp Socket that unmarshals receiving types (R) and marshals sending types (S)
pub struct TypedTcpStream<R, S> {
    inner: TcpStream,
    _marker: PhantomData<(R, S)>,
}

impl<R, S> TypedTcpStream<R, S> where for <'de>R: serde::Deserialize<'de>, S: serde::Serialize {
    pub fn new(stream: TcpStream) -> Self {
        stream.set_nonblocking(true).expect("this should never fail");
        TypedTcpStream { inner: stream, _marker: PhantomData }
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
    pub fn try_recv(&self) -> Result<Option<R>, std::io::Error> {
        let mut len_bytes = [0u8;4];
        // TcpStream implements Read, which takes in a mut ref
        // However, &TcpStream also implements Read, so this is how we get around it
        let mut stream = &self.inner;
        match stream.read_exact(&mut len_bytes) {
            Ok(()) => {},
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                return Ok(None);
            },
            Err(e) => {
                return Err(e);
            },
        }
        let len = u32::from_ne_bytes(len_bytes) as usize;

        let mut buf = vec![0u8; len];
        loop {
            match stream.read_exact(&mut buf) {
                Ok(()) => {
                    break;
                },
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    continue;
                },
                Err(e) => {
                    return Err(e);
                },
            }
        }
        let res = Self::deserialize(&buf)?;
        Ok(Some(res))
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
        let len = s.view().len() as u32;
        // See above (try_recv) for &TcpStream impl Read discussion
        let mut stream = &self.inner;
        stream.write_all(&len.to_ne_bytes())?;
        if let Err(e) = stream.write_all(s.view()) {
            vlib::veprintln!("warning: non-atomic write of len + payload failed");
            return Err(e);
        }
        Ok(())
    }

    pub fn local_addr(&self) -> SocketAddr {
        self.inner.local_addr().expect("local addr should be set")
    }

    pub fn peer_addr(&self) -> SocketAddr {
        self.inner.peer_addr().expect("peer addr should be set")
    }
}

#[verifier::external_body]
pub struct TcpListener {
    listener: std::net::TcpListener,
    id: u64,
}

impl TcpListener {
    #[verifier::external_body]
    pub fn listen<A: ToSocketAddrs>(addr: A, id: u64) -> std::io::Result<Self> {
        let listener = std::net::TcpListener::bind(addr)?;
        listener.set_nonblocking(true).expect("this should never fail");
        Ok(TcpListener { listener, id })
    }
}

#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct TcpConnector<A: ToSocketAddrs> {
    listening_addr: A,
}

impl<A: ToSocketAddrs> TcpConnector<A> {
    #[verifier::external_body]
    pub fn new(listening_addr: A) -> std::io::Result<Self> {
        Ok(TcpConnector { listening_addr })
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
    stream: TypedTcpStream<R, S>,
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
    stream: TypedTcpStream<R, S>,
    server_id: u64,
    client_id: u64,
}

impl<K, R, S> ClientChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        stream: TypedTcpStream<R, S>,
    ) -> Self {
        ClientChannel { pred, stream, server_id, client_id }
    }
}

impl<K, R, S> ServerChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        pred: Ghost<K>,
        server_id: u64,
        client_id: u64,
        stream: TypedTcpStream<R, S>,
    ) -> Self {
        ServerChannel { pred, stream, server_id, client_id }
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

// TODO: this is where we create the ghost map and the channel invariant
impl<K, R, S> Listener<ClientChannel<K, R, S>> for TcpListener where
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
        stream.read_exact(&mut client_id_buf)?;
        stream.write_all(&self.id.to_ne_bytes())?;
        let client_id = u64::from_ne_bytes(client_id_buf);
        stream.set_nonblocking(true).expect("this should never fail");

        let pred = Ghost(gen_pred@(self));
        let tstream = TypedTcpStream::new(stream);
        let chan = ClientChannel::new(pred, self.id, client_id, tstream);

        vlib::veprintln!("[server|{:>3}]: accepted connection from client {client_id} (channel_id: {:?})", self.id, chan.id());

        Ok(chan)
    }
}

impl<K, R, S, A> Connector<ServerChannel<K, R, S>> for TcpConnector<A> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    for <'de>R: serde::Deserialize<'de>,
    S: Clone + serde::Serialize,
    A: ToSocketAddrs + Clone,
 {
    #[verifier::external_body]
    fn connect<F>(&self, local_id: u64, gen_pred: F) -> Result<
        ServerChannel<K, R, S>,
        ConnectError,
    > where F: FnOnce(&Self, u64) -> Ghost<K> {
        vlib::veprintln!(
            "[client|{:>3}]: connecting to server", local_id,
        );
        let mut stream = TcpStream::connect(self.listening_addr.clone())?;
        stream.set_nonblocking(false).expect("this should never fail");
        stream.write_all(&local_id.to_ne_bytes())?;
        let mut server_id_buf = [0u8;8];
        stream.read_exact(&mut server_id_buf)?;
        let server_id = u64::from_ne_bytes(server_id_buf);
        stream.set_nonblocking(true).expect("this should never fail");

        let tstream = TypedTcpStream::new(stream);
        let pred = gen_pred(self, local_id);

        let peer_addr = tstream.peer_addr();
        let chan = ServerChannel::new(pred, server_id, local_id, tstream);
        vlib::veprintln!(
            "[client|{:>3}]: connected to server {server_id} (channel_id: {:?}, server addr: {:?})", local_id, chan.id(),
            peer_addr
        );
        Ok(chan)
    }
}

} // verus!
