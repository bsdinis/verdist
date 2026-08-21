use crossbeam_channel::unbounded;
use crossbeam_channel::Receiver;
use crossbeam_channel::Sender;

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::network::channel::Connector;
use crate::network::channel::Listener;
use crate::network::error::ConnectError;
use crate::network::error::SendError;
use crate::network::error::TryListenError;
use crate::network::error::TryRecvError;

use vstd::prelude::*;

verus! {

#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct ModelledListener<R, S> {
    id: u64,
    registering_rx: Receiver<u64>,
    connection_tx: Sender<(u64, Sender<R>, Receiver<S>)>,
}

#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct ModelledConnector<R, S> {
    #[allow(dead_code)]
    server_id: u64,
    registering_tx: Sender<u64>,
    connection_rx: Receiver<(u64, Sender<S>, Receiver<R>)>,
}

/// Channel TO Client
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct ClientChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    tx: Sender<S>,
    rx: Receiver<R>,
    client_id: u64,
    server_id: u64,
}

/// Channel TO Server
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(S)]
pub struct ServerChannel<K, R, S> {
    #[allow(dead_code)]
    pred: Ghost<K>,
    tx: Sender<S>,
    rx: Receiver<R>,
    client_id: u64,
    server_id: u64,
}

impl<K, R, S> ClientChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        client_id: u64,
        server_id: u64,
        pred: Ghost<K>,
        tx: Sender<S>,
        rx: Receiver<R>,
    ) -> Self {
        ClientChannel { pred, tx, rx, client_id, server_id }
    }
}

impl<K, R, S> ServerChannel<K, R, S> {
    #[verifier::external_body]
    pub fn new(
        server_id: u64,
        client_id: u64,
        pred: Ghost<K>,
        tx: Sender<S>,
        rx: Receiver<R>,
    ) -> Self {
        ServerChannel { pred, tx, rx, server_id, client_id }
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
    S: Clone,
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
    fn try_recv(&self) -> Result<R, TryRecvError> {
        let r = self.rx.try_recv()?;
        Ok(r)
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), SendError> {
        self.tx.send(v.clone())?;
        Ok(())
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
    S: Clone,
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
    fn try_recv(&self) -> Result<R, TryRecvError> {
        self.rx.try_recv().map_err(|e| e.into())
    }

    #[verifier::external_body]
    fn send(&self, v: &S) -> Result<(), SendError> {
        self.tx.send(v.clone())?;
        Ok(())
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

// NOTE: `try_accept` does not itself construct the channel invariant/ghost map -- that already
// exists by this point. The `Service` establishes it once up front from its own state/resources
// (e.g. `abd`'s `ChannelInv::from_state_pred(..)` in `abd/src/server/mod.rs::create_server`,
// which folds in the per-server ghost-location map) and hands it to `Server::new`, which passes
// it down as the `gen_pred` closure threaded through every `try_accept` call (see
// `Listener::try_accept`'s `gen_pred: Ghost<spec_fn(&Self) -> C::K>` in
// `verdist/src/network/channel.rs`, and `Server::poll_accept`'s call site in
// `verdist/src/service/mod.rs`). All `try_accept` does here is capture that already-built
// invariant into the new channel's `pred` field (`Ghost(gen_pred@(self))`) so `constant()` can
// return it later.
//
// `#[verifier::external_body]` on this fn is an intentional, permanent trust boundary: the real
// work here is a blocking I/O accept + registration handshake, which Verus cannot reason about.
// The postcondition `r.constant() == gen_pred(self)` (declared on the `Listener` trait) is
// therefore assumed rather than checked, but it holds by construction since the body does
// nothing to `pred` other than store the given ghost value verbatim. This pattern is identical
// across all three network impls (tcp, udp, modelled), so none of them is more/less complete
// than the others here.
impl<K, R, S> Listener<ClientChannel<K, R, S>> for ModelledListener<R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    S: Clone,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.id
    }

    #[allow(unused_variables)]
    #[verifier::external_body]
    fn try_accept(&self, gen_pred: Ghost<spec_fn(&Self) -> K>) -> (r: Result<
        ClientChannel<K, R, S>,
        TryListenError,
    >) {
        let client_id = self.registering_rx.try_recv()?;
        vlib::veprintln!(
            "[server|{:>3}]: accepting a connection from client {client_id}", self.id
        );

        let (resp_tx, resp_rx) = unbounded();
        let (req_tx, req_rx) = unbounded();

        self.connection_tx.send((self.id, req_tx, resp_rx)).map_err(
            |_x| TryListenError::Disconnected,
        )?;

        let pred = Ghost(gen_pred@(self));

        let chan = ClientChannel::new(client_id, self.id, pred, resp_tx, req_rx);

        vlib::veprintln!("[server|{:>3}]: accepted connection from client {client_id} (channel_id: {:?})", self.id, chan.id());

        Ok(chan)
    }
}

impl<K, R, S> Connector<ServerChannel<K, R, S>> for ModelledConnector<R, S> where
    K: ChannelInvariant<K, (u64, u64), R, S>,
    S: Clone,
 {
    #[verifier::external_body]
    closed spec fn spec_id(self) -> u64 {
        self.server_id
    }

    #[verifier::external_body]
    fn connect<F>(&self, local_id: u64, gen_pred: F) -> (r: Result<
        ServerChannel<K, R, S>,
        ConnectError,
    >) where F: FnOnce(&Self, u64) -> Ghost<K> {
        vlib::veprintln!(
            "[client|{:>3}]: connecting to server", local_id,
        );
        self.registering_tx.send(local_id).map_err(|_e| ConnectError::Failed)?;
        let (server_id, tx, rx) = self.connection_rx.recv().map_err(|_e| ConnectError::Failed)?;
        let pred = gen_pred(self, local_id);
        let chan = ServerChannel::new(server_id, local_id, pred, tx, rx);
        vlib::veprintln!(
            "[client|{:>3}]: connected to server {server_id}  (channel_id: {:?})", local_id, chan.id()
        );
        Ok(chan)
    }
}

#[verifier::external_body]
pub fn listen_channel<R, S>(server_id: u64) -> (ModelledListener<R, S>, ModelledConnector<S, R>) {
    let (registering_tx, registering_rx) = unbounded();
    let (connection_tx, connection_rx) = unbounded();
    let listener = ModelledListener { id: server_id, registering_rx, connection_tx };

    let connector = ModelledConnector { server_id, registering_tx, connection_rx };

    (listener, connector)
}

} // verus!
