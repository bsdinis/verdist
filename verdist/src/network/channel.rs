use std::collections::HashMap;
use std::marker::PhantomData;

use crate::network::error::ConnectError;
use crate::network::error::SendError;
use crate::network::error::TryListenError;
use crate::network::error::TryRecvError;
use crate::rpc::proto::TaggedMessage;

use vstd::prelude::*;
use vstd::rwlock::RwLock;

verus! {

pub trait ChannelInvariant<K, Id, R, S> {
    spec fn recv_inv(k: K, id: Id, r: R) -> bool;

    spec fn send_inv(k: K, id: Id, s: S) -> bool;
}

// NOTE: On channel equality
//
// Something is weird about Verus's model for equality.
// Verus generally assumes that shared references imply immutability.
// Meaning if you have
// ```
// fn f(x: &usize) { ... }
//
// fn g() {
//      let x = 5;
//      let ghost x_cpy = x;
//      f(&x);
//      assert(x == x_cpy)
// }
// ```
//
// Always verifies.
//
// However, consider something like
// ```
// fn f(x: &RwLock<usize, _>) { *x.lock() *= 5  }
//
// fn g() {
//      let x = RwLock::new(5);
//      let ghost x_cpy = x;
//      f(&x);
//      assert(x == x_cpy)
// }
// ```
//
// This should verify?
// Meaning two RwLocks would be the same if their predicates are the same??
/// A reliable and typed channel
///
/// The spec is in the type -- by virtue of having a type `R` the receiver learns something
pub trait Channel {
    /// Id of the channel
    type Id: Ord;

    /// Type being received
    type R;

    /// Type being sent
    type S: Clone;

    /// Constant maintained by the channel
    // (e.g., K holds the loc of the gmap from req_id \to X)
    // in our case X can be a more specific set of locations
    type K: ChannelInvariant<Self::K, Self::Id, Self::R, Self::S>;

    fn send(&self, s: &Self::S) -> Result<(), SendError>
        requires
            Self::K::send_inv(self.constant(), self.spec_id(), *s),
    ;

    fn try_recv(&self) -> (r: Result<Self::R, TryRecvError>)
        ensures
            r is Ok ==> Self::K::recv_inv(self.constant(), self.spec_id(), r->Ok_0),
    ;

    fn id(&self) -> (r: Self::Id)
        ensures
            r == self.spec_id(),
    ;

    spec fn spec_id(self) -> Self::Id;

    spec fn constant(self) -> Self::K;
}

pub trait Listener<C> where C: Channel {
    fn try_accept(&self, gen_pred: Ghost<spec_fn(&Self) -> C::K>) -> (r: Result<C, TryListenError>)
        ensures
            r is Ok ==> r->Ok_0.constant() == gen_pred(self),
    ;
}

pub trait Connector<C> where C: Channel {
    fn connect<F>(&self, local_id: u64, gen_pred: F) -> (r: Result<C, ConnectError>) where
        F: FnOnce(&Self, u64) -> Ghost<C::K>,

        ensures
            r is Ok ==> gen_pred.ensures((self, local_id), Ghost(r->Ok_0.constant())),
    ;
}

#[allow(dead_code)]
struct BufChannelInv<K, Id, S> {
    ghost channel_inv: K,
    ghost channel_id: Id,
    _marker: PhantomData<S>,
}

impl<K, Id, R, S> vstd::rwlock::RwLockPredicate<HashMap<u64, R>> for BufChannelInv<K, Id, S> where
    K: ChannelInvariant<K, Id, R, S>,
    R: TaggedMessage,
 {
    closed spec fn inv(self, v: HashMap<u64, R>) -> bool {
        forall|tag: u64| #[trigger]
            v@.contains_key(tag) ==> {
                &&& v@[tag].spec_tag() == tag
                &&& K::recv_inv(self.channel_inv, self.channel_id, v@[tag])
            }
    }
}

pub struct BufChannel<C> where C: Channel, C::R: TaggedMessage {
    channel: C,
    #[allow(dead_code, clippy::type_complexity)]
    buffered: RwLock<HashMap<u64, C::R>, BufChannelInv<C::K, C::Id, C::S>>,
}

impl<C> BufChannel<C> where C: Channel, C::R: TaggedMessage {
    pub fn new(channel: C) -> (r: Self)
        ensures
            r.spec_id() == channel.spec_id(),
            r.constant() == channel.constant(),
    {
        let ghost lock_pred = BufChannelInv {
            channel_inv: channel.constant(),
            channel_id: channel.spec_id(),
            _marker: PhantomData,
        };
        BufChannel { channel, buffered: RwLock::new(HashMap::new(), Ghost(lock_pred)) }
    }

    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.buffered.pred().channel_inv == self.constant()
        &&& self.buffered.pred().channel_id == self.spec_id()
    }
}

impl<C> BufChannel<C> where C: Channel, C::R: TaggedMessage, C::Id: std::fmt::Debug {
    pub fn try_recv_tag(&self, tag: u64) -> (r: Result<Option<C::R>, TryRecvError>)
        ensures
            r is Ok && r->Ok_0 is Some ==> {
                let resp = r->Ok_0->Some_0;
                &&& C::K::recv_inv(self.constant(), self.spec_id(), resp)
                &&& resp.spec_tag() == tag
            },
    {
        proof {
            use_type_invariant(self);
        }
        let (mut guard, handle) = self.buffered.acquire_write();
        if let Some(r) = guard.remove(&tag) {
            handle.release_write(guard);
            return Ok(Some(r));
        }
        handle.release_write(guard);

        //vlib::veprintln!("[client]: polling on channel {:?}", self.id());
        match self.channel.try_recv() {
            Ok(r) if r.tag() == tag => {
                // vlib::veprintln!("[client]: received correct message on channel {:?}", self.id());
                assert(r.spec_tag() == tag);
                assert(C::K::recv_inv(self.constant(), self.spec_id(), r));
                Ok(Some(r))
            },
            Ok(r) => {
                // vlib::veprintln!("[client]: received message on channel {:?} (wrong tag)", self.id());
                let (mut guard, handle) = self.buffered.acquire_write();
                guard.insert(r.tag(), r);
                handle.release_write(guard);
                Ok(None)
            },
            Err(crate::network::error::TryRecvError::Empty) => Ok(None),
            Err(e) => Err(e),
        }
    }
}

impl<C> Channel for BufChannel<C> where C: Channel, C::R: TaggedMessage {
    type R = C::R;

    type S = C::S;

    type Id = C::Id;

    type K = C::K;

    closed spec fn constant(self) -> Self::K {
        self.channel.constant()
    }

    fn id(&self) -> Self::Id {
        self.channel.id()
    }

    closed spec fn spec_id(self) -> Self::Id {
        self.channel.spec_id()
    }

    fn try_recv(&self) -> Result<Self::R, TryRecvError> {
        self.channel.try_recv()
    }

    fn send(&self, v: &Self::S) -> Result<(), SendError> {
        self.channel.send(v)
    }
}

} // verus!
