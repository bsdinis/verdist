use std::collections::{BTreeMap, BTreeSet};

use crate::network::channel::Channel;
#[cfg(verus_only)]
use crate::network::channel::ChannelInvariant;
use crate::network::error::TryRecvError;
use crate::rpc::proto::TaggedMessage;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub trait ReplyAccumulator<C, Pred>: Sized where
    C: Channel,
    C::R: TaggedMessage,
    Pred: InvariantPredicate<Pred, Self>,
 {
    fn insert(&mut self, pred: Ghost<Pred>, id: C::Id, reply: C::R)
        requires
            Pred::inv(pred@, *old(self)),
            old(self).request_tag() == reply.spec_tag(),
            old(self).channels().contains_key(id),
            ({
                let chan = old(self).channels()[id];
                &&& chan.spec_id() == id
                &&& C::K::recv_inv(chan.constant(), id, reply)
            }),
        ensures
            Pred::inv(pred@, *final(self)),
            final(self).request_tag() == old(self).request_tag(),
            final(self).spec_handled_replies() == old(self).spec_handled_replies().insert(id),
            final(self).channels() == old(self).channels(),
        no_unwind
    ;

    spec fn request_tag(self) -> u64;

    spec fn spec_handled_replies(self) -> Set<C::Id>;

    // This could be some generic thing that implements view to Set
    // But we'll just make it a BTreeSet
    fn handled_replies(&self) -> (r: BTreeSet<C::Id>)
        ensures
            r@ == self.spec_handled_replies(),
    ;

    spec fn channels(self) -> Map<C::Id, C>;
}

pub struct Replies<C, Pred, A> where
    C: Channel,
    C::R: TaggedMessage,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<C, Pred>,
 {
    pred: Ghost<Pred>,
    accum: A,
    errors: BTreeMap<C::Id, TryRecvError>,
}

impl<C, Pred, A> Replies<C, Pred, A> where
    C: Channel,
    C::R: TaggedMessage,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<C, Pred>,
 {
    pub fn new(pred: Ghost<Pred>, accum: A) -> (r: Self)
        requires
            Pred::inv(pred@, accum),
            accum.spec_handled_replies().is_empty(),
            vstd::laws_cmp::obeys_cmp::<C::Id>(),
        ensures
            r.spec_len() == 0,
            r.pred() == pred@,
            r.channels() == accum.channels(),
            r.request_tag() == accum.request_tag(),
    {
        Replies { pred, accum, errors: BTreeMap::new() }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& vstd::laws_cmp::obeys_cmp::<C::Id>()
        &&& Pred::inv(self.pred(), self.accum)
    }

    pub fn lemma_pred(&self)
        ensures
            Pred::inv(self.pred(), self.spec_accumulator()),
    {
        proof {
            use_type_invariant(self);
        }
    }

    pub closed spec fn request_tag(self) -> u64 {
        self.accum.request_tag()
    }

    pub closed spec fn pred(self) -> Pred {
        self.pred@
    }

    pub closed spec fn channels(self) -> Map<C::Id, C> {
        self.accum.channels()
    }

    pub fn len(&self) -> (r: usize)
        ensures
            r as nat == self.spec_len(),
    {
        proof {
            use_type_invariant(self);
        }
        self.accum.handled_replies().len()
    }

    pub fn is_empty(&self) -> (r: bool)
        ensures
            r <==> self.spec_len() == 0,
    {
        proof {
            use_type_invariant(self);
        }
        self.len() == 0
    }

    pub open spec fn spec_len(self) -> (r: nat) {
        self.spec_handled_replies().len()
    }

    pub closed spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.accum.spec_handled_replies()
    }

    pub fn n_received(&self) -> usize {
        assume(self.spec_len() + self.errors.len() <= usize::MAX);  // XXX: arithmetic overflow
        self.len() + self.errors.len()
    }

    pub closed spec fn spec_accumulator(self) -> A {
        self.accum
    }

    pub fn accumulator(&self) -> &A
        returns
            self.spec_accumulator(),
    {
        &self.accum
    }

    pub fn into_accumulator(self) -> (r: A)
        ensures
            r.spec_handled_replies() == self.spec_handled_replies(),
            r == self.spec_accumulator(),
    {
        self.accum
    }

    pub closed spec fn spec_errors(self) -> (r: Map<C::Id, TryRecvError>) {
        self.errors@
    }

    pub fn errors(&self) -> (r: &BTreeMap<C::Id, TryRecvError>)
        ensures
            r@ == self.spec_errors(),
    {
        &self.errors
    }

    pub fn into_errors(self) -> (r: BTreeMap<C::Id, TryRecvError>)
        ensures
            r@ == self.spec_errors(),
    {
        self.errors
    }

    pub fn insert_reply(&mut self, id: C::Id, reply: C::R)
        requires
            old(self).channels().contains_key(id),
            old(self).request_tag() == reply.spec_tag(),
            ({
                let chan = old(self).channels()[id];
                &&& chan.spec_id() == id
                &&& C::K::recv_inv(chan.constant(), id, reply)
            }),
        ensures
            final(self).request_tag() == old(self).request_tag(),
            final(self).spec_handled_replies() == old(self).spec_handled_replies().insert(id),
            final(self).spec_errors() == old(self).spec_errors(),
            final(self).pred() == old(self).pred(),
            final(self).channels() == old(self).channels(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        self.accum.insert(self.pred, id, reply);
    }

    pub fn insert_error(&mut self, id: C::Id, err: TryRecvError)
        ensures
            final(self).request_tag() == old(self).request_tag(),
            final(self).spec_accumulator() == old(self).spec_accumulator(),
            final(self).spec_errors() == old(self).spec_errors().insert(id, err),
            final(self).pred() == old(self).pred(),
            final(self).channels() == old(self).channels(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        self.errors.insert(id, err);
    }
}

} // verus!
