#[cfg(verus_only)]
use crate::network::channel::Channel;
#[cfg(verus_only)]
use crate::network::channel::ChannelInvariant;
use crate::pool::ChannelId;
use crate::pool::ChannelResp;
use crate::pool::ConnectionPool;
use crate::pool::PoolChannel;
use crate::rpc::replies::ReplyAccumulator;
use crate::rpc::Replies;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

use super::proto::TaggedMessage;

verus! {

pub struct RequestContext<'a, Pool, Pred, A> where
    Pool: ConnectionPool,
    ChannelResp<Pool>: TaggedMessage,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<PoolChannel<Pool>, Pred>,
 {
    pool: &'a Pool,
    request_tag: u64,
    replies: Replies<PoolChannel<Pool>, Pred, A>,
}

impl<'a, Pool, Pred, A> RequestContext<'a, Pool, Pred, A> where
    Pool: ConnectionPool,
    ChannelResp<Pool>: TaggedMessage,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<PoolChannel<Pool>, Pred>,
 {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.pool.spec_channels() == self.replies.channels()
        &&& self.request_tag == self.replies.request_tag()
    }
}

pub type WaitForResult<C, Pred, A> = Result<Replies<C, Pred, A>, Replies<C, Pred, A>>;

impl<'a, Pool, Pred, A> RequestContext<'a, Pool, Pred, A> where
    Pool: ConnectionPool,
    ChannelId<Pool>: std::fmt::Debug,
    ChannelResp<Pool>: TaggedMessage,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<PoolChannel<Pool>, Pred>,
 {
    pub fn new(pool: &'a Pool, request_tag: u64, pred: Ghost<Pred>, accum: A) -> (r: Self)
        requires
            Pred::inv(pred@, accum),
            accum.request_tag() == request_tag,
            accum.spec_handled_replies().is_empty(),
            accum.channels() == pool.spec_channels(),
            vstd::laws_cmp::obeys_cmp::<ChannelId<Pool>>(),
        ensures
            r.pred() == pred@,
            r.channels() == pool.spec_channels(),
    {
        RequestContext { pool, request_tag, replies: Replies::new(pred, accum) }
    }

    pub fn tag(&self) -> u64 {
        self.request_tag
    }

    pub fn n_nodes(&self) -> usize {
        self.pool.len()
    }

    pub closed spec fn pred(self) -> Pred {
        self.replies.pred()
    }

    pub closed spec fn channels(self) -> Map<ChannelId<Pool>, PoolChannel<Pool>> {
        self.pool.spec_channels()
    }

    #[verifier::exec_allows_no_decreases_clause]
    // TODO: a mechanism to ensure that the Replies we get back is the same we put in (i.e., same
    // identity, not same value, would be useful, maybe)
    pub fn wait_for<F>(self, termination_cond: F) -> (r: WaitForResult<
        PoolChannel<Pool>,
        Pred,
        A,
    >) where F: Fn(&Replies<PoolChannel<Pool>, Pred, A>) -> bool
        requires
            forall|replies| termination_cond.requires((&replies,)),
        ensures
            r is Ok ==> {
                &&& call_ensures(termination_cond, (&r->Ok_0,), true)
                &&& Pred::inv(self.pred(), r->Ok_0.spec_accumulator())
            },
            r is Err ==> {
                &&& Pred::inv(self.pred(), r->Err_0.spec_accumulator())
            },
    {
        proof {
            use_type_invariant(&self);
        }
        let ghost pred = self.pred();
        let ghost channels = self.channels();
        let ghost request_tag = self.request_tag;
        let mut self_mut = self;
        loop
            invariant
                forall|replies| termination_cond.requires((&replies,)),
                pred == self_mut.pred(),
                pred == self.pred(),
                channels == self_mut.channels(),
                channels == self.channels(),
                self_mut.pool.spec_channels() == channels,
                self_mut.replies.channels() == channels,
                self_mut.request_tag == request_tag,
                self_mut.replies.request_tag() == request_tag,
        {
            if termination_cond(&self_mut.replies) {
                self_mut.replies.lemma_pred();
                assert(Pred::inv(self_mut.replies.pred(), self_mut.replies.spec_accumulator()));
                assert(self_mut.replies.pred() == pred);
                return Ok(self_mut.replies);
            }
            // TODO: we can try to figure out a better "give up" condition

            if self_mut.replies.n_received() >= self_mut.n_nodes() {
                let replies = self_mut.replies;
                replies.lemma_pred();

                assert(Pred::inv(replies.pred(), replies.spec_accumulator()));
                assert(replies.pred() == pred);
                assert(Pred::inv(pred, replies.spec_accumulator()));
                assert(Pred::inv(self.pred(), replies.spec_accumulator()));
                return Err(replies);
            }
            let resps = self_mut.pool.poll(self_mut.request_tag);
            if resps.is_empty() {
                continue;
            }
            #[allow(unused)]
            let mut idx = 0usize;
            #[allow(clippy::explicit_counter_loop)]
            for (id, r) in it: resps
                invariant
                    pred == self_mut.pred(),
                    channels == self_mut.channels(),
                    self_mut.pool.spec_channels() == channels,
                    self_mut.replies.channels() == channels,
                    idx == it.index,
                    forall|idx|
                        0 <= idx < resps@.len() ==> {
                            let (id, r) = #[trigger] resps@[idx];
                            &&& self_mut.pool.spec_channels().contains_key(id)
                            &&& {
                                let chan = self_mut.pool.spec_channels()[id];
                                r is Ok && r->Ok_0 is Some ==> {
                                    let resp = r->Ok_0->Some_0;
                                    &&& <<Pool as ConnectionPool>::C as Channel>::K::recv_inv(
                                        chan.constant(),
                                        id,
                                        resp,
                                    )
                                    &&& resp.spec_tag() == request_tag
                                }
                            }
                        },
                    self_mut.request_tag == request_tag,
                    self_mut.replies.request_tag() == request_tag,
            {
                proof {
                    self_mut.pool.lemma_channels();
                }
                let ghost chan = self_mut.pool.spec_channels()[id];

                match r {
                    Ok(Some(resp)) => {
                        assert(chan.spec_id() == id);
                        assert(<<Pool as ConnectionPool>::C as Channel>::K::recv_inv(
                            chan.constant(),
                            id,
                            resp,
                        ));
                        self_mut.replies.insert_reply(id, resp)
                    },
                    Ok(None) => {},
                    Err(e) => {
                        self_mut.replies.insert_error(id, e);
                    },
                }

                assume(idx < usize::MAX);  // XXX: overflow
                #[allow(unused)]
                {
                    idx += 1;
                }
            }
        }
    }
}

} // verus!
