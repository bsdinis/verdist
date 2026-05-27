use crate::network::channel::Channel;
#[cfg(verus_only)]
use crate::network::channel::ChannelInvariant;
#[cfg(verus_only)]
use crate::pool::connection_pool::channel_seq_to_map;
#[cfg(verus_only)]
use crate::pool::connection_pool::lemma_channel_seq_to_map;
use crate::pool::ChannelId;
use crate::pool::ChannelResp;
use crate::pool::ConnectionPool;
use crate::pool::PoolChannel;
use crate::rpc::proto::TaggedMessage;
use crate::rpc::replies::ReplyAccumulator;
use crate::rpc::RequestContext;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub struct BroadcastPool<'a, Pool> {
    pub pool: &'a Pool,
}

// TODO: remove request generic
impl<'a, Pool, Request> BroadcastPool<'a, Pool> where
    Pool: ConnectionPool,
    ChannelResp<Pool>: TaggedMessage,
    ChannelId<Pool>: std::fmt::Debug,
    Pool::C: Channel<S = Request>,
    ChannelResp<Pool>: TaggedMessage + std::fmt::Debug,
    Request: TaggedMessage + Clone + std::fmt::Debug,
 {
    pub fn new(pool: &'a Pool) -> (r: BroadcastPool<'a, Pool>)
        ensures
            r.spec_channels() == pool.spec_channels(),
    {
        BroadcastPool { pool }
    }

    pub open spec fn spec_channels(self) -> Map<ChannelId<Pool>, PoolChannel<Pool>> {
        self.pool.spec_channels()
    }

    pub fn broadcast_filter<Pred, A, F>(
        self,
        request: Request,
        pred: Ghost<Pred>,
        accum: A,
        filter_fn: F,
    ) -> (r: RequestContext<'a, Pool, Pred, A>) where
        Pred: InvariantPredicate<Pred, A>,
        A: ReplyAccumulator<PoolChannel<Pool>, Pred>,
        F: Fn(ChannelId<Pool>) -> bool,

        requires
            Pred::inv(pred@, accum),
            accum.request_tag() == request.spec_tag(),
            accum.spec_handled_replies().is_empty(),
            accum.channels() == self.spec_channels(),
            vstd::laws_cmp::obeys_cmp::<ChannelId<Pool>>(),
            forall|id| #[trigger]
                self.spec_channels().contains_key(id) ==> {
                    let chan = self.spec_channels()[id];
                    &&& filter_fn.requires((chan.spec_id(),))
                    &&& <PoolChannel<Pool> as Channel>::K::send_inv(
                        chan.constant(),
                        chan.spec_id(),
                        request,
                    )
                },
        ensures
            r.pred() == pred@,
    {
        let channels = self.pool.channels();
        let ghost g_channels = self.spec_channels();
        proof {
            lemma_channel_seq_to_map(channels@, self.spec_channels());
        }
        #[allow(clippy::explicit_iter_loop)]
        for chan in channels.iter()
            invariant
                self.spec_channels() == g_channels,
                self.spec_channels() == channel_seq_to_map(channels@),
                channels@.map_values(|c: PoolChannel<Pool>| c.spec_id()).no_duplicates(),
                forall|id| #[trigger]
                    self.spec_channels().contains_key(id) ==> {
                        let c = self.spec_channels()[id];
                        &&& filter_fn.requires((c.spec_id(),))
                        &&& <PoolChannel<Pool> as Channel>::K::send_inv(
                            c.constant(),
                            c.spec_id(),
                            request,
                        )
                    },
        {
            proof {
                lemma_channel_seq_to_map(channels@, self.spec_channels());
                assert(self.spec_channels().contains_key(chan.spec_id()));
            }
            if filter_fn(chan.id()) {
                let _res = chan.send(&request);
            }
        }
        RequestContext::new(self.pool, request.tag(), pred, accum)
    }

    pub fn broadcast<Pred, A>(self, request: Request, pred: Ghost<Pred>, accum: A) -> (r:
        RequestContext<'a, Pool, Pred, A>) where
        Pred: InvariantPredicate<Pred, A>,
        A: ReplyAccumulator<PoolChannel<Pool>, Pred>,

        requires
            Pred::inv(pred@, accum),
            accum.request_tag() == request.spec_tag(),
            accum.spec_handled_replies().is_empty(),
            accum.channels() == self.spec_channels(),
            vstd::laws_cmp::obeys_cmp::<ChannelId<Pool>>(),
            forall|id| #[trigger]
                self.spec_channels().contains_key(id) ==> {
                    let chan = self.spec_channels()[id];
                    <PoolChannel<Pool> as Channel>::K::send_inv(
                        chan.constant(),
                        chan.spec_id(),
                        request,
                    )
                },
        ensures
            r.pred() == pred@,
    {
        self.broadcast_filter(request, pred, accum, |_s| true)
    }
}

} // verus!
