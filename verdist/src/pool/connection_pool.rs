use crate::network::channel::BufChannel;
use crate::network::channel::Channel;
#[cfg(verus_only)]
use crate::network::channel::ChannelInvariant;
use crate::rpc::proto::TaggedMessage;

use vstd::prelude::*;

use super::ChannelResp;

verus! {

pub open spec fn channel_seq_to_map<C: Channel>(s: Seq<C>) -> Map<C::Id, C>
    recommends
        s.map_values(|c: C| c.spec_id()).no_duplicates(),
{
    Map::new(
        s.map_values(|c: C| c.spec_id()).to_set(),
        |id|
            {
                let idx = choose|idx| 0 <= idx < s.len() && #[trigger] s[idx].spec_id() == id;
                s[idx]
            },
    )
}

pub proof fn lemma_channel_seq_to_map<C: Channel>(s: Seq<C>, m: Map<C::Id, C>)
    requires
        m == channel_seq_to_map(s),
        s.map_values(|c: C| c.spec_id()).no_duplicates(),
    ensures
        m.dom() == s.map_values(|c: C| c.spec_id()).to_set(),
        m.values() == s.to_set(),
        forall|id| #[trigger] m.contains_key(id) ==> m[id].spec_id() == id,
        forall|idx|
            0 <= idx < s.len() ==> {
                let channel = #[trigger] s[idx];
                &&& m.contains_key(channel.spec_id())
                &&& m[channel.spec_id()] == channel
            },
{
    let ghost seq_channels = s.to_set();
    let ghost seq_ids = s.map_values(|c: C| c.spec_id());
    let ghost map_channels = m.values();
    s.lemma_to_set_map_commutes(|c: C| c.spec_id());
    assert(seq_ids.no_duplicates());

    assert forall|c| #[trigger] seq_channels.contains(c) implies map_channels.contains(c) by {
        let id = c.spec_id();

        assert(exists|idx| 0 <= idx < s.len() && #[trigger] s[idx] == c);
        assert(exists|idx| 0 <= idx < s.len() && #[trigger] s[idx].spec_id() == c.spec_id());
        let idx = choose|idx| 0 <= idx < s.len() && #[trigger] s[idx] == c;
        let idx2 = choose|idx| 0 <= idx < s.len() && #[trigger] s[idx].spec_id() == id;
        vstd::assert_by_contradiction!(idx == idx2, {
            assert(s[idx].spec_id() == s[idx2].spec_id());
            assert(seq_ids[idx] == id);
            assert(seq_ids[idx2] == id);
        });

        assert(m.contains_key(id));
    }
    assert forall|c| map_channels.contains(c) implies seq_channels.contains(c) by {
        let id = c.spec_id();
        assert(m.contains_key(id));
        assert(exists|idx| 0 <= idx < s.len() && #[trigger] s[idx].spec_id() == id);
        let idx = choose|idx| 0 <= idx < s.len() && #[trigger] s[idx].spec_id() == id;
    }

    assert forall|idx| 0 <= idx < s.len() implies {
        let channel = #[trigger] s[idx];
        &&& m.contains_key(channel.spec_id())
        &&& m[channel.spec_id()] == channel
    } by {
        let channel = s[idx];
        let id = channel.spec_id();
        assert(seq_ids[idx] == id);
        assert(m.contains_key(id));

        assert(s.to_set().contains(channel));
        assert(m.values().contains(channel));
    }
}

pub trait ConnectionPool {
    type R: TaggedMessage;

    type C: Channel<R = Self::R>;

    fn len(&self) -> (r: usize)
        ensures
            r == self.spec_len(),
    ;

    spec fn spec_len(self) -> nat;

    fn channels(&self) -> (r: &[Self::C])
        ensures
            self.spec_channels() == channel_seq_to_map(r@),
            r@.map_values(|c: Self::C| c.spec_id()).no_duplicates(),
    ;

    spec fn spec_channels(&self) -> Map<<Self::C as Channel>::Id, Self::C>;

    fn poll(&self, request_tag: u64) -> (r: Vec<
        (
            <Self::C as Channel>::Id,
            Result<Option<ChannelResp<Self>>, crate::network::error::TryRecvError>,
        ),
    >)
        ensures
            forall|idx|
                0 <= idx < r@.len() ==> {
                    let (id, r) = #[trigger] r@[idx];
                    &&& self.spec_channels().contains_key(id)
                    &&& r is Ok && r->Ok_0 is Some ==> {
                        let resp = r->Ok_0->Some_0;
                        &&& resp.spec_tag() == request_tag
                        &&& <Self::C as Channel>::K::recv_inv(
                            self.spec_channels()[id].constant(),
                            id,
                            resp,
                        )
                    }
                },
    ;

    proof fn lemma_len(tracked &self)
        ensures
            self.spec_len() == self.spec_channels().len(),
    ;

    proof fn lemma_channels(tracked &self)
        ensures
            forall|id| #[trigger]
                self.spec_channels().contains_key(id) ==> self.spec_channels()[id].spec_id() == id,
    ;
}

pub struct FlawlessPool<C> where C: Channel {
    pool: Vec<C>,
}

impl<C> FlawlessPool<C> where C: Channel {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        // all channel ids are different
        self.pool@.map_values(|c: C| c.spec_id()).no_duplicates()
    }

    fn _channels(&self) -> (r: &[C])
        ensures
            self._spec_channels() == channel_seq_to_map(r@),
            r@.map_values(|c: C| c.spec_id()).no_duplicates(),
    {
        proof {
            use_type_invariant(self);
            self._lemma_channels();
            lemma_channel_seq_to_map(self.pool@, self._spec_channels());
        }
        self.pool.as_slice()
    }

    closed spec fn _spec_channels(self) -> Map<<C as Channel>::Id, C> {
        channel_seq_to_map(self.pool@)
    }

    fn _len(&self) -> (r: usize)
        ensures
            r == self._spec_len(),
    {
        self.pool.len()
    }

    closed spec fn _spec_len(self) -> nat {
        self.pool@.len()
    }

    proof fn _lemma_len(tracked &self)
        ensures
            self._spec_len() == self._spec_channels().len(),
    {
        use_type_invariant(self);
        self._lemma_channels();
        lemma_channel_seq_to_map(self.pool@, self._spec_channels());
        let ghost pool_ids = self.pool@.map_values(|c: C| c.spec_id());
        assert(self._spec_len() == pool_ids.len());
        assert(self._spec_channels().len() == pool_ids.to_set().len());
        pool_ids.unique_seq_to_set();
    }

    proof fn _lemma_channels(tracked &self)
        ensures
            self.pool@.map_values(|c: C| c.spec_id()).no_duplicates(),
            self._spec_channels() == channel_seq_to_map(self.pool@),
    {
        use_type_invariant(self);
    }
}

impl<C> FlawlessPool<BufChannel<C>> where
    C: Channel,
    C::Id: std::fmt::Debug,
    C::S: TaggedMessage,
    C::R: TaggedMessage,
 {
    pub fn new(pool: Vec<BufChannel<C>>) -> (r: Self)
        requires
            pool@.map_values(|c: BufChannel<C>| c.spec_id()).no_duplicates(),
        ensures
            r.spec_len() == pool@.len(),
            r.spec_channels() == channel_seq_to_map(pool@),
    {
        FlawlessPool { pool }
    }
}

impl<C> ConnectionPool for FlawlessPool<BufChannel<C>> where
    C: Channel,
    C::Id: std::fmt::Debug,
    C::S: TaggedMessage,
    C::R: TaggedMessage,
 {
    type R = C::R;

    type C = BufChannel<C>;

    fn len(&self) -> usize {
        self._len()
    }

    closed spec fn spec_len(self) -> nat {
        self._spec_len()
    }

    fn channels(&self) -> &[Self::C] {
        self._channels()
    }

    closed spec fn spec_channels(&self) -> Map<<Self::C as Channel>::Id, Self::C> {
        self._spec_channels()
    }

    fn poll(&self, request_tag: u64) -> Vec<
        (C::Id, Result<Option<C::R>, crate::network::error::TryRecvError>),
    > {
        proof {
            use_type_invariant(self);
            self._lemma_channels();
            lemma_channel_seq_to_map(self.pool@, self._spec_channels());
            assert(forall|idx|
                0 <= idx < self.pool@.len() ==> {
                    let channel = #[trigger] self.pool@[idx];
                    &&& self.spec_channels().contains_key(channel.spec_id())
                    &&& self.spec_channels()[channel.spec_id()] == channel
                })
        }
        let mut v = Vec::new();

        for idx in 0..self.pool.len()
            invariant
                forall|v_idx|
                    0 <= v_idx < v@.len() ==> {
                        let (id, resp): (C::Id, Result<Option<C::R>, _>) = #[trigger] v@[v_idx];
                        &&& self.spec_channels().contains_key(id)
                        &&& resp is Ok && resp->Ok_0 is Some ==> {
                            let x = resp->Ok_0->Some_0;
                            &&& x.spec_tag() == request_tag
                            &&& <Self::C as Channel>::K::recv_inv(
                                self.spec_channels()[id].constant(),
                                id,
                                x,
                            )
                        }
                    },
                forall|idx|
                    0 <= idx < self.pool@.len() ==> {
                        let channel = #[trigger] self.pool@[idx];
                        &&& self._spec_channels().contains_key(channel.spec_id())
                        &&& self._spec_channels()[channel.spec_id()] == channel
                    },
        {
            let channel = &self.pool[idx];
            let ghost idx_i = idx as int;
            let res = channel.try_recv_tag(request_tag);
            let ghost old_v = v@;
            v.push((channel.id(), res));
        }

        v
    }

    proof fn lemma_len(tracked &self) {
        self._lemma_len()
    }

    proof fn lemma_channels(tracked &self) {
        self._lemma_channels();
        lemma_channel_seq_to_map(self.pool@, self._spec_channels());
    }
}

} // verus!
