use vstd::prelude::*;

use crate::network::channel::BufChannel;
use crate::network::channel::Channel;
#[cfg(verus_only)]
use crate::network::channel::ChannelInvariant;
use crate::network::error::InvokeError;
use crate::network::error::SendError;
use crate::network::error::TryRecvError;
use crate::rpc::proto::TaggedMessage;

verus! {

pub struct RpcChannel<C> where C: Channel, C::R: TaggedMessage, C::S: TaggedMessage {
    channel: BufChannel<C>,
}

impl<C> RpcChannel<C> where
    C: Channel,
    C::Id: std::fmt::Debug,
    C::R: TaggedMessage,
    C::S: TaggedMessage,
 {
    pub fn new(channel: BufChannel<C>) -> (r: Self)
        ensures
            r.channel() == channel,
    {
        RpcChannel { channel }
    }

    pub closed spec fn channel(self) -> BufChannel<C> {
        self.channel
    }

    pub open spec fn spec_id(self) -> C::Id {
        self.channel().spec_id()
    }

    pub open spec fn constant(self) -> C::K {
        self.channel().constant()
    }

    pub fn async_invoke<'a>(&'a self, req: &C::S) -> (r: Result<RpcContext<'a, C>, SendError>)
        requires
            C::K::send_inv(self.channel().constant(), self.channel().spec_id(), *req),
        ensures
            r is Ok ==> {
                let ctx = r->Ok_0;
                &&& ctx.spec_tag() == req.spec_tag()
                &&& ctx.channel() == self.channel()
            },
    {
        self.channel.send(req)?;
        Ok(RpcContext { channel: &self.channel, tag: req.tag() })
    }

    pub fn invoke(&self, req: &C::S) -> (r: Result<C::R, InvokeError>)
        requires
            C::K::send_inv(self.channel().constant(), self.channel().spec_id(), *req),
        ensures
            r is Ok ==> {
                let resp = r->Ok_0;
                &&& resp.spec_tag() == req.spec_tag()
                &&& C::K::recv_inv(self.channel().constant(), self.channel().spec_id(), resp)
            },
    {
        let ctx = self.async_invoke(req)?;
        let resp = ctx.wait()?;
        Ok(resp)
    }
}

pub struct RpcContext<'a, C> where C: Channel, C::R: TaggedMessage, C::S: TaggedMessage {
    channel: &'a BufChannel<C>,
    tag: u64,
}

impl<'a, C> RpcContext<'a, C> where
    C: Channel,
    C::Id: std::fmt::Debug,
    C::R: TaggedMessage,
    C::S: TaggedMessage,
 {
    pub closed spec fn spec_tag(self) -> u64 {
        self.tag
    }

    pub closed spec fn channel(self) -> BufChannel<C> {
        *self.channel
    }

    pub fn try_poll(&self) -> (r: Result<Option<C::R>, TryRecvError>)
        ensures
            r is Ok && r->Ok_0 is Some ==> {
                let resp = r->Ok_0->Some_0;
                &&& resp.spec_tag() == self.spec_tag()
                &&& C::K::recv_inv(self.channel().constant(), self.channel().spec_id(), resp)
            },
    {
        self.channel.try_recv_tag(self.tag)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn wait(self) -> (r: Result<C::R, TryRecvError>)
        ensures
            r is Ok ==> {
                let resp = r->Ok_0;
                &&& resp.spec_tag() == self.spec_tag()
                &&& C::K::recv_inv(self.channel().constant(), self.channel().spec_id(), resp)
            },
    {
        loop {
            if let Some(r) = self.try_poll()? {
                return Ok(r);
            }
        }
    }
}

} // verus!
