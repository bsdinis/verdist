#[cfg(verus_only)]
use crate::invariants::StatePredicate;
use crate::proto::Request;
use crate::proto::Response;

use verdist::network::channel::ChannelInvariant;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;

use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

#[allow(dead_code)]
pub struct ChannelInv {
    pub commitment_id: Loc,
    pub request_map_id: Loc,
    pub server_tokens_id: Loc,
    pub server_locs: Map<u64, Loc>,
}

impl ChannelInv {
    pub open spec fn from_state_pred(s_inv: StatePredicate) -> Self {
        ChannelInv {
            commitment_id: s_inv.commitments_ids.commitment_id,
            request_map_id: s_inv.request_map_ids.request_auth_id,
            server_tokens_id: s_inv.server_tokens_id,
            server_locs: s_inv.server_locs,
        }
    }
}

pub open spec fn chan_request_inv<const N: usize>(
    k: ChannelInv,
    client_id: u64,
    server_id: u64,
    r: Request<N>,
) -> bool {
    &&& r.request_key() == (client_id, r.spec_tag())
    &&& r.request_id() == k.request_map_id
    &&& r.req_type() is Get ==> {
        let get_req = r.get();
        &&& k.server_locs == get_req.servers().locs()
    }
    &&& r.req_type() is GetTimestamp ==> {
        let get_ts_req = r.get_timestamp();
        &&& k.server_locs == get_ts_req.servers().locs()
    }
    &&& r.req_type() is Write ==> {
        let write_req = r.write();
        &&& k.server_locs == write_req.servers().locs()
        &&& k.commitment_id == write_req.commitment_id()
    }
}

pub open spec fn chan_response_inv<const N: usize>(
    k: ChannelInv,
    client_id: u64,
    server_id: u64,
    r: Response<N>,
) -> bool {
    &&& r.request_id() == k.request_map_id
    &&& r.server_id() == server_id
    &&& r.request_key().0 == client_id
    &&& r.req_type() is Get ==> {
        let get_resp = r.get();
        &&& get_resp.spec_commitment().id() == k.commitment_id
        &&& get_resp.server_token_id() == k.server_tokens_id
        &&& k.server_locs.contains_key(get_resp.server_id())
        &&& k.server_locs[get_resp.server_id()] == get_resp.loc()
    }
    &&& r.req_type() is GetTimestamp ==> {
        let get_ts_resp = r.get_timestamp();
        &&& get_ts_resp.server_token_id() == k.server_tokens_id
        &&& k.server_locs.contains_key(get_ts_resp.server_id())
        &&& k.server_locs[get_ts_resp.server_id()] == get_ts_resp.loc()
    }
    &&& r.req_type() is Write ==> {
        let write_resp = r.write();
        &&& write_resp.server_token_id() == k.server_tokens_id
        &&& k.server_locs.contains_key(write_resp.server_id())
        &&& k.server_locs[write_resp.server_id()] == write_resp.loc()
    }
}

// Invariant on server
impl<const N: usize> ChannelInvariant<ChannelInv, (u64, u64), Request<N>, Response<N>> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Request<N>) -> bool {
        chan_request_inv(k, id.1, id.0, r)
    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Response<N>) -> bool {
        chan_response_inv(k, id.1, id.0, s)
    }
}

// Invariant on client
impl<const N: usize> ChannelInvariant<ChannelInv, (u64, u64), Response<N>, Request<N>> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Response<N>) -> bool {
        chan_response_inv(k, id.0, id.1, r)
    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Request<N>) -> bool {
        chan_request_inv(k, id.0, id.1, s)
    }
}

} // verus!
