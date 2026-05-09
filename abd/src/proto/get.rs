use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::ServerToken;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

use vstd::prelude::*;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::Loc;

verus! {

pub struct GetRequest {
    #[allow(unused)]
    servers: Tracked<ServerUniverse>,
}

#[allow(unused)]
pub struct GetResponse {
    value: Option<u64>,
    timestamp: Timestamp,
    #[allow(unused)]
    lb: Tracked<MonotonicTimestampResource>,
    #[allow(unused)]
    commitment: Tracked<WriteCommitment>,
    #[allow(unused)]
    server_token: Tracked<ServerToken>,
}

#[allow(unused)]
impl GetRequest {
    pub fn new(servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.servers() == servers@,
    {
        GetRequest { servers }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.servers@.inv()
        &&& self.servers@.is_lb()
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub fn server_lower_bound(&mut self, server_id: Ghost<u64>) -> (r: Tracked<
        MonotonicTimestampResource,
    >)
        requires
            old(self).servers().contains_key(server_id@),
        ensures
            final(self).servers().locs() == old(self).servers().locs(),
            final(self).servers().spec_eq(old(self).servers()),
            r@.loc() == final(self).servers()[server_id@]@.loc(),
            r@@.timestamp() == final(self).servers()[server_id@]@@.timestamp(),
            r@@ is LowerBound,
    {
        let tracked new_lb;
        proof {
            use_type_invariant(&*self);

            let ghost old_servers = self.servers@;

            self.servers@.lemma_locs();  // TRIGGER
            old_servers.lemma_locs();  // TRIGGER

            let tracked lb = self.servers.borrow_mut().tracked_remove_lb(server_id@);
            let ghost unchanged_servers = self.servers@;

            new_lb = lb.extract_lower_bound();
            self.servers.borrow_mut().tracked_insert_lb(server_id@, lb);

            assert forall|id| #[trigger] self.servers@.contains_key(id) implies {
                &&& self.servers@[id]@.loc() == old_servers[id]@.loc()
                &&& self.servers@[id]@@.timestamp() == old_servers[id]@@.timestamp()
            } by {
                if id != server_id@ {
                    assert(unchanged_servers.contains_key(id));  // TRIGGER
                }
            }

            assert forall|id| #[trigger] old_servers.contains_key(id) implies {
                &&& self.servers@[id]@.loc() == old_servers[id]@.loc()
                &&& self.servers@[id]@@.timestamp() == old_servers[id]@@.timestamp()
            } by {
                if id != server_id@ {
                    assert(unchanged_servers.contains_key(id));  // TRIGGER
                }
            }

            assert(self.servers@.locs() == old_servers.locs());
        }

        Tracked(new_lb)
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        self.servers@.eq(other.servers@)
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        assume(a.servers@.inv());  // TODO(verus): type invariants on spec items
        ServerUniverse::lemma_eq_refl(a.servers@)
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
        assume(a.servers@.inv());  // TODO(verus): type invariants on spec items
        assume(b.servers@.inv());  // TODO(verus): type invariants on spec items
        assume(c.servers@.inv());  // TODO(verus): type invariants on spec items
        ServerUniverse::lemma_eq_trans(a.servers@, b.servers@, c.servers@)
    }

    pub broadcast proof fn lemma_spec_eq(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            a.servers().eq(b.servers()),
    {
    }

    pub proof fn duplicate(tracked &self) -> (tracked r: Self)
        ensures
            self.spec_eq(r),
    {
        let tracked new_servers;
        use_type_invariant(self);
        new_servers = self.servers.borrow().extract_lbs();
        ServerUniverse::lemma_eq_timestamp_lb_is_eq(new_servers, self.servers@);
        GetRequest { servers: Tracked(new_servers) }
    }
}

#[allow(unused)]
impl GetResponse {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lb@@ is LowerBound
        &&& self.lb@.loc() == self.server_token@.value()
        &&& self.lb@@.timestamp() == self.timestamp
        &&& self.commitment@.key() == self.timestamp
        &&& self.commitment@.value() == self.value
    }

    pub closed spec fn lb(self) -> MonotonicTimestampResource {
        self.lb@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn spec_value(self) -> Option<u64> {
        self.value
    }

    pub closed spec fn spec_commitment(self) -> WriteCommitment {
        self.commitment@
    }

    pub closed spec fn spec_server_token(self) -> ServerToken {
        self.server_token@
    }

    pub closed spec fn server_token_id(self) -> Loc {
        self.server_token@.id()
    }

    pub closed spec fn server_id(self) -> u64 {
        self.server_token@.key()
    }

    pub open spec fn loc(self) -> Loc {
        self.lb().loc()
    }

    pub fn new(
        value: Option<u64>,
        timestamp: Timestamp,
        lb: Tracked<MonotonicTimestampResource>,
        commitment: Tracked<WriteCommitment>,
        server_token: Tracked<ServerToken>,
    ) -> (r: Self)
        requires
            lb@@ is LowerBound,
            lb@.loc() == server_token@.value(),
            lb@@.timestamp() == timestamp,
            commitment@.key() == timestamp,
            commitment@.value() == value,
        ensures
            r.lb().loc() == lb@.loc(),
            r.lb()@.timestamp() == lb@@.timestamp(),
            r.spec_timestamp() == timestamp,
            r.spec_value() == value,
            r.spec_commitment() == commitment@,
            r.spec_server_token() == server_token@,
            r.server_id() == server_token@.key(),
            r.server_token_id() == server_token@.id(),
            r.loc() == server_token@.value(),
    {
        GetResponse { value, timestamp, lb, commitment, server_token }
    }

    pub fn timestamp(&self) -> (ts: Timestamp)
        ensures
            ts == self.spec_timestamp(),
        no_unwind
    {
        self.timestamp
    }

    pub fn value(&self) -> (value: &Option<u64>)
        ensures
            *value == self.spec_value(),
        no_unwind
    {
        &self.value
    }

    pub fn into_inner(self) -> (r: (Option<u64>, Timestamp))
        ensures
            r.0 == self.spec_value(),
            r.1 == self.spec_timestamp(),
    {
        (self.value, self.timestamp)
    }

    pub fn duplicate_lb(&self) -> (r: Tracked<MonotonicTimestampResource>)
        ensures
            r@.loc() == self.lb().loc(),
            r@@.timestamp() == self.lb()@.timestamp(),
            r@@ is LowerBound,
        no_unwind
    {
        let tracked lb;
        proof {
            use_type_invariant(self);
            lb = self.lb.borrow().extract_lower_bound();
        }
        Tracked(lb)
    }

    pub fn commitment(&self) -> (r: Tracked<WriteCommitment>)
        ensures
            r@.id() == self.spec_commitment().id(),
            r@.key() == self.spec_timestamp(),
            r@.value() == self.spec_value(),
        no_unwind
    {
        let tracked commitment;
        proof {
            use_type_invariant(self);
            commitment = self.commitment.borrow().duplicate();
        }
        Tracked(commitment)
    }

    pub fn lemma_get_response(&self)
        ensures
            self.lb()@ is LowerBound,
            self.spec_timestamp() == self.lb()@.timestamp(),
        no_unwind
    {
        proof {
            use_type_invariant(self);
        }
    }

    pub fn lemma_token_agree(&self, server_tokens: &mut Tracked<GhostPersistentSubmap<u64, Loc>>)
        requires
            self.server_token_id() == old(server_tokens)@.id(),
        ensures
            final(server_tokens)@.id() == old(server_tokens)@.id(),
            final(server_tokens)@@ == old(server_tokens)@@,
            final(server_tokens)@@.contains_key(self.server_id())
                ==> final(server_tokens)@@[self.server_id()] == self.loc(),
        no_unwind
    {
        proof {
            use_type_invariant(self);
            server_tokens.borrow_mut().intersection_agrees_points_to(self.server_token.borrow());
        }
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.value == other.value
        &&& self.timestamp == other.timestamp
        &&& self.lb@.loc() == other.lb@.loc()
        &&& self.lb@@.timestamp() == other.lb@@.timestamp()
        &&& self.commitment@.id() == other.commitment@.id()
        &&& self.commitment@@ == other.commitment@@
        &&& self.server_token@.id() == other.server_token@.id()
        &&& self.server_token@@ == other.server_token@@
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
    }

    pub broadcast proof fn lemma_spec_eq(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            a.lb().loc() == b.lb().loc(),
            a.lb()@.timestamp() == b.lb()@.timestamp(),
            a.spec_timestamp() == b.spec_timestamp(),
            a.spec_value() == b.spec_value(),
            a.spec_commitment().id() == b.spec_commitment().id(),
            a.spec_commitment()@ == b.spec_commitment()@,
            a.spec_server_token().id() == b.spec_server_token().id(),
            a.spec_server_token()@ == b.spec_server_token()@,
            a.server_token_id() == b.server_token_id(),
            a.server_id() == b.server_id(),
    {
    }
}

impl Clone for GetRequest {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        let tracked new_servers;
        proof {
            use_type_invariant(self);
            new_servers = self.servers.borrow().extract_lbs();
            ServerUniverse::lemma_eq_timestamp_lb_is_eq(new_servers, self.servers@);
        }
        GetRequest { servers: Tracked(new_servers) }
    }
}

impl Clone for GetResponse {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
    {
        let tracked lb;
        let tracked commitment;
        let tracked server_token;
        proof {
            use_type_invariant(self);
            lb = self.lb.borrow().extract_lower_bound();
            commitment = self.commitment.borrow().duplicate();
            server_token = self.server_token.borrow().duplicate();
        }
        GetResponse::new(
            self.value.clone(),
            self.timestamp.clone(),
            Tracked(lb),
            Tracked(commitment),
            Tracked(server_token),
        )
    }
}

} // verus!
impl std::fmt::Debug for GetRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetRequest").finish()
    }
}

impl std::fmt::Debug for GetResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetResponse")
            .field("value", &self.value)
            .field("timestamp", &self.timestamp)
            .finish()
    }
}
