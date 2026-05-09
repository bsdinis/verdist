use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::ServerToken;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

use vstd::prelude::*;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::Loc;

verus! {

pub struct WriteRequest {
    value: Option<u64>,
    timestamp: Timestamp,
    #[allow(unused)]
    commitment: Tracked<WriteCommitment>,
    #[allow(unused)]
    servers: Tracked<ServerUniverse>,
}

#[allow(unused)]
pub struct WriteResponse {
    #[allow(unused)]
    lb: Tracked<MonotonicTimestampResource>,
    #[allow(unused)]
    server_token: Tracked<ServerToken>,
}

#[allow(unused)]
impl WriteRequest {
    pub fn new(
        value: Option<u64>,
        timestamp: Timestamp,
        commitment: Tracked<WriteCommitment>,
        servers: Tracked<ServerUniverse>,
    ) -> (r: Self)
        requires
            commitment@.key() == timestamp,
            commitment@.value() == value,
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.spec_timestamp() == timestamp,
            r.spec_value() == value,
            r.commitment_id() == commitment@.id(),
            r.servers() == servers@,
    {
        WriteRequest { value, timestamp, commitment, servers }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.commitment@.key() == self.timestamp
        &&& self.commitment@.value() == self.value
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

            let tracked lb = self.servers.borrow_mut().tracked_remove_lb(server_id@);
            let ghost unchanged_servers = self.servers@;

            new_lb = lb.extract_lower_bound();
            self.servers.borrow_mut().tracked_insert_lb(server_id@, lb);

            assert forall|id| #[trigger] self.servers@.contains_key(id) implies {
                &&& self.servers@[id]@.loc() == old_servers[id]@.loc()
                &&& self.servers@[id]@@.timestamp() == old_servers[id]@@.timestamp()
            } by {
                if id != server_id@ {
                    assert(unchanged_servers.contains_key(id));  // XXX: trigger
                }
            }

            assert forall|id| #[trigger] old_servers.contains_key(id) implies {
                &&& self.servers@[id]@.loc() == old_servers[id]@.loc()
                &&& self.servers@[id]@@.timestamp() == old_servers[id]@@.timestamp()
            } by {
                if id != server_id@ {
                    assert(unchanged_servers.contains_key(id));  // XXX: trigger
                }
            }

            assert(self.servers@.locs() == old_servers.locs());  // XXX: trigger
        }

        Tracked(new_lb)
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.commitment@.id()
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn spec_value(self) -> Option<u64> {
        self.value
    }

    pub fn destruct(self, server_id: u64) -> (r: (
        Option<u64>,
        Timestamp,
        Tracked<WriteCommitment>,
        Tracked<MonotonicTimestampResource>,
    ))
        requires
            self.servers().contains_key(server_id),
        ensures
            r.0 == self.spec_value(),
            r.1 == self.spec_timestamp(),
            r.2@.key() == self.spec_timestamp(),
            r.2@.value() == self.spec_value(),
            r.2@.id() == self.commitment_id(),
            r.3@.loc() == self.servers()[server_id]@.loc(),
            r.3@@ == self.servers()[server_id]@@,
            r.3@@ is LowerBound,
    {
        let mut self_mut = self;
        let tracked lb;
        proof {
            use_type_invariant(&self_mut);
            lb = self_mut.servers.borrow_mut().tracked_remove_lb(server_id);
        }

        (self_mut.value, self_mut.timestamp, self_mut.commitment, Tracked(lb))
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.value == other.value
        &&& self.timestamp == other.timestamp
        &&& self.commitment@.id() == other.commitment@.id()
        &&& self.commitment@@ == other.commitment@@
        &&& self.servers@.eq(other.servers@)
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
            a.spec_value() == b.spec_value(),
            a.spec_timestamp() == b.spec_timestamp(),
            a.commitment_id() == b.commitment_id(),
    {
    }

    pub proof fn duplicate(tracked &self) -> (tracked r: Self)
        ensures
            self.spec_eq(r),
    {
        let tracked new_commitment;
        let tracked new_servers;
        use_type_invariant(self);
        new_commitment = self.commitment.borrow().duplicate();
        new_servers = self.servers.borrow().extract_lbs();
        ServerUniverse::lemma_eq_timestamp_lb_is_eq(new_servers, self.servers@);
        WriteRequest {
            value: self.value,
            timestamp: self.timestamp,
            commitment: Tracked(new_commitment),
            servers: Tracked(new_servers),
        }
    }
}

#[allow(unused)]
impl WriteResponse {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lb@@ is LowerBound
        &&& self.lb@.loc() == self.server_token@.value()
    }

    pub closed spec fn lb(self) -> MonotonicTimestampResource {
        self.lb@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.lb@@.timestamp()
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

    pub fn new(lb: Tracked<MonotonicTimestampResource>, server_token: Tracked<ServerToken>) -> (r:
        Self)
        requires
            lb@@ is LowerBound,
            lb@.loc() == server_token@.value(),
        ensures
            r.lb() == lb@,
            r.lb().loc() == lb@.loc(),
            r.spec_timestamp() == lb@@.timestamp(),
            r.spec_server_token() == server_token@,
            r.server_id() == server_token@.key(),
            r.server_token_id() == server_token@.id(),
    {
        WriteResponse { lb, server_token }
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.lb@.loc() == other.lb@.loc()
        &&& self.lb@@.timestamp() == other.lb@@.timestamp()
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
            a.spec_server_token().id() == b.spec_server_token().id(),
            a.spec_server_token()@ == b.spec_server_token()@,
            a.server_token_id() == b.server_token_id(),
            a.spec_timestamp() == b.spec_timestamp(),
            a.server_id() == b.server_id(),
    {
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

    pub fn lemma_write_response(&self)
        ensures
            self.lb()@ is LowerBound,
            self.spec_timestamp() == self.lb()@.timestamp(),
        no_unwind
    {
        proof {
            use_type_invariant(self);
        }
    }
}

impl Clone for WriteRequest {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        let tracked new_commitment;
        let tracked new_servers;
        proof {
            use_type_invariant(self);
            new_commitment = self.commitment.borrow().duplicate();
            new_servers = self.servers.borrow().extract_lbs();
            ServerUniverse::lemma_eq_timestamp_lb_is_eq(new_servers, self.servers@);
        }
        WriteRequest {
            value: self.value.clone(),
            timestamp: self.timestamp.clone(),
            commitment: Tracked(new_commitment),
            servers: Tracked(new_servers),
        }
    }
}

impl Clone for WriteResponse {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        let tracked new_lb;
        let tracked server_token;
        proof {
            use_type_invariant(self);
            new_lb = self.lb.borrow().extract_lower_bound();
            server_token = self.server_token.borrow().duplicate();
        }
        WriteResponse::new(Tracked(new_lb), Tracked(server_token))
    }
}

} // verus!
impl std::fmt::Debug for WriteRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WriteRequest")
            .field("value", &self.value)
            .field("timestamp", &self.timestamp)
            .finish()
    }
}
impl std::fmt::Debug for WriteResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WriteResponse").finish()
    }
}
