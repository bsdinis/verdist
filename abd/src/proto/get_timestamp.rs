use crate::invariants::quorum::ServerUniverse;
use crate::invariants::ServerToken;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

use vstd::prelude::*;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::Loc;

verus! {

pub struct GetTimestampRequest {
    #[allow(unused)]
    servers: Tracked<ServerUniverse>,
}

pub struct GetTimestampResponse {
    timestamp: Timestamp,
    #[allow(unused)]
    lb: Tracked<MonotonicTimestampResource>,
    #[allow(unused)]
    server_token: Tracked<ServerToken>,
}

#[allow(unused)]
impl GetTimestampRequest {
    pub fn new(servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.servers() == servers@,
    {
        GetTimestampRequest { servers }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.servers@.inv()
        &&& self.servers@.is_lb()
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
        }

        Tracked(new_lb)
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
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
        GetTimestampRequest { servers: Tracked(new_servers) }
    }

    /// Create a GetTimestampRequest (to be used for deserialization)
    fn axiom_forge() -> Self {
        proof { assume(false) }
        GetTimestampRequest { servers: Tracked(proof_from_false()) }
    }
}

#[allow(unused)]
impl GetTimestampResponse {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lb@@ is LowerBound
        &&& self.lb@.loc() == self.server_token@.value()
        &&& self.lb@@.timestamp() == self.timestamp
    }

    pub closed spec fn lb(self) -> MonotonicTimestampResource {
        self.lb@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.timestamp
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
        timestamp: Timestamp,
        lb: Tracked<MonotonicTimestampResource>,
        server_token: Tracked<ServerToken>,
    ) -> (r: Self)
        requires
            lb@@ is LowerBound,
            lb@@.timestamp() == timestamp,
            lb@.loc() == server_token@.value(),
        ensures
            r.lb() == lb@,
            r.spec_timestamp() == timestamp,
            r.spec_server_token() == server_token@,
            r.server_id() == server_token@.key(),
            r.server_token_id() == server_token@.id(),
            r.loc() == server_token@.value(),
    {
        GetTimestampResponse { timestamp, lb, server_token }
    }

    pub fn timestamp(&self) -> (ts: Timestamp)
        ensures
            ts == self.spec_timestamp(),
        no_unwind
    {
        self.timestamp
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

    pub fn lemma_get_timestamp_response(&self)
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
        &&& self.timestamp == other.timestamp
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
            a.spec_timestamp() == b.spec_timestamp(),
            a.spec_server_token().id() == b.spec_server_token().id(),
            a.spec_server_token()@ == b.spec_server_token()@,
            a.server_token_id() == b.server_token_id(),
            a.server_id() == b.server_id(),
    {
    }

    /// Create a GetTimestampResponse (to be used for deserialization)
    fn axiom_forge(timestamp: Timestamp) -> Self {
        proof {
            assume(false);
        }

        GetTimestampResponse {
            timestamp,
            lb: Tracked(proof_from_false()),
            server_token: Tracked(proof_from_false()),
        }
    }
}

impl Clone for GetTimestampRequest {
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
        GetTimestampRequest { servers: Tracked(new_servers) }
    }
}

impl Clone for GetTimestampResponse {
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
        GetTimestampResponse::new(self.timestamp.clone(), Tracked(new_lb), Tracked(server_token))
    }
}

} // verus!
impl std::fmt::Debug for GetTimestampRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetTimestampRequest").finish()
    }
}

impl std::fmt::Debug for GetTimestampResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetTimestampResponse")
            .field("timestamp", &self.timestamp)
            .finish()
    }
}

mod serde_impls {
    use super::GetTimestampRequest;
    use super::GetTimestampResponse;
    use serde::ser::SerializeStruct;

    impl serde::Serialize for GetTimestampRequest {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            let state = serializer.serialize_struct("GetTimestampRequest", 0)?;
            state.end()
        }
    }

    impl<'de> serde::Deserialize<'de> for GetTimestampRequest {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            struct StructVisitor;

            impl<'de> serde::de::Visitor<'de> for StructVisitor {
                type Value = GetTimestampRequest;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("struct GetTimestampRequest")
                }

                fn visit_seq<V>(self, _seq: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::SeqAccess<'de>,
                {
                    Ok(GetTimestampRequest::axiom_forge())
                }

                fn visit_map<V>(self, _map: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::MapAccess<'de>,
                {
                    Ok(GetTimestampRequest::axiom_forge())
                }
            }

            deserializer.deserialize_struct("GetTimestampRequest", &[], StructVisitor)
        }
    }

    impl serde::Serialize for GetTimestampResponse {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            let mut state = serializer.serialize_struct("GetTimestampResponse", 1)?;
            state.serialize_field("timestamp", &self.timestamp)?;
            state.end()
        }
    }

    impl<'de> serde::Deserialize<'de> for GetTimestampResponse {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            const FIELDS: &'static [&'static str] = &["timestamp"];

            enum Field {
                Timestamp,
            }

            struct FieldVisitor;

            impl<'de> serde::de::Visitor<'de> for FieldVisitor {
                type Value = Field;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("`timestamp`")
                }

                fn visit_str<E>(self, value: &str) -> Result<Field, E>
                where
                    E: serde::de::Error,
                {
                    match value {
                        "timestamp" => Ok(Field::Timestamp),
                        _ => Err(serde::de::Error::unknown_field(value, FIELDS)),
                    }
                }
            }

            impl<'de> serde::Deserialize<'de> for Field {
                fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
                where
                    D: serde::Deserializer<'de>,
                {
                    deserializer.deserialize_identifier(FieldVisitor)
                }
            }

            struct StructVisitor;

            impl<'de> serde::de::Visitor<'de> for StructVisitor {
                type Value = GetTimestampResponse;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("struct GetTimestampResponse")
                }

                fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::SeqAccess<'de>,
                {
                    let timestamp = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;
                    Ok(GetTimestampResponse::axiom_forge(timestamp))
                }

                fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::MapAccess<'de>,
                {
                    let mut timestamp = None;
                    loop {
                        if let Some(key) = map.next_key()? {
                            match key {
                                Field::Timestamp => {
                                    if timestamp.is_some() {
                                        return Err(serde::de::Error::duplicate_field("timestamp"));
                                    }
                                    timestamp = Some(map.next_value()?);
                                }
                            }
                        } else {
                            break;
                        }
                    }
                    let timestamp =
                        timestamp.ok_or_else(|| serde::de::Error::missing_field("timestamp"))?;
                    Ok(GetTimestampResponse::axiom_forge(timestamp))
                }
            }
            deserializer.deserialize_struct("GetTimestampResponse", FIELDS, StructVisitor)
        }
    }
}
