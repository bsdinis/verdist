use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::requests::RequestProof;
use crate::proto::get::GetRequest;
use crate::proto::get_timestamp::GetTimestampRequest;
use crate::proto::write::WriteRequest;
#[cfg(verus_only)]
use crate::proto::ReqType;
use crate::timestamp::Timestamp;

use verdist::rpc::proto::TaggedMessage;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

pub struct Request {
    request_id: u64,
    inner: RequestInner,
    request: Tracked<RequestProof>,
}

pub enum RequestInner {
    Get(GetRequest),
    GetTimestamp(GetTimestampRequest),
    Write(WriteRequest),
}

impl TaggedMessage for Request {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl RequestInner {
    pub open spec fn req_type(self) -> ReqType {
        match self {
            RequestInner::Get(_) => ReqType::Get,
            RequestInner::GetTimestamp(_) => ReqType::GetTimestamp,
            RequestInner::Write(_) => ReqType::Write,
        }
    }

    pub open spec fn spec_eq(self, other: Self) -> bool {
        match (self, other) {
            (RequestInner::Get(a), RequestInner::Get(b)) => a.spec_eq(b),
            (RequestInner::GetTimestamp(a), RequestInner::GetTimestamp(b)) => a.spec_eq(b),
            (RequestInner::Write(a), RequestInner::Write(b)) => a.spec_eq(b),
            (_, _) => false,
        }
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        match a {
            RequestInner::Get(a) => { GetRequest::spec_eq_refl(a) },
            RequestInner::GetTimestamp(a) => { GetTimestampRequest::spec_eq_refl(a) },
            RequestInner::Write(a) => WriteRequest::spec_eq_refl(a),
        }
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        match (a, b) {
            (RequestInner::Get(a), RequestInner::Get(b)) => GetRequest::spec_eq_symm(a, b),
            (
                RequestInner::GetTimestamp(a),
                RequestInner::GetTimestamp(b),
            ) => GetTimestampRequest::spec_eq_symm(a, b),
            (RequestInner::Write(a), RequestInner::Write(b)) => WriteRequest::spec_eq_symm(a, b),
            (_, _) => {},
        }
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
        match (a, b, c) {
            (
                RequestInner::Get(a),
                RequestInner::Get(b),
                RequestInner::Get(c),
            ) => GetRequest::spec_eq_trans(a, b, c),
            (
                RequestInner::GetTimestamp(a),
                RequestInner::GetTimestamp(b),
                RequestInner::GetTimestamp(c),
            ) => GetTimestampRequest::spec_eq_trans(a, b, c),
            (
                RequestInner::Write(a),
                RequestInner::Write(b),
                RequestInner::Write(c),
            ) => WriteRequest::spec_eq_trans(a, b, c),
            (_, _, _) => {},
        }
    }

    pub fn new_get(servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.req_type() is Get,
            ({
                let req = r->Get_0;
                req.servers() == servers@
            }),
    {
        RequestInner::Get(GetRequest::new(servers))
    }

    pub fn new_get_timestamp(servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.req_type() is GetTimestamp,
            ({
                let req = r->GetTimestamp_0;
                req.servers() == servers@
            }),
    {
        RequestInner::GetTimestamp(GetTimestampRequest::new(servers))
    }

    pub fn new_write(
        value: Option<u64>,
        timestamp: Timestamp,
        commitment: Tracked<WriteCommitment>,
        servers: Tracked<ServerUniverse>,
    ) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
            commitment@.key() == timestamp,
            commitment@.value() == value,
        ensures
            r.req_type() is Write,
            ({
                let req = r->Write_0;
                &&& req.servers() == servers@
                &&& req.spec_timestamp() == timestamp
                &&& req.spec_value() == value
                &&& req.commitment_id() == commitment@.id()
            }),
    {
        RequestInner::Write(WriteRequest::new(value, timestamp, commitment, servers))
    }

    pub proof fn duplicate(tracked &self) -> (tracked r: Self)
        ensures
            self.spec_eq(r),
    {
        match self {
            RequestInner::Get(get) => { RequestInner::Get(get.duplicate()) },
            RequestInner::GetTimestamp(get_ts) => { RequestInner::GetTimestamp(get_ts.duplicate())
            },
            RequestInner::Write(write) => { RequestInner::Write(write.duplicate()) },
        }
    }
}

impl Request {
    pub closed spec fn request_id(self) -> Loc {
        self.request.id()
    }

    pub closed spec fn request_key(self) -> (u64, u64) {
        self.request@.key()
    }

    pub closed spec fn request(self) -> RequestInner {
        self.request@@
    }

    pub closed spec fn req_type(self) -> ReqType {
        self.inner.req_type()
    }

    pub closed spec fn get(self) -> GetRequest
        recommends
            self.req_type() is Get,
    {
        self.inner->Get_0
    }

    pub closed spec fn get_timestamp(self) -> GetTimestampRequest
        recommends
            self.req_type() is GetTimestamp,
    {
        self.inner->GetTimestamp_0
    }

    pub closed spec fn write(self) -> WriteRequest
        recommends
            self.req_type() is Write,
    {
        self.inner->Write_0
    }

    pub closed spec fn client_id(self) -> u64 {
        self.request@.key().0
    }

    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.request@.key().1 == self.request_id
        &&& self.request@@.spec_eq(self.inner)
    }

    pub fn new(
        #[allow(unused_variables)]
        client_id: u64,
        request_id: u64,
        request_inner: RequestInner,
        request_proof: Tracked<RequestProof>,
    ) -> (r: Self)
        requires
            request_proof@.key() == (client_id, request_id),
            request_proof@@.spec_eq(request_inner),
        ensures
            r.req_type() == request_inner.req_type(),
            r.request_key() == (r.client_id(), r.spec_tag()),
            r.request_id() == request_proof@.id(),
            r.client_id() == client_id,
            r.spec_tag() == request_id,
            r.req_type() is Get ==> r.get() == request_inner->Get_0,
            r.req_type() is GetTimestamp ==> r.get_timestamp() == request_inner->GetTimestamp_0,
            r.req_type() is Write ==> r.write() == request_inner->Write_0,
    {
        Request { request_id, inner: request_inner, request: request_proof }
    }

    pub fn destruct(self) -> (r: (u64, RequestInner, Tracked<RequestProof>))
        ensures
            r.0 == self.spec_tag(),
            r.2@@.spec_eq(r.1),
            r.2@.id() == self.request_id(),
            r.2@@ == self.request(),
            r.2@.req_type() == self.req_type(),
            r.2@.key() == self.request_key(),
            r.2@.key() == (self.client_id(), self.spec_tag()),
            r.2@@.spec_eq(r.1),
            r.1 is Get <==> self.req_type() is Get,
            r.1 is GetTimestamp <==> self.req_type() is GetTimestamp,
            r.1 is Write <==> self.req_type() is Write,
            self.req_type() is Get ==> r.1->Get_0 == self.get(),
            self.req_type() is GetTimestamp ==> r.1->GetTimestamp_0 == self.get_timestamp(),
            self.req_type() is Write ==> r.1->Write_0 == self.write(),
        no_unwind
    {
        proof {
            use_type_invariant(&self);
        }
        (self.request_id, self.inner, self.request)
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.request_id == other.request_id
        &&& self.inner.spec_eq(other.inner)
        &&& self.request@.id() == other.request@.id()
        &&& self.request@@ == other.request@@
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        RequestInner::spec_eq_refl(a.inner);
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        RequestInner::spec_eq_symm(a.inner, b.inner);
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
        RequestInner::spec_eq_trans(a.inner, b.inner, c.inner);
    }

    /// Create a request from the executable parts only, for deserialization purposes
    fn axiom_forge(request_id: u64, inner: RequestInner) -> Self {
        proof {
            assume(false);
        }
        let request = Tracked(proof_from_false());
        Request { request_id, inner, request }
    }
}

impl Clone for Request {
    #[allow(unused_variables)]
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        broadcast use RequestInner::spec_eq_trans;
        broadcast use RequestInner::spec_eq_symm;

        proof {
            use_type_invariant(self);
        }
        let inner = self.inner.clone();
        assert(inner.spec_eq(self.inner));
        assert(self.request@@.spec_eq(self.inner));
        assert(self.request@@.spec_eq(inner));
        let request = Tracked(self.request.borrow().duplicate());
        Request { request_id: self.request_id, inner, request }
    }
}

impl Clone for RequestInner {
    #[allow(unused_variables)]
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        match self {
            RequestInner::Get(get) => { RequestInner::Get(get.clone()) },
            RequestInner::GetTimestamp(get_ts) => { RequestInner::GetTimestamp(get_ts.clone()) },
            RequestInner::Write(write) => { RequestInner::Write(write.clone()) },
        }
    }
}

} // verus!
impl std::fmt::Debug for RequestInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RequestInner::Get(get) => f.debug_tuple("Get").field(&get).finish(),
            RequestInner::GetTimestamp(get_ts) => {
                f.debug_tuple("GetTimestamp").field(&get_ts).finish()
            }
            RequestInner::Write(write) => f.debug_tuple("Write").field(&write).finish(),
        }
    }
}

impl std::fmt::Debug for Request {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Request")
            .field("request_id", &self.request_id)
            .field("request", &self.inner)
            .finish()
    }
}

mod serde_impls {
    use serde::de::VariantAccess;
    use serde::ser::SerializeStruct;

    use super::Request;
    use super::RequestInner;

    impl serde::Serialize for Request {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            let mut state = serializer.serialize_struct("Request", 2)?;
            state.serialize_field("request_id", &self.request_id)?;
            state.serialize_field("inner", &self.inner)?;
            state.end()
        }
    }

    impl<'de> serde::Deserialize<'de> for Request {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            const FIELDS: &[&str] = &["request_id", "inner"];

            enum Field {
                RequestId,
                Inner,
            }

            struct FieldVisitor;

            impl<'de> serde::de::Visitor<'de> for FieldVisitor {
                type Value = Field;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("`request_id` or `inner`")
                }

                fn visit_str<E>(self, value: &str) -> Result<Field, E>
                where
                    E: serde::de::Error,
                {
                    match value {
                        "request_id" => Ok(Field::RequestId),
                        "inner" => Ok(Field::Inner),
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
                type Value = Request;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("struct Request")
                }

                fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::SeqAccess<'de>,
                {
                    let request_id = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;
                    let inner = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(1, &self))?;
                    Ok(Request::axiom_forge(request_id, inner))
                }

                fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::MapAccess<'de>,
                {
                    let mut request_id = None;
                    let mut inner = None;
                    while let Some(key) = map.next_key()? {
                        match key {
                            Field::RequestId => {
                                if request_id.is_some() {
                                    return Err(serde::de::Error::duplicate_field("request_id"));
                                }
                                request_id = Some(map.next_value()?);
                            }
                            Field::Inner => {
                                if inner.is_some() {
                                    return Err(serde::de::Error::duplicate_field("inner"));
                                }
                                inner = Some(map.next_value()?);
                            }
                        }
                    }
                    let request_id =
                        request_id.ok_or_else(|| serde::de::Error::missing_field("request_id"))?;
                    let inner = inner.ok_or_else(|| serde::de::Error::missing_field("inner"))?;
                    Ok(Request::axiom_forge(request_id, inner))
                }
            }
            deserializer.deserialize_struct("Request", FIELDS, StructVisitor)
        }
    }

    impl serde::Serialize for RequestInner {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            match self {
                RequestInner::Get(get) => {
                    serializer.serialize_newtype_variant("RequestInner", 0, "Get", get)
                }
                RequestInner::GetTimestamp(get_timestamp) => serializer.serialize_newtype_variant(
                    "RequestInner",
                    1,
                    "GetTimestamp",
                    get_timestamp,
                ),
                RequestInner::Write(write) => {
                    serializer.serialize_newtype_variant("RequestInner", 2, "Write", write)
                }
            }
        }
    }

    impl<'de> serde::Deserialize<'de> for RequestInner {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            const VARIANTS: &[&str] = &["Get", "GetTimestamp", "Write"];

            enum Variant {
                Get,
                GetTimestamp,
                Write,
            }
            impl<'de> serde::Deserialize<'de> for Variant {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: serde::de::Deserializer<'de>,
                {
                    struct FieldVisitor;

                    impl<'de> serde::de::Visitor<'de> for FieldVisitor {
                        type Value = Variant;

                        fn expecting(
                            &self,
                            formatter: &mut std::fmt::Formatter,
                        ) -> std::fmt::Result {
                            formatter.write_str("variant identifier")
                        }

                        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
                        where
                            E: serde::de::Error,
                        {
                            match value {
                                "Get" => Ok(Variant::Get),
                                "GetTimestamp" => Ok(Variant::GetTimestamp),
                                "Write" => Ok(Variant::Write),
                                _ => Err(serde::de::Error::unknown_variant(value, VARIANTS)),
                            }
                        }

                        fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
                        where
                            E: serde::de::Error,
                        {
                            self.visit_str(&value)
                        }
                    }

                    deserializer.deserialize_identifier(FieldVisitor)
                }
            }

            struct EnumVisitor;

            impl<'de> serde::de::Visitor<'de> for EnumVisitor {
                type Value = RequestInner;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("enum RequestInner")
                }

                fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
                where
                    A: serde::de::EnumAccess<'de>,
                {
                    let (variant, variant_access) = data.variant::<Variant>()?;
                    match variant {
                        Variant::Get => {
                            let get = variant_access.newtype_variant()?;
                            Ok(RequestInner::Get(get))
                        }
                        Variant::GetTimestamp => {
                            let get_timestamp = variant_access.newtype_variant()?;
                            Ok(RequestInner::GetTimestamp(get_timestamp))
                        }
                        Variant::Write => {
                            let write = variant_access.newtype_variant()?;
                            Ok(RequestInner::Write(write))
                        }
                    }
                }
            }
            deserializer.deserialize_enum("RequestInner", VARIANTS, EnumVisitor)
        }
    }
}
