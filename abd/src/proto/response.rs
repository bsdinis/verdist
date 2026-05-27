use crate::invariants::requests::RequestProof;
use crate::proto::get::GetResponse;
use crate::proto::get_timestamp::GetTimestampResponse;
#[cfg(verus_only)]
use crate::proto::request::RequestInner;
use crate::proto::write::WriteResponse;
#[cfg(verus_only)]
use crate::proto::ReqType;

use verdist::rpc::proto::TaggedMessage;

use vstd::pervasive::unreached;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

pub struct Response {
    request_id: u64,
    inner: ResponseInner,
    #[allow(unused)]
    request: Tracked<RequestProof>,
}

pub enum ResponseInner {
    Get(GetResponse),
    GetTimestamp(GetTimestampResponse),
    Write(WriteResponse),
}

impl TaggedMessage for Response {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Response {
    pub fn new(request_id: u64, inner: ResponseInner, request: Tracked<RequestProof>) -> (r: Self)
        requires
            request@.key().1 == request_id,
            request@.req_type() is Get <==> inner is Get,
            request@.req_type() is GetTimestamp <==> inner is GetTimestamp,
            request@.req_type() is Write <==> inner is Write,
            request@.req_type() is Get ==> {
                let get_req = request@.get();
                let get_resp = inner->Get_0;
                &&& get_req.servers().contains_key(get_resp.server_id())
                &&& get_req.servers()[get_resp.server_id()]@@.timestamp()
                    <= get_resp.spec_timestamp()
            },
            request@.req_type() is GetTimestamp ==> {
                let get_ts_req = request@.get_timestamp();
                let get_ts_resp = inner->GetTimestamp_0;
                &&& get_ts_req.servers().contains_key(get_ts_resp.server_id())
                &&& get_ts_req.servers()[get_ts_resp.server_id()]@@.timestamp()
                    <= get_ts_resp.spec_timestamp()
            },
            request@.req_type() is Write ==> {
                let write_req = request@.write();
                let write_resp = inner->Write_0;
                &&& write_req.servers().contains_key(write_resp.server_id())
                &&& write_req.servers()[write_resp.server_id()]@@.timestamp()
                    <= write_resp.spec_timestamp()
                &&& write_req.spec_timestamp() <= write_resp.spec_timestamp()
            },
        ensures
            r.spec_tag() == request_id,
            r.request_id() == request.id(),
            r.request_key() == request@.key(),
            r.request() == request@@,
            inner is Get ==> {
                &&& r.req_type() is Get
                &&& inner->Get_0 == r.get()
            },
            inner is GetTimestamp ==> {
                &&& r.req_type() is GetTimestamp
                &&& inner->GetTimestamp_0 == r.get_timestamp()
            },
            inner is Write ==> {
                &&& r.req_type() is Write
                &&& inner->Write_0 == r.write()
            },
    {
        Response { request_id, inner, request }
    }

    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.request_key().1 == self.spec_tag()
        &&& self.request().req_type() == self.req_type()
        &&& self.req_type() is Get ==> {
            let get_req = self.request()->Get_0;
            let get_resp = self.get();
            &&& get_req.servers().contains_key(get_resp.server_id())
            &&& get_req.servers()[get_resp.server_id()]@@.timestamp() <= get_resp.spec_timestamp()
        }
        &&& self.req_type() is GetTimestamp ==> {
            let get_ts_req = self.request()->GetTimestamp_0;
            let get_ts_resp = self.get_timestamp();
            &&& get_ts_req.servers().contains_key(get_ts_resp.server_id())
            &&& get_ts_req.servers()[get_ts_resp.server_id()]@@.timestamp()
                <= get_ts_resp.spec_timestamp()
        }
        &&& self.req_type() is Write ==> {
            let write_req = self.request()->Write_0;
            let write_resp = self.write();
            &&& write_req.servers().contains_key(write_resp.server_id())
            &&& write_req.servers()[write_resp.server_id()]@@.timestamp()
                <= write_resp.spec_timestamp()
            &&& write_req.spec_timestamp() <= write_resp.spec_timestamp()
        }
    }

    pub open spec fn server_id(self) -> u64 {
        match self.req_type() {
            ReqType::Get => self.get().server_id(),
            ReqType::GetTimestamp => self.get_timestamp().server_id(),
            ReqType::Write => self.write().server_id(),
        }
    }

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
        match self.inner {
            ResponseInner::Get(_) => ReqType::Get,
            ResponseInner::GetTimestamp(_) => ReqType::GetTimestamp,
            ResponseInner::Write(_) => ReqType::Write,
        }
    }

    pub closed spec fn get(self) -> GetResponse
        recommends
            self.req_type() is Get,
    {
        self.inner->Get_0
    }

    pub closed spec fn get_timestamp(self) -> GetTimestampResponse
        recommends
            self.req_type() is GetTimestamp,
    {
        self.inner->GetTimestamp_0
    }

    pub closed spec fn write(self) -> WriteResponse
        recommends
            self.req_type() is Write,
    {
        self.inner->Write_0
    }

    pub fn destruct_get(self) -> (r: GetResponse)
        requires
            self.req_type() is Get,
        ensures
            r == self.get(),
            ({
                let get_req = self.request()->Get_0;
                let get_resp = self.get();
                &&& get_req.servers().contains_key(get_resp.server_id())
                &&& get_req.servers()[get_resp.server_id()]@@.timestamp()
                    <= get_resp.spec_timestamp()
            }),
        no_unwind
    {
        proof {
            use_type_invariant(&self);
        }
        match self.inner {
            ResponseInner::Get(g) => g,
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    pub fn destruct_get_timestamp(self) -> (r: GetTimestampResponse)
        requires
            self.req_type() is GetTimestamp,
        ensures
            r == self.get_timestamp(),
            ({
                let get_ts_req = self.request()->GetTimestamp_0;
                let get_ts_resp = self.get_timestamp();
                &&& get_ts_req.servers().contains_key(get_ts_resp.server_id())
                &&& get_ts_req.servers()[get_ts_resp.server_id()]@@.timestamp()
                    <= get_ts_resp.spec_timestamp()
            }),
        no_unwind
    {
        proof {
            use_type_invariant(&self);
        }
        match self.inner {
            ResponseInner::GetTimestamp(g) => g,
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    pub fn destruct_write(self) -> (r: WriteResponse)
        requires
            self.req_type() is Write,
        ensures
            r == self.write(),
            ({
                let write_req = self.request()->Write_0;
                let write_resp = self.write();
                &&& write_req.servers().contains_key(write_resp.server_id())
                &&& write_req.spec_timestamp() <= write_resp.spec_timestamp()
            }),
        no_unwind
    {
        proof {
            use_type_invariant(&self);
        }
        match self.inner {
            ResponseInner::Write(g) => g,
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.request_id == other.request_id
        &&& self.inner.spec_eq(other.inner)
        &&& self.request@.id() == other.request@.id()
        &&& self.request@.key() == other.request@.key()
        &&& self.request@@ == other.request@@
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        ResponseInner::spec_eq_refl(a.inner);
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        ResponseInner::spec_eq_symm(a.inner, b.inner);
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
        ResponseInner::spec_eq_trans(a.inner, b.inner, c.inner);
    }

    pub broadcast proof fn lemma_spec_eq(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            a.spec_tag() == b.spec_tag(),
            a.request_id() == b.request_id(),
            a.request_key() == b.request_key(),
            a.request() == b.request(),
            a.req_type() == b.req_type(),
            a.req_type() is Get ==> GetResponse::spec_eq(a.get(), b.get()),
            a.req_type() is GetTimestamp ==> GetTimestampResponse::spec_eq(
                a.get_timestamp(),
                b.get_timestamp(),
            ),
            a.req_type() is Write ==> WriteResponse::spec_eq(a.write(), b.write()),
    {
    }

    pub fn agree_request(
        &self,
        #[allow(unused_variables)]
        request_proof: &mut Tracked<RequestProof>,
    )
        requires
            self.request_id() == old(request_proof)@.id(),
        ensures
            final(request_proof)@.id() == old(request_proof)@.id(),
            final(request_proof)@.key() == old(request_proof)@.key(),
            final(request_proof)@@ == old(request_proof)@@,
            self.request_key() == final(request_proof)@.key() ==> self.request()
                == final(request_proof)@@,
        no_unwind
    {
        proof { request_proof.borrow_mut().intersection_agrees(self.request.borrow()) }
    }

    pub fn agree_request_opt(
        &self,
        #[allow(unused_variables)]
        request_proof: &mut Tracked<Option<RequestProof>>,
    )
        requires
            old(request_proof)@ is Some,
            self.request_id() == old(request_proof)@->Some_0.id(),
        ensures
            final(request_proof)@ is Some,
            final(request_proof)@->Some_0.id() == old(request_proof)@->Some_0.id(),
            final(request_proof)@->Some_0.key() == old(request_proof)@->Some_0.key(),
            final(request_proof)@->Some_0@ == old(request_proof)@->Some_0@,
            self.request_key() == final(request_proof)@->Some_0.key() ==> self.request()
                == final(request_proof)@->Some_0@,
        no_unwind
    {
        proof {
            let tracked mut pf = request_proof.borrow_mut().tracked_take();
            pf.intersection_agrees(self.request.borrow());
            *request_proof.borrow_mut() = Some(pf);
        }
    }

    pub fn lemma_inv(&self)
        ensures
            self.request_key().1 == self.spec_tag(),
            self.request().req_type() == self.req_type(),
        no_unwind
    {
        proof {
            use_type_invariant(self);
        }
    }

    /// Create a response from the executable parts only, for deserialization purposes
    fn axiom_forge(request_id: u64, inner: ResponseInner) -> Self {
        proof {
            assume(false);
        }
        let request = Tracked(proof_from_false());
        Response { request_id, inner, request }
    }
}

impl ResponseInner {
    pub open spec fn spec_eq(self, other: Self) -> bool {
        match (self, other) {
            (ResponseInner::Get(a), ResponseInner::Get(b)) => a.spec_eq(b),
            (ResponseInner::GetTimestamp(a), ResponseInner::GetTimestamp(b)) => a.spec_eq(b),
            (ResponseInner::Write(a), ResponseInner::Write(b)) => a.spec_eq(b),
            (_, _) => false,
        }
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        match a {
            ResponseInner::Get(a) => GetResponse::spec_eq_refl(a),
            ResponseInner::GetTimestamp(a) => GetTimestampResponse::spec_eq_refl(a),
            ResponseInner::Write(a) => WriteResponse::spec_eq_refl(a),
        }
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        match (a, b) {
            (ResponseInner::Get(a), ResponseInner::Get(b)) => GetResponse::spec_eq_symm(a, b),
            (
                ResponseInner::GetTimestamp(a),
                ResponseInner::GetTimestamp(b),
            ) => GetTimestampResponse::spec_eq_symm(a, b),
            (ResponseInner::Write(a), ResponseInner::Write(b)) => WriteResponse::spec_eq_symm(a, b),
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
                ResponseInner::Get(a),
                ResponseInner::Get(b),
                ResponseInner::Get(c),
            ) => GetResponse::spec_eq_trans(a, b, c),
            (
                ResponseInner::GetTimestamp(a),
                ResponseInner::GetTimestamp(b),
                ResponseInner::GetTimestamp(c),
            ) => GetTimestampResponse::spec_eq_trans(a, b, c),
            (
                ResponseInner::Write(a),
                ResponseInner::Write(b),
                ResponseInner::Write(c),
            ) => WriteResponse::spec_eq_trans(a, b, c),
            (_, _, _) => {},
        }
    }
}

impl Clone for Response {
    #[allow(unused_variables)]
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
    {
        proof {
            use_type_invariant(self);
        }
        let inner = self.inner.clone();
        let request = Tracked(self.request.borrow().duplicate());
        proof {
            if inner is Get {
                GetResponse::lemma_spec_eq(self.inner->Get_0, inner->Get_0);
            }
            if inner is GetTimestamp {
                GetTimestampResponse::lemma_spec_eq(
                    self.inner->GetTimestamp_0,
                    inner->GetTimestamp_0,
                );
            }
            if inner is Write {
                WriteResponse::lemma_spec_eq(self.inner->Write_0, inner->Write_0);
            }
        }
        Response { request_id: self.request_id, inner, request }
    }
}

impl Clone for ResponseInner {
    #[allow(unused_variables)]
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
    {
        match self {
            ResponseInner::Get(get) => { ResponseInner::Get(get.clone()) },
            ResponseInner::GetTimestamp(get_ts) => { ResponseInner::GetTimestamp(get_ts.clone()) },
            ResponseInner::Write(write) => { ResponseInner::Write(write.clone()) },
        }
    }
}

} // verus!
impl std::fmt::Debug for ResponseInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResponseInner::Get(get) => f.debug_tuple("Get").field(&get).finish(),
            ResponseInner::GetTimestamp(get_ts) => {
                f.debug_tuple("GetTimestamp").field(&get_ts).finish()
            }
            ResponseInner::Write(write) => f.debug_tuple("Write").field(&write).finish(),
        }
    }
}

impl std::fmt::Debug for Response {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Response")
            .field("request_id", &self.request_id)
            .field("response", &self.inner)
            .finish()
    }
}

mod serde_impls {
    use serde::de::VariantAccess;
    use serde::ser::SerializeStruct;

    use super::Response;
    use super::ResponseInner;

    impl serde::Serialize for Response {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            let mut state = serializer.serialize_struct("Response", 2)?;
            state.serialize_field("request_id", &self.request_id)?;
            state.serialize_field("inner", &self.inner)?;
            state.end()
        }
    }

    impl<'de> serde::Deserialize<'de> for Response {
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
                type Value = Response;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("struct Response")
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
                    Ok(Response::axiom_forge(request_id, inner))
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
                    Ok(Response::axiom_forge(request_id, inner))
                }
            }
            deserializer.deserialize_struct("Response", FIELDS, StructVisitor)
        }
    }

    impl serde::Serialize for ResponseInner {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            match self {
                ResponseInner::Get(get) => {
                    serializer.serialize_newtype_variant("ResponseInner", 0, "Get", get)
                }
                ResponseInner::GetTimestamp(get_timestamp) => serializer.serialize_newtype_variant(
                    "ResponseInner",
                    1,
                    "GetTimestamp",
                    get_timestamp,
                ),
                ResponseInner::Write(write) => {
                    serializer.serialize_newtype_variant("ResponseInner", 2, "Write", write)
                }
            }
        }
    }

    impl<'de> serde::Deserialize<'de> for ResponseInner {
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
                type Value = ResponseInner;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("enum ResponseInner")
                }

                fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
                where
                    A: serde::de::EnumAccess<'de>,
                {
                    let (variant, variant_access) = data.variant::<Variant>()?;
                    match variant {
                        Variant::Get => {
                            let get = variant_access.newtype_variant()?;
                            Ok(ResponseInner::Get(get))
                        }
                        Variant::GetTimestamp => {
                            let get_timestamp = variant_access.newtype_variant()?;
                            Ok(ResponseInner::GetTimestamp(get_timestamp))
                        }
                        Variant::Write => {
                            let write = variant_access.newtype_variant()?;
                            Ok(ResponseInner::Write(write))
                        }
                    }
                }
            }
            deserializer.deserialize_enum("ResponseInner", VARIANTS, EnumVisitor)
        }
    }
}
