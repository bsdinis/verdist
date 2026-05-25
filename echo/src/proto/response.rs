use crate::invariants::requests::RequestProof;
use crate::proto::echo::EchoResponse;
#[cfg(verus_only)]
use crate::proto::request::RequestInner;
#[cfg(verus_only)]
use crate::proto::ReqType;

use verdist::rpc::proto::TaggedMessage;

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
    Echo(EchoResponse),
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
            request@.value().req_type() is Echo <==> inner is Echo,
            request@.value().req_type() is Echo ==> {
                let echo_req = request@.value()->Echo_0;
                let echo_resp = inner->Echo_0;
                &&& echo_resp.spec_message() == echo_req.spec_message()
            },
        ensures
            r.spec_tag() == request_id,
            r.request_id() == request.id(),
            r.request_key() == request@.key(),
            r.request() == request@.value(),
            inner is Echo ==> {
                &&& r.req_type() is Echo
                &&& inner->Echo_0 == r.echo()
            },
    {
        Response { request_id, inner, request }
    }

    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.request_key().1 == self.spec_tag()
        &&& self.request().req_type() == self.req_type()
        &&& self.req_type() is Echo ==> {
            let echo_req = self.request()->Echo_0;
            let echo_resp = self.echo();
            &&& echo_resp.spec_message() == echo_req.spec_message()
        }
    }

    pub closed spec fn request_id(self) -> Loc {
        self.request.id()
    }

    pub closed spec fn request_key(self) -> (u64, u64) {
        self.request@.key()
    }

    pub closed spec fn request(self) -> RequestInner {
        self.request@.value()
    }

    pub closed spec fn req_type(self) -> ReqType {
        match self.inner {
            ResponseInner::Echo(_) => ReqType::Echo,
        }
    }

    pub closed spec fn echo(self) -> EchoResponse
        recommends
            self.req_type() is Echo,
    {
        self.inner->Echo_0
    }

    pub fn destruct_echo(self) -> (r: EchoResponse)
        requires
            self.req_type() is Echo,
        ensures
            r == self.echo(),
            ({
                let echo_req = self.request()->Echo_0;
                let echo_resp = self.echo();
                &&& echo_req.spec_message() == echo_resp.spec_message()
            }),
        no_unwind
    {
        proof {
            use_type_invariant(&self);
        }
        match self.inner {
            ResponseInner::Echo(g) => g,
        }
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
            a.req_type() is Echo ==> EchoResponse::spec_eq(a.echo(), b.echo()),
    {
    }

    pub proof fn agree_request(
        tracked &self,
        #[allow(unused_variables)]
        tracked request_proof: &mut RequestProof,
    )
        requires
            self.request_id() == old(request_proof).id(),
        ensures
            final(request_proof).id() == old(request_proof).id(),
            final(request_proof)@ == old(request_proof)@,
            self.request_key() == final(request_proof).key() ==> self.request()
                == final(request_proof).value(),
    {
        request_proof.intersection_agrees(self.request.borrow())
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
            (ResponseInner::Echo(a), ResponseInner::Echo(b)) => a.spec_eq(b),
        }
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        match a {
            ResponseInner::Echo(a) => EchoResponse::spec_eq_refl(a),
        }
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        match (a, b) {
            (ResponseInner::Echo(a), ResponseInner::Echo(b)) => EchoResponse::spec_eq_symm(a, b),
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
                ResponseInner::Echo(a),
                ResponseInner::Echo(b),
                ResponseInner::Echo(c),
            ) => EchoResponse::spec_eq_trans(a, b, c),
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
            if inner is Echo {
                EchoResponse::lemma_spec_eq(self.inner->Echo_0, inner->Echo_0);
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
            ResponseInner::Echo(echo) => { ResponseInner::Echo(echo.clone()) },
        }
    }
}

} // verus!
impl std::fmt::Debug for ResponseInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResponseInner::Echo(echo) => f.debug_tuple("Echo").field(&echo).finish(),
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

    use crate::proto::EchoResponse;

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
            const FIELDS: &'static [&'static str] = &["request_id", "inner"];

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
                    loop {
                        if let Some(key) = map.next_key()? {
                            match key {
                                Field::RequestId => {
                                    if request_id.is_some() {
                                        return Err(serde::de::Error::duplicate_field(
                                            "request_id",
                                        ));
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
                        } else {
                            break;
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
                ResponseInner::Echo(e) => {
                    serializer.serialize_newtype_variant("ResponseInner", 0, "Echo", e)
                }
            }
        }
    }

    impl<'de> serde::Deserialize<'de> for ResponseInner {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            const VARIANTS: &'static [&'static str] = &["Echo"];

            enum Variant {
                Echo,
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
                                "Echo" => Ok(Variant::Echo),
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
                        Variant::Echo => {
                            let echo: EchoResponse = variant_access.newtype_variant()?;
                            Ok(ResponseInner::Echo(echo))
                        }
                    }
                }
            }
            deserializer.deserialize_enum("ResponseInner", VARIANTS, EnumVisitor)
        }
    }
}
