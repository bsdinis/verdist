use crate::invariants::requests::RequestProof;
use crate::proto::echo::EchoRequest;
#[cfg(verus_only)]
use crate::proto::ReqType;

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
    Echo(EchoRequest),
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
            RequestInner::Echo(_) => ReqType::Echo,
        }
    }

    pub fn new_echo(message: String) -> (r: Self)
        ensures
            r.req_type() is Echo,
            ({
                let req = r->Echo_0;
                req.spec_message() == message
            }),
    {
        RequestInner::Echo(EchoRequest::new(message))
    }

    pub open spec fn spec_eq(self, other: Self) -> bool {
        match (self, other) {
            (RequestInner::Echo(a), RequestInner::Echo(b)) => a.spec_eq(b),
        }
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        match a {
            RequestInner::Echo(a) => { EchoRequest::spec_eq_refl(a) },
        }
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        match (a, b) {
            (RequestInner::Echo(a), RequestInner::Echo(b)) => EchoRequest::spec_eq_symm(a, b),
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
                RequestInner::Echo(a),
                RequestInner::Echo(b),
                RequestInner::Echo(c),
            ) => EchoRequest::spec_eq_trans(a, b, c),
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
        self.request@.value()
    }

    pub closed spec fn req_type(self) -> ReqType {
        self.inner.req_type()
    }

    pub closed spec fn echo(self) -> EchoRequest
        recommends
            self.req_type() is Echo,
    {
        self.inner->Echo_0
    }

    pub closed spec fn client_id(self) -> u64 {
        self.request@.key().0
    }

    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.request@.key().1 == self.request_id
        &&& self.request@.value().spec_eq(self.inner)
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
            request_proof@.value().spec_eq(request_inner),
        ensures
            r.req_type() == request_inner.req_type(),
            r.request_key() == (r.client_id(), r.spec_tag()),
            r.request_id() == request_proof@.id(),
            r.client_id() == client_id,
            r.spec_tag() == request_id,
            r.req_type() is Echo ==> r.echo() == request_inner->Echo_0,
    {
        Request { request_id, inner: request_inner, request: request_proof }
    }

    pub fn destruct(self) -> (r: (u64, RequestInner, Tracked<RequestProof>))
        ensures
            r.0 == self.spec_tag(),
            r.2@.value().spec_eq(r.1),
            r.2@.id() == self.request_id(),
            r.2@.value() == self.request(),
            r.2@.value().req_type() == self.req_type(),
            r.2@.key() == self.request_key(),
            r.2@.key() == (self.client_id(), self.spec_tag()),
            r.2@.value().spec_eq(r.1),
            r.1 is Echo <==> self.req_type() is Echo,
            self.req_type() is Echo ==> r.1->Echo_0 == self.echo(),
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
        assert(self.request@.value().spec_eq(self.inner));
        assert(self.request@.value().spec_eq(inner));
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
            RequestInner::Echo(echo) => { RequestInner::Echo(echo.clone()) },
        }
    }
}

} // verus!
impl std::fmt::Debug for RequestInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RequestInner::Echo(echo) => f.debug_tuple("Echo").field(&echo).finish(),
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
                RequestInner::Echo(e) => {
                    serializer.serialize_newtype_variant("RequestInner", 0, "Echo", e)
                }
            }
        }
    }

    impl<'de> serde::Deserialize<'de> for RequestInner {
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
                        Variant::Echo => {
                            let echo = variant_access.newtype_variant()?;
                            Ok(RequestInner::Echo(echo))
                        }
                    }
                }
            }
            deserializer.deserialize_enum("RequestInner", VARIANTS, EnumVisitor)
        }
    }
}
