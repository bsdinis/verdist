use vstd::prelude::*;

verus! {

pub struct EchoRequest {
    #[allow(unused)]
    message: String,
}

pub struct EchoResponse {
    #[allow(unused)]
    message: String,
}

#[allow(unused)]
impl EchoRequest {
    pub fn new(message: String) -> (r: Self)
        ensures
            r.spec_message() == message,
    {
        EchoRequest { message }
    }

    pub closed spec fn spec_message(self) -> String {
        self.message
    }

    pub fn message(self) -> String
        returns
            self.spec_message(),
    {
        self.message
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        self.spec_message() == other.spec_message()
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
            a.spec_message() == b.spec_message(),
    {
    }
}

#[allow(unused)]
impl EchoResponse {
    pub fn new(message: String) -> (r: Self)
        ensures
            r.spec_message() == message,
    {
        EchoResponse { message }
    }

    pub closed spec fn spec_message(self) -> String {
        self.message
    }

    pub fn message(self) -> String
        returns
            self.spec_message(),
    {
        self.message
    }
}

impl EchoResponse {
    pub closed spec fn spec_eq(self, other: Self) -> bool {
        self.spec_message() == other.spec_message()
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
            a.spec_message() == b.spec_message(),
    {
    }
}

impl Clone for EchoRequest {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        EchoRequest { message: self.message.clone() }
    }
}

impl Clone for EchoResponse {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        EchoResponse { message: self.message.clone() }
    }
}

} // verus!
impl std::fmt::Debug for EchoRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EchoRequest")
            .field("message", &self.message)
            .finish()
    }
}

impl std::fmt::Debug for EchoResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EchoResponse")
            .field("message", &self.message)
            .finish()
    }
}

mod serde_impls {
    use super::EchoRequest;
    use super::EchoResponse;
    use serde;
    use serde::ser::SerializeStruct;

    impl serde::Serialize for EchoRequest {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            let mut state = serializer.serialize_struct("EchoRequest", 1)?;
            state.serialize_field("message", &self.message)?;
            state.end()
        }
    }

    impl<'de> serde::Deserialize<'de> for EchoRequest {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            const FIELDS: &'static [&'static str] = &["message"];

            enum Field {
                Message,
            }

            struct FieldVisitor;

            impl<'de> serde::de::Visitor<'de> for FieldVisitor {
                type Value = Field;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("`message`")
                }

                fn visit_str<E>(self, value: &str) -> Result<Field, E>
                where
                    E: serde::de::Error,
                {
                    match value {
                        "message" => Ok(Field::Message),
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
                type Value = EchoRequest;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("struct EchoRequest")
                }

                fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::SeqAccess<'de>,
                {
                    let message = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;
                    Ok(EchoRequest { message })
                }

                fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::MapAccess<'de>,
                {
                    let mut message = None;
                    loop {
                        if let Some(key) = map.next_key()? {
                            match key {
                                Field::Message => {
                                    if message.is_some() {
                                        return Err(serde::de::Error::duplicate_field("message"));
                                    }
                                    message = Some(map.next_value()?);
                                }
                            }
                        } else {
                            break;
                        }
                    }
                    let message =
                        message.ok_or_else(|| serde::de::Error::missing_field("message"))?;
                    Ok(EchoRequest { message })
                }
            }

            deserializer.deserialize_struct("EchoRequest", FIELDS, StructVisitor)
        }
    }

    impl serde::Serialize for EchoResponse {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            let mut state = serializer.serialize_struct("EchoResponse", 1)?;
            state.serialize_field("message", &self.message)?;
            state.end()
        }
    }

    impl<'de> serde::Deserialize<'de> for EchoResponse {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            const FIELDS: &'static [&'static str] = &["message"];

            enum Field {
                Message,
            }

            struct FieldVisitor;

            impl<'de> serde::de::Visitor<'de> for FieldVisitor {
                type Value = Field;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("`message`")
                }

                fn visit_str<E>(self, value: &str) -> Result<Field, E>
                where
                    E: serde::de::Error,
                {
                    match value {
                        "message" => Ok(Field::Message),
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
                type Value = EchoResponse;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("struct EchoResponse")
                }

                fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::SeqAccess<'de>,
                {
                    let message = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;
                    Ok(EchoResponse { message })
                }

                fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::MapAccess<'de>,
                {
                    let mut message = None;
                    loop {
                        if let Some(key) = map.next_key()? {
                            match key {
                                Field::Message => {
                                    if message.is_some() {
                                        return Err(serde::de::Error::duplicate_field("message"));
                                    }
                                    message = Some(map.next_value()?);
                                }
                            }
                        } else {
                            break;
                        }
                    }
                    let message =
                        message.ok_or_else(|| serde::de::Error::missing_field("message"))?;
                    Ok(EchoResponse { message })
                }
            }
            deserializer.deserialize_struct("EchoResponse", FIELDS, StructVisitor)
        }
    }
}
