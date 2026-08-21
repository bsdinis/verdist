use vstd::prelude::*;

verus! {

#[derive(Structural, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Timestamp {
    pub seqno: u64,
    pub client_id: u64,
    pub client_ctr: u64,
}

#[cfg(verus_only)]
impl vstd::std_specs::cmp::PartialOrdSpecImpl for Timestamp {
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.seqno == other.seqno && self.client_id == other.client_id && self.client_ctr
            == other.client_ctr {
            Some(std::cmp::Ordering::Equal)
        } else if self.seqno < other.seqno || (self.seqno == other.seqno && self.client_id
            < other.client_id) || (self.seqno == other.seqno && self.client_id == other.client_id
            && self.client_ctr < other.client_ctr) {
            Some(std::cmp::Ordering::Less)
        } else {
            Some(std::cmp::Ordering::Greater)
        }
    }
}

#[cfg(verus_only)]
impl vstd::std_specs::cmp::OrdSpecImpl for Timestamp {
    open spec fn obeys_cmp_spec() -> bool {
        true
    }

    open spec fn cmp_spec(&self, other: &Self) -> std::cmp::Ordering {
        if self.seqno == other.seqno && self.client_id == other.client_id && self.client_ctr
            == other.client_ctr {
            std::cmp::Ordering::Equal
        } else if self.seqno < other.seqno || (self.seqno == other.seqno && self.client_id
            < other.client_id) || (self.seqno == other.seqno && self.client_id == other.client_id
            && self.client_ctr < other.client_ctr) {
            std::cmp::Ordering::Less
        } else {
            std::cmp::Ordering::Greater
        }
    }
}

impl Timestamp {
    // Ideally we would implement default, but not sure if trait extension is working
    #[allow(clippy::should_implement_trait)]
    pub fn default() -> (r: Self)
        ensures
            r.seqno == 0,
            r.client_id == 0,
            r.client_ctr == 0,
    {
        Timestamp { seqno: 0, client_id: 0, client_ctr: 0 }
    }

    pub open spec fn spec_default() -> (r: Self) {
        Timestamp { seqno: 0, client_id: 0, client_ctr: 0 }
    }

    pub open spec fn spec_lt(self, other: Self) -> bool {
        ||| self.seqno < other.seqno
        ||| (self.seqno == other.seqno && self.client_id < other.client_id)
        ||| (self.seqno == other.seqno && self.client_id == other.client_id && self.client_ctr
            < other.client_ctr)
    }

    pub open spec fn spec_le(self, other: Self) -> bool {
        self < other || self == other
    }

    pub open spec fn spec_gt(self, other: Self) -> bool {
        !(self <= other)
    }

    pub open spec fn spec_ge(self, other: Self) -> bool {
        !(self < other)
    }

    pub open spec fn spec_eq(self, other: Self) -> bool {
        &&& self.seqno == other.seqno
        &&& self.client_id == other.client_id
        &&& self.client_ctr == other.client_ctr
    }
}

} // verus!
impl std::fmt::Debug for Timestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.seqno.fmt(f)?;
        f.write_str(".")?;
        self.client_id.fmt(f)
    }
}

mod serde_impls {
    use serde::ser::SerializeStruct;

    use super::Timestamp;

    impl serde::Serialize for Timestamp {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            let mut state = serializer.serialize_struct("Timestamp", 3)?;
            state.serialize_field("seqno", &self.seqno)?;
            state.serialize_field("client_id", &self.client_id)?;
            state.serialize_field("client_ctr", &self.client_ctr)?;
            state.end()
        }
    }

    impl<'de> serde::Deserialize<'de> for Timestamp {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            const FIELDS: &[&str] = &["seqno", "client_id", "client_ctr"];

            enum Field {
                Seqno,
                ClientId,
                ClientCtr,
            }

            struct FieldVisitor;

            impl<'de> serde::de::Visitor<'de> for FieldVisitor {
                type Value = Field;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("`seqno`, `client_id`, or `client_ctr`")
                }

                fn visit_str<E>(self, value: &str) -> Result<Field, E>
                where
                    E: serde::de::Error,
                {
                    match value {
                        "seqno" => Ok(Field::Seqno),
                        "client_id" => Ok(Field::ClientId),
                        "client_ctr" => Ok(Field::ClientCtr),
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
                type Value = Timestamp;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("struct Timestamp")
                }

                fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::SeqAccess<'de>,
                {
                    let seqno = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;
                    let client_id = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(1, &self))?;
                    let client_ctr = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(2, &self))?;
                    Ok(Timestamp {
                        seqno,
                        client_id,
                        client_ctr,
                    })
                }

                fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
                where
                    V: serde::de::MapAccess<'de>,
                {
                    let mut seqno = None;
                    let mut client_id = None;
                    let mut client_ctr = None;
                    while let Some(key) = map.next_key()? {
                        match key {
                            Field::Seqno => {
                                if seqno.is_some() {
                                    return Err(serde::de::Error::duplicate_field("seqno"));
                                }
                                seqno = Some(map.next_value()?);
                            }
                            Field::ClientId => {
                                if client_id.is_some() {
                                    return Err(serde::de::Error::duplicate_field("client_id"));
                                }
                                client_id = Some(map.next_value()?);
                            }
                            Field::ClientCtr => {
                                if client_ctr.is_some() {
                                    return Err(serde::de::Error::duplicate_field("client_ctr"));
                                }
                                client_ctr = Some(map.next_value()?);
                            }
                        }
                    }
                    let seqno = seqno.ok_or_else(|| serde::de::Error::missing_field("seqno"))?;
                    let client_id =
                        client_id.ok_or_else(|| serde::de::Error::missing_field("client_id"))?;
                    let client_ctr =
                        client_ctr.ok_or_else(|| serde::de::Error::missing_field("client_ctr"))?;
                    Ok(Timestamp {
                        seqno,
                        client_id,
                        client_ctr,
                    })
                }
            }
            deserializer.deserialize_struct("Timestamp", FIELDS, StructVisitor)
        }
    }
}
