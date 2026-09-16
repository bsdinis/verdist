//! Manual (de)serialization for the register's `Option<[u8; N]>` value field.
//!
//! serde's built-in fixed-size-array impls only cover `[T; N]` for `N <= 32`
//! (`array_impls!` in serde's `ser`/`de` modules is a macro invoked for
//! lengths 1..=32, not a fully const-generic impl), so once the register
//! value grows past that (this crate uses `N` in the thousands, sized
//! against the UDP datagram ceiling), it cannot go through the blanket
//! `Option<T>`/`[T; N]` `Serialize`/`Deserialize` impls. Instead these
//! helpers encode the array as a single length-prefixed byte string via
//! `Serializer::serialize_bytes`/`Deserializer::deserialize_bytes`, which
//! serde (and postcard, the wire format this crate actually uses -- see
//! `postcard::ser::serializer::Serializer::serialize_bytes`/
//! `de::deserializer::Deserializer::deserialize_bytes`) support for any
//! length, and hand-decode it back on the way in.
use serde::de::DeserializeSeed;
use serde::de::Deserializer;
use serde::de::Visitor;
use serde::ser::Serializer;

/// Wraps `&Option<[u8; N]>` so it can be passed to `SerializeStruct::serialize_field`
/// (which requires its argument to implement `Serialize`) without going through the
/// N-limited blanket array impls.
pub(crate) struct OptArr<'a, const N: usize>(pub &'a Option<[u8; N]>);

impl<'a, const N: usize> serde::Serialize for OptArr<'a, N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self.0 {
            Some(v) => serializer.serialize_some(&RawBytes(v.as_slice())),
            None => serializer.serialize_none(),
        }
    }
}

struct RawBytes<'a>(&'a [u8]);

impl<'a> serde::Serialize for RawBytes<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(self.0)
    }
}

/// `DeserializeSeed` for `Option<[u8; N]>`, for use with `next_element_seed`/
/// `next_value_seed` (the seeded counterparts of `next_element`/`next_value`,
/// needed here since plain `Deserialize` isn't implemented for `[u8; N]` at
/// this size).
pub(crate) struct OptArrSeed<const N: usize>;

impl<'de, const N: usize> DeserializeSeed<'de> for OptArrSeed<N> {
    type Value = Option<[u8; N]>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_option(OptArrVisitor::<N>)
    }
}

struct OptArrVisitor<const N: usize>;

impl<'de, const N: usize> Visitor<'de> for OptArrVisitor<N> {
    type Value = Option<[u8; N]>;

    fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "an optional {N}-byte array")
    }

    fn visit_none<E>(self) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(None)
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bytes(BytesArrayVisitor::<N>).map(Some)
    }
}

struct BytesArrayVisitor<const N: usize>;

impl<'de, const N: usize> Visitor<'de> for BytesArrayVisitor<N> {
    type Value = [u8; N];

    fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{N} bytes")
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        <[u8; N]>::try_from(v).map_err(|_| E::invalid_length(v.len(), &self))
    }

    fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        self.visit_bytes(v)
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        self.visit_bytes(&v)
    }
}
