use vstd::prelude::*;

verus! {

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExSerError: Sized + core::error::Error {
    type ExternalTraitSpecificationFor: serde::ser::Error;
}

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExSerializer: Sized {
    type ExternalTraitSpecificationFor: serde::ser::Serializer;

    type Ok;

    type Error: serde::ser::Error;
}

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExSerialize {
    type ExternalTraitSpecificationFor: serde::ser::Serialize;

    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where
        S: serde::ser::Serializer,
    ;
}

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExDeserError: Sized + core::error::Error {
    type ExternalTraitSpecificationFor: serde::de::Error;
}

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExDeserializer<'de>: Sized {
    type ExternalTraitSpecificationFor: serde::de::Deserializer<'de>;

    type Error: serde::de::Error;
}

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExDeserialize<'de>: Sized {
    type ExternalTraitSpecificationFor: serde::de::Deserialize<'de>;

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where
        D: serde::de::Deserializer<'de>,
    ;
}

} // verus!
