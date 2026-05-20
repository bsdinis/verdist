use vstd::prelude::*;

verus! {

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExError: core::fmt::Debug + core::fmt::Display {
    type ExternalTraitSpecificationFor: core::error::Error;
}

} // verus!
