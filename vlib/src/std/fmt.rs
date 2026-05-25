#![allow(unused)]
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
pub struct ExError(core::fmt::Error);

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExFormatter<'a>(core::fmt::Formatter<'a>);

pub assume_specification<'a>[ core::fmt::Formatter::<'a>::write_str ](
    f: &mut core::fmt::Formatter<'a>,
    data: &str,
) -> (r: core::fmt::Result)
    no_unwind
;

} // verus!
