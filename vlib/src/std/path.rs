use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExPathBuf(std::path::PathBuf);

} // verus!
