use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExError(std::io::Error);

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExErrorKind(std::io::ErrorKind);

pub assume_specification[ std::io::Error::from_raw_os_error ](code: std::io::RawOsError) -> (r:
    std::io::Error)
    no_unwind
;

pub assume_specification[ std::io::Error::kind ](err: &std::io::Error) -> (r: std::io::ErrorKind)
    no_unwind
;

} // verus!
