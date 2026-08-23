#![allow(unused)]
use vstd::prelude::*;

verus! {

// ExError/ExFormatter used to be declared here, but vstd::std_specs::fmt now provides both
// natively (as ExError/ExFormatter), so declaring them again here is a duplicate specification
// error.
pub assume_specification<'a>[ core::fmt::Formatter::<'a>::write_str ](
    f: &mut core::fmt::Formatter<'a>,
    data: &str,
) -> (r: core::fmt::Result)
    no_unwind
;

} // verus!
