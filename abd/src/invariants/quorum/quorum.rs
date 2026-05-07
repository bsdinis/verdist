use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::set::Set;

verus! {

pub type Quorum = Set<u64>;

} // verus!
