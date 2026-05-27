use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::set::Set;

mod server_universe;

pub use server_universe::ServerUniverse;

verus! {

pub type Quorum = Set<u64>;

} // verus!
