use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::set::Set;

mod auth;
mod lb;
mod server_map;

pub use auth::ServerUniverseAuth;
pub use lb::ServerUniverseLb;

verus! {

pub type Quorum = Set<u64>;

} // verus!
