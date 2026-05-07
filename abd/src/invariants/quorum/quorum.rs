use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::set::Set;

verus! {

pub tracked struct Quorum {
    pub servers: Set<u64>,
}

impl Quorum {
    pub open spec fn view(self) -> Set<u64> {
        self.servers
    }

    pub open spec fn from_set(servers: Set<u64>) -> Self {
        Quorum { servers }
    }

    pub open spec fn inv(self) -> bool {
        &&& self@.finite()
        &&& self@.len() > 0
        &&& !self@.is_empty()
    }
}

} // verus!
