use vstd::prelude::*;

verus! {

pub assume_specification[ std::time::Duration::from_millis ](millis: u64) -> std::time::Duration
;

pub assume_specification[ std::thread::sleep ](dur: std::time::Duration)
;

} // verus!
