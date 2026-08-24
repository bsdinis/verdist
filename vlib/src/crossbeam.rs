use vstd::prelude::*;
verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(T)]
#[allow(dead_code)]
pub struct ExReceiver<T>(crossbeam_channel::Receiver<T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(T)]
#[allow(dead_code)]
pub struct ExSender<T>(crossbeam_channel::Sender<T>);

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExTryRecvError(crossbeam_channel::TryRecvError);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(S)]
#[allow(dead_code)]
pub struct ExSendError<S>(crossbeam_channel::SendError<S>);

pub assume_specification[ crossbeam_channel::TryRecvError::is_empty ](
    err: &crossbeam_channel::TryRecvError,
) -> (b: bool)
    ensures
        b == (*err is Empty),
    no_unwind
;

// Blanket, type-generic only (never per-instance) -- no `ensures` beyond well-typedness. This
// is deliberately the minimal possible spec: an ordinary MPSC queue that doesn't corrupt or
// fabricate values, nothing more. Callers that need a received value to satisfy some invariant
// must establish that invariant themselves after receiving it (e.g. by only ever sending
// ghost-inert payloads and reconstructing anything invariant-relevant on the receiving side) --
// this spec makes no claim linking a `send`'s argument to a later `try_recv`'s result.
pub assume_specification<T>[ crossbeam_channel::Sender::<T>::send ](
    sender: &crossbeam_channel::Sender<T>,
    msg: T,
) -> (r: Result<(), crossbeam_channel::SendError<T>>)
    no_unwind
;

pub assume_specification<T>[ crossbeam_channel::Receiver::<T>::try_recv ](
    receiver: &crossbeam_channel::Receiver<T>,
) -> (r: Result<T, crossbeam_channel::TryRecvError>)
    no_unwind
;

} // verus!
