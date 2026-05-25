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
    no_unwind
;

} // verus!
