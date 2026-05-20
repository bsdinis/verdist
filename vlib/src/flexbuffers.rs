use vstd::prelude::*;

verus! {

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExBuffer: std::ops::Deref<Target = [u8]> + Sized {
    type ExternalTraitSpecificationFor: flexbuffers::Buffer;
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExReaderError(flexbuffers::ReaderError);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExSerializationError(flexbuffers::SerializationError);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExDeserializationError(flexbuffers::DeserializationError);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(B)]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExReader<B>(flexbuffers::Reader<B>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExFlexbufferSerializer(flexbuffers::FlexbufferSerializer);

pub assume_specification<B>[ flexbuffers::Reader::<B>::get_root ](buffer: B) -> (r: Result<
    flexbuffers::Reader::<B>,
    flexbuffers::ReaderError,
>) where B: flexbuffers::Buffer
    no_unwind
;

pub assume_specification[ flexbuffers::FlexbufferSerializer::new ]() -> (r:
    flexbuffers::FlexbufferSerializer)
    no_unwind
;

} // verus!
