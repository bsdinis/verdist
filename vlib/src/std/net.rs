use vstd::prelude::*;

verus! {

#[allow(unused)]
#[verifier::external_trait_specification]
pub trait ExToSocketAddrs {
    type ExternalTraitSpecificationFor: std::net::ToSocketAddrs;
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExSocketAddr(std::net::SocketAddr);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExUdpSocket(std::net::UdpSocket);

pub assume_specification[ std::net::UdpSocket::local_addr ](s: &std::net::UdpSocket) -> (r:
    std::io::Result<std::net::SocketAddr>)
    no_unwind
;

pub assume_specification[ std::net::UdpSocket::peer_addr ](s: &std::net::UdpSocket) -> (r:
    std::io::Result<std::net::SocketAddr>)
    no_unwind
;

} // verus!
