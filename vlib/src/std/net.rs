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

pub assume_specification[ std::net::SocketAddr::new ](ip: std::net::IpAddr, port: u16) -> (r:
    std::net::SocketAddr)
// TODO: specify port ip

    no_unwind
;

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExIpAddr(pub std::net::IpAddr);

pub assume_specification[ std::net::Ipv4Addr::new ](_0: u8, _1: u8, _2: u8, _3: u8) -> (r:
    std::net::Ipv4Addr)
    no_unwind
;

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExIpv4Addr(std::net::Ipv4Addr);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExIpv6Addr(std::net::Ipv6Addr);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExTcpListener(std::net::TcpListener);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExTcpStream(std::net::TcpStream);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExUdpSocket(std::net::UdpSocket);

pub assume_specification[ std::net::UdpSocket::local_addr ](s: &std::net::UdpSocket) -> (r:
    std::io::Result<std::net::SocketAddr>)
    ensures
        r is Ok,  // BSD: I cannot see this failing

    no_unwind
;

pub assume_specification[ std::net::UdpSocket::peer_addr ](s: &std::net::UdpSocket) -> (r:
    std::io::Result<std::net::SocketAddr>)
    ensures
        r is Ok,  // BSD: I cannot see this failing

    no_unwind
;

pub assume_specification[ std::net::UdpSocket::set_nonblocking ](
    s: &std::net::UdpSocket,
    b: bool,
) -> (r: std::io::Result<()>)
    ensures
        r is Ok,  // BSD: I cannot see this failing

    no_unwind
;

pub assume_specification[ std::net::TcpStream::local_addr ](s: &std::net::TcpStream) -> (r:
    std::io::Result<std::net::SocketAddr>)
    ensures
        r is Ok,  // BSD: I cannot see this failing

    no_unwind
;

pub assume_specification[ std::net::TcpStream::peer_addr ](s: &std::net::TcpStream) -> (r:
    std::io::Result<std::net::SocketAddr>)
    ensures
        r is Ok,  // BSD: I cannot see this failing

    no_unwind
;

pub assume_specification[ std::net::TcpStream::set_nonblocking ](
    s: &std::net::TcpStream,
    b: bool,
) -> (r: std::io::Result<()>)
    ensures
        r is Ok,  // BSD: I cannot see this failing

    no_unwind
;

} // verus!
