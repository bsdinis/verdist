use clap::Parser;
use std::net::IpAddr;
use std::net::Ipv4Addr;

use echo_example::cli;
use echo_example::cli::Args;
use echo_example::server;

fn main() {
    let args = Args::parse();

    match args.network {
        cli::NetworkType::Modelled => {
            let (listener, connector) = verdist::network::modelled::listen_channel(args.server_id);
            server::spawn_server(args.server_id, listener);
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::Udp => {
            let my_ip = IpAddr::V4(Ipv4Addr::LOCALHOST);
            let connector =
                verdist::network::udp::UdpConnector::new(echo_example::LISTEN_ADDR, my_ip)
                    .expect("failed to create connector");
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::Tcp => {
            unimplemented!()
        }
    }
}
