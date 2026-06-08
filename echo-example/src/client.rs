use clap::Parser;

use echo_example::cli;
use echo_example::cli::ClientArgs;
use echo_example::server;

fn main() {
    let args = match ClientArgs::parse().apply_config() {
        Ok(args) => args,
        Err(e) => {
            eprintln!("failed to parse config: {e:?}");
            return;
        }
    };

    match args.network {
        cli::NetworkType::Modelled => {
            let (listener, connector) = verdist::network::modelled::listen_channel(args.server_id);
            server::spawn_server(args.server_id, listener);
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::Udp => {
            let connector =
                verdist::network::udp::UdpConnector::new(args.server_addr, args.client_addr)
                    .expect("failed to create connector");
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::Tcp => {
            unimplemented!()
        }
    }
}
