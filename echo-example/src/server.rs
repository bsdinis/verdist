use clap::Parser;

use echo_example::cli;
use echo_example::cli::ServerArgs;

fn main() {
    let args = match ServerArgs::parse().apply_config() {
        Ok(args) => args,
        Err(e) => {
            eprintln!("failed to parse config: {e:?}");
            return;
        }
    };

    match args.network {
        cli::NetworkType::Modelled => {
            eprintln!("server: the modelled server is instantiated in the same process as the client; shutting down server process");
        }
        cli::NetworkType::Udp => {
            let listener =
                verdist::network::udp::UdpListener::listen(args.server_addr, args.server_id)
                    .expect("failed to create listener");
            echo_example::server::run_server(args.server_id, listener);
        }
        cli::NetworkType::Tcp => {
            let listener =
                verdist::network::tcp::TcpListener::listen(args.server_addr, args.server_id)
                    .expect("failed to create listener");
            echo_example::server::run_server(args.server_id, listener);
        }
    }
}
