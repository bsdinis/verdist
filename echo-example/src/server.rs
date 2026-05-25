use clap::Parser;

use echo_example::cli;
use echo_example::cli::Args;

fn main() {
    let args = Args::parse();

    match args.network {
        cli::NetworkType::Modelled => {
            eprintln!("server: the modelled server is instantiated in the same process as the client; shutting down server process");
        }
        cli::NetworkType::Udp => {
            let listener = verdist::network::udp::UdpListener::listen(
                echo_example::LISTEN_ADDR,
                args.server_id,
            )
            .expect("failed to create listener");
            echo_example::server::run_server(args.server_id, listener);
        }
        cli::NetworkType::Tcp => {
            unimplemented!()
        }
    }
}
