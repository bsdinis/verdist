use clap::Parser;

use echo_example::cli;
use echo_example::cli::Args;
use echo_example::server;

fn main() {
    let args = Args::parse();

    match args.network {
        cli::NetworkType::Modelled => {
            let (listener, connector) = verdist::network::modelled::listen_channel(42);
            server::run_server(42, listener);
            echo_example::run_client(args, &connector).expect("error");
        }
        cli::NetworkType::Tcp => {
            unimplemented!()
        }
        cli::NetworkType::Udp => {
            unimplemented!()
        }
    }
}
