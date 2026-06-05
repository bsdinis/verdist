use clap::Parser;

use abd_example::cli::Args;
use abd_example::server;

/*
fn main() {
    let args = Args::parse();

    match args.network {
        cli::NetworkType::Modelled => {
            let (listener, connector) = verdist::network::modelled::listen_channel(args.server_id);
            server::spawn_server(args.server_id, listener);
            abd_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::Udp => {
            let my_ip = IpAddr::V4(Ipv4Addr::LOCALHOST);
            let connector =
                verdist::network::udp::UdpConnector::new(echo_example::LISTEN_ADDR, my_ip)
                    .expect("failed to create connector");
            abd_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::Tcp => {
            unimplemented!()
        }
    }
}
*/

fn main() {
    let args = Args::parse();

    if args.n_servers == 0 {
        eprintln!("need at least one server");
        return;
    }

    let connectors: Vec<_> = (0..args.n_servers)
        .map(server::modelled::run_server)
        .collect();

    abd_example::run_client(args, &connectors).expect("error");
}
