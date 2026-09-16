use clap::Parser;

use echo_example::cli;
use echo_example::cli::ClientArgs;
use echo_example::server;

fn main() {
    // Opt-in only: silent with no `RUST_LOG` set; set `RUST_LOG=debug` to see per-op client trace
    // output.
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_writer(std::io::stderr)
        .init();

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
            server::spawn_server(args.server_id, listener, cli::default_num_threads());
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::Udp => {
            let connector = verdist::network::udp_muxed::MuxedConnector::new(
                args.server_addr,
                args.client_addr,
                args.server_id,
            )
            .expect("failed to create connector");
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::UdpLegacy => {
            let connector = verdist::network::udp::UdpConnector::new(
                args.server_addr,
                args.client_addr,
                args.server_id,
            )
            .expect("failed to create connector");
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::Tcp => {
            let connector =
                verdist::network::tcp::TcpConnector::new(args.server_addr, args.server_id)
                    .expect("failed to create connector");
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::IoUringTcp => {
            let connector = verdist::network::io_uring_tcp::IoUringTcpConnector::new(
                args.server_addr,
                args.server_id,
            )
            .expect("failed to create connector");
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
        cli::NetworkType::IoUringUdp => {
            let connector = verdist::network::io_uring_udp::IoUringUdpConnector::new(
                args.server_addr,
                args.client_addr,
                args.server_id,
            )
            .expect("failed to create connector");
            echo_example::run_client(args, &connector).expect("run_client: error");
        }
    }
}
