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
            // Explicit turbofish needed: `MuxedConnector` implements `Connector` for both this
            // (plain) and `io_uring_udp_muxed`'s channel type, so type inference alone is
            // ambiguous (see the `IoUringUdp` arm below for the same disambiguation).
            let connector = verdist::network::udp_muxed::MuxedConnector::new(
                args.server_addr,
                args.client_addr,
                args.server_id,
            )
            .expect("failed to create connector");
            echo_example::run_client::<
                verdist::network::udp_muxed::MuxedServerChannel<
                    echo::channel::ChannelInv,
                    echo::proto::Response,
                    echo::proto::Request,
                >,
                _,
            >(args, &connector)
            .expect("run_client: error");
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
            // Reuses the plain `MuxedConnector` (no new connector type needed -- see
            // `verdist::network::io_uring_udp_muxed`'s top doc): it implements `Connector` for
            // both `udp_muxed::MuxedServerChannel` and `io_uring_udp_muxed::IoUringMuxedServerChannel`,
            // so an explicit turbofish is needed to pick the io_uring-backed one (type inference
            // alone is ambiguous between the two `Connector` impls this connector type has).
            let connector = verdist::network::udp_muxed::MuxedConnector::new(
                args.server_addr,
                args.client_addr,
                args.server_id,
            )
            .expect("failed to create connector");
            echo_example::run_client::<
                verdist::network::io_uring_udp_muxed::IoUringMuxedServerChannel<
                    echo::channel::ChannelInv,
                    echo::proto::Response,
                    echo::proto::Request,
                >,
                _,
            >(args, &connector)
            .expect("run_client: error");
        }
        cli::NetworkType::IoUringUdpLegacy => {
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
