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

    // `0` is not a valid thread count -- treat it the same as "unset" rather than handing
    // Server::new a value that violates its `num_shards > 0` precondition.
    let num_threads = args
        .num_threads
        .filter(|n| *n != 0)
        .unwrap_or_else(cli::default_num_threads);

    // --no-epoll always wins if both are (redundantly) given.
    let use_epoll = args.epoll && !args.no_epoll;

    match args.network {
        cli::NetworkType::Modelled => {
            eprintln!("server: the modelled server is instantiated in the same process as the client; shutting down server process");
        }
        cli::NetworkType::Udp => {
            let listener =
                verdist::network::udp::UdpListener::listen(args.server_addr, args.server_id)
                    .expect("failed to create listener");
            if use_epoll {
                echo_example::server::run_server_epoll(args.server_id, listener, num_threads);
            } else {
                echo_example::server::run_server(args.server_id, listener, num_threads);
            }
        }
        cli::NetworkType::Tcp => {
            let listener =
                verdist::network::tcp::TcpListener::listen(args.server_addr, args.server_id)
                    .expect("failed to create listener");
            if use_epoll {
                echo_example::server::run_server_epoll(args.server_id, listener, num_threads);
            } else {
                echo_example::server::run_server(args.server_id, listener, num_threads);
            }
        }
        cli::NetworkType::IoUringTcp => {
            let listener = verdist::network::io_uring_tcp::IoUringTcpListener::listen(
                args.server_addr,
                args.server_id,
            )
            .expect("failed to create listener");
            if use_epoll {
                echo_example::server::run_server_epoll(args.server_id, listener, num_threads);
            } else {
                echo_example::server::run_server(args.server_id, listener, num_threads);
            }
        }
        cli::NetworkType::IoUringUdp => {
            let listener = verdist::network::io_uring_udp::IoUringUdpListener::listen(
                args.server_addr,
                args.server_id,
            )
            .expect("failed to create listener");
            if use_epoll {
                echo_example::server::run_server_epoll(args.server_id, listener, num_threads);
            } else {
                echo_example::server::run_server(args.server_id, listener, num_threads);
            }
        }
    }
}
