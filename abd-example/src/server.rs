use abd_example::cli;
use abd_example::cli::ServerArgs;
use specs::register::OwnedReadPerm;
use specs::register::OwnedWritePerm;

fn main() {
    // Opt-in only: silent with no `RUST_LOG` set (`vlib::vdebug!`/`vinfo!` short-circuit before
    // formatting anything either way); set `RUST_LOG=debug` to see per-request server trace output.
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_writer(std::io::stderr)
        .init();

    let args = match ServerArgs::parse() {
        Ok(args) => args,
        Err(e) => {
            eprintln!("failed to parse config: {e:?}");
            return;
        }
    };

    let server_ids = args.servers.keys().copied().collect();
    let backend = args.backend.to_abd_backend();

    match args.network {
        cli::NetworkType::Modelled => {
            eprintln!("server: the modelled server is instantiated in the same process as the client; shutting down server process");
        }
        cli::NetworkType::Udp => {
            // No `--epoll` support yet for this backend (see `verdist::network::udp_muxed`'s
            // module doc) -- always the plain backoff-based `run_server`, regardless of
            // `args.epoll`.
            if args.epoll {
                eprintln!("server: --epoll is not yet supported for udp; running without it");
            }
            let listener = verdist::network::udp_muxed::MuxedListener::listen_reuseport(
                args.addr(),
                args.server_id,
                args.num_router_threads,
            )
            .expect("failed to create listener");
            abd_example::server::run_server::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                &server_ids,
                args.server_id,
                listener,
                args.num_threads,
                backend,
            );
        }
        cli::NetworkType::UdpLegacy => {
            let listener = verdist::network::udp::UdpListener::listen(args.addr(), args.server_id)
                .expect("failed to create listener");
            if args.epoll {
                abd_example::server::run_server_epoll::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                    &server_ids,
                    args.server_id,
                    listener,
                    args.num_threads,
                    backend,
                );
            } else {
                abd_example::server::run_server::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                    &server_ids,
                    args.server_id,
                    listener,
                    args.num_threads,
                    backend,
                );
            }
        }
        cli::NetworkType::Tcp => {
            let listener = verdist::network::tcp::TcpListener::listen(args.addr(), args.server_id)
                .expect("failed to create listener");
            if args.epoll {
                abd_example::server::run_server_epoll::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                    &server_ids,
                    args.server_id,
                    listener,
                    args.num_threads,
                    backend,
                );
            } else {
                abd_example::server::run_server::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                    &server_ids,
                    args.server_id,
                    listener,
                    args.num_threads,
                    backend,
                );
            }
        }
        cli::NetworkType::IoUringTcp => {
            let listener = verdist::network::io_uring_tcp::IoUringTcpListener::listen(
                args.addr(),
                args.server_id,
            )
            .expect("failed to create listener");
            if args.epoll {
                abd_example::server::run_server_epoll::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                    &server_ids,
                    args.server_id,
                    listener,
                    args.num_threads,
                    backend,
                );
            } else {
                abd_example::server::run_server::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                    &server_ids,
                    args.server_id,
                    listener,
                    args.num_threads,
                    backend,
                );
            }
        }
        cli::NetworkType::IoUringUdp => {
            let listener = verdist::network::io_uring_udp::IoUringUdpListener::listen(
                args.addr(),
                args.server_id,
            )
            .expect("failed to create listener");
            if args.epoll {
                abd_example::server::run_server_epoll::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                    &server_ids,
                    args.server_id,
                    listener,
                    args.num_threads,
                    backend,
                );
            } else {
                abd_example::server::run_server::<{ abd_example::VALUE_SIZE }, _, _, OwnedWritePerm<{ abd_example::VALUE_SIZE }>, OwnedReadPerm<{ abd_example::VALUE_SIZE }>>(
                    &server_ids,
                    args.server_id,
                    listener,
                    args.num_threads,
                    backend,
                );
            }
        }
    }
}
