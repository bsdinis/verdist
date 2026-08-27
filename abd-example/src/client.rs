use clap::Parser;

use abd_example::cli;
use abd_example::server;
use specs::register::OwnedReadPerm;
use specs::register::OwnedWritePerm;

fn main() {
    let args = match cli::ClientArgs::parse() {
        Ok(args) => args,
        Err(e) => {
            eprintln!("failed to parse config: {e:?}");
            return;
        }
    };

    let server_ids = args.servers.keys().copied().collect();

    match args.network {
        cli::NetworkType::Modelled => {
            // The client process is also responsible for spawning the (test-only) in-process
            // server(s) a modelled-network run needs; re-read the same `--config` file purely to
            // learn which register backend those spawned servers should use. `RegisterBackend`
            // never becomes a field of `ClientArgs` itself -- the client's own protocol code has
            // no use for it.
            let register_backend = {
                let raw = cli::ClientParsedArgs::parse();
                abd_example::config::Config::parse(raw.config)
                    .map(|c| c.backend)
                    .unwrap_or_default()
                    .to_abd_backend()
            };
            let connectors = args
                .servers
                .values()
                .map(|server_conf| {
                    let (listener, connector) =
                        verdist::network::modelled::listen_channel(server_conf.id);
                    server::spawn_server::<_, _, OwnedWritePerm, OwnedReadPerm>(
                        &server_ids,
                        server_conf.id,
                        listener,
                        cli::default_num_threads(),
                        register_backend,
                    );
                    connector
                })
                .collect::<Vec<_>>();
            abd_example::run_client(args, &connectors).expect("run_client: error");
        }
        cli::NetworkType::Udp => {
            let connectors = args
                .servers
                .values()
                .map(|server_conf| {
                    let addr = server_conf.addr.expect("server addr should be set");
                    verdist::network::udp::UdpConnector::new(addr, args.client_addr, server_conf.id)
                        .expect("failed to create connector")
                })
                .collect::<Vec<_>>();

            abd_example::run_client(args, &connectors).expect("run_client: error");
        }
        cli::NetworkType::Tcp => {
            let connectors = args
                .servers
                .values()
                .map(|server_conf| {
                    let addr = server_conf.addr.expect("server addr should be set");
                    verdist::network::tcp::TcpConnector::new(addr, server_conf.id)
                        .expect("failed to create connector")
                })
                .collect::<Vec<_>>();

            abd_example::run_client(args, &connectors).expect("run_client: error");
        }
    }
}
