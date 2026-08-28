use clap::Parser;

use specs::register::{OwnedReadPerm, OwnedWritePerm};

pub mod cli;
pub mod client;
pub mod config;
pub mod error;
pub mod invariant;

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
                config::Config::parse(raw.config)
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
                        args.num_threads,
                        register_backend,
                    );
                    connector
                })
                .collect::<Vec<_>>();

            client::run_client(args, &connectors).expect("run_client: error");
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

            client::run_client(args, &connectors).expect("run_client: error");
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

            client::run_client(args, &connectors).expect("run_client: error");
        }
    }
}

pub mod server {
    use abd::channel::ChannelInv;
    use abd::proto::Request;
    use abd::proto::Response;
    use abd::server::create_server;
    use specs::register::RegisterRead;
    use specs::register::RegisterWrite;
    use vstd::logatom::MutLinearizer;
    use vstd::logatom::ReadLinearizer;

    use std::collections::HashSet;
    use std::sync::Arc;
    use verdist::network::channel::Channel;
    use verdist::network::channel::Listener;

    // Why is this unverified:
    // - major: verus does not support scoped threads (see verdist::service::Server::run)
    pub fn spawn_server<L, C, ML, RL>(
        server_ids: &HashSet<u64>,
        server_id: u64,
        listener: L,
        num_threads: usize,
        backend: abd::server::RegisterBackend,
    ) where
        L: Listener<C> + Send + Sync + 'static,
        C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>
            + Send
            + Sync
            + 'static,
        ML: MutLinearizer<RegisterWrite> + Send + 'static,
        RL: ReadLinearizer<RegisterRead> + Send + 'static,
        <ML as MutLinearizer<RegisterWrite>>::Completion: Send,
        <RL as ReadLinearizer<RegisterRead>>::Completion: Send,
    {
        let (server, raw_receivers) =
            create_server::<_, _, ML, RL>(server_ids, server_id, listener, num_threads, backend);
        let server = Arc::new(server);
        std::thread::spawn(move || {
            vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

            server.run(raw_receivers);
        });
    }

    pub fn run_server<L, C, ML, RL>(
        server_ids: &HashSet<u64>,
        server_id: u64,
        listener: L,
        num_threads: usize,
        backend: abd::server::RegisterBackend,
    ) where
        L: Listener<C> + Sync,
        C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
        ML: MutLinearizer<RegisterWrite> + Send,
        RL: ReadLinearizer<RegisterRead> + Send,
        <ML as MutLinearizer<RegisterWrite>>::Completion: Send,
        <RL as ReadLinearizer<RegisterRead>>::Completion: Send,
    {
        let (server, raw_receivers) =
            create_server::<_, _, ML, RL>(server_ids, server_id, listener, num_threads, backend);
        vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

        server.run(raw_receivers);
    }
}
