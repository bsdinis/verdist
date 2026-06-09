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
                    );
                    connector
                })
                .collect::<Vec<_>>();
            abd_example::run_client(args, &connectors).expect("run_client: error");
        }
        cli::NetworkType::Udp => {
            unimplemented!()
        }
        cli::NetworkType::Tcp => {
            unimplemented!()
        }
    }
}
