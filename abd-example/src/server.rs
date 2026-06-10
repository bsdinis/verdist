use abd_example::cli;
use abd_example::cli::ServerArgs;
use specs::register::OwnedReadPerm;
use specs::register::OwnedWritePerm;

fn main() {
    let args = match ServerArgs::parse() {
        Ok(args) => args,
        Err(e) => {
            eprintln!("failed to parse config: {e:?}");
            return;
        }
    };

    let server_ids = args.servers.keys().copied().collect();

    match args.network {
        cli::NetworkType::Modelled => {
            eprintln!("server: the modelled server is instantiated in the same process as the client; shutting down server process");
        }
        cli::NetworkType::Udp => {
            let listener = verdist::network::udp::UdpListener::listen(args.addr(), args.server_id)
                .expect("failed to create listener");
            abd_example::server::run_server::<_, _, OwnedWritePerm, OwnedReadPerm>(
                &server_ids,
                args.server_id,
                listener,
            );
        }
        cli::NetworkType::Tcp => {
            let listener = verdist::network::tcp::TcpListener::listen(args.addr(), args.server_id)
                .expect("failed to create listener");
            abd_example::server::run_server::<_, _, OwnedWritePerm, OwnedReadPerm>(
                &server_ids,
                args.server_id,
                listener,
            );
        }
    }
}
