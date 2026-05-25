pub mod modelled {
    use abd::proto::Request;
    use abd::proto::Response;
    use abd::server::create_server;
    use specs::register::OwnedReadPerm;
    use specs::register::OwnedWritePerm;

    use std::sync::Arc;
    use verdist::network::modelled::ModelledConnector;

    // Why is this unverified:
    // - minor: no support for tracing
    // - major: verus does not support threads
    // TODO: make this take in a listener
    pub fn run_server(server_id: u64) -> ModelledConnector<Response, Request> {
        let (listener, connector) = verdist::network::modelled::listen_channel(server_id);
        std::thread::spawn(move || {
            let server = Arc::new(create_server::<_, _, OwnedWritePerm, OwnedReadPerm>(
                server_id, listener,
            ));
            vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

            std::thread::scope(|s| {
                for _ in 0..5 {
                    let serv = server.clone();
                    s.spawn(move || while serv.poll() {});
                }
            });
        });

        connector
    }
}
