use echo::channel::ChannelInv;
use echo::proto::Request;
use echo::proto::Response;
use echo::server::create_server;

use std::sync::Arc;
use verdist::network::channel::Channel;
use verdist::network::channel::Listener;

// Why is this unverified:
// - minor: no support for tracing
// - major: verus does not support threads
pub fn run_server<L, C>(server_id: u64, listener: L)
where
    L: Listener<C> + Send + Sync + 'static,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv> + Send + Sync + 'static,
{
    let server = Arc::new(create_server::<_, _>(server_id, listener));
    // let (listener, connector) = verdist::network::modelled::listen_channel(server_id);
    std::thread::spawn(move || {
        vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

        std::thread::scope(|s| {
            s.spawn(move || while server.poll() {});
        });
    });
}
