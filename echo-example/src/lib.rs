use std::sync::Arc;

use rand::distr::Alphanumeric;
use rand::distr::SampleString;
use rand::rng;

use vstd::atomic::PAtomicU64;
use vstd::prelude::*;

use verdist::network::channel::BufChannel;
use verdist::network::channel::Channel;
use verdist::network::channel::Connector;
use verdist::network::error::ConnectError;

use specs::echo::EchoClient as _;

use echo::channel::ChannelInv;
use echo::client::EchoClient;

pub mod cli;
pub mod config;
pub mod error;
pub mod invariant;

use cli::ClientArgs;
use error::Error;
use invariant::get_invariant_state;

verus! {

fn connect<C, Conn>(
    connector: &Conn,
    client_id: u64,
    #[allow(unused_variables)]
    state_inv: &Tracked<Arc<echo::invariants::StateInvariant>>,
) -> (r: Result<BufChannel<C>, ConnectError>) where
    Conn: Connector<C>,
    C: Channel<
        Id = (u64, u64),
        K = ChannelInv,
        R = echo::proto::Response,
        S = echo::proto::Request,
    >,

    ensures
        r is Ok ==> {
            let chan = r->Ok_0;
            &&& chan.constant().request_map_id
                == state_inv@.constant().request_map_ids.request_auth_id
            &&& chan.spec_id().0 == client_id
        },
{
    let ghost constant = ChannelInv {
        request_map_id: state_inv@.constant().request_map_ids.request_auth_id,
    };
    let channel = connector.connect(
        client_id,
        |_connector, _client_id| -> (x: Ghost<ChannelInv>)
            ensures
                x == constant,
            { Ghost(constant) },
    )?;
    assume(channel.spec_id().0 == client_id);  // TODO(verdist/connector): connector spec is lacking
    Ok(BufChannel::new(channel))
}

pub fn run_client<C, Conn>(args: ClientArgs, connector: &Conn) -> Result<(), Error> where
    Conn: Connector<C> + Send + Sync,
    C: Channel<
        K = echo::channel::ChannelInv,
        R = echo::proto::Response,
        S = echo::proto::Request,
        Id = (u64, u64),
    >,
 {
    let (request_ctr, request_ctr_perm) = PAtomicU64::new(0);

    #[allow(unused)]
    let (request_ctr_token, state_inv) = get_invariant_state(args.client_id, request_ctr_perm);

    let channel = connect(connector, args.client_id, &state_inv)?;

    let mut client = EchoClient::new(
        channel,
        args.client_id,
        request_ctr,
        request_ctr_token,
        state_inv,
    );

    for _ in 0..args.n_ops {
        let input = generate_string(args.payload_size);
        vlib::vdebug!(client_id = args.client_id, %input, "sending");
        match client.echo(input) {
            Ok(output) => {
                assert(input == output);
                vlib::vdebug!(client_id = args.client_id, %output, "output == input");
            },
            Err(e) => {
                vlib::vprintln!("echo failed: {e:?}");
                return Err(e.into());
            },
        }
    }

    Ok(())
}

#[verifier::external_body]
fn generate_string(len: usize) -> String {
    Alphanumeric.sample_string(&mut rng(), len)
}

} // verus!
pub mod server {
    use echo::channel::ChannelInv;
    use echo::proto::Request;
    use echo::proto::Response;
    use echo::server::create_server;
    use echo::server::create_service;

    use std::sync::Arc;
    use verdist::network::channel::Channel;
    use verdist::network::channel::Listener;
    use verdist::network::channel::RawFdChannel;
    use verdist::network::channel::RawFdListener;

    // Why is this unverified:
    // - minor: no support for tracing
    // - major: verus does not support scoped threads (see verdist::service::Server::run)
    pub fn spawn_server<L, C>(server_id: u64, listener: L, num_threads: usize)
    where
        L: Listener<C> + Send + Sync + 'static,
        C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>
            + Send
            + Sync
            + 'static,
    {
        let (server, raw_receivers) = create_server::<_, _>(server_id, listener, num_threads);
        let server = Arc::new(server);
        std::thread::spawn(move || {
            vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

            server.run(raw_receivers);
        });
    }

    pub fn run_server<L, C>(server_id: u64, listener: L, num_threads: usize)
    where
        L: Listener<C> + Sync,
        C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    {
        let (server, raw_receivers) = create_server::<_, _>(server_id, listener, num_threads);
        vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

        server.run(raw_receivers);
    }

    /// Same as `run_server`, but drives the server with `Server::run_epoll` (real epoll-driven
    /// blocking, see §9/§10 of Performance.md) instead of `Server::run`'s backoff-based polling.
    /// Only usable with fd-backed networks (TCP/UDP) -- the in-process modelled network has no
    /// real fd, so it keeps using `run_server`.
    pub fn run_server_epoll<L, C>(server_id: u64, listener: L, num_threads: usize)
    where
        L: RawFdListener<C> + Sync,
        C: RawFdChannel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    {
        let (server, raw_receivers) = create_server::<_, _>(server_id, listener, num_threads);
        vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

        server.run_epoll(raw_receivers);
    }

    /// Same role as `run_server_epoll`, but for `udp_muxed`'s backends specifically -- see
    /// `verdist::network::udp_muxed::run_epoll`'s doc for why this backend needs its own driver
    /// (no real per-channel fd to register with `mio`) rather than `Server::run_epoll` itself.
    pub fn run_server_epoll_udp_muxed(
        server_id: u64,
        listener: verdist::network::udp_muxed::MuxedListener<Request, Response>,
        num_threads: usize,
    ) {
        let (server, raw_receivers) = create_server::<_, _>(server_id, listener, num_threads);
        vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

        verdist::network::udp_muxed::run_epoll(&server, raw_receivers);
    }

    /// `udp_ephemeral`'s driver has no `Listener`/`Channel`/shard machinery at all -- it takes the
    /// bare `EchoService` directly (see `verdist::network::udp_ephemeral::run_ephemeral`'s doc) and
    /// blocks forever running `num_router_threads`-many independent recv->handle->reply loops.
    /// `--num-threads` has no meaning here; the only concurrency knob is `num_router_threads`.
    pub fn run_server_ephemeral(server_id: u64, addr: std::net::SocketAddr, num_router_threads: usize) {
        let service = create_service(server_id);
        vlib::veprintln!("[server|{:>3}]: starting (ephemeral)", server_id);

        verdist::network::udp_ephemeral::run_ephemeral(addr, service, num_router_threads)
            .expect("run_ephemeral: error");
    }
}
