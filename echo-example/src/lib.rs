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

const REQUEST_LATENCY_DEFAULT_MS: u64 = 100;

const REQUEST_STDDEV_DEFAULT_MS: u64 = 200;

fn connect<C, Conn>(
    args: &ClientArgs,
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
    let mut channel = connector.connect(
        client_id,
        |_connector, _client_id| -> (x: Ghost<ChannelInv>)
            ensures
                x == constant,
            { Ghost(constant) },
    )?;
    assume(channel.spec_id().0 == client_id);  // TODO(verdist/connector): connector spec is lacking
    if args.delay {
        channel.add_latency(
            std::time::Duration::from_millis(REQUEST_LATENCY_DEFAULT_MS),
            std::time::Duration::from_millis(REQUEST_STDDEV_DEFAULT_MS),
        );
    }
    Ok(BufChannel::new(channel))
}

pub fn run_client<C, Conn, 'a>(args: ClientArgs, connector: &Conn) -> Result<(), Error> where
    Conn: Connector<C> + Send + Sync,
    C: Channel<
        K = echo::channel::ChannelInv,
        R = echo::proto::Response,
        S = echo::proto::Request,
        Id = (u64, u64),
    >,
    C: Sync + Send,
 {
    let (request_ctr, request_ctr_perm) = PAtomicU64::new(0);

    #[allow(unused)]
    let (request_ctr_token, state_inv) = get_invariant_state(args.client_id, request_ctr_perm);

    let channel = connect(&args, connector, args.client_id, &state_inv)?;

    let mut client = EchoClient::new(
        channel,
        args.client_id,
        request_ctr,
        request_ctr_token,
        state_inv,
    );

    for _ in 0..args.n_ops {
        let input = generate_string(32);
        vlib::veprintln!("[client|{:>3}]: sending {input}", args.client_id);
        match client.echo(input) {
            Ok(output) => {
                assert(input == output);
                vlib::vprintln!("[client|{:>3}]: output == input {output}", args.client_id);
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

    use std::sync::Arc;
    use verdist::network::channel::Channel;
    use verdist::network::channel::Listener;

    // Why is this unverified:
    // - minor: no support for tracing
    // - major: verus does not support threads
    pub fn spawn_server<L, C>(server_id: u64, listener: L)
    where
        L: Listener<C> + Send + Sync + 'static,
        C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>
            + Send
            + Sync
            + 'static,
    {
        let server = Arc::new(create_server::<_, _>(server_id, listener));
        std::thread::spawn(move || {
            vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

            std::thread::scope(|s| {
                s.spawn(move || while server.poll() {});
            });
        });
    }

    pub fn run_server<L, C>(server_id: u64, listener: L)
    where
        L: Listener<C>,
        C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    {
        let server = create_server::<_, _>(server_id, listener);
        vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

        while server.poll() {}
    }
}
