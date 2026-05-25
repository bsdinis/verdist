use std::sync::Arc;

use rand::{
    distr::{Alphanumeric, SampleString},
    rng,
};

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
pub mod error;
pub mod invariant;
pub mod server;

use cli::Args;
use error::Error;
use invariant::get_invariant_state;

verus! {

pub assume_specification[ std::time::Duration::from_millis ](millis: u64) -> std::time::Duration
;

const REQUEST_LATENCY_DEFAULT_MS: u64 = 100;

const REQUEST_STDDEV_DEFAULT_MS: u64 = 200;

fn connect<C, Conn>(
    args: &Args,
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
    if !args.no_delay {
        channel.add_latency(
            std::time::Duration::from_millis(REQUEST_LATENCY_DEFAULT_MS),
            std::time::Duration::from_millis(REQUEST_STDDEV_DEFAULT_MS),
        );
    }
    Ok(BufChannel::new(channel))
}

pub fn run_client<C, Conn, 'a>(args: Args, connector: &Conn) -> Result<(), Error> where
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
        let output_res = client.echo(input);
        if let Ok(output) = output_res {
            assert(input == output);
            vlib::vprintln!("output == input: {output}");
        }
    }

    Ok(())
}

#[verifier::external_body]
fn generate_string(len: usize) -> String {
    Alphanumeric.sample_string(&mut rng(), len)
}

} // verus!
