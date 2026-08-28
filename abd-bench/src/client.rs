use polars::prelude::*;
use specs::register::OwnedReadPerm;
use specs::register::OwnedWritePerm;
use vstd::atomic::PAtomicU64;
use vstd::resource::ghost_var::GhostVar;

use verdist::network::channel::BufChannel;
use verdist::network::channel::Channel;
use verdist::network::channel::Connector;
use verdist::network::error::ConnectError;
use verdist::pool::FlawlessPool;

use specs::register::LinRegisterClient;

use abd::channel::ChannelInv;
use abd::client::AbdPool;

use crate::cli::ClientArgs;
use crate::error::Error;
use crate::invariant::fake_ghost;
use crate::invariant::fake_tracked;
use crate::invariant::get_invariant_state;

fn connect<C, Conn>(connector: &Conn, client_id: u64) -> Result<BufChannel<C>, ConnectError>
where
    Conn: Connector<C>,
    C: Channel<Id = (u64, u64), K = ChannelInv, R = abd::proto::Response, S = abd::proto::Request>,
{
    let channel = connector.connect(client_id, |_connector, _client_id| fake_ghost())?;
    Ok(BufChannel::new(channel))
}

fn connect_all<C, Conn>(
    connectors: &[Conn],
    client_id: u64,
) -> Result<Vec<BufChannel<C>>, ConnectError>
where
    Conn: Connector<C>,
    C: Channel<Id = (u64, u64), K = ChannelInv, R = abd::proto::Response, S = abd::proto::Request>,
{
    let mut v = Vec::with_capacity(connectors.len());
    for connector in connectors {
        let conn = connect(connector, client_id)?;
        v.push(conn);
    }

    Ok(v)
}

type ClientRunError =
    Error<OwnedWritePerm, GhostVar<Option<u64>>, OwnedReadPerm, GhostVar<Option<u64>>>;

pub fn run_client<C, Conn>(args: ClientArgs, connectors: &[Conn]) -> Result<(), ClientRunError>
where
    Conn: Connector<C> + Send + Sync,
    C: Channel<
        K = abd::channel::ChannelInv,
        R = abd::proto::Response,
        S = abd::proto::Request,
        Id = (u64, u64),
    >,
{
    let (client_ctr, _) = PAtomicU64::new(0);
    let (request_ctr, _) = PAtomicU64::new(0);
    let (client_ctr_token, request_ctr_token, state_inv, _) =
        get_invariant_state::<OwnedWritePerm, OwnedReadPerm>();

    let pool = connect_all(connectors, args.client_id)?;
    vlib::veprintln!("[client|{:>3}]: finished connecting\n", args.client_id);
    let pool = FlawlessPool::new(pool);

    // let tracked mut register_perm = register_perm.get();
    let mut client = AbdPool::<_, OwnedWritePerm, OwnedReadPerm>::new(
        pool,
        args.client_id,
        client_ctr,
        client_ctr_token,
        request_ctr,
        request_ctr_token,
        state_inv,
    );

    if let Some(start) = args.start {
        while std::time::SystemTime::now() < start {}
    }

    vlib::veprintln!("[client|{:>3}]: starting\n", args.client_id);

    let begin = std::time::Instant::now();
    let mut times = Vec::with_capacity(10_000);
    let mut n = 0;
    while begin.elapsed() < args.duration {
        match args.op {
            crate::cli::Operation::Read => {
                let op_begin = std::time::Instant::now();
                client.read(fake_tracked()).expect("read error");
                times.push(op_begin.elapsed());
            }
            crate::cli::Operation::Write => {
                let op_begin = std::time::Instant::now();
                client.write(Some(n), fake_tracked()).expect("write error");
                times.push(op_begin.elapsed());
                n += 1;
            }
        }
    }

    process_results(times, args.duration);

    Ok(())
}

fn process_results(times: Vec<std::time::Duration>, total_duration: std::time::Duration) {
    let times: Vec<f64> = times
        .into_iter()
        .map(|x| x.as_secs_f64() * 1_000_000f64)
        .collect();
    let s = Series::new("times".into(), &times);
    let tput: f64 = (s.len() as f64) / (total_duration.as_secs_f64() * 1_000f64);
    let max: f64 = s.max().unwrap().unwrap();
    let min: f64 = s.min().unwrap().unwrap();
    let mean = s.mean().unwrap();
    let median = s.median().unwrap();
    let quantiles = s
        .quantiles_reduce(&[0.25, 0.75, 0.90, 0.95, 0.99], QuantileMethod::Linear)
        .unwrap();
    println!("min:    {min}us");
    println!("max:    {max}us");
    println!("mean:   {mean}us");
    println!("median: {median}us");
    println!("throughtput: {tput}KOps/s");
    println!("quantiles: {quantiles:?}");
}
