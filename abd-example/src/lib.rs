use vstd::atomic::PAtomicU64;
#[cfg(verus_only)]
use vstd::logatom::ReadLinearizer;
#[cfg(verus_only)]
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::resource::ghost_var::GhostVar;
#[cfg(verus_only)]
use vstd::resource::ghost_var::GhostVarAuth;

use verdist::network::channel::BufChannel;
use verdist::network::channel::Channel;
use verdist::network::channel::Connector;
use verdist::network::error::ConnectError;
#[cfg(verus_only)]
use verdist::pool::ConnectionPool;
use verdist::pool::FlawlessPool;

use specs::register::LinRegisterClient;
use specs::register::OwnedReadPerm;
use specs::register::OwnedWritePerm;
#[cfg(verus_only)]
use specs::register::RegisterRead;
#[cfg(verus_only)]
use specs::register::RegisterWrite;

use abd::channel::ChannelInv;
use abd::client::AbdPool;

pub mod cli;
pub mod config;
pub mod error;
pub mod invariant;

use cli::ClientArgs;
use error::Error;
use invariant::get_invariant_state;

verus! {

fn connect<C, Conn>(connector: &Conn, client_id: u64) -> Result<BufChannel<C>, ConnectError> where
    Conn: Connector<C>,
    C: Channel<Id = (u64, u64), K = ChannelInv, R = abd::proto::Response, S = abd::proto::Request>,
 {
    let channel = connector.connect(
        client_id,
        |_connector, _client_id|
            Ghost(
                ChannelInv {
                    commitment_id: arbitrary(),
                    request_map_id: arbitrary(),
                    server_locs: arbitrary(),
                    server_tokens_id: arbitrary(),
                },
            ),
    )?;
    Ok(BufChannel::new(channel))
}

fn connect_all<C, Conn>(connectors: &[Conn], client_id: u64) -> (r: Result<
    Vec<BufChannel<C>>,
    ConnectError,
>) where
    Conn: Connector<C>,
    C: Channel<Id = (u64, u64), K = ChannelInv, R = abd::proto::Response, S = abd::proto::Request>,

    ensures
        r is Ok ==> {
            let v = r->Ok_0;
            &&& connectors.len() == v.len()
            &&& forall|idx| 0 <= idx < v@.len() ==> #[trigger] v@[idx].spec_id().0 == client_id
            &&& forall|i, j|
                0 <= i < j < v@.len() ==> #[trigger] v@[i].spec_id() != #[trigger] v@[j].spec_id()
        },
{
    let mut v = Vec::with_capacity(connectors.len());
    for connector in connectors.iter() {
        let conn = connect(connector, client_id)?;
        v.push(conn);
    }

    proof {
        admit();  // XXX(assume): this is trivial but seems like something should be able to get
    }
    Ok(v)
}

pub fn run_client<C, Conn, 'a>(args: ClientArgs, connectors: &[Conn]) -> Result<
    (),
    Error<OwnedWritePerm, GhostVar<Option<u64>>, OwnedReadPerm, GhostVar<Option<u64>>>,
> where
    Conn: Connector<C> + Send + Sync,
    C: Channel<
        K = abd::channel::ChannelInv,
        R = abd::proto::Response,
        S = abd::proto::Request,
        Id = (u64, u64),
    >,
    C: Sync + Send,

    requires
        connectors.len() == args.servers@.len(),
        args.servers@.len() > 0,
{
    let (client_ctr, client_ctr_perm) = PAtomicU64::new(0);
    let (request_ctr, request_ctr_perm) = PAtomicU64::new(0);
    let server_ids = Ghost(args.servers@.dom());
    #[allow(unused)]
    let (client_ctr_token, request_ctr_token, state_inv, register_perm) = get_invariant_state::<
        OwnedWritePerm,
        OwnedReadPerm,
    >(&server_ids, args.client_id, client_ctr_perm, request_ctr_perm);

    let pool = connect_all(connectors, args.client_id)?;
    vlib::veprintln!("[client|{:>3}]: finished connecting\n", args.client_id);
    let pool = FlawlessPool::new(pool);
    assert(pool.spec_len() == connectors.len());

    // TODO(connector): connector trait should preserve the ids
    assume(forall|cid| #[trigger]
        pool.spec_channels().dom().contains(cid) ==> {
            let c = pool.spec_channels()[cid];
            &&& cid.0 == args.client_id
            &&& state_inv.constant().server_locs.contains_key(cid.1)
            &&& state_inv.constant().request_map_ids.request_auth_id == c.constant().request_map_id
            &&& state_inv.constant().commitments_ids.commitment_id == c.constant().commitment_id
            &&& state_inv.constant().server_tokens_id == c.constant().server_tokens_id
            &&& state_inv.constant().server_locs == c.constant().server_locs
        });

    let tracked mut register_perm = register_perm.get();
    let mut client = AbdPool::<_, OwnedWritePerm, OwnedReadPerm>::new(
        pool,
        args.client_id,
        client_ctr,
        client_ctr_token,
        request_ctr,
        request_ctr_token,
        state_inv,
    );
    assert(client.inv()) by { abd::client::lemma_inv(client) };

    let mut remaining_writes = args.n_writes;
    let mut remaining_reads = if args.n_reads > 0 {
        args.n_reads
    } else {
        1
    };
    assume(remaining_writes + remaining_reads < usize::MAX);  // XXX: arithmetic overflow

    // do the first read
    let tracked perm;
    proof {
        let tracked (_, mut dummy) = GhostVarAuth::new(None);
        tracked_swap(&mut register_perm, &mut dummy);
        perm = dummy;
    }
    let tracked read_perm = OwnedReadPerm { register: perm };
    #[allow(unused)]
    let (v, ts, orig_view) = match client.read(Tracked(read_perm)) {
        Ok((v, ts, view)) => {
            vlib::veprintln!("[client|{:>3}]: read completed: {:?} @ {:?}\n", args.client_id, v, ts);
            (v, ts, view)
        },
        Err(e) => {
            vlib::veprintln!("[client|{:>3}]: read error: {}", args.client_id, e);
            return Err(Error::Empty);
        },
    };
    let tracked mut orig_view = orig_view.get();
    #[allow(unused_variables)]
    let mut expected_value = v;
    assert(orig_view@ == v);
    proof {
        tracked_swap(&mut register_perm, &mut orig_view);
    }

    assert(register_perm@ == expected_value);
    remaining_reads -= 1;
    let mut last_was_read = true;
    let ghost register_perm_id = register_perm.id();
    #[allow(unused_variables)]
    while remaining_writes + remaining_reads > 0
        invariant
            register_perm@ == expected_value,
            register_perm.id() == register_perm_id,
            remaining_writes + remaining_reads < usize::MAX,
            client.inv(),
            client.register_loc() == register_perm.id(),
        decreases remaining_writes + remaining_reads,
    {
        let tracked perm;
        proof {
            let tracked (_, mut dummy) = GhostVarAuth::new(None);
            tracked_swap(&mut register_perm, &mut dummy);
            perm = dummy;
        }
        #[allow(unused_assignments)]
        if (last_was_read && remaining_writes > 0) || remaining_reads == 0 {
            let value = Some(remaining_writes);
            let tracked write_perm = OwnedWritePerm { register: perm, value };
            let write_view = match client.write(value, Tracked(write_perm)) {
                Ok(comp) => {
                    vlib::veprintln!("[client|{:>3}]: write completed: {:?}\n", args.client_id, value);
                    comp
                },
                Err(e) => {
                    vlib::veprintln!("[client|{:>3}]: write error: {}", args.client_id, e);
                    return Err(Error::Empty);
                },
            };
            let tracked mut write_view = write_view.get();
            assert(write_view@ == value);
            proof {
                tracked_swap(&mut register_perm, &mut write_view);
            }
            expected_value = value;
            last_was_read = false;
            remaining_writes -= 1;
        } else {
            let tracked read_perm = OwnedReadPerm { register: perm };
            let (v, ts, read_view) = match client.read(Tracked(read_perm)) {
                Ok((v, ts, comp)) => {
                    vlib::veprintln!("[client|{:>3}]: read completed: {:?} @ {:?}\n", args.client_id, v, ts);
                    (v, ts, comp)
                },
                Err(e) => {
                    vlib::veprintln!("[client|{:>3}]: read error: {}", args.client_id, e);
                    return Err(Error::Empty);
                },
            };
            let tracked mut read_view = read_view.get();
            assert(read_view@ == v);
            assert(read_view@ == expected_value);
            proof {
                tracked_swap(&mut register_perm, &mut read_view);
            }
            last_was_read = true;
            remaining_reads -= 1;
        }
    }

    Ok(())
}

} // verus!
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
    // - major: verus does not support threads
    pub fn spawn_server<L, C, ML, RL>(server_ids: &HashSet<u64>, server_id: u64, listener: L)
    where
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
        let server = Arc::new(create_server::<_, _, ML, RL>(
            server_ids, server_id, listener,
        ));
        std::thread::spawn(move || {
            vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

            std::thread::scope(|s| {
                s.spawn(move || while server.poll() {});
            });
        });
    }

    pub fn run_server<L, C, ML, RL>(server_ids: &HashSet<u64>, server_id: u64, listener: L)
    where
        L: Listener<C>,
        C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
        ML: MutLinearizer<RegisterWrite>,
        RL: ReadLinearizer<RegisterRead>,
    {
        let server = create_server::<_, _, ML, RL>(server_ids, server_id, listener);
        vlib::veprintln!("[server|{:>3}]: starting", server.server_id());

        while server.poll() {}
    }
}
