use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};

use clap::Parser;
use vstd::prelude::*;

pub const SERVER_LISTEN_ADDR_DEFAULT: &str = "127.0.0.1:6432";

#[derive(
    serde::Deserialize, serde::Serialize, clap::ValueEnum, Clone, Copy, Default, Debug, PartialEq,
)]
#[serde(rename_all = "lowercase")]
pub enum NetworkType {
    /// Run a modelled network
    ///
    /// This will spawn the servers and client in the same process, communicating over in-memory channels
    #[default]
    Modelled,

    /// Run with TCP connections
    Tcp,

    /// Run with UDP connections
    Udp,

    /// Run with TCP connections over io_uring instead of blocking read/write syscalls (see
    /// `verdist::network::io_uring_tcp`'s design doc, `claude-files/io_uring_design.md`)
    #[serde(rename = "io_uring_tcp")]
    #[value(name = "io_uring_tcp")]
    IoUringTcp,

    /// Run with UDP connections over io_uring instead of blocking recv/send syscalls (see
    /// `verdist::network::io_uring_udp`)
    #[serde(rename = "io_uring_udp")]
    #[value(name = "io_uring_udp")]
    IoUringUdp,
}

/// Which register backend the server should build (design doc
/// `claude-files/monotonic_register_backend_switch.md`, section 5.5/6). Wired exactly like
/// `NetworkType` above (same derives, same `rename_all`), but server-only -- it never reaches
/// `ClientArgs`, since the client's own protocol code has no use for it.
#[derive(
    serde::Deserialize, serde::Serialize, clap::ValueEnum, Clone, Copy, Default, Debug, PartialEq,
)]
#[serde(rename_all = "lowercase")]
pub enum RegisterBackend {
    /// The original `MonotonicRegister`: an `RwLock`-guarded register (exclusive writers, shared
    /// readers). See `abd/src/server/register.rs`.
    #[default]
    Locked,

    /// The lock-free `EpochMonotonicRegister`: epoch-reclaimed snapshots, readers never block
    /// behind a writer. See `abd/src/server/lockfree.rs`.
    Lockfree,
}

impl RegisterBackend {
    /// Convert to `abd`'s own (Verus-native) `RegisterBackend`, the type `create_server` actually
    /// takes. A plain associated fn rather than a `From` impl: `Self` and
    /// `abd::server::RegisterBackend` each live in a different crate from `From`'s definition, so
    /// neither direction of `impl From<..> for ..` between them would satisfy the orphan rules
    /// here.
    pub fn to_abd_backend(self) -> abd::server::RegisterBackend {
        match self {
            RegisterBackend::Locked => abd::server::RegisterBackend::Locked,
            RegisterBackend::Lockfree => abd::server::RegisterBackend::Lockfree,
        }
    }
}

#[derive(serde::Deserialize, serde::Serialize, Clone, Copy, Debug)]
pub struct ServerConfig {
    pub id: u64,
    pub addr: Option<std::net::SocketAddr>,
}

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
pub struct ClientParsedArgs {
    /// Number of reads to perform
    #[arg(long)]
    pub n_reads: Option<u64>,

    /// Number of writes to perform
    #[arg(long)]
    pub n_writes: Option<u64>,

    /// Id of the client
    #[arg(long)]
    pub client_id: Option<u64>,

    /// IP client will bind to
    #[arg(long)]
    pub client_addr: Option<std::net::IpAddr>,

    #[arg(short, long)]
    pub config: std::path::PathBuf,
}

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
pub struct ServerParsedArgs {
    /// Id of the server
    #[arg(long)]
    pub server_id: u64,

    /// Number of request-processing worker threads to spawn (in addition to one dedicated
    /// accept thread). Defaults to `available_parallelism() - 1`, so as not to oversubscribe
    /// cores with busy-spinning threads.
    #[arg(long)]
    pub num_threads: Option<usize>,

    /// Use mio/epoll-driven blocking instead of the default backoff-based polling loop
    /// (TCP/UDP only, ignored for the modelled network). See §9/§10 of Performance.md.
    #[arg(long, action = clap::ArgAction::SetTrue)]
    pub epoll: bool,

    /// Explicitly keep the default backoff-based polling loop -- present for symmetry with
    /// --epoll; omitting --epoll already means this.
    #[arg(long, action = clap::ArgAction::SetTrue)]
    pub no_epoll: bool,

    #[arg(short, long)]
    pub config: std::path::PathBuf,
}

pub struct ClientArgs {
    /// Number of reads to perform
    pub n_reads: u64,

    /// Number of writes to perform
    pub n_writes: u64,

    /// Id of the client
    pub client_id: u64,

    /// IP client will bind to
    pub client_addr: std::net::IpAddr,

    /// What network type to run
    pub network: NetworkType,

    /// Servers in the system
    pub servers: HashMap<u64, ServerConfig>,
}

pub struct ServerArgs {
    /// Id of the server
    pub server_id: u64,

    /// Number of request-processing worker threads to spawn
    pub num_threads: usize,

    /// What network type to run
    pub network: NetworkType,

    /// Which register backend to use
    pub backend: RegisterBackend,

    /// Use mio/epoll-driven blocking instead of the default backoff-based polling loop
    /// (TCP/UDP only, ignored for the modelled network)
    pub epoll: bool,

    /// Servers in the system
    pub servers: HashMap<u64, ServerConfig>,
}

/// `available_parallelism() - 1`, reserving one core for the dedicated accept thread so the
/// default doesn't oversubscribe cores with busy-spinning worker threads (see
/// `verdist::service::Server::run`).
pub fn default_num_threads() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(2)
        .saturating_sub(1)
        .max(1)
}

verus! {

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExNetworkType(NetworkType);

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExServerConfig(ServerConfig);

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExClientParsedArgs(ClientParsedArgs);

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExClientArgs(ClientArgs);

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExServerParsedArgs(ServerParsedArgs);

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExServerArgs(ServerArgs);

impl ClientArgs {
    #[verifier::external_body]
    pub fn parse() -> Result<Self, String> {
        let args = ClientParsedArgs::parse();
        let config = crate::config::Config::parse(args.config)?;
        Ok(
            ClientArgs {
                n_reads: args.n_reads.or(config.n_reads).unwrap_or(2),
                n_writes: args.n_writes.or(config.n_writes).unwrap_or(1),
                client_id: args.client_id.or(config.client_id).unwrap_or(42),
                client_addr: args.client_addr.or(config.client_addr).unwrap_or(
                    IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
                ),
                network: config.network,
                servers: config.servers,
            },
        )
    }
}

impl ServerArgs {
    #[verifier::external_body]
    pub fn parse() -> Result<Self, String> {
        let args = ServerParsedArgs::parse();
        let config = crate::config::Config::parse(args.config)?;
        if !config.servers.contains_key(&args.server_id) {
            return Err(
                format!("config: cannot find server {} in config (available servers: {:?})",
            args.server_id,
            config.servers.keys().collect::<Vec<_>>(),
            ),
            );
        }
        // `0` is not a valid thread count, and `create_server`'s `num_threads + 2 <=
        // vlib::reclaim::atomic_ptr::INDEX_SPACE` precondition (needed for the `Lockfree`
        // backend's `EpochAtomicPtr` slot sizing, and required unconditionally since a `requires`
        // can't branch on the runtime `backend` choice) rules out anything within 2 of
        // `usize::MAX` too -- treat either as "unset" rather than handing `create_server` a value
        // that violates its precondition.

        let valid_num_threads = |n: &usize|
            *n != 0 && *n <= vlib::reclaim::atomic_ptr::INDEX_SPACE - 2;
        Ok(
            ServerArgs {
                server_id: args.server_id,
                num_threads: args.num_threads.filter(valid_num_threads).or(
                    config.num_threads.filter(valid_num_threads),
                ).unwrap_or_else(default_num_threads),
                network: config.network,
                backend: config.backend,
                // --no-epoll always wins if both are (redundantly) given.
                epoll: args.epoll && !args.no_epoll,
                servers: config.servers,
            },
        )
    }

    #[verifier::external_body]
    pub fn addr(&self) -> std::net::SocketAddr {
        self.servers.get(&self.server_id).expect(
            "server args should always have their own server id (did you mannually construct the args?)",
        ).addr.expect("asked for server addr when the network is modelled")
    }
}

} // verus!
