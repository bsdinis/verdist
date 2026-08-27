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

#[derive(serde::Deserialize, serde::Serialize, clap::ValueEnum, Clone, Copy, Debug, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum Operation {
    Read,
    Write,
}

#[derive(serde::Deserialize, serde::Serialize, Clone, Copy, Debug)]
pub struct ServerConfig {
    pub id: u64,
    pub addr: Option<std::net::SocketAddr>,
}

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
pub struct ClientParsedArgs {
    /// Id of the client
    #[arg(long)]
    pub client_id: Option<u64>,

    /// IP client will bind to
    #[arg(long)]
    pub client_addr: Option<std::net::IpAddr>,

    #[arg(short, long)]
    pub config: std::path::PathBuf,

    #[arg(short, long)]
    pub op: Operation,

    #[arg(short, long)]
    pub duration: humantime::Duration,

    #[arg(short, long)]
    pub start: Option<humantime::Timestamp>,

    /// Number of request-processing worker threads each in-process (modelled-network) server
    /// should spawn. Defaults to `available_parallelism() - 1`, so as not to oversubscribe cores
    /// with busy-spinning threads.
    #[arg(long)]
    pub num_threads: Option<usize>,
}

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
pub struct ServerParsedArgs {
    /// Id of the server
    #[arg(long)]
    pub server_id: u64,

    #[arg(short, long)]
    pub config: std::path::PathBuf,
}

pub struct ClientArgs {
    /// Id of the client
    pub client_id: u64,

    /// IP client will bind to
    pub client_addr: std::net::IpAddr,

    /// What network type to run
    pub network: NetworkType,

    /// Servers in the system
    pub servers: HashMap<u64, ServerConfig>,

    pub op: Operation,

    pub duration: std::time::Duration,

    pub start: Option<std::time::SystemTime>,

    /// Number of request-processing worker threads each in-process (modelled-network) server
    /// should spawn.
    pub num_threads: usize,
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

pub struct ServerArgs {
    /// Id of the server
    pub server_id: u64,

    /// What network type to run
    pub network: NetworkType,

    /// Which register backend to use
    pub backend: RegisterBackend,

    /// Servers in the system
    pub servers: HashMap<u64, ServerConfig>,
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
                client_id: args.client_id.or(config.client_id).unwrap_or(42),
                client_addr: args.client_addr.or(config.client_addr).unwrap_or(
                    IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
                ),
                network: config.network,
                servers: config.servers,
                op: args.op,
                start: args.start.map(|x| x.into()),
                duration: args.duration.into(),
                // `0` is not a valid thread count, and `create_server`'s `num_threads + 2 <=
                // vlib::reclaim::atomic_ptr::INDEX_SPACE` precondition (needed for the
                // `Lockfree` backend's `EpochAtomicPtr` slot sizing, and required
                // unconditionally since a `requires` can't branch on the runtime `backend`
                // choice) rules out anything within 2 of `usize::MAX` too -- treat either as
                // "unset" rather than handing `create_server` a value that violates its
                // precondition.
                num_threads: args.num_threads.filter(
                    |n| { *n != 0 && *n <= vlib::reclaim::atomic_ptr::INDEX_SPACE - 2 },
                ).or(
                    config.num_threads.filter(
                        |n| { *n != 0 && *n <= vlib::reclaim::atomic_ptr::INDEX_SPACE - 2 },
                    ),
                ).unwrap_or_else(default_num_threads),
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
        Ok(
            ServerArgs {
                server_id: args.server_id,
                network: config.network,
                backend: config.backend,
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
