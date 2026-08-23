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
        Ok(
            ServerArgs {
                server_id: args.server_id,
                // `0` is not a valid thread count -- treat it the same as "unset" rather than
                // handing Server::new a value that violates its `num_shards > 0` precondition.
                num_threads: args.num_threads.filter(|n| *n != 0).or(
                    config.num_threads.filter(|n| *n != 0),
                ).unwrap_or_else(default_num_threads),
                network: config.network,
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
