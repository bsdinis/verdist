use clap::Parser;
use vstd::prelude::*;

#[derive(clap::ValueEnum, Clone, Copy, Default, Debug)]
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

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
pub struct ClientArgs {
    /// Number of servers to spawn (only relevant when network is modelled)
    #[arg(short, long, default_value_t = 5)]
    pub n_servers: u64,

    /// Number of reads to perform
    #[arg(long, default_value_t = 3)]
    pub n_reads: u64,

    /// Number of writes to perform
    #[arg(long, default_value_t = 2)]
    pub n_writes: u64,

    /// Whether to introduce artificial delays
    #[arg(long)]
    pub delay: bool,

    /// Id of the client
    #[arg(long, default_value_t = 1)]
    pub client_id: u64,

    /// What network type to run
    #[arg(long, value_enum, default_value_t)]
    pub network: NetworkType,
}

verus! {

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExClientArgs(crate::cli::ClientArgs);

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExNetworkType(crate::cli::NetworkType);

} // verus!
