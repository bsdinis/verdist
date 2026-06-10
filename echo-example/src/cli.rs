use clap::Parser;
use vstd::prelude::*;

pub const SERVER_LISTEN_ADDR_DEFAULT: &str = "127.0.0.1:6432";

#[derive(serde::Deserialize, serde::Serialize, clap::ValueEnum, Clone, Copy, Default, Debug)]
#[serde(rename_all = "lowercase")]
pub enum NetworkType {
    /// Run a modelled network
    ///
    /// This will spawn the server and client in the same process, communicating over in-memory channels
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
    /// How many operations to do
    #[arg(long, default_value_t = 3)]
    pub n_ops: u64,

    /// Id of the client
    #[arg(long, default_value_t = 1)]
    pub client_id: u64,

    /// IP client will bind to
    #[arg(long, default_value = "127.0.0.1")]
    pub client_addr: std::net::IpAddr,

    /// Id of the server (only meaningful when the network is modelled)
    #[arg(long, default_value_t = 42)]
    pub server_id: u64,

    /// IP:port address server is listening for connections on
    #[arg(long, default_value = SERVER_LISTEN_ADDR_DEFAULT)]
    pub server_addr: std::net::SocketAddr,

    /// What network type to run
    #[arg(long, value_enum, default_value_t)]
    pub network: NetworkType,

    #[arg(short, long)]
    pub config: Option<std::path::PathBuf>,
}

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
pub struct ServerArgs {
    /// Id of the server
    #[arg(long, default_value_t = 42)]
    pub server_id: u64,

    /// IP:port address server will listen for connections on
    #[arg(long, default_value = SERVER_LISTEN_ADDR_DEFAULT)]
    pub server_addr: std::net::SocketAddr,

    /// What network type to run
    #[arg(long, value_enum, default_value_t)]
    pub network: NetworkType,

    #[arg(short, long)]
    pub config: Option<std::path::PathBuf>,
}

verus! {

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExClientArgs(ClientArgs);

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExServerArgs(ServerArgs);

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExNetworkType(NetworkType);

impl ClientArgs {
    #[verifier::external_body]
    pub fn apply_config(self) -> Result<Self, String> {
        let mut mself = self;
        if let Some(config_path) = mself.config.as_ref() {
            let config = crate::config::Config::parse(config_path)?;
            if let Some(n_ops) = config.n_ops {
                mself.n_ops = n_ops;
            }
            if let Some(client_addr) = config.client_addr {
                mself.client_addr = client_addr;
            }
            if let Some(server_addr) = config.server_addr {
                mself.server_addr = server_addr;
            }
            mself.client_id = config.client_id;
            mself.server_id = config.server_id;
            mself.network = config.network;
        }
        Ok(mself)
    }
}

impl ServerArgs {
    #[verifier::external_body]
    pub fn apply_config(self) -> Result<Self, String> {
        let mut mself = self;
        if let Some(config_path) = mself.config.as_ref() {
            let config = crate::config::Config::parse(config_path)?;
            mself.server_id = config.server_id;
            mself.network = config.network;
            if let Some(server_addr) = config.server_addr {
                mself.server_addr = server_addr;
            }
        }
        Ok(mself)
    }
}

} // verus!
