use std::collections::HashMap;

use vstd::prelude::*;

use crate::cli::ServerConfig;

#[derive(serde::Serialize, serde::Deserialize, Clone, Default, Debug)]
pub struct ParsedConfig {
    /// How many read operations to do
    pub n_reads: Option<u64>,

    /// How many read operations to do
    pub n_writes: Option<u64>,

    /// Whether to introduce artificial delays
    pub delay: Option<bool>,

    /// Id of the client
    pub client_id: Option<u64>,

    /// IP client will bind to
    pub client_addr: Option<std::net::IpAddr>,

    /// Number of request-processing worker threads the server should spawn
    pub num_threads: Option<usize>,

    /// What network type to run
    pub network: crate::cli::NetworkType,

    /// Configuration of the servers
    pub server: Vec<ServerConfig>,
}

#[derive(Clone, Default, Debug)]
pub struct Config {
    /// How many read operations to do
    pub n_reads: Option<u64>,

    /// How many read operations to do
    pub n_writes: Option<u64>,

    /// Whether to introduce artificial delays
    pub delay: Option<bool>,

    /// Id of the client
    pub client_id: Option<u64>,

    /// IP client will bind to
    pub client_addr: Option<std::net::IpAddr>,

    /// Number of request-processing worker threads the server should spawn
    pub num_threads: Option<usize>,

    /// What network type to run
    pub network: crate::cli::NetworkType,

    /// Configuration of the servers
    pub servers: HashMap<u64, ServerConfig>,
}

impl ParsedConfig {
    fn parse<P: AsRef<std::path::Path>>(path: P) -> Result<Self, String> {
        let config_contents =
            std::fs::read_to_string(path).map_err(|e| format!("file error: {e:?}"))?;
        let config: ParsedConfig = toml::from_str(&config_contents)
            .map_err(|e| format!("toml: failed to parse: {e:?}"))?;
        if config.server.is_empty() {
            return Err("config: no servers specified".to_string());
        }
        // all servers must have an addr in a non-modelled network
        if config.network != crate::cli::NetworkType::Modelled {
            let servers_without_addr = config
                .server
                .iter()
                .filter_map(|conf| {
                    if conf.addr.is_none() {
                        Some(conf.id)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            if !servers_without_addr.is_empty() {
                return Err(format!("config: non-modelled network without fully specified server addresses (missing server addrs: {servers_without_addr:?})"));
            }
        }
        Ok(config)
    }
}

impl Config {
    pub fn parse<P: AsRef<std::path::Path>>(path: P) -> Result<Self, String> {
        let config = ParsedConfig::parse(path)?;
        let mut servers = HashMap::with_capacity(config.server.len());
        for server_conf in config.server {
            if servers.insert(server_conf.id, server_conf).is_some() {
                return Err(format!("config: duplicate server id {}", server_conf.id));
            }
        }
        Ok(Config {
            n_reads: config.n_reads,
            n_writes: config.n_writes,
            delay: config.delay,
            client_id: config.client_id,
            client_addr: config.client_addr,
            num_threads: config.num_threads,
            network: config.network,
            servers,
        })
    }
}

verus! {

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExConfig(Config);

} // verus!
