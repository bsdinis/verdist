use vstd::prelude::*;

#[derive(serde::Serialize, serde::Deserialize, Clone, Copy, Default, Debug)]
pub struct Config {
    /// How many operations to do
    pub n_ops: Option<u64>,

    /// Whether to introduce artificial delays
    pub delay: Option<bool>,

    /// Id of the client
    pub client_id: u64,

    /// IP client will bind to
    pub client_addr: Option<std::net::IpAddr>,

    /// IP:port address server will listen for connections on
    pub server_addr: Option<std::net::SocketAddr>,

    /// Id of the server (only meaningful when the network is modelled)
    pub server_id: u64,

    /// What network type to run
    pub network: crate::cli::NetworkType,
}

impl Config {
    pub fn parse<P: AsRef<std::path::Path>>(path: P) -> Result<Self, String> {
        let config_contents =
            std::fs::read_to_string(path).map_err(|e| format!("file error: {e:?}"))?;
        let config: Config = toml::from_str(&config_contents)
            .map_err(|e| format!("toml: failed to parse: {e:?}"))?;
        config.validate()?;
        Ok(config)
    }

    fn validate(&self) -> Result<(), String> {
        if self.client_id == self.server_id {
            Err("config: `client_id` and `server_id` must be distinct".to_string())
        } else {
            Ok(())
        }
    }
}
verus! {

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExConfig(Config);

} // verus!
