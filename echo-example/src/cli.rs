use clap::Parser;
use vstd::prelude::*;

#[derive(clap::ValueEnum, Clone, Copy, Default, Debug)]
pub(crate) enum NetworkType {
    #[default]
    Modelled,
    Tcp,
    Udp,
}

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
pub(crate) struct Args {
    #[arg(long, default_value_t = 3)]
    pub(crate) n_ops: u64,

    #[arg(long)]
    pub(crate) no_delay: bool,

    #[arg(long, default_value_t = 1)]
    pub(crate) client_id: u64,

    #[arg(long, value_enum, default_value_t)]
    pub(crate) network: NetworkType,
}

verus! {

#[allow(unused)]
#[verifier::external_type_specification]
pub(crate) struct ExArgs(crate::cli::Args);

} // verus!
