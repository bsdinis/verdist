use clap::Parser;
use vstd::prelude::*;

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
pub struct Args {
    #[arg(short, long, default_value_t = 5)]
    pub n_servers: u64,

    #[arg(long, default_value_t = 3)]
    pub n_reads: u64,

    #[arg(long, default_value_t = 2)]
    pub n_writes: u64,

    #[arg(long)]
    pub no_delay: bool,

    #[arg(long, default_value_t = 1)]
    pub client_id: u64,
}

verus! {

#[allow(unused)]
#[verifier::external_type_specification]
pub struct ExArgs(crate::cli::Args);

} // verus!
