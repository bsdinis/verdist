use clap::Parser;

use abd_example::cli::Args;
use abd_example::server;

fn main() {
    let args = Args::parse();

    if args.n_servers == 0 {
        eprintln!("need at least one server");
        return;
    }

    let connectors: Vec<_> = (0..args.n_servers)
        .map(server::modelled::run_server)
        .collect();

    abd_example::run_client(args, &connectors).expect("error");

    // let realtime_order = realtime(&trace);
    // println!("realtime ordering:\n{realtime_order:?}");
    // let part_order = partial(&trace);
    // println!("implied partial ordering:\n{part_order:?}");

    // if orders_agree(&realtime_order, &part_order) {
    // println!("partial orderings agree");
    // } else {
    // println!("partial orderings do not agree");
    // }
}
