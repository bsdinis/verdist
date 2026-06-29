# Verdist - proving distributed systems with Verus

This monorepo has:
- [`verdist`](./verdist): a framework/library for building verified distributed systems with Verus
- [`vlib`](./vlib): extensions to `vstd`, including assumed specifications on foreign crates (things that may one day be merged there -- or not)
- [`specs`](./specs): a small crate with specifications for distributed protocols
- [`abd`](./abd): an implementation of the ABD protocol
- [`echo`](./echo): an implementation of a single server Echo protocol
- [`echo-trivial`](./echo-trivial): a trivial implementation of Echo
- [`abd-example`](./abd-example): an example usage of the ABD protocol
- [`echo-example`](./echo-example): an example usage of the Echo protocol
