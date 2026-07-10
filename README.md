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

# Quick Install

Clone relevant repos

```zsh
git clone https://github.com/verus-lang/verus
git clone https://github.com/bsdinis/verdist
```

Install Rust
```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Install direnv
```
curl -sfL https://direnv.net/install.sh | bash
```

Update your shell configuration with the following. (Example for bash)

```
. "${HOME}/.cargo/env"
if [[ -r "${HOME}/verus/source/target-verus/release/verus" ]]; then
	PATH="${HOME}/verus/source/target-verus/release":"${PATH}"
	export VERUS_BINARY_PATH="${HOME}/verus"
	export PATH
fi

eval "$(direnv hook bash)"
```

Build verus
```zsh
cd ~/verus/source
tools/get-z3.sh
vargo build --release
```

Build verdist
```zsh
cd ~/verdist
cargo build --release
```

Full script
```zsh
```
