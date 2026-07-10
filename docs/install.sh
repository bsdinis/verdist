#!/usr/bin/env bash

# Install verdist on a fresh machine
# Tested on Ubuntu 24.04
#
# Assume git and curl are installed, and that bash is running

set -xe

# install direnv and rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
curl -sfL https://direnv.net/install.sh | bash

# clone repos
git clone https://github.com/verus-lang/verus
git clone https://github.com/bsdinis/verdist

# update bashrc
cat >> ~/.bashrc << 'EOF'

. "${HOME}/.cargo/env"
if [[ -r "${HOME}/verus/source/target-verus/release/verus" ]]; then
	PATH="${HOME}/verus/source/target-verus/release":"${PATH}"
	export VERUS_BINARY_PATH="${HOME}/verus"
	export PATH
fi

eval "$(direnv hook bash)"
EOF

# build verus
cd ~/verus/source
direnv allow
tools/get-z3.sh
vargo build --release

# build verdist
cd ~/verdist
direnv allow
cargo build --release
