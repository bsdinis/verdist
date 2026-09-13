set shell := ["fish", "-c"]

verified_crates := "abd abd-example echo echo-example echo-trivial specs verdist vlib"
examples := "abd echo"

fmt:
    verusfmt (fd '.rs$' -E third_party); \

check:
    RUSTFLAGS="-D warnings" cargo check;

clippy:
    cargo clippy -- -D warnings;

[default]
run-examples:
    for name in {{examples}}; \
        for config in (rg -l  '^network = "modelled"$' sample_configs/{$name}*.toml); \
            cargo run -p {$name}-example --bin {$name}_client  -- --config {$config}; \
        end; \
    end

verify:
    cargo verus verify

# real end-to-end smoke tests: spawns a real abd_server + abd_client over io_uring_tcp/udp
# (real sockets, not the modelled network run-examples above exercises) and fails loudly if
# the wire path is broken. Not a benchmark -- just a handful of ops, seconds not minutes.
#
# KNOWN FLAKE (pre-existing, not fixed by --test-threads=1 below -- kept anyway since it removes
# one plausible source of cross-test interference even though it isn't the root cause): either
# test can independently hang for the full 10s wait_with_timeout deadline and fail with "abd_client
# did not exit within 10s (hung?)", at roughly 1-in-3 to 1-in-4 runs, order-independent, and it's
# not specific to either transport (both io_uring_tcp_smoke and io_uring_udp_smoke have been seen
# failing this way, in isolation and together, serial and parallel). Root cause not found --
# consistent with this sandbox's already-documented noisy/contended-machine timing (see
# claude-docs/PROFILING.md §2.6), but not confirmed. If this starts failing your run, retry once
# before assuming a real regression.
test-smoke:
    cargo test -p abd-example --test io_uring_network_smoke -- --test-threads=1

# profile a change to verified code: `just profile-proof "closed up Pending and Committed"`
# logs to timing_tracker/, prepends a summary.md entry, and flags a regression
# against the previous logged run. Not part of pre-commit -- run it by hand
# whenever a proof-structure change (new invariant, refactored lemma, etc.) is
# worth tracking, not on every commit.
profile-proof *desc:
    ./scripts/profile_proof.sh {{desc}}

pre-commit: fmt check clippy verify run-examples test-smoke
