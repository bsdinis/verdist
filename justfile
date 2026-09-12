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

# profile a change to verified code: `just profile-proof "closed up Pending and Committed"`
# logs to timing_tracker/, prepends a summary.md entry, and flags a regression
# against the previous logged run. Not part of pre-commit -- run it by hand
# whenever a proof-structure change (new invariant, refactored lemma, etc.) is
# worth tracking, not on every commit.
profile-proof *desc:
    ./scripts/profile_proof.sh {{desc}}

pre-commit: fmt check clippy verify run-examples
