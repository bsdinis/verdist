set shell := ["fish", "-c"]

verified_crates := "abd abd-example echo echo-example echo-trivial specs verdist vlib"
examples := "abd echo"

fmt:
    verusfmt (fd '.rs$' -E third_party); \

check:
    RUSTFLAGS="-D warnings" cargo check;

[default]
run-examples:
    for name in {{examples}}; \
        for config in (rg -l  '^network = "modelled"$' sample_configs/{$name}*.toml); \
            cargo run -p {$name}-example --bin {$name}_client  -- --config {$config}; \
        end; \
    end

verify:
    cargo verus verify

pre-commit: fmt check verify run-examples
