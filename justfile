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
        cargo run -p {$name}-example --bin {$name}_client  -- --no-delay --network modelled; \
    end

verify:
    cargo verus verify

pre-commit: fmt check verify run-examples
