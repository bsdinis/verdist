set shell := ["fish", "-c"]

verified_crates := "abd abd-example echo echo-example echo-trivial specs verdist vlib"
runnable_crates := "abd-example echo-example"

fmt:
    verusfmt (fd '.rs'); \

check:
    RUSTFLAGS="-D warnings" cargo check;

[default]
run:
    for crate in {{runnable_crates}}; \
        cargo run -p $crate -- --no-delay; \
    end

verify:
    cargo verus verify

pre-commit: fmt check verify run
