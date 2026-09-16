//! End-to-end smoke tests for `verdist::network::udp_muxed` (the handshake-free UDP backend --
//! see that module's doc for the design). These spawn a real `echo_server` subprocess and several
//! real, *concurrent* `echo_client` subprocesses (the same binaries `cargo run -p echo-example
//! --bin echo_server`/`echo_client` would run) and confirm:
//!
//! - a client can complete every op with no prior handshake traffic (implicit accept works), and
//! - multiple concurrent clients get correctly demultiplexed with no cross-talk (each client's
//!   own echoed values come back to *it*, not to another client) -- this is the property that
//!   would break silently if source-address demuxing (or, for the reuseport variant,
//!   `SO_REUSEPORT` flow stickiness) were wrong, since a client whose response was misrouted would
//!   just see "echo failed" (a value mismatch) or hang, rather than crash outright.
//!
//! Correctness smoke test, not a benchmark: small op counts, not CPU-pinned, no latency/throughput
//! assertions. Mirrors `abd-example/tests/io_uring_network_smoke.rs`'s subprocess-spawn/timeout/
//! content-check pattern.

use std::io::Read;
use std::net::SocketAddr;
use std::net::UdpSocket;
use std::process::Child;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;
use std::time::Duration;
use std::time::Instant;

/// Same rationale as `abd-example/tests/io_uring_network_smoke.rs`'s identical guard: a plain
/// `Child` + `.kill()` on drop, so a failing `assert!`/`panic!`/timeout anywhere in a test can
/// never leave the server subprocess running, and so it can't miss a process backgrounded by a
/// different shell invocation the way a `pkill -f` from a fresh shell could.
struct ChildGuard {
    child: Child,
    name: &'static str,
}

impl Drop for ChildGuard {
    fn drop(&mut self) {
        if matches!(self.child.try_wait(), Ok(None))
            && let Err(e) = self.child.kill()
        {
            eprintln!("warning: failed to kill {}: {e}", self.name);
        }
        let _ = self.child.wait();
    }
}

/// Same polling trick as `io_uring_network_smoke.rs::wait_until_bound`: as long as *we* can bind
/// `addr` ourselves, nothing else is listening there yet.
fn wait_until_bound(addr: SocketAddr, timeout: Duration) -> bool {
    let deadline = Instant::now() + timeout;
    loop {
        if UdpSocket::bind(addr).is_err() {
            return true;
        }
        if Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

fn wait_with_timeout(mut child: Child, timeout: Duration) -> Output {
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait().expect("failed to poll client process") {
            Some(_status) => break,
            None => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("echo_client did not exit within {timeout:?} (hung?)");
                }
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }
    child
        .wait_with_output()
        .expect("failed to collect client output")
}

/// Spawns one `echo_server` (udp_muxed, `num_router_threads` router sockets/threads) plus
/// `num_clients` concurrent `echo_client`s against it, each doing `n_ops` ops, and confirms every
/// client both exits successfully and actually completed every op with the correct echoed value
/// (not just a zero exit status -- see `io_uring_network_smoke.rs`'s identical "belt and braces"
/// rationale).
fn run_smoke_test(addr: SocketAddr, num_router_threads: usize, num_clients: u64, n_ops: u64) {
    let server = Command::new(env!("CARGO_BIN_EXE_echo_server"))
        .args([
            "--server-id",
            "1",
            "--server-addr",
            &addr.to_string(),
            "--network",
            "udp",
            "--num-threads",
            "4",
            "--num-router-threads",
            &num_router_threads.to_string(),
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn echo_server");
    let mut server = ChildGuard {
        child: server,
        name: "echo_server",
    };

    if !wait_until_bound(addr, Duration::from_secs(5)) {
        panic!("echo_server never bound {addr} within 5s");
    }

    let clients: Vec<Child> = (0..num_clients)
        .map(|i| {
            Command::new(env!("CARGO_BIN_EXE_echo_client"))
                .args([
                    "--n-ops",
                    &n_ops.to_string(),
                    "--client-id",
                    &(100 + i).to_string(),
                    "--client-addr",
                    "127.0.0.1",
                    "--server-id",
                    "1",
                    "--server-addr",
                    &addr.to_string(),
                    "--network",
                    "udp",
                ])
                // Per-op completion logging is silent by default -- force it on so the content
                // check below has something to look at (same as `io_uring_network_smoke.rs`).
                .env("RUST_LOG", "debug")
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap_or_else(|e| panic!("failed to spawn echo_client {i}: {e}"))
        })
        .collect();

    let outputs: Vec<Output> = clients
        .into_iter()
        .map(|c| wait_with_timeout(c, Duration::from_secs(10)))
        .collect();

    if let Err(e) = server.child.kill() {
        eprintln!("note: echo_server already exited on its own before being killed: {e}");
    }
    let _ = server.child.wait();
    let mut server_stderr = String::new();
    if let Some(mut stderr) = server.child.stderr.take() {
        let _ = stderr.read_to_string(&mut server_stderr);
    }

    for (i, output) in outputs.iter().enumerate() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            output.status.success(),
            "echo_client {i} exited with {:?}\n--- stdout ---\n{stdout}\n--- stderr ---\n{stderr}\n--- server stderr (so far) ---\n{server_stderr}",
            output.status,
        );
        assert!(
            !stderr.contains("echo failed"),
            "echo_client {i} reported a value mismatch (cross-talk between demultiplexed clients?)\n--- stderr ---\n{stderr}",
        );
        let completed = stderr.matches("output == input").count() as u64;
        assert_eq!(
            completed, n_ops,
            "echo_client {i} only completed {completed}/{n_ops} ops\n--- stderr ---\n{stderr}",
        );
    }

    // Every client that got a connection accepted should have gotten *its own* -- no client's
    // traffic should have been silently folded into another's demux entry (which would show up
    // as fewer than `num_clients` "accepted connection" lines despite every client completing).
    let accepted = server_stderr.matches("accepted connection").count() as u64;
    assert_eq!(
        accepted, num_clients,
        "expected exactly {num_clients} implicit accepts, saw {accepted}\n--- server stderr ---\n{server_stderr}",
    );

    drop(server);
}

#[test]
fn udp_muxed_single_socket_concurrent_clients() {
    run_smoke_test("127.0.0.1:16780".parse().unwrap(), 1, 8, 20);
}

#[test]
fn udp_muxed_reuseport_concurrent_clients() {
    run_smoke_test("127.0.0.1:16781".parse().unwrap(), 4, 16, 20);
}
