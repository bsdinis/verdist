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
use std::process::ExitStatus;
use std::process::Stdio;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::Duration;
use std::time::Instant;

/// Continuously drains one already-`Stdio::piped()` stream (stdout or stderr) into a shared
/// buffer on a dedicated background thread, so the writing child process's pipe never fills up
/// and blocks it -- unlike reading a piped stream only *after* the child exits (e.g.
/// `Child::wait_with_output`), which deadlocks if the child writes more than one pipe buffer's
/// worth (~64KiB on Linux) before its own exit: the child blocks on the next write with nobody
/// reading, and the parent is waiting for the child to exit before it reads. This is exactly what
/// `RUST_LOG=debug`'s per-poll-iteration tracing (`verdist::network::channel`'s "polling on
/// channel", logged once per non-blocking `try_recv` attempt -- for an io_uring-backed channel
/// that peeks the completion queue rather than blocking, that can be thousands of attempts within
/// a few tens of milliseconds, easily tens of KiB of log text per op) can trigger well within a
/// single small smoke test, independent of anything being actually slow or hung.
struct DrainedPipe {
    buf: Arc<Mutex<Vec<u8>>>,
    handle: std::thread::JoinHandle<()>,
}

fn drain_pipe<R: Read + Send + 'static>(pipe: R) -> DrainedPipe {
    let buf = Arc::new(Mutex::new(Vec::new()));
    let buf_writer = Arc::clone(&buf);
    let handle = std::thread::spawn(move || {
        let mut pipe = pipe;
        let mut chunk = [0u8; 8192];
        loop {
            match pipe.read(&mut chunk) {
                Ok(0) => return,
                Ok(n) => buf_writer.lock().unwrap().extend_from_slice(&chunk[..n]),
                Err(_) => return,
            }
        }
    });
    DrainedPipe { buf, handle }
}

impl DrainedPipe {
    /// Joins the drain thread (blocking until it has observed EOF -- safe to call once the
    /// writing process has actually exited, which every call site here already waited for) and
    /// returns everything it read as a `String`.
    fn join_and_get_string(self) -> String {
        let _ = self.handle.join();
        String::from_utf8_lossy(&self.buf.lock().unwrap()).into_owned()
    }

    /// Snapshot of what's been read so far, without joining -- used for the server, which is
    /// still running (and being drained) when this is read.
    fn snapshot_string(&self) -> String {
        String::from_utf8_lossy(&self.buf.lock().unwrap()).into_owned()
    }
}

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

fn wait_with_timeout(mut child: Child, timeout: Duration) -> ExitStatus {
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait().expect("failed to poll client process") {
            Some(status) => return status,
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
}

/// Spawns one `echo_server` (udp_muxed, `num_router_threads` router sockets/threads) plus
/// `num_clients` concurrent `echo_client`s against it, each doing `n_ops` ops, and confirms every
/// client both exits successfully and actually completed every op with the correct echoed value
/// (not just a zero exit status -- see `io_uring_network_smoke.rs`'s identical "belt and braces"
/// rationale).
#[allow(clippy::too_many_arguments)]
fn run_smoke_test(
    addr: SocketAddr,
    network: &str,
    num_router_threads: usize,
    epoll: bool,
    num_clients: u64,
    n_ops: u64,
) {
    // `udp_ephemeral` never logs "accepted connection" -- there is no persistent per-client state
    // (demux entry or otherwise) to bring into existence, by design (see `udp_ephemeral`'s module
    // doc). Every other backend this harness drives does log it once per client.
    let expect_accept_log = network != "udp_ephemeral";
    let mut server_args = vec![
        "--server-id".to_string(),
        "1".to_string(),
        "--server-addr".to_string(),
        addr.to_string(),
        "--network".to_string(),
        network.to_string(),
        "--num-threads".to_string(),
        "4".to_string(),
        "--num-router-threads".to_string(),
        num_router_threads.to_string(),
    ];
    if epoll {
        server_args.push("--epoll".to_string());
    }
    let mut server = Command::new(env!("CARGO_BIN_EXE_echo_server"))
        .args(&server_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn echo_server");
    let server_stderr_pipe = drain_pipe(server.stderr.take().expect("server stderr was piped"));
    let _server_stdout_pipe = drain_pipe(server.stdout.take().expect("server stdout was piped"));
    let mut server = ChildGuard {
        child: server,
        name: "echo_server",
    };

    if !wait_until_bound(addr, Duration::from_secs(5)) {
        panic!("echo_server never bound {addr} within 5s");
    }

    let clients: Vec<(Child, DrainedPipe, DrainedPipe)> = (0..num_clients)
        .map(|i| {
            let mut child = Command::new(env!("CARGO_BIN_EXE_echo_client"))
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
                    network,
                ])
                // Per-op completion logging is silent by default -- force it on so the content
                // check below has something to look at (same as `io_uring_network_smoke.rs`).
                .env("RUST_LOG", "debug")
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap_or_else(|e| panic!("failed to spawn echo_client {i}: {e}"));
            // Drain both pipes concurrently, from the moment each client is spawned -- see
            // `drain_pipe`'s doc for why this can't wait until `wait_with_timeout` returns.
            let stdout_pipe = drain_pipe(child.stdout.take().expect("client stdout was piped"));
            let stderr_pipe = drain_pipe(child.stderr.take().expect("client stderr was piped"));
            (child, stdout_pipe, stderr_pipe)
        })
        .collect();

    let results: Vec<(ExitStatus, DrainedPipe, DrainedPipe)> = clients
        .into_iter()
        .map(|(c, stdout_pipe, stderr_pipe)| {
            (wait_with_timeout(c, Duration::from_secs(10)), stdout_pipe, stderr_pipe)
        })
        .collect();

    if let Err(e) = server.child.kill() {
        eprintln!("note: echo_server already exited on its own before being killed: {e}");
    }
    let _ = server.child.wait();
    // Give the drain thread a moment to observe EOF and flush the last chunk after the kill.
    std::thread::sleep(Duration::from_millis(50));
    let server_stderr = server_stderr_pipe.snapshot_string();

    for (i, (status, _stdout_pipe, stderr_pipe)) in results.into_iter().enumerate() {
        // Each client already exited (`wait_with_timeout` above returned its status), so joining
        // its drain threads here is guaranteed to complete promptly -- they hit EOF the moment
        // the child's fds closed.
        let stderr = stderr_pipe.join_and_get_string();

        assert!(
            status.success(),
            "echo_client {i} exited with {status:?}\n--- stderr ---\n{stderr}\n--- server stderr (so far) ---\n{server_stderr}",
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
    // Doesn't apply to `udp_ephemeral` (see `expect_accept_log` above): the no-cross-talk property
    // there is instead fully established by the per-client "every op completed with the correct
    // echoed value, no mismatch" checks above -- there is no separate accept event to also count.
    if expect_accept_log {
        let accepted = server_stderr.matches("accepted connection").count() as u64;
        assert_eq!(
            accepted, num_clients,
            "expected exactly {num_clients} implicit accepts, saw {accepted}\n--- server stderr ---\n{server_stderr}",
        );
    }

    drop(server);
}

#[test]
fn udp_muxed_single_socket_concurrent_clients() {
    run_smoke_test("127.0.0.1:16780".parse().unwrap(), "udp", 1, false, 8, 20);
}

#[test]
fn udp_muxed_reuseport_concurrent_clients() {
    run_smoke_test("127.0.0.1:16781".parse().unwrap(), "udp", 4, false, 16, 20);
}

/// `--epoll` for `udp_muxed` (`verdist::network::udp_muxed::run_epoll`'s
/// `crossbeam_channel::Select`-based driver -- see that function's doc for why this backend
/// can't use `Server::run_epoll` directly). Combined with `--num-router-threads 2` so this also
/// exercises the epoll driver alongside `SO_REUSEPORT` fan-out, not just the single-socket case.
#[test]
fn udp_muxed_epoll_concurrent_clients() {
    run_smoke_test("127.0.0.1:16782".parse().unwrap(), "udp", 2, true, 20, 100);
}

/// io_uring/`RecvMsg`-based router thread (`verdist::network::io_uring_udp_muxed`) -- same
/// demux/implicit-accept correctness properties as plain `udp`, different receive mechanism.
#[test]
fn udp_muxed_io_uring_single_socket_concurrent_clients() {
    run_smoke_test("127.0.0.1:16783".parse().unwrap(), "io_uring_udp", 1, false, 8, 20);
}

#[test]
fn udp_muxed_io_uring_reuseport_concurrent_clients() {
    run_smoke_test("127.0.0.1:16784".parse().unwrap(), "io_uring_udp", 4, false, 16, 20);
}

/// `udp_ephemeral` (`verdist::network::udp_ephemeral`): no persistent per-client `Channel` at all,
/// each datagram is received/handled/replied-to and immediately forgotten. The property this
/// harness checks (no cross-talk between concurrent clients, every op's echoed value correct) is
/// exactly the one most at risk from a bug in that design -- e.g. two clients' one-shot channels
/// somehow sharing a response, or a reply going to the wrong peer address.
#[test]
fn udp_ephemeral_single_socket_concurrent_clients() {
    run_smoke_test("127.0.0.1:16785".parse().unwrap(), "udp_ephemeral", 1, false, 8, 20);
}

/// Same, but with several independent `SO_REUSEPORT`-sharing router threads -- unlike `udp_muxed`,
/// flow stickiness across datagrams is *not* load-bearing here (no per-peer state persists between
/// messages, see the module doc), so this also incidentally exercises that two consecutive
/// datagrams from the same client landing on *different* router threads is fine.
#[test]
fn udp_ephemeral_reuseport_concurrent_clients() {
    run_smoke_test("127.0.0.1:16786".parse().unwrap(), "udp_ephemeral", 4, false, 20, 50);
}
