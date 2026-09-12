//! End-to-end smoke tests for the io_uring-backed networks.
//!
//! `just run-examples` only ever exercises the in-process `modelled` network (see the
//! `run-examples` recipe in the root `justfile`), so a real `abd_server` <-> `abd_client` wire
//! path over `io_uring_tcp`/`io_uring_udp` is otherwise never actually run by the standard
//! pre-commit gate -- only type-checked and verified, never executed. These tests close that
//! gap: they spawn a real `abd_server` subprocess and a real `abd_client` subprocess (the same
//! binaries `cargo run -p abd-example --bin abd_server`/`abd_client` would run) and confirm they
//! can complete a handful of reads/writes over a real socket.
//!
//! This is a correctness smoke test, not a benchmark: it is not CPU-pinned, does not measure
//! latency/throughput, and uses the small op counts already in the `*_smoke.toml` configs. It
//! uses dedicated ports (16663/16673) distinct from the plain `abd_1_io_uring_{tcp,udp}.toml`
//! sample configs (6663/6673) so it can't collide with a developer's own manual run of those.

use std::io::Read;
use std::net::SocketAddr;
use std::net::TcpListener;
use std::net::UdpSocket;
use std::path::PathBuf;
use std::process::Child;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;
use std::time::Duration;
use std::time::Instant;

/// Kills (and reaps) the wrapped child on drop, so a failing `assert!`/`panic!` anywhere in a
/// test -- including a timeout -- can never leave the server subprocess running. Plain
/// `std::process::Child` + `.kill()` rather than `pkill -f` from a shell: a fresh shell's
/// `pkill -f` can fail to reach a process backgrounded by a *different* shell invocation (see
/// `claude-docs/PROFILING.md` §2.7), whereas a captured `Child` handle always refers to the exact
/// PID we spawned.
struct ChildGuard {
    child: Child,
    name: &'static str,
}

impl Drop for ChildGuard {
    fn drop(&mut self) {
        // Only kill if still running: this guard also covers the normal (non-panicking) path,
        // where the caller has usually already killed+reaped the child itself (to safely drain
        // its stderr, see `run_smoke_test`) before this runs -- avoid a spurious "already
        // exited" warning on every successful test.
        if matches!(self.child.try_wait(), Ok(None))
            && let Err(e) = self.child.kill()
        {
            eprintln!("warning: failed to kill {}: {e}", self.name);
        }
        let _ = self.child.wait();
    }
}

enum Proto {
    Tcp,
    Udp,
}

/// Polls `addr` by repeatedly trying to bind it ourselves: as long as *we* can bind it, nothing
/// else is listening there yet; once our bind fails with "address in use", the server has bound
/// it and is ready for the client to connect. This works identically for TCP and UDP and needs
/// no cooperation from the server binary (no readiness print to scrape, no fixed sleep to guess
/// at), so it's used for both smoke tests below.
fn wait_until_bound(addr: SocketAddr, proto: &Proto, timeout: Duration) -> bool {
    let deadline = Instant::now() + timeout;
    loop {
        let we_could_bind = match proto {
            Proto::Tcp => TcpListener::bind(addr).is_ok(),
            Proto::Udp => UdpSocket::bind(addr).is_ok(),
        };
        if !we_could_bind {
            return true;
        }
        if Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

/// Runs `child` to completion, killing it and failing loudly if it doesn't exit within
/// `timeout`. A plain `Command::output()` (blocking, unbounded) would let a real hang in the
/// client -- exactly one of the failure modes this test exists to catch -- wedge `cargo test`
/// forever instead of failing the check.
fn wait_with_timeout(mut child: Child, timeout: Duration) -> Output {
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait().expect("failed to poll client process") {
            Some(_status) => break,
            None => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("abd_client did not exit within {timeout:?} (hung?)");
                }
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }
    child
        .wait_with_output()
        .expect("failed to collect client output")
}

fn sample_config_path(name: &str) -> PathBuf {
    // CARGO_MANIFEST_DIR is abd-example/; sample_configs/ is a sibling at the workspace root.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("sample_configs")
        .join(name)
}

fn run_smoke_test(config_name: &str, addr: SocketAddr, proto: Proto) {
    let config_path = sample_config_path(config_name);
    assert!(
        config_path.is_file(),
        "missing test fixture: {config_path:?}"
    );

    let server = Command::new(env!("CARGO_BIN_EXE_abd_server"))
        .arg("--server-id")
        .arg("1")
        .arg("--config")
        .arg(&config_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn abd_server");
    let mut server = ChildGuard {
        child: server,
        name: "abd_server",
    };

    if !wait_until_bound(addr, &proto, Duration::from_secs(5)) {
        panic!("abd_server never bound {addr} within 5s");
    }

    let client = Command::new(env!("CARGO_BIN_EXE_abd_client"))
        .arg("--config")
        .arg(&config_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn abd_client");

    let output = wait_with_timeout(client, Duration::from_secs(10));

    // Kill (and reap) the server now, then drain its buffered stderr for diagnostics. Order
    // matters here: while the server is still alive its stderr pipe never reaches EOF, so
    // `read_to_string` would block forever if attempted before killing it.
    if let Err(e) = server.child.kill() {
        eprintln!("note: abd_server already exited on its own before being killed: {e}");
    }
    let _ = server.child.wait();
    let mut server_stderr = String::new();
    if let Some(mut stderr) = server.child.stderr.take() {
        let _ = stderr.read_to_string(&mut server_stderr);
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if !output.status.success() {
        let status = output.status;
        panic!(
            "abd_client exited with {status:?} against {config_name}\n\
             --- client stdout ---\n{stdout}\n\
             --- client stderr ---\n{stderr}\n\
             --- server stderr (so far) ---\n{server_stderr}"
        );
    }

    // Belt-and-braces content check: don't just trust a zero exit status, confirm the client
    // actually reported completing every op (n_reads=4 + n_writes=3 = 7 in the *_smoke.toml
    // configs) rather than e.g. silently short-circuiting.
    let completed = stderr.matches("completed").count();
    assert!(
        completed >= 7,
        "expected at least 7 completed ops, saw {completed}\n--- client stderr ---\n{stderr}"
    );

    drop(server); // explicit: kill+reap the server now rather than at end of scope.
}

#[test]
fn io_uring_tcp_smoke() {
    run_smoke_test(
        "abd_1_io_uring_tcp_smoke.toml",
        "127.0.0.1:16663".parse().unwrap(),
        Proto::Tcp,
    );
}

#[test]
fn io_uring_udp_smoke() {
    run_smoke_test(
        "abd_1_io_uring_udp_smoke.toml",
        "127.0.0.1:16673".parse().unwrap(),
        Proto::Udp,
    );
}
