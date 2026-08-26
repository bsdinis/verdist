//! Micro-benchmark: `vlib::reclaim::EpochAtomicPtr` (the hazard-pointer-style epoch reclamation
//! built to replace ABD's register lock) versus a plain `RwLock` baseline, under the access
//! pattern ABD's server hot path actually drives it with (see `abd/src/server/register.rs`,
//! `MonotonicRegister::read`/`write`): many concurrent readers each taking a single-value
//! snapshot of the current register version, and one or more writers each replacing the whole
//! published value with a fresh one.
//!
//! Run: `cargo run -p vlib --release --example reclaim_vs_rwlock`
//!
//! Not verified, not wired into `just pre-commit` -- this is a plain, unverified performance
//! comparison, as requested; nothing here participates in `cargo verus verify`.
//!
//! Caveat on the baseline: ABD's *actual* current lock is `vstd::rwlock::RwLock`, a hand-rolled
//! reader/writer spinlock over an `AtomicBool` + `AtomicUsize` (see `verus/source/vstd/rwlock.rs`)
//! -- not `std::sync::RwLock`. The former can't be constructed from plain, non-Verus code: its
//! `new` takes a `Ghost<Pred>`, and `Ghost::new` only exists under `cfg(verus_keep_ghost)`, which
//! plain `cargo run`/`cargo bench` never sets. `std::sync::RwLock` stands in here as the
//! realistic "if you didn't build epoch reclamation, you'd reach for a lock" baseline; it parks
//! contending threads rather than spinning, which if anything favors it over what ABD actually
//! had, so this is a conservative (not a strawman) comparison.
//!
//! `EpochAtomicPtr<T>`/`Slot<T>` are `Send + Sync` for `T: Send + Sync` (see the `unsafe impl`
//! block at the end of `vlib/src/reclaim/slot.rs`), so this benchmark shares them across threads
//! the ordinary way -- `Arc<EpochAtomicPtr<T>>` -- with no wrapper needed here.
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::sync::RwLock;
use std::thread;
use std::time::Duration;

use vlib::reclaim::atomic_ptr::EpochAtomicPtr;

/// Stand-in for the value ABD's register keeps behind its lock (`MonotonicRegisterInner`'s
/// `value: Option<u64>` + `timestamp: Timestamp`, minus the ghost/verification-only fields, which
/// are zero-sized at runtime and irrelevant to performance either way).
#[derive(Clone, Copy)]
struct RegisterVersion {
    value: u64,
    timestamp: u64,
}

struct BenchResult {
    reads: u64,
    writes: u64,
    elapsed: Duration,
}

impl BenchResult {
    fn reads_per_sec(&self) -> f64 {
        self.reads as f64 / self.elapsed.as_secs_f64()
    }

    fn writes_per_sec(&self) -> f64 {
        self.writes as f64 / self.elapsed.as_secs_f64()
    }
}

fn run_epoch(num_readers: usize, num_writers: usize, duration: Duration) -> BenchResult {
    // Generous relative to writer count: bounds how many in-flight retired generations this
    // tolerates before a writer would have to wait on reclaim, which we don't want dominating
    // the measurement here.
    let num_slots = num_writers.max(1) * 4 + 4;
    let initial = RegisterVersion {
        value: 0,
        timestamp: 0,
    };
    let ptr = Arc::new(EpochAtomicPtr::new(initial, num_slots, num_readers));
    let stop = Arc::new(AtomicBool::new(false));

    let readers: Vec<_> = (0..num_readers)
        .map(|reader_idx| {
            let ptr = Arc::clone(&ptr);
            let stop = Arc::clone(&stop);
            thread::spawn(move || {
                let mut ops: u64 = 0;
                let mut sink: u64 = 0;
                while !stop.load(Ordering::Relaxed) {
                    let guard = ptr.pin(reader_idx);
                    let v = *guard.get_ref();
                    guard.unpin();
                    sink ^= v.value ^ v.timestamp;
                    ops += 1;
                }
                (ops, sink)
            })
        })
        .collect();

    let writers: Vec<_> = (0..num_writers)
        .map(|_| {
            let ptr = Arc::clone(&ptr);
            let stop = Arc::clone(&stop);
            thread::spawn(move || {
                let mut ops: u64 = 0;
                let mut next: u64 = 0;
                while !stop.load(Ordering::Relaxed) {
                    next += 1;
                    ptr.write(RegisterVersion {
                        value: next,
                        timestamp: next,
                    });
                    ops += 1;
                }
                ops
            })
        })
        .collect();

    thread::sleep(duration);
    stop.store(true, Ordering::Relaxed);

    let mut reads = 0u64;
    let mut sink_acc = 0u64;
    for h in readers {
        let (ops, sink) = h.join().unwrap();
        reads += ops;
        sink_acc ^= sink;
    }
    let writes = writers.into_iter().map(|h| h.join().unwrap()).sum();
    std::hint::black_box(sink_acc);

    BenchResult {
        reads,
        writes,
        elapsed: duration,
    }
}

fn run_rwlock(num_readers: usize, num_writers: usize, duration: Duration) -> BenchResult {
    let initial = RegisterVersion {
        value: 0,
        timestamp: 0,
    };
    let lock = Arc::new(RwLock::new(initial));
    let stop = Arc::new(AtomicBool::new(false));

    let readers: Vec<_> = (0..num_readers)
        .map(|_| {
            let lock = Arc::clone(&lock);
            let stop = Arc::clone(&stop);
            thread::spawn(move || {
                let mut ops: u64 = 0;
                let mut sink: u64 = 0;
                while !stop.load(Ordering::Relaxed) {
                    let v = *lock.read().unwrap();
                    sink ^= v.value ^ v.timestamp;
                    ops += 1;
                }
                (ops, sink)
            })
        })
        .collect();

    let writers: Vec<_> = (0..num_writers)
        .map(|_| {
            let lock = Arc::clone(&lock);
            let stop = Arc::clone(&stop);
            thread::spawn(move || {
                let mut ops: u64 = 0;
                let mut next: u64 = 0;
                while !stop.load(Ordering::Relaxed) {
                    next += 1;
                    *lock.write().unwrap() = RegisterVersion {
                        value: next,
                        timestamp: next,
                    };
                    ops += 1;
                }
                ops
            })
        })
        .collect();

    thread::sleep(duration);
    stop.store(true, Ordering::Relaxed);

    let mut reads = 0u64;
    let mut sink_acc = 0u64;
    for h in readers {
        let (ops, sink) = h.join().unwrap();
        reads += ops;
        sink_acc ^= sink;
    }
    let writes = writers.into_iter().map(|h| h.join().unwrap()).sum();
    std::hint::black_box(sink_acc);

    BenchResult {
        reads,
        writes,
        elapsed: duration,
    }
}

fn fmt_rate(ops_per_sec: f64) -> String {
    if ops_per_sec >= 1e6 {
        format!("{:>8.2} M/s", ops_per_sec / 1e6)
    } else {
        format!("{:>8.2} K/s", ops_per_sec / 1e3)
    }
}

fn main() {
    // Read-heavy sweep (fixed 1 writer, growing reader count) is the primary ABD scenario: a
    // register's hot path is dominated by reads, with occasional writes. The writer-scaling
    // configs at the end exercise the other axis this design specifically supports: multiple
    // *concurrent* writers (the extended ABD protocol allows more than one).
    let configs: &[(usize, usize)] = &[(1, 1), (2, 1), (4, 1), (8, 1), (2, 2), (2, 4)];
    let run_duration = Duration::from_millis(500);

    println!(
        "{:<18}{:<8}{:>12}{:>12}",
        "config", "impl", "reads/s", "writes/s"
    );
    for &(readers, writers) in configs {
        let label = format!("r={readers} w={writers}");

        let epoch = run_epoch(readers, writers, run_duration);
        println!(
            "{:<18}{:<8}{:>12}{:>12}",
            label,
            "epoch",
            fmt_rate(epoch.reads_per_sec()),
            fmt_rate(epoch.writes_per_sec())
        );

        let rwlock = run_rwlock(readers, writers, run_duration);
        println!(
            "{:<18}{:<8}{:>12}{:>12}",
            label,
            "rwlock",
            fmt_rate(rwlock.reads_per_sec()),
            fmt_rate(rwlock.writes_per_sec())
        );
    }
}
