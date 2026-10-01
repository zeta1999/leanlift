//! One loom model per core. Each prints the number of executions explored and
//! the wall time, so a run states how large its search was. The preemption
//! bound comes from `LOOM_MAX_PREEMPTIONS` (set by `run.sh`; unset means loom's
//! default of no bound). Run with `--test-threads=1 --nocapture`.
//!
//! **Harness shape.** Every role runs in a spawned thread and the model's main
//! thread only joins and checks. With loom 0.7.2, a model where the main thread
//! plays one role and the spawned thread does independent loads before its
//! conflicting store explored a single execution (the race was never tried);
//! the same accesses with every role spawned explored 45. See `LOOM.md`.

use leanlift_loom::{chase_lev::Deque, mpsc::Mpsc, seqlock::SeqLock, spmc::Spmc, spsc::Spsc, treiber::Treiber};
use loom::sync::Arc;
use loom::thread;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

fn check(name: &str, f: impl Fn() + Sync + Send + 'static) {
    static EXECUTIONS: AtomicUsize = AtomicUsize::new(0);
    EXECUTIONS.store(0, Ordering::SeqCst);
    let start = Instant::now();
    let builder = loom::model::Builder::new();
    let bound = builder.preemption_bound;
    builder.check(move || {
        EXECUTIONS.fetch_add(1, Ordering::SeqCst);
        f();
    });
    eprintln!(
        "[LOOM] {name}: clean, {} executions explored, preemption bound {:?}, {:.2?}",
        EXECUTIONS.load(Ordering::SeqCst),
        bound,
        start.elapsed()
    );
}

#[test]
fn spsc() {
    check("spsc", || {
        let q = Arc::new(Spsc::<2>::new());
        let (p, c) = (q.clone(), q.clone());
        let prod = thread::spawn(move || {
            assert!(p.push(1));
            assert!(p.push(2));
        });
        let cons = thread::spawn(move || (0..2).filter_map(|_| c.pop()).collect::<Vec<u32>>());
        prod.join().unwrap();
        let got = cons.join().unwrap();
        assert_eq!(got[..], [1, 2][..got.len()], "out-of-order or wrong value");
    });
}

#[test]
fn seqlock() {
    check("seqlock", || {
        let l = Arc::new(SeqLock::new());
        let (w, r) = (l.clone(), l.clone());
        let writer = thread::spawn(move || {
            w.write(1);
            w.write(2);
        });
        let reader = thread::spawn(move || r.try_read());
        writer.join().unwrap();
        if let Some((a, b)) = reader.join().unwrap() {
            assert_eq!(a, b, "torn snapshot accepted");
        }
    });
}

#[test]
fn mpsc() {
    check("mpsc", || {
        let q = Arc::new(Mpsc::<2>::new());
        let (p1, p2, c) = (q.clone(), q.clone(), q.clone());
        let a = thread::spawn(move || assert!(p1.push(1)));
        let b = thread::spawn(move || assert!(p2.push(2)));
        let cons = thread::spawn(move || (0..2).filter_map(|_| c.pop()).collect::<Vec<u32>>());
        a.join().unwrap();
        b.join().unwrap();
        let mut got = cons.join().unwrap();
        got.extend(std::iter::from_fn(|| q.pop()));
        got.sort();
        assert_eq!(got, vec![1, 2], "lost or duplicated element");
    });
}

#[test]
fn spmc() {
    check("spmc", || {
        let r = Arc::new(Spmc::<1>::new());
        let (w, r1, r2) = (r.clone(), r.clone(), r.clone());
        let writer = thread::spawn(move || {
            w.publish(1);
            w.publish(2);
        });
        let a = thread::spawn(move || r1.try_read(0));
        let b = thread::spawn(move || r2.try_read(0));
        writer.join().unwrap();
        for got in [a.join().unwrap(), b.join().unwrap()].into_iter().flatten() {
            assert_eq!(got.0, got.1, "torn slot accepted");
        }
    });
}

#[test]
fn treiber() {
    check("treiber", || {
        let s = Arc::new(Treiber::new());
        let (s1, s2, c) = (s.clone(), s.clone(), s.clone());
        let a = thread::spawn(move || s1.push(1));
        let b = thread::spawn(move || s2.push(2));
        let popper = thread::spawn(move || (0..2).filter_map(|_| c.pop()).collect::<Vec<u32>>());
        a.join().unwrap();
        b.join().unwrap();
        let mut got = popper.join().unwrap();
        got.extend(std::iter::from_fn(|| s.pop()));
        got.sort();
        assert_eq!(got, vec![1, 2], "lost or duplicated element");
    });
}

#[test]
fn chase_lev() {
    check("chase_lev", || {
        let d = Arc::new(Deque::<4>::new());
        assert!(d.push(1));
        assert!(d.push(2));
        let (o, t) = (d.clone(), d.clone());
        let owner = thread::spawn(move || o.take());
        let thief = thread::spawn(move || [t.steal(), t.steal()]);
        let mut got: Vec<u32> = owner.join().unwrap().into_iter().collect();
        got.extend(thief.join().unwrap().into_iter().flatten());
        got.extend(std::iter::from_fn(|| d.take()));
        got.sort();
        assert_eq!(got, vec![1, 2], "element claimed twice or lost");
    });
}
