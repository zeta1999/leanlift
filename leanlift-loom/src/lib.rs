//! `[LOOM]` — bounded weak-memory model checking of the concurrency corpus.
//!
//! Six cores, each a small Rust reimplementation of an algorithm in the corpus
//! of `docs/PLAN-concurrency.md`, written against `loom`'s atomics so that
//! `loom::model` explores their executions under its C11 model:
//! SPSC ring, seqlock, MPSC stamp queue, SPMC broadcast ring, Treiber stack,
//! Chase–Lev deque.
//!
//! **This is bounded model checking, not a proof.** A clean run says no bug was
//! found within the bound and within what loom models; see `LOOM.md` for the
//! bounds, the run times, the ordering bug injected into each core to show the
//! checker can fail, and loom's own documented unsoundness (load buffering is
//! not explored) and incompleteness (`SeqCst` accesses are treated as `AcqRel`).
//!
//! Each core carries one deliberate ordering mutation behind a cargo feature
//! (`mutant-<core>`). With the feature off the core is the intended algorithm;
//! with it on, exactly one ordering is weakened. `run.sh` checks that every core
//! passes clean and fails mutated.

pub mod chase_lev;
pub mod mpsc;
pub mod seqlock;
pub mod spmc;
pub mod spsc;
pub mod treiber;

use loom::sync::atomic::Ordering;

/// The ordering to use at a mutation site: `good` normally, `bad` when the
/// core's mutant feature is enabled.
#[inline]
pub(crate) const fn pick(mutant: bool, good: Ordering, bad: Ordering) -> Ordering {
    if mutant {
        bad
    } else {
        good
    }
}
