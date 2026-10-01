//! #3 Seqlock snapshot: one writer, readers that never block it.
//!
//! The payload is two words the writer always sets equal, so a torn read is
//! visible as `a != b`. Writer: odd sequence, `Release` fence, payload,
//! even sequence with `Release`. Reader: sequence with `Acquire`, payload,
//! `Acquire` fence, sequence again; the read is accepted only if both sequence
//! values are equal and even.
//!
//! Mutation (`mutant-seqlock`): the reader's `Acquire` fence between the
//! payload reads and the second sequence read is weakened to `Relaxed`-only
//! ordering (no fence). The second sequence read can then be satisfied before
//! the payload reads, so a reader can accept a payload mixed across writes.

use loom::sync::atomic::{fence, AtomicU32, AtomicUsize, Ordering::*};

const MUTANT: bool = cfg!(feature = "mutant-seqlock");

#[derive(Default)]
pub struct SeqLock {
    seq: AtomicUsize,
    a: AtomicU32,
    b: AtomicU32,
}

impl SeqLock {
    pub fn new() -> Self {
        Self::default()
    }

    /// Single writer only.
    pub fn write(&self, v: u32) {
        let s = self.seq.load(Relaxed);
        self.seq.store(s + 1, Relaxed);
        fence(Release);
        self.a.store(v, Relaxed);
        self.b.store(v, Relaxed);
        self.seq.store(s + 2, Release);
    }

    /// One attempt; `None` if a write was in progress or overlapped.
    pub fn try_read(&self) -> Option<(u32, u32)> {
        let s1 = self.seq.load(Acquire);
        if s1 % 2 == 1 {
            return None;
        }
        let a = self.a.load(Relaxed);
        let b = self.b.load(Relaxed);
        if !MUTANT {
            fence(Acquire);
        }
        let s2 = self.seq.load(Relaxed);
        if s1 == s2 {
            Some((a, b))
        } else {
            None
        }
    }
}
