//! #5 SPMC broadcast ring: one producer, many readers, slots reused each lap.
//!
//! Each slot is a seqlock: the producer marks the slot's stamp odd, `Release`
//! fence, writes the two-word payload (always equal words), then stores the
//! even stamp with `Release`. A reader takes the stamp with `Acquire`, reads the
//! payload, `Acquire` fence, re-reads the stamp, and accepts only an unchanged
//! even stamp. The stamp grows every lap, so an overrun is a changed stamp.
//!
//! Mutation (`mutant-spmc`) — on the *writer* side, unlike the seqlock core's
//! reader-side mutation: the `Release` fence after marking the stamp odd is
//! removed, so the payload stores may become visible before the odd stamp and a
//! reader can accept a payload mixed across laps under an unchanged even stamp.

use loom::sync::atomic::{fence, AtomicU32, AtomicUsize, Ordering::*};

const MUTANT: bool = cfg!(feature = "mutant-spmc");

#[derive(Default)]
struct Slot {
    stamp: AtomicUsize,
    a: AtomicU32,
    b: AtomicU32,
}

pub struct Spmc<const N: usize> {
    slots: [Slot; N],
    next: AtomicUsize,
}

impl<const N: usize> Default for Spmc<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Spmc<N> {
    pub fn new() -> Self {
        Self { slots: std::array::from_fn(|_| Slot::default()), next: AtomicUsize::new(0) }
    }

    /// Single producer: publish `v` into the next slot (overwriting a lap ago).
    pub fn publish(&self, v: u32) {
        let i = self.next.load(Relaxed);
        let s = &self.slots[i % N];
        let st = s.stamp.load(Relaxed);
        s.stamp.store(st + 1, Relaxed);
        if !MUTANT {
            fence(Release);
        }
        s.a.store(v, Relaxed);
        s.b.store(v, Relaxed);
        s.stamp.store(st + 2, Release);
        self.next.store(i + 1, Release);
    }

    /// One attempt at slot `i % N`.
    pub fn try_read(&self, i: usize) -> Option<(u32, u32)> {
        let s = &self.slots[i % N];
        let s1 = s.stamp.load(Acquire);
        if s1 % 2 == 1 {
            return None;
        }
        let a = s.a.load(Relaxed);
        let b = s.b.load(Relaxed);
        fence(Acquire);
        let s2 = s.stamp.load(Relaxed);
        if s1 == s2 {
            Some((a, b))
        } else {
            None
        }
    }
}
