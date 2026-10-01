//! #1 SPSC ring: one producer, one consumer, bounded, index-based.
//!
//! The producer writes the slot, then publishes `tail` with `Release`; the
//! consumer reads `tail` with `Acquire` before reading the slot, and publishes
//! `head` with `Release` so the producer can reuse the slot.
//!
//! Mutation (`mutant-spsc`): the consumer's `tail` load is `Relaxed`. The slot
//! read is then unordered with the producer's write — a data race on the slot,
//! which loom's `UnsafeCell` reports as a causality violation.

use crate::pick;
use loom::cell::UnsafeCell;
use loom::sync::atomic::{AtomicUsize, Ordering::*};

const MUTANT: bool = cfg!(feature = "mutant-spsc");

pub struct Spsc<const N: usize> {
    buf: [UnsafeCell<u32>; N],
    head: AtomicUsize,
    tail: AtomicUsize,
}

unsafe impl<const N: usize> Sync for Spsc<N> {}

impl<const N: usize> Default for Spsc<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Spsc<N> {
    pub fn new() -> Self {
        Self {
            buf: std::array::from_fn(|_| UnsafeCell::new(0)),
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
        }
    }

    /// Producer only.
    pub fn push(&self, v: u32) -> bool {
        let t = self.tail.load(Relaxed);
        let h = self.head.load(Acquire);
        if t - h == N {
            return false;
        }
        self.buf[t % N].with_mut(|p| unsafe { *p = v });
        self.tail.store(t + 1, Release);
        true
    }

    /// Consumer only.
    pub fn pop(&self) -> Option<u32> {
        let h = self.head.load(Relaxed);
        let t = self.tail.load(pick(MUTANT, Acquire, Relaxed));
        if h == t {
            return None;
        }
        let v = self.buf[h % N].with(|p| unsafe { *p });
        self.head.store(h + 1, Release);
        Some(v)
    }
}
