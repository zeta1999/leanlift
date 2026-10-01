//! #2 MPSC stamp queue (bounded, Vyukov-style cells, fetch-and-add tickets).
//!
//! A producer takes a ticket with `fetch_add` on `tail` (the contention point:
//! distinct tickets by the read-modify-write alone), writes the cell's value,
//! then publishes the cell by storing its stamp `ticket + 1` with `Release`.
//! The consumer reads the stamp with `Acquire`; only a published stamp lets it
//! read the value, after which it stamps the cell free for the next lap.
//!
//! The test sizes the ring so no producer ever waits for a lap; the waiting
//! path is not exercised.
//!
//! Mutation (`mutant-mpsc`): the consumer's stamp load is `Relaxed`, so the
//! value read is unordered with the producer's write — a data race on the cell.

use crate::pick;
use loom::cell::UnsafeCell;
use loom::sync::atomic::{AtomicUsize, Ordering::*};

const MUTANT: bool = cfg!(feature = "mutant-mpsc");

struct Cell {
    stamp: AtomicUsize,
    val: UnsafeCell<u32>,
}

pub struct Mpsc<const N: usize> {
    cells: [Cell; N],
    tail: AtomicUsize,
    head: AtomicUsize,
}

unsafe impl<const N: usize> Sync for Mpsc<N> {}

impl<const N: usize> Default for Mpsc<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Mpsc<N> {
    pub fn new() -> Self {
        Self {
            cells: std::array::from_fn(|i| Cell { stamp: AtomicUsize::new(i), val: UnsafeCell::new(0) }),
            tail: AtomicUsize::new(0),
            head: AtomicUsize::new(0),
        }
    }

    /// Any number of producers. Returns `false` if the cell for this ticket is
    /// still a lap behind (never happens in the checked configuration).
    pub fn push(&self, v: u32) -> bool {
        let t = self.tail.fetch_add(1, Relaxed);
        let c = &self.cells[t % N];
        if c.stamp.load(Acquire) != t {
            return false;
        }
        c.val.with_mut(|p| unsafe { *p = v });
        c.stamp.store(t + 1, Release);
        true
    }

    /// Single consumer.
    pub fn pop(&self) -> Option<u32> {
        let h = self.head.load(Relaxed);
        let c = &self.cells[h % N];
        if c.stamp.load(pick(MUTANT, Acquire, Relaxed)) != h + 1 {
            return None;
        }
        let v = c.val.with(|p| unsafe { *p });
        c.stamp.store(h + N, Release);
        self.head.store(h + 1, Relaxed);
        Some(v)
    }
}
