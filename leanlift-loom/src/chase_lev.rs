//! #8 Chase–Lev work-stealing deque, fixed capacity (growth out of scope),
//! after the C11 version of Lê, Pop, Cohen and Zappa Nardelli (PPoPP 2013).
//!
//! The owner pushes and takes at `bottom`; thieves steal at `top`. Both `take`
//! and `steal` need a `SeqCst` fence between their two index accesses: without
//! it the owner's store to `bottom` and its load of `top` can be reordered
//! (store buffering) against a thief's accesses, and owner and thief can claim
//! the same element. The fences are `fence(SeqCst)`, which loom models fully;
//! the `SeqCst` CASes are treated by loom as `AcqRel`, which this algorithm does
//! not rely on.
//!
//! Mutation (`mutant-chaselev`): the owner's `fence(SeqCst)` in `take` is
//! removed — exactly the fence the Lê et al. argument turns on.

use loom::sync::atomic::{fence, AtomicIsize, AtomicU32, Ordering::*};

const MUTANT: bool = cfg!(feature = "mutant-chaselev");

pub struct Deque<const N: usize> {
    top: AtomicIsize,
    bottom: AtomicIsize,
    buf: [AtomicU32; N],
}

impl<const N: usize> Default for Deque<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Deque<N> {
    pub fn new() -> Self {
        Self { top: AtomicIsize::new(0), bottom: AtomicIsize::new(0), buf: std::array::from_fn(|_| AtomicU32::new(0)) }
    }

    fn slot(&self, i: isize) -> &AtomicU32 {
        &self.buf[(i as usize) % N]
    }

    /// Owner only. Returns `false` when full.
    pub fn push(&self, v: u32) -> bool {
        let b = self.bottom.load(Relaxed);
        let t = self.top.load(Acquire);
        if b - t >= N as isize {
            return false;
        }
        self.slot(b).store(v, Relaxed);
        fence(Release);
        self.bottom.store(b + 1, Relaxed);
        true
    }

    /// Owner only.
    pub fn take(&self) -> Option<u32> {
        let b = self.bottom.load(Relaxed) - 1;
        self.bottom.store(b, Relaxed);
        if !MUTANT {
            fence(SeqCst);
        }
        let t = self.top.load(Relaxed);
        if t > b {
            self.bottom.store(b + 1, Relaxed);
            return None;
        }
        let v = self.slot(b).load(Relaxed);
        if t == b {
            let won = self.top.compare_exchange(t, t + 1, SeqCst, Relaxed).is_ok();
            self.bottom.store(b + 1, Relaxed);
            return if won { Some(v) } else { None };
        }
        Some(v)
    }

    /// Any thief. One attempt.
    pub fn steal(&self) -> Option<u32> {
        let t = self.top.load(Acquire);
        fence(SeqCst);
        let b = self.bottom.load(Acquire);
        if t >= b {
            return None;
        }
        let v = self.slot(t).load(Relaxed);
        if self.top.compare_exchange(t, t + 1, SeqCst, Relaxed).is_ok() {
            Some(v)
        } else {
            None
        }
    }
}
