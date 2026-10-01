//! #7 Treiber stack (push from many threads, pop from one).
//!
//! `push` writes the node, links it to the observed head, and installs it with
//! a `Release` CAS. `pop` loads the head with `Acquire`, reads the node's link
//! and value, and unlinks it with a CAS. Reclamation is out of scope here (that
//! is the hazard-pointer half of #7): with a single popper, the popper frees
//! what it popped, and pushers never dereference another thread's node, so the
//! checked configuration has no use-after-free by construction.
//!
//! Mutation (`mutant-treiber`): `pop`'s head load is `Relaxed`, so the reads of
//! the node's link and value are unordered with the pusher's writes — a data
//! race on the node, reported by loom's `UnsafeCell`.

use crate::pick;
use loom::cell::UnsafeCell;
use loom::sync::atomic::{AtomicPtr, Ordering::*};
use std::ptr;

const MUTANT: bool = cfg!(feature = "mutant-treiber");

struct Node {
    val: UnsafeCell<u32>,
    next: UnsafeCell<*mut Node>,
}

pub struct Treiber {
    head: AtomicPtr<Node>,
}

unsafe impl Sync for Treiber {}
unsafe impl Send for Treiber {}

impl Default for Treiber {
    fn default() -> Self {
        Self::new()
    }
}

impl Treiber {
    pub fn new() -> Self {
        Self { head: AtomicPtr::new(ptr::null_mut()) }
    }

    pub fn push(&self, v: u32) {
        let n = Box::into_raw(Box::new(Node { val: UnsafeCell::new(v), next: UnsafeCell::new(ptr::null_mut()) }));
        loop {
            let h = self.head.load(Relaxed);
            unsafe { (*n).next.with_mut(|p| *p = h) };
            if self.head.compare_exchange(h, n, Release, Relaxed).is_ok() {
                return;
            }
            loom::thread::yield_now();
        }
    }

    /// Single popper only (it frees the node it unlinks).
    pub fn pop(&self) -> Option<u32> {
        loop {
            let h = self.head.load(pick(MUTANT, Acquire, Relaxed));
            if h.is_null() {
                return None;
            }
            let next = unsafe { (*h).next.with(|p| *p) };
            let v = unsafe { (*h).val.with(|p| *p) };
            if self.head.compare_exchange(h, next, Relaxed, Relaxed).is_ok() {
                drop(unsafe { Box::from_raw(h) });
                return Some(v);
            }
            loom::thread::yield_now();
        }
    }
}

impl Drop for Treiber {
    fn drop(&mut self) {
        let mut p = self.head.load(Relaxed);
        while !p.is_null() {
            let next = unsafe { (*p).next.with(|q| *q) };
            drop(unsafe { Box::from_raw(p) });
            p = next;
        }
    }
}
