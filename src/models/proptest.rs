//! Tier-1 property-based tests (PLAN-verification §2) — dependency-free, seeded.
//! Generate random models and assert relations that must hold for *every* model,
//! not just the six fixed examples. The starter set: determinism (guards the
//! HashMap-ordering trap), rename-invariance (guards naming bugs), and a
//! differential reachable-count check against an independent BFS. Run by
//! `cargo test`.

#![cfg(test)]

use super::check;
use super::ir::{Lts, Model};
use std::collections::{HashMap, HashSet, VecDeque};

/// A tiny seeded xorshift PRNG (no dependency).
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn upto(&mut self, n: usize) -> usize {
        (self.next() as usize) % n.max(1)
    }
}

/// A random FSM: 2–6 states, 1–4 events, random partial transition relation,
/// 0–2 forbidden states.
fn random_lts(seed: u64) -> Lts {
    let mut r = Rng(seed | 1);
    let ns = 2 + r.upto(5);
    let ne = 1 + r.upto(4);
    let states: Vec<String> = (0..ns).map(|i| format!("s{i}")).collect();
    let alphabet: Vec<String> = (0..ne).map(|i| format!("e{i}")).collect();
    let mut transitions = HashMap::new();
    for s in &states {
        for e in &alphabet {
            // ~60% of (state,event) pairs get a transition (the rest are blocked).
            if r.upto(10) < 6 {
                let to = states[r.upto(ns)].clone();
                transitions.insert((s.clone(), e.clone()), to);
            }
        }
    }
    let nf = r.upto(3);
    let mut forbid = Vec::new();
    for _ in 0..nf {
        let f = states[r.upto(ns)].clone();
        if !forbid.contains(&f) {
            forbid.push(f);
        }
    }
    Lts { family: "fsm", states, alphabet, initial: "s0".into(), transitions, forbid }
}

/// Independent BFS reachable-set size (the oracle for `check`'s count).
fn reachable_count(m: &dyn Model) -> usize {
    let mut seen = HashSet::new();
    let mut q = VecDeque::new();
    let init = m.initial();
    seen.insert(init.clone());
    q.push_back(init);
    while let Some(s) = q.pop_front() {
        for a in m.enabled(&s) {
            if let Some(t) = m.step(&s, &a) {
                if seen.insert(t.clone()) {
                    q.push_back(t);
                }
            }
        }
    }
    seen.len()
}

/// Rename every state `s` → `r_s` (a bijection); the behaviour is unchanged.
fn rename(lts: &Lts) -> Lts {
    let f = |s: &str| format!("r_{s}");
    Lts {
        family: lts.family,
        states: lts.states.iter().map(|s| f(s)).collect(),
        alphabet: lts.alphabet.clone(),
        initial: f(&lts.initial),
        transitions: lts.transitions.iter().map(|((s, e), t)| ((f(s), e.clone()), f(t))).collect(),
        forbid: lts.forbid.iter().map(|s| f(s)).collect(),
    }
}

#[test]
fn determinism() {
    // check is a pure function: same model ⇒ identical report (no HashMap-order
    // leakage into reachable count / violations / deadlocks).
    for seed in 1..200u64 {
        let m = random_lts(seed.wrapping_mul(0x9E3779B97F4A7C15));
        let a = check::check(&m, check::DEFAULT_BOUND);
        let b = check::check(&m, check::DEFAULT_BOUND);
        assert_eq!(a.reachable, b.reachable, "seed {seed}");
        assert_eq!(a.violations, b.violations, "seed {seed}");
        assert_eq!(a.deadlocks, b.deadlocks, "seed {seed}");
    }
}

#[test]
fn rename_invariance() {
    // A bijective state renaming preserves the verdict and the reachable size.
    for seed in 1..200u64 {
        let m = random_lts(seed.wrapping_mul(0x2545F4914F6CDD1D));
        let a = check::check(&m, check::DEFAULT_BOUND);
        let b = check::check(&rename(&m), check::DEFAULT_BOUND);
        assert_eq!(a.reachable, b.reachable, "seed {seed}");
        assert_eq!(a.safe(), b.safe(), "seed {seed}");
        assert_eq!(a.deadlocks.len(), b.deadlocks.len(), "seed {seed}");
    }
}

#[test]
fn reachable_count_matches_independent_bfs() {
    // Differential: check's reachable count == an independent BFS (these models
    // are small, never truncated).
    for seed in 1..300u64 {
        let m = random_lts(seed.wrapping_mul(0x9E3779B97F4A7C15) ^ 0xDEAD);
        let r = check::check(&m, check::DEFAULT_BOUND);
        assert!(!r.truncated);
        assert_eq!(r.reachable, reachable_count(&m), "seed {seed}");
    }
}

#[test]
fn reachable_subset_of_declared_states() {
    // Sanity: a checked model never reports more reachable states than declared,
    // and at least the initial one.
    for seed in 1..200u64 {
        let m = random_lts(seed);
        let r = check::check(&m, check::DEFAULT_BOUND);
        assert!(r.reachable >= 1 && r.reachable <= m.states.len(), "seed {seed}");
    }
}
