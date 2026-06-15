//! Tier-1 property-based tests (PLAN-verification §2) — dependency-free, seeded.
//! Generate random models and assert relations that must hold for *every* model,
//! not just the six fixed examples. The starter set: determinism (guards the
//! HashMap-ordering trap), rename-invariance (guards naming bugs), and a
//! differential reachable-count check against an independent BFS. Run by
//! `cargo test`.

#![cfg(test)]

use super::ir::{Lts, Model, PtNet, PtTrans};
use super::{check, format};
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

// --- V0.3 metamorphic properties (PLAN-verification §V0.3) ------------------ //

#[test]
fn product_commutativity() {
    // The synchronous product is commutative up to the `a|b` ↔ `b|a` state
    // renaming: A∥B and B∥A explore the same number of (reachable) states and
    // the same number of deadlocks. A bug in the sync/self-loop logic that
    // treated the two operands asymmetrically would break this.
    for seed in 1..300u64 {
        let a = random_lts(seed.wrapping_mul(0x9E3779B97F4A7C15));
        let b = random_lts(seed.wrapping_mul(0x2545F4914F6CDD1D) ^ 0xBEEF);
        let ab = check::check(&format::product(&a, &b), check::DEFAULT_BOUND);
        let ba = check::check(&format::product(&b, &a), check::DEFAULT_BOUND);
        assert_eq!(ab.reachable, ba.reachable, "seed {seed}: reachable");
        assert_eq!(ab.deadlocks.len(), ba.deadlocks.len(), "seed {seed}: deadlocks");
    }
}

#[test]
fn dead_state_addition_invariance() {
    // Adding an UNREACHABLE state — even a forbidden one, with outgoing edges —
    // changes neither the reachable count nor the verdict: the checker explores
    // forward from the initial state and must never be perturbed by garbage it
    // can't reach. (Catches an accidental "scan all declared states" regression.)
    for seed in 1..300u64 {
        let m = random_lts(seed.wrapping_mul(0x9E3779B97F4A7C15) ^ 0x5151);
        let base = check::check(&m, check::DEFAULT_BOUND);

        let dead = "zzz_unreachable".to_string();
        let mut states = m.states.clone();
        states.push(dead.clone());
        // Give the dead state OUTGOING edges (to s0) but no INCOMING edge, so it
        // stays unreachable; declare it forbidden to make the test bite harder.
        let mut transitions = m.transitions.clone();
        for e in &m.alphabet {
            transitions.insert((dead.clone(), e.clone()), m.initial.clone());
        }
        let mut forbid = m.forbid.clone();
        forbid.push(dead.clone());
        let m2 = Lts { family: m.family, states, alphabet: m.alphabet.clone(), initial: m.initial.clone(), transitions, forbid };

        let aug = check::check(&m2, check::DEFAULT_BOUND);
        assert_eq!(base.reachable, aug.reachable, "seed {seed}: reachable");
        assert_eq!(base.safe(), aug.safe(), "seed {seed}: verdict");
        assert_eq!(base.deadlocks.len(), aug.deadlocks.len(), "seed {seed}: deadlocks");
    }
}

/// A random PT-net whose every transition is NON-INCREASING in total token mass
/// (`post_sum ≤ pre_sum`) — the loss / conservative regime. 2–4 places, 1–4
/// transitions, small initial marking.
fn random_nonincreasing_ptnet(seed: u64) -> PtNet {
    let mut r = Rng(seed | 1);
    let np = 2 + r.upto(3);
    let nt = 1 + r.upto(4);
    let places: Vec<String> = (0..np).map(|i| format!("p{i}")).collect();
    let mut initial: Vec<u32> = (0..np).map(|_| r.upto(3) as u32).collect();
    if initial.iter().all(|&c| c == 0) {
        initial[0] = 1; // ensure a non-empty initial marking
    }
    let mut transitions = Vec::new();
    for ti in 0..nt {
        let pre: Vec<u32> = (0..np).map(|_| r.upto(3) as u32).collect();
        let pre_sum: u32 = pre.iter().sum();
        // Distribute k ≤ pre_sum produced tokens across the places at random.
        let mut post = vec![0u32; np];
        let k = r.upto((pre_sum + 1) as usize) as u32;
        for _ in 0..k {
            post[r.upto(np)] += 1;
        }
        transitions.push(PtTrans { name: format!("t{ti}"), pre, post });
    }
    PtNet { places, transitions, initial, bound: 8, bounds: Vec::new(), conserved: None }
}

#[test]
fn petri_loss_monotonicity() {
    // The Rust analogue of `Petri.le_preserved`: if every transition is
    // non-increasing, firing can only keep or shrink the total token mass, so
    // EVERY reachable marking has total ≤ the initial total. This is exactly the
    // upper bound the Lean export inducts on; a sign error in `PtNet::step`
    // (e.g. `+ pre` instead of `- pre`) would let the total grow and trip it.
    let mut nontrivial = 0usize; // non-vacuity: count nets that actually move
    for seed in 1..400u64 {
        let net = random_nonincreasing_ptnet(seed.wrapping_mul(0x9E3779B97F4A7C15));
        let cap: u32 = net.initial.iter().sum();

        // Independent BFS collecting markings (check only returns a count).
        let mut seen: HashSet<String> = HashSet::new();
        let mut q: VecDeque<String> = VecDeque::new();
        let init = net.initial();
        seen.insert(init.clone());
        q.push_back(init);
        while let Some(s) = q.pop_front() {
            let total: u32 = PtNet::decode(&s).iter().sum();
            assert!(total <= cap, "seed {seed}: marking {s} total {total} > cap {cap}");
            for a in net.enabled(&s) {
                if let Some(t) = net.step(&s, &a) {
                    if seen.insert(t.clone()) {
                        assert!(seen.len() < 200_000, "seed {seed}: net failed to stay finite");
                        q.push_back(t);
                    }
                }
            }
        }
        if seen.len() > 1 {
            nontrivial += 1;
        }
    }
    assert!(nontrivial > 50, "loss-monotonicity test was near-vacuous: only {nontrivial} nets moved");
}

#[test]
fn reachable_set_closed_under_step() {
    // V3.5 invariant (the contract a Creusot proof would discharge, checked here
    // over random models): the set `check::reachable_set` returns is CLOSED under
    // `step` — every enabled successor of a reachable state is itself in the set.
    // That fixpoint property is what makes the M1 verdict sound; a BFS bug that
    // dropped a successor would leave the set non-closed and trip this.
    let mut checked = 0;
    // Random FSMs.
    for seed in 1..300u64 {
        let m = random_lts(seed.wrapping_mul(0x9E3779B97F4A7C15) ^ 0xC105E);
        let (set, truncated) = check::reachable_set(&m, check::DEFAULT_BOUND);
        assert!(!truncated, "FSM seed {seed} truncated unexpectedly");
        assert!(set.contains(&m.initial()), "FSM seed {seed}: initial not in set");
        for s in &set {
            for a in m.enabled(s) {
                if let Some(t) = m.step(s, &a) {
                    assert!(set.contains(&t), "FSM seed {seed}: successor {t} of {s} not closed");
                }
            }
        }
        checked += 1;
    }
    // Random non-increasing PT-nets (bounded ⇒ finite reachable set).
    for seed in 1..300u64 {
        let net = random_nonincreasing_ptnet(seed.wrapping_mul(0x2545F4914F6CDD1D) ^ 0xFEED);
        let (set, truncated) = check::reachable_set(&net, check::DEFAULT_BOUND);
        assert!(!truncated, "PtNet seed {seed} truncated unexpectedly");
        for s in &set {
            for a in net.enabled(s) {
                if let Some(t) = net.step(s, &a) {
                    assert!(set.contains(&t), "PtNet seed {seed}: successor not closed under step");
                }
            }
        }
        checked += 1;
    }
    assert_eq!(checked, 598, "expected to check 598 random models");
}
