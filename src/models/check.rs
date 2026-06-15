//! Native checker — the M1 backend (docs/SPEC-models.md §6). A bounded BFS over
//! the DTS-IR `Model`, ported from `petri.py`'s engine. The cardinal rule
//! (PLAN-models §0.2): **never diverge silently.** If the reachable set exceeds
//! the bound the exploration stops and `truncated` is set, so the report can say
//! "checked up to N states" rather than implying total coverage.
//!
//! What it computes, all in one sweep:
//!   * reachable-state count (and whether the bound was hit),
//!   * every reachable state that violates the safety property (`forbidden`),
//!   * every reachable deadlock (a state with no enabled action).
//!
//! Pure Rust, instant on 1-safe nets; the same explorer FSM, PT-net, BT and the
//! unfolded CPN all ride.

use super::ir::{Model, State};
use std::collections::{HashSet, VecDeque};

/// Default exploration ceiling. Generous for 1-safe models; a genuinely
/// unbounded net trips it and is reported as truncated (never silently capped).
pub const DEFAULT_BOUND: usize = 100_000;

pub struct CheckResult {
    pub family: String,
    pub reachable: usize,
    pub bound: usize,
    pub truncated: bool,
    /// (state, reason) for every reachable forbidden state.
    pub violations: Vec<(State, String)>,
    /// Reachable states with no enabled action.
    pub deadlocks: Vec<State>,
    /// Family-specific findings (e.g. the Petri safety-survives-loss split).
    /// Filled by the caller after `check`; empty for the FSM path.
    pub notes: Vec<String>,
}

impl CheckResult {
    /// The headline verdict: M1-checked iff fully explored, no safety violation.
    /// Deadlocks are *reported* but do not by themselves fail the default check
    /// (a model may legitimately terminate); a declared liveness property
    /// (Phase 2.5) is what turns a deadlock red.
    pub fn safe(&self) -> bool {
        !self.truncated && self.violations.is_empty()
    }
}

/// Bounded BFS reachability — the FIXPOINT core, factored out so its loop
/// invariant can be verified independently (PLAN-verification §V3.5): the
/// returned set is **closed under `step`** (every enabled successor of a member
/// is a member) UNLESS `truncated` — i.e. it is exactly the reachable set up to
/// the bound. This is the contract a Creusot deductive proof would discharge,
/// and the `reachable_set_closed_under_step` property test checks today.
pub(crate) fn reachable_set(model: &dyn Model, bound: usize) -> (HashSet<State>, bool) {
    let mut seen: HashSet<State> = HashSet::new();
    let mut queue: VecDeque<State> = VecDeque::new();
    let mut truncated = false;

    let init = model.initial();
    seen.insert(init.clone());
    queue.push_back(init);

    while let Some(s) = queue.pop_front() {
        for a in model.enabled(&s) {
            if let Some(t) = model.step(&s, &a) {
                if !seen.contains(&t) {
                    if seen.len() >= bound {
                        truncated = true;
                        continue;
                    }
                    seen.insert(t.clone());
                    queue.push_back(t);
                }
            }
        }
    }
    (seen, truncated)
}

/// The M1 check: compute the reachable set (closed under `step`, `reachable_set`),
/// then scan it for safety violations and deadlocks.
pub fn check(model: &dyn Model, bound: usize) -> CheckResult {
    let (seen, truncated) = reachable_set(model, bound);

    let mut violations = Vec::new();
    let mut deadlocks = Vec::new();
    for s in &seen {
        if let Some(reason) = model.forbidden(s) {
            violations.push((s.clone(), reason));
        }
        if model.enabled(s).is_empty() {
            deadlocks.push(s.clone());
        }
    }

    // Determinism for the report (the set is unordered; sort the findings).
    violations.sort();
    deadlocks.sort();

    CheckResult {
        family: model.family().to_string(),
        reachable: seen.len(),
        bound,
        truncated,
        violations,
        deadlocks,
        notes: Vec::new(),
    }
}
