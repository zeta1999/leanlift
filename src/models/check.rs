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

/// Breadth-first reachability with a hard bound. Visits the initial state, then
/// every successor via `enabled` + `step`, recording violations and deadlocks.
pub fn check(model: &dyn Model, bound: usize) -> CheckResult {
    let mut seen: HashSet<State> = HashSet::new();
    let mut queue: VecDeque<State> = VecDeque::new();
    let mut violations = Vec::new();
    let mut deadlocks = Vec::new();
    let mut truncated = false;

    let init = model.initial();
    seen.insert(init.clone());
    queue.push_back(init);

    while let Some(s) = queue.pop_front() {
        if let Some(reason) = model.forbidden(&s) {
            violations.push((s.clone(), reason));
        }
        let acts = model.enabled(&s);
        if acts.is_empty() {
            deadlocks.push(s.clone());
            continue;
        }
        for a in acts {
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

    // Determinism for the report (BFS order is insertion-stable but the violation
    // / deadlock lists read better sorted).
    violations.sort();
    deadlocks.sort();

    CheckResult {
        family: model.family().to_string(),
        reachable: seen.len(),
        bound,
        truncated,
        violations,
        deadlocks,
    }
}
