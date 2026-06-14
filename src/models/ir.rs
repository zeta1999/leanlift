//! DTS-IR — the unifying abstraction (docs/SPEC-models.md §4). Every family —
//! FSM, PT-net, CPN, BT, SPN — is one transition system: an initial state plus
//! a partial `step`. That single shape is why one native checker (`check.rs`)
//! and one Lean induction principle (`LeanLift/Models/Fsm.lean`) serve them all.
//!
//! States and actions are carried as their *canonical string encoding*. That
//! keeps the checker fully generic and dependency-free (a `String` hashes and
//! compares out of the box): an FSM state is its name; a Petri marking (Phase 2)
//! will canonicalise to `"p0=1,p1=0"`. Families differ only in how they realise
//! `step` — never in the engine that explores it.

pub type State = String;
pub type Action = String;

/// The one trait every behavioural family implements (the Rust twin of
/// day48's `fsm.py` / `petri.py`). `enabled` + `step` are the transition
/// relation; `forbidden` carries the default/declared safety property so the
/// checker can flag a bad state the moment BFS reaches it.
pub trait Model {
    /// Family tag, for the report and for auto-detection feedback.
    fn family(&self) -> &'static str;
    /// The initial (canonical) state.
    fn initial(&self) -> State;
    /// Actions enabled at `s`. Empty ⇒ `s` is a deadlock (no successor).
    fn enabled(&self, s: &State) -> Vec<Action>;
    /// Fire `a` at `s`. `None` ⇒ blocked (mirrors `step s e = none` in Lean).
    fn step(&self, s: &State, a: &Action) -> Option<State>;
    /// `Some(reason)` if `s` violates the safety property; `None` if safe.
    fn forbidden(&self, s: &State) -> Option<String>;
}

/// An explicit labelled transition system / FSM (Phase 0 + Phase 1). States and
/// the alphabet are named; the transition relation is a total map from
/// `(from, action)` to a successor, partial by omission (a missing entry =
/// BLOCKED, exactly `fsm.py`'s partial step).
pub struct Lts {
    pub family: &'static str,
    /// Declared state set. Consumed by the Phase 1 Lean exporter (it becomes the
    /// `inductive State`); the checker explores from `initial` and need not read it.
    #[allow(dead_code)]
    pub states: Vec<String>,
    pub alphabet: Vec<String>,
    pub initial: String,
    /// `(from, action) -> to`
    pub transitions: std::collections::HashMap<(String, String), String>,
    /// States the safety property forbids (default property: none forbidden,
    /// so `check` falls back to reachability + deadlock-freedom).
    pub forbid: Vec<String>,
}

impl Model for Lts {
    fn family(&self) -> &'static str {
        self.family
    }
    fn initial(&self) -> State {
        self.initial.clone()
    }
    fn enabled(&self, s: &State) -> Vec<Action> {
        self.alphabet
            .iter()
            .filter(|a| self.transitions.contains_key(&(s.clone(), (*a).clone())))
            .cloned()
            .collect()
    }
    fn step(&self, s: &State, a: &Action) -> Option<State> {
        self.transitions.get(&(s.clone(), a.clone())).cloned()
    }
    fn forbidden(&self, s: &State) -> Option<String> {
        if self.forbid.iter().any(|f| f == s) {
            Some(format!("state `{s}` is declared forbidden"))
        } else {
            None
        }
    }
}
