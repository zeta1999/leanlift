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

/// A place/transition Petri net (Phase 2). Markings are vectors of token counts
/// aligned to `places`; the canonical state encoding is the comma-joined counts
/// (e.g. `"1,0,0,0,0"`) so the generic checker hashes/compares markings for
/// free. `pre`/`post` are likewise aligned to `places`; a *pure-loss* transition
/// has `post` all-zero (`petri.py`'s `is_loss`).
pub struct PtNet {
    pub places: Vec<String>,
    pub transitions: Vec<PtTrans>,
    pub initial: Vec<u32>,
    /// Per-place token cap (authored but reserved): the generic checker's global
    /// state-count bound (`check::DEFAULT_BOUND`) already prevents silent
    /// divergence via its `truncated` flag, so this finer per-place guard is not
    /// yet consulted. Kept so 1-safe intent is recorded in the model file.
    #[allow(dead_code)]
    pub bound: u32,
    /// Declared upper-bound safety properties: `sum(places[idx]) ≤ max`.
    pub bounds: Vec<BoundProp>,
    /// The place subset whose weighted (weight-1) token sum is the inductive
    /// invariant the Lean proof strengthens to (a *place invariant*, Jensen
    /// §6–7). `None` = all places (the dock's global-total case); a proper
    /// subset is what proves a coloured mutex (lock + crit) once unfolded.
    pub conserved: Option<Vec<usize>>,
}

pub struct PtTrans {
    pub name: String,
    pub pre: Vec<u32>,
    pub post: Vec<u32>,
}

pub struct BoundProp {
    pub name: String,
    pub places: Vec<usize>,
    pub max: u32,
}

impl PtTrans {
    /// A pure-loss transition consumes tokens and produces none.
    pub fn is_loss(&self) -> bool {
        self.post.iter().all(|&c| c == 0) && self.pre.iter().any(|&c| c > 0)
    }
    /// Token mass consumed / produced (for the conservation classification).
    pub fn pre_sum(&self) -> u32 {
        self.pre.iter().sum()
    }
    pub fn post_sum(&self) -> u32 {
        self.post.iter().sum()
    }
}

impl PtNet {
    pub fn encode(m: &[u32]) -> State {
        m.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",")
    }
    pub fn decode(s: &State) -> Vec<u32> {
        s.split(',').map(|x| x.parse().unwrap_or(0)).collect()
    }
    fn enabled_at(&self, m: &[u32], t: &PtTrans) -> bool {
        marking_enabled(m, &t.pre)
    }
}

/// Enabling test as pure marking arithmetic (no `&self`, no strings): every arc
/// weight `pre[i]` is covered by the tokens `m[i]`. Factored out of `step`/
/// `enabled` so the kernel can be verified directly — no-underflow by Kani
/// (V1.2) and against `Petri.lean` by Aeneas (V3).
pub(crate) fn marking_enabled(m: &[u32], pre: &[u32]) -> bool {
    pre.iter().zip(m).all(|(&c, &have)| c <= have)
}

/// Fire kernel: the successor marking `m − pre + post`, index-wise.
/// PRECONDITION: `marking_enabled(m, pre)` — under it no `u32` underflow occurs,
/// which the `fire_no_underflow` Kani harness proves. Shared by `PtNet::step`,
/// so the proof covers production.
pub(crate) fn fire_marking(m: &[u32], pre: &[u32], post: &[u32]) -> Vec<u32> {
    (0..m.len()).map(|i| m[i] - pre[i] + post[i]).collect()
}

impl Model for PtNet {
    fn family(&self) -> &'static str {
        "petri"
    }
    fn initial(&self) -> State {
        Self::encode(&self.initial)
    }
    fn enabled(&self, s: &State) -> Vec<Action> {
        let m = Self::decode(s);
        self.transitions
            .iter()
            .filter(|t| self.enabled_at(&m, t))
            .map(|t| t.name.clone())
            .collect()
    }
    fn step(&self, s: &State, a: &Action) -> Option<State> {
        let m = Self::decode(s);
        let t = self.transitions.iter().find(|t| &t.name == a)?;
        if !self.enabled_at(&m, t) {
            return None;
        }
        let next = fire_marking(&m, &t.pre, &t.post);
        Some(Self::encode(&next))
    }
    fn forbidden(&self, s: &State) -> Option<String> {
        let m = Self::decode(s);
        for b in &self.bounds {
            let sum: u32 = b.places.iter().map(|&i| m[i]).sum();
            if sum > b.max {
                let names: Vec<&str> = b.places.iter().map(|&i| self.places[i].as_str()).collect();
                return Some(format!(
                    "{}: {} = {} > {}",
                    b.name,
                    names.join("+"),
                    sum,
                    b.max
                ));
            }
        }
        None
    }
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

/// Bounded model-checking harness (PLAN-verification §V1.2). Inert for normal
/// `cargo build`/`test` — compiled only under `cargo kani`, which injects the
/// `kani` crate. Bounds are kept small so CBMC stays light.
#[cfg(kani)]
mod kani_harness {
    use super::{fire_marking, marking_enabled};

    /// `PtNet::fire` never underflows: for any bounded marking and transition,
    /// IF the transition is enabled THEN `m − pre + post` computes without a
    /// `u32` subtraction underflow (Kani auto-checks overflow; reaching the
    /// asserts means no panic). Drop the `assume(enabled)` and Kani finds the
    /// underflow — i.e. the precondition is exactly what makes `step` safe.
    #[kani::proof]
    fn fire_no_underflow() {
        const N: usize = 3;
        let m: [u32; N] = kani::any();
        let pre: [u32; N] = kani::any();
        let post: [u32; N] = kani::any();
        for i in 0..N {
            kani::assume(m[i] <= 8);
            kani::assume(pre[i] <= 8);
            kani::assume(post[i] <= 8);
        }
        kani::assume(marking_enabled(&m, &pre));
        let next = fire_marking(&m, &pre, &post);
        for i in 0..N {
            // non-increasing transitions cannot raise the per-place count above
            // what pre removed + post added; and the value is exactly the spec.
            assert!(next[i] == m[i] - pre[i] + post[i]);
        }
    }
}
