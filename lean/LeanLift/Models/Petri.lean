/-
  LeanLift/Models/Petri.lean — generic theory of Petri nets (the ASYNC companion
  to Fsm.lean). Mathlib-free: core Lean 4 + `omega`.

  Fsm.lean modelled SYNCHRONOUS composition. A Petri net is the ASYNCHRONOUS
  picture:

    a marking  m : P → Nat        (tokens per place)
    a transition  t = ⟨pre, post⟩ (consumed / produced, per place)

  `t` is *enabled* at `m` when every place has ≥ `pre` tokens; *firing* maps
  `m ↦ fun p => m p - pre p + post p`. Crucially a Petri net is STILL a
  transition system: pick a transition-id type `T` and a guarded
  `step : Marking → T → Option Marking`, and reuse `Fsm.Reachable` and
  `Fsm.invariant_of_preserved` verbatim. The induction principle does not care
  whether the "event" is a CSP event or the firing of a Petri transition — that
  is the unifying point (docs/SPEC-models.md §4: "a Petri net IS a transition
  system").

  What this file adds is specific to *tokens*, and to **losing** them:
    * `fire`, `Enabled` — the firing rule.
    * `fire_le` — firing a transition that produces no more at `p` than it
      consumes cannot INCREASE the count at `p` (the formal heart of "loss only
      removes tokens").
    * `le_preserved` — an UPPER-BOUND invariant `m p ≤ k` survives such a
      transition. Safety as upper bounds (e.g. "at most one machine in its
      critical section") is *monotone under loss*; conservation EQUALITIES,
      which liveness needs, are not. See docs/SPEC-models.md §6 and the
      safety-survives-loss / liveness-doesn't split.
-/

namespace LeanLift.Models.Petri

/-- A marking assigns a token count to every place. -/
abbrev Marking (P : Type) := P → Nat

/-- A transition consumes `pre p` and produces `post p` at place `p`. A
    *pure-loss* transition has `post = 0`: it eats tokens, makes none. -/
structure Trans (P : Type) where
  pre  : P → Nat
  post : P → Nat

/-- The firing rule (Nat subtraction truncates, but on an enabled transition no
    truncation occurs — see `Enabled`). -/
def fire {P : Type} (m : Marking P) (t : Trans P) : Marking P :=
  fun p => m p - t.pre p + t.post p

/-- `t` is enabled at `m` when every place holds enough tokens to be consumed. -/
def Enabled {P : Type} (m : Marking P) (t : Trans P) : Prop :=
  ∀ p, t.pre p ≤ m p

/-- THE loss lemma. If `t` is enabled at `p` and produces no more than it
    consumes there (`post p ≤ pre p`), firing cannot increase the count at `p`.
    A pure-loss transition (`post p = 0`) is the headline instance. -/
theorem fire_le {P : Type} (m : Marking P) (t : Trans P) (p : P)
    (hen : t.pre p ≤ m p) (hnp : t.post p ≤ t.pre p) :
    fire m t p ≤ m p := by
  simp only [fire]; omega

/-- A pure-loss transition is non-increasing everywhere it is enabled. -/
theorem loss_noninc {P : Type} (m : Marking P) (t : Trans P) (p : P)
    (hen : t.pre p ≤ m p) (hloss : t.post p = 0) :
    fire m t p ≤ m p := by
  simp only [fire]; omega

/-- Upper-bound invariants are preserved by non-increasing transitions: if
    `m p ≤ k` then after firing `fire m t p ≤ k`. This is why "≤ k" safety is
    robust to message/token loss. -/
theorem le_preserved {P : Type} (m : Marking P) (t : Trans P) (p : P) (k : Nat)
    (hen : t.pre p ≤ m p) (hnp : t.post p ≤ t.pre p) (hk : m p ≤ k) :
    fire m t p ≤ k := by
  have := fire_le m t p hen hnp; omega

/-- Conservation, by contrast, is an EQUALITY at the level of a weighted token
    count. A transition *conserves* weight when it produces exactly as much
    weighted mass as it consumes; loss transitions violate this (consume, no
    production) — exactly why liveness, which leans on conservation, does not
    survive loss. The two-place case the dock net (Phase 2) uses; `omega`
    discharges concrete instances. -/
def Conserves2 {P : Type} (t : Trans P) (a b : P) : Prop :=
  t.pre a + t.pre b = t.post a + t.post b

end LeanLift.Models.Petri
