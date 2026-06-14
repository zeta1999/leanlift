/-
  LeanLift/Models/Fsm.lean — generic theory of (partial) finite-state machines.

  The REUSABLE substrate of the behavioural-models axis (docs/SPEC-models.md
  §4): a transition system is an initial state plus a *partial* step function

      init : S            step : S → E → Option S

  `step s e = none` means event `e` is BLOCKED in state `s`; `some s'` means the
  machine moves to `s'`. Partiality is what makes *synchronous composition*
  meaningful: a shared event fires only if EVERY component accepts it.

  Three results:
    1. `invariant_of_preserved` — model checking by proof: an inductive
       predicate that holds initially and is preserved by every step holds in
       every reachable state.
    2. `prodStep` + `reachable_fst/snd` — synchronous product and the
       projection theorem (joint reachability ⇒ component reachability).
    3. `prod_invariant` — component invariants lift to the product.

  Mathlib-free: core Lean 4 only, so this rides leanlift's integer toolchain
  (no Mathlib gate). Ported from the day48 FSM/Petri→Lean spike; the generated
  per-model files (Phase 1) reuse `Reachable` and `invariant_of_preserved`
  verbatim. The DTS-IR insight (docs/SPEC-models.md §4): every family — FSM,
  PT-net, CPN, BT — is one `step`, so this one induction principle serves all.
-/

namespace LeanLift.Models.Fsm

/-- States reachable from `init` under partial step function `step`.
    Two constructors = the two ways to be reachable: you are the initial state,
    or one enabled step away from a reachable state. -/
inductive Reachable {S E : Type} (init : S) (step : S → E → Option S) : S → Prop
  | refl : Reachable init step init
  | tail {s : S} {e : E} {s' : S} :
      Reachable init step s → step s e = some s' → Reachable init step s'

/-- THE workhorse: an inductive invariant holds in every reachable state.
    `hstep` must hold for ALL states satisfying `P`, not just reachable ones;
    if your property isn't inductive you must strengthen it first. -/
theorem invariant_of_preserved {S E : Type} {init : S} {step : S → E → Option S}
    (P : S → Prop) (h0 : P init)
    (hstep : ∀ s e s', P s → step s e = some s' → P s') :
    ∀ s, Reachable init step s → P s := by
  intro s h
  induction h with
  | refl => exact h0
  | tail _ hst ih => exact hstep _ _ _ ih hst

/-- Synchronous (lock-step) product: an event fires iff BOTH components accept
    it. Components share an event type; a component that "doesn't care" about an
    event should self-loop on it — see `lift`. -/
def prodStep {S₁ S₂ E : Type}
    (st₁ : S₁ → E → Option S₁) (st₂ : S₂ → E → Option S₂)
    (s : S₁ × S₂) (e : E) : Option (S₁ × S₂) :=
  match st₁ s.1 e, st₂ s.2 e with
  | some a, some b => some (a, b)
  | _, _ => none

/-- Inversion: a successful product step is a successful step in each component. -/
theorem prodStep_eq_some {S₁ S₂ E : Type}
    {st₁ : S₁ → E → Option S₁} {st₂ : S₂ → E → Option S₂}
    {s s' : S₁ × S₂} {e : E}
    (h : prodStep st₁ st₂ s e = some s') :
    st₁ s.1 e = some s'.1 ∧ st₂ s.2 e = some s'.2 := by
  unfold prodStep at h
  cases h₁ : st₁ s.1 e with
  | none => simp [h₁] at h
  | some a =>
    cases h₂ : st₂ s.2 e with
    | none => simp [h₁, h₂] at h
    | some b =>
      simp [h₁, h₂] at h
      subst h
      exact ⟨rfl, rfl⟩

/-- Projection (left): reachable in the product ⇒ first component reachable. -/
theorem reachable_fst {S₁ S₂ E : Type}
    {i₁ : S₁} {i₂ : S₂} {st₁ : S₁ → E → Option S₁} {st₂ : S₂ → E → Option S₂}
    {p : S₁ × S₂}
    (h : Reachable (i₁, i₂) (prodStep st₁ st₂) p) :
    Reachable i₁ st₁ p.1 := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact .tail ih (prodStep_eq_some hst).1

/-- Projection (right). -/
theorem reachable_snd {S₁ S₂ E : Type}
    {i₁ : S₁} {i₂ : S₂} {st₁ : S₁ → E → Option S₁} {st₂ : S₂ → E → Option S₂}
    {p : S₁ × S₂}
    (h : Reachable (i₁, i₂) (prodStep st₁ st₂) p) :
    Reachable i₂ st₂ p.2 := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact .tail ih (prodStep_eq_some hst).2

/-- COMPOSITION: invariants of the components conjoin to an invariant of the
    product. Free from the projections — no new induction. The converse is
    false (the product reaches FEWER states than the cartesian product of the
    component reachable sets), so cross-machine safety must be proved by
    induction on the PRODUCT, not assembled per-machine. -/
theorem prod_invariant {S₁ S₂ E : Type}
    {i₁ : S₁} {i₂ : S₂} {st₁ : S₁ → E → Option S₁} {st₂ : S₂ → E → Option S₂}
    (P₁ : S₁ → Prop) (P₂ : S₂ → Prop)
    (h₁ : ∀ s, Reachable i₁ st₁ s → P₁ s)
    (h₂ : ∀ s, Reachable i₂ st₂ s → P₂ s) :
    ∀ p, Reachable (i₁, i₂) (prodStep st₁ st₂) p → P₁ p.1 ∧ P₂ p.2 :=
  fun _ hp => ⟨h₁ _ (reachable_fst hp), h₂ _ (reachable_snd hp)⟩

/-- Alphabet lifting: make a machine TOTAL on events it doesn't handle by
    self-looping. The exporter performs exactly this when padding a machine's
    step over the shared event type. -/
def lift {S E : Type} (step : S → E → Option S) (handles : E → Bool) :
    S → E → Option S :=
  fun s e => if handles e then step s e else some s

end LeanLift.Models.Fsm
