/-
  LeanLift/Models/Ctmc.lean — the QUALITATIVE half of the stochastic story
  (docs/SPEC-models.md §5/§6, day49). Mathlib-free.

  The division of labour for a stochastic system:
    * QUALITATIVE — `freed` reachable, `freed` absorbing, and the chain
      INEVITABLY reaches `freed` (the probability-1 absorption skeleton, CTL
      `AF`). First-order and kernel-checkable. Proved here.
    * QUANTITATIVE — P(freed) = 1−p^(K+1), E[time], P(freed ≤ T). Numerical CTMC
      analysis (`lift model prism` / PRISM), NOT cheap in a proof assistant.

  In slogan form: **Lean says it must happen; PRISM says how fast.** PRISM's
  CSL `P=?[F freed]` is the quantitative refinement of CTL's `AF freed` (`Inev`)
  proved below — the proof certifies the event the model checker measures is one
  that can and must occur.

  This file proves the lease-mode dock skeleton (the embedded jump chain, rates
  erased). The generic `Inev` + `inev_of_variant` machinery is reusable for any
  qualitative liveness argument.
-/

namespace LeanLift.Models.Ctmc

/-- Tangible state of the lease CTMC: in-flight with budget `b`, or freed.
    (The immediate `send` is pre-collapsed, as in the exported PRISM model.) -/
inductive Stage | inflight | freed
  deriving DecidableEq, Repr

structure S where
  stage : Stage
  b : Nat
  deriving DecidableEq, Repr

/-- The embedded jump chain (which jumps are POSSIBLE, rates erased). `lose` is
    `b+1 → b`, so it is only possible with budget left — at `b = 0` the sole jump
    is `deliver`: bounded loss ⇒ forced delivery. -/
inductive Step : S → S → Prop
  | deliver {b} : Step ⟨.inflight, b⟩ ⟨.freed, b⟩
  | lose    {b} : Step ⟨.inflight, b + 1⟩ ⟨.inflight, b⟩

/-- The goal: the dock is freed. -/
def done (s : S) : Prop := s.stage = .freed

/-- `freed` is ABSORBING: no jump leaves it (a bottom SCC — the precondition for
    "absorption probability" to be well-defined). -/
theorem freed_absorbing (b : Nat) (s' : S) : ¬ Step ⟨.freed, b⟩ s' := by
  intro h; cases h

/-- The variant: `rank` strictly decreases on every jump. -/
def rank (s : S) : Nat :=
  match s.stage with
  | .freed => 0
  | .inflight => s.b + 1

/-- "Inevitably `P`" (CTL's AF), inlined. -/
inductive Inev (step : S → S → Prop) (P : S → Prop) : S → Prop
  | here   {s} : P s → Inev step P s
  | onward {s} : (∃ s', step s s') → (∀ s', step s s' → Inev step P s') → Inev step P s

/-- Variant ⇒ inevitability (the liveness proof rule), by strong induction on rank. -/
theorem inev_of_variant (step : S → S → Prop) (P : S → Prop) (rank : S → Nat)
    (prog : ∀ s, ¬ P s → ∃ s', step s s')
    (decr : ∀ s s', step s s' → rank s' < rank s) :
    ∀ s, Inev step P s := by
  have key : ∀ n s, rank s = n → Inev step P s := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n IH =>
      intro s hs
      by_cases hP : P s
      · exact .here hP
      · refine .onward (prog s hP) ?_
        intro s' hstep
        exact IH (rank s') (by have := decr s s' hstep; omega) s' rfl
  intro s; exact key (rank s) s rfl

/-- Progress: every non-freed state can jump (`deliver` is always available). -/
theorem prog : ∀ s, ¬ done s → ∃ s', Step s s' := by
  intro s hnd
  obtain ⟨st, b⟩ := s
  cases st with
  | inflight => exact ⟨_, .deliver⟩
  | freed => exact absurd rfl hnd

/-- Every jump strictly decreases the variant. -/
theorem decr : ∀ s s', Step s s' → rank s' < rank s := by
  intro s s' h
  cases h <;> simp only [rank] <;> omega

/-- THE qualitative theorem: from ANY state the dock is INEVITABLY freed — every
    path reaches `freed` in finitely many jumps. The probability-1 absorption
    skeleton; PRISM computes the rate/time, but cannot reach `freed` with
    positive probability unless this holds. -/
theorem inevitably_freed : ∀ s, Inev Step done s :=
  inev_of_variant Step done rank prog decr

/-- And `freed` is reachable: from the start in one `deliver`. -/
theorem freed_reachable (K : Nat) : Step ⟨.inflight, K⟩ ⟨.freed, K⟩ := .deliver

end LeanLift.Models.Ctmc
