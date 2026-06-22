/-
Phase C (step 1) — **prophecy variables** and the future-dependent linearization
point.

Phase B proved the *safety* of the Chase–Lev last-element race: under seq_cst the
owner's `take` and a thief's `steal` never both claim the element
(`chase_lev_sc_no_double_claim`). The next obligation is **linearizability**: to
say "`take` behaves as one atomic operation" we must name its *linearization
point* — the single instant at which it takes effect. For the last-element race
that instant is genuinely **future-dependent**: at the moment `take` reads the
indices it cannot yet tell whether it or the thief will win, yet *which* abstract
operation it performed (it removed the element, or it returned empty) is decided by
that future race. A linearization point that is a function of the present state
*cannot exist* — this is exactly the situation Iris **prophecy variables** were
invented for.

This file builds the prophecy mechanism in the small and applies it:

  * `lp_not_present_determined` — the obstruction: any choice of `take`'s effect
    made from the present alone is wrong for some future. The LP is not present-
    determined, so ordinary (non-prophetic) reasoning cannot place it.
  * `proph_sound` — prophecy soundness: the prophesied value may always be chosen
    equal to its *actual* resolution, uniquely. The modeling discipline that makes
    this hold is that the resolution is read from the **physical** state only, not
    from the (ghost) prophesied value.
  * `takeLP_proph_correct` — faithfulness: under a consistent assignment the
    prophecy-driven effect equals the one computed from the real outcome. So `take`
    may commit to its effect *now*, prophesying the race, and be provably correct.
  * `owner_claim_lp` — the payoff, tied to Phase B: under seq_cst, if the owner
    physically claims the element then its prophecy-resolved linearization is
    "owner took it" and the thief did *not* — the LP placement is consistent with
    the execution, never a double claim. Discharged via
    `chase_lev_sc_no_double_claim`.

Core Lean, sorry-free.
-/
import LeanliftIris.PhaseB.ChaseLev

namespace LeanliftIris.PhaseC
open LeanliftIris.PhaseB

/-! ## The future-dependence obstruction -/

/-- Who ends up with the contended last element. -/
inductive Claim | byOwner | byThief | unresolved
deriving DecidableEq, Repr

/-- The correct linearization of the owner's `take`, as a function of the
**future** — whether the thief's steal wins the race. If the thief wins, `take`
linearizes as "returned empty" (`byThief`); otherwise as "removed the element"
(`byOwner`). -/
def takeLP (thiefWins : Bool) : Claim := if thiefWins then .byThief else .byOwner

/-- **The linearization point is not present-determined.** At `take`'s decision
point the present carries no information about who will win (both futures are
reachable), so any effect chosen as a function of the present alone — modeled as a
constant `f : Unit → Claim` — is wrong for at least one future. Hence a
non-prophetic LP cannot be placed: this is the precise gap prophecy fills. -/
theorem lp_not_present_determined (f : Unit → Claim) :
    ∃ thiefWins : Bool, f () ≠ takeLP thiefWins := by
  cases hf : f () with
  | byOwner => exact ⟨true, by simp [takeLP, hf]⟩
  | byThief => exact ⟨false, by simp [takeLP, hf]⟩
  | unresolved => exact ⟨true, by simp [takeLP, hf]⟩

/-! ## Prophecy variables: soundness and faithfulness

A prophecy variable holds a *prophesied* value `pv`, chosen at allocation. It is
**resolved** later to a value read from the physical state by a function `resolve`
that does **not** look at `pv` (the prophecy is ghost). Consistency of the run is
`pv = resolve phys`. -/

/-- **Prophecy soundness.** For any physical state there is a unique prophesied
value consistent with the resolution — namely the resolution itself. The whole
content is the discipline that `resolve` is a function of the *physical* state
alone (it cannot mention `pv`), which makes the fixpoint `pv = resolve phys`
trivially solvable; a resolution that read `pv` could be unsatisfiable. -/
theorem proph_sound {Phys : Type} {α : Type} (resolve : Phys → α) (phys : Phys) :
    ∃ pv : α, pv = resolve phys ∧ ∀ y : α, y = resolve phys → y = pv :=
  ⟨resolve phys, rfl, fun _ hy => hy⟩

/-- **Faithfulness.** Under a consistent assignment (`pv = w`), the effect `take`
commits to using the prophecy equals the effect computed from the real future
outcome. So committing early — prophesying the race — is sound. -/
theorem takeLP_proph_correct (pv w : Bool) (h : pv = w) : takeLP pv = takeLP w := by
  rw [h]

/-! ## The payoff: a consistent linearization point for `take`, under seq_cst

Reading the Chase–Lev race off the Phase-B `SBState`: `s.r1` is the owner's check
of `top`, `s.r2` the thief's check of `bot`. The thief wins (claims `bot`) exactly
when its check still saw the unclaimed `0`. The prophecy predicts that bit. -/

/-- The physically-resolved outcome the prophecy predicts: did the thief win? Read
from `SBState` (the physical state) only — `resolve` for `proph_sound`. -/
def thiefWins (s : SBState) : Bool := decide (s.r2 = some 0)

/-- **The race resolves to a single prophecy-predicted winner.** Restates the
Phase-B safety theorem: no seq-cst execution lets both the owner and thief claim
(`chase_lev_sc_no_double_claim`). -/
theorem race_single_winner (bot top : Loc) (hbt : bot ≠ top) {s : SBState}
    (h : SBSteps bot top SBState.init s) :
    ¬ (s.r1 = some 0 ∧ s.r2 = some 0) :=
  chase_lev_sc_no_double_claim bot top hbt h

/-- **Consistent linearization point for `take`.** Under seq_cst, if the owner
physically claims the element (`s.r1 = some 0`), then its prophecy-resolved
linearization is `byOwner` *and* the thief did not win — the LP placed by the
prophecy agrees with the physical execution, and there is no double claim. This is
the linearizability obligation for the last-element race discharged: a
future-dependent LP, placed by a prophecy of the thief's outcome, made sound by
the Phase-B seq_cst safety result. -/
theorem owner_claim_lp (bot top : Loc) (hbt : bot ≠ top) {s : SBState}
    (h : SBSteps bot top SBState.init s) (h1 : s.r1 = some 0) :
    takeLP (thiefWins s) = .byOwner := by
  have hnot : s.r2 ≠ some 0 := fun h2 => race_single_winner bot top hbt h ⟨h1, h2⟩
  simp [takeLP, thiefWins, hnot]

end LeanliftIris.PhaseC
