/-
Phase A2 (step 2) — the weakest precondition over `λ-conc`.

Defines `wp γ e Φ` as the guarded fixpoint of a contractive functor `wpF`, with
the heap interpreted by the authoritative resource `stateInterp` (from
`HeapRes`). Structure follows the upstream worked example
`Iris/Examples/IProp.lean` (Example 3), adapted to `λ-conc`'s **relational**
`prim_step`.

The step case quantifies over `prim_step e σ e' σ' efs` and imposes the
**forked-thread obligation** `forkObl wp efs` (= `[∗ list] ef ∈ efs, wp ef True`):
every thread spawned by the step must itself be verified (against the trivial
postcondition), exactly as upstream Iris' `wp` does. This is what makes the
thread-pool adequacy (`PoolAdequacy.lean`) possible — without it a forked thread
could mutate the heap behind the primary thread's back. `forkObl` is a plain
list recursion (not `bigSep`, whose singleton case is not definitional), so
`forkObl wp [] = emp` and `forkObl wp (ef :: efs) = wp ef True ∗ forkObl wp efs`
hold by `rfl`. The progress (`reducible`) conjunct is still omitted, as in the
upstream template. Sorry-free.
-/
import LeanliftIris.PhaseA.HeapRes

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE HeapView One DFrac Agree LeibnizO OFE

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-- Project the value of an expression, if it is one. -/
def toVal : Expr → Option Val
  | .val v => some v
  | _      => none

/-- An expression is reducible in a heap if it can take some primitive step. -/
def reducible (e : Expr) (σ : Heap) : Prop :=
  ∃ e' σ' efs, prim_step e σ e' σ' efs

/-- View the heap as a map into agreed-upon values (the authoritative content). -/
def toAgreeHeap (σ : Heap) : Nat → Option (Agree (LeibnizO Val)) :=
  fun l => (σ l).map (fun v => toAgree ⟨v⟩)

/-- State interpretation: full authoritative ownership of the whole heap. The
points-to fragments (`HeapRes.pointsTo`) carve pieces out of this. -/
def stateInterp (γ : GName) [HasHeap γ GF F] (σ : Heap) : IProp GF :=
  iOwn (GF := GF) (F := FHeap (F := F)) γ (Auth (own one) (toAgreeHeap σ))

/-- **Forked-thread obligation.** Every thread in `efs` is verified by `wp`
against the trivial postcondition. Defined by list recursion so both equations
are definitional. -/
def forkObl (wp : Expr → (Val → IProp GF) → IProp GF) : List Expr → IProp GF
  | [] => iprop(emp)
  | ef :: efs => iprop(wp ef (fun _ => iprop(True)) ∗ forkObl wp efs)

@[simp] theorem forkObl_nil (wp : Expr → (Val → IProp GF) → IProp GF) :
    forkObl wp [] = iprop(emp) := rfl

@[simp] theorem forkObl_cons (wp : Expr → (Val → IProp GF) → IProp GF) (ef : Expr)
    (efs : List Expr) :
    forkObl wp (ef :: efs) = iprop(wp ef (fun _ => iprop(True)) ∗ forkObl wp efs) := rfl

/-- `forkObl` is non-expansive in the `wp` argument, pointwise. -/
theorem forkObl_dist {n : Nat} {wp1 wp2 : Expr → (Val → IProp GF) → IProp GF}
    (h : ∀ e Φ, wp1 e Φ ≡{n}≡ wp2 e Φ) (efs : List Expr) :
    forkObl wp1 efs ≡{n}≡ forkObl wp2 efs := by
  induction efs with
  | nil => exact .of_eq rfl
  | cons ef efs ih => exact sep_ne.ne (h ef _) ih

/-- The weakest-precondition functor, in the standard `match toVal e` shape so
that `wp (val v)` is invertible (`= |==> Φ v`) and a leading update can be
absorbed (`bupd_wp`), which `wp_bind` needs. The step case re-establishes the
state interpretation, the primary continuation, and the forked-thread obligation.
`wp` recurs only under `▷`, so `wpF` is contractive. -/
def wpF (γ : GName) [HasHeap γ GF F]
    (wp : Expr → (Val → IProp GF) → IProp GF) (e : Expr) (Φ : Val → IProp GF) :
    IProp GF :=
  match toVal e with
  | some v => iprop(|==> Φ v)
  | none =>
    iprop(∀ σ, stateInterp γ σ -∗ |==>
      (∀ e' σ' efs, ⌜prim_step e σ e' σ' efs⌝ -∗
        ▷ |==> (stateInterp γ σ' ∗ wp e' Φ ∗ forkObl wp efs)))

instance wpF_contractive (γ : GName) [HasHeap γ GF F] :
    Contractive (wpF (F := F) γ) where
  distLater_dist {n x y HL} e Φ := by
    simp only [wpF]
    split
    · exact .of_eq rfl
    · refine forall_ne (fun σ => ?_)
      refine wand_ne.ne (.of_eq rfl) ?_
      refine BIUpdate.bupd_ne.ne ?_
      refine forall_ne (fun e' => ?_)
      refine forall_ne (fun σ' => ?_)
      refine forall_ne (fun efs => ?_)
      refine wand_ne.ne (.of_eq rfl) ?_
      refine Contractive.distLater_dist (fun m Hm => ?_)
      refine BIUpdate.bupd_ne.ne ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (HL m Hm e' Φ) ?_
      exact forkObl_dist (fun e Ψ => HL m Hm e Ψ) efs

/-- The weakest precondition: the guarded fixpoint of `wpF`. -/
def wp (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  (fixpoint (wpF (F := F) γ)) e Φ

/-- The fixpoint equation: `wp` unfolds to one application of `wpF`. -/
theorem wp_unfold (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ : Val → IProp GF) :
    wp (F := F) γ e Φ ≡ wpF (F := F) γ (wp (F := F) γ) e Φ := by
  apply fixpoint_unfold (f := ⟨wpF (F := F) γ, ne_of_contractive _⟩)

/-- **Value rule.** `wp (val v)` is exactly an update of the postcondition. -/
theorem wp_value (γ : GName) [HasHeap γ GF F] (v : Val) (Φ : Val → IProp GF) :
    (|==> Φ v) ⊢ wp (F := F) γ (.val v) Φ := by
  iintro H
  iapply wp_unfold
  simp only [wpF, toVal]
  iexact H

/-- `wp` unfolded as a forward entailment. -/
theorem wp_unfold_fwd (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ : Val → IProp GF) :
    wp (F := F) γ e Φ ⊢ wpF (F := F) γ (wp (F := F) γ) e Φ :=
  (equiv_iff.mp (wp_unfold γ e Φ)).mp

/-- The functor absorbs a leading update (`match`-shape: value case is `|==> Φ v`,
step case has the update after `stateInterp`). -/
theorem bupd_wpF (γ : GName) [HasHeap γ GF F]
    (wp : Expr → (Val → IProp GF) → IProp GF) (e : Expr) (Φ : Val → IProp GF) :
    (|==> wpF (F := F) γ wp e Φ) ⊢ wpF (F := F) γ wp e Φ := by
  cases hv : toVal e with
  | some v =>
    simp only [wpF, hv]
    iintro H
    imod H with H
    iexact H
  | none =>
    simp only [wpF, hv]
    iintro H
    iintro %σ Hσ
    imod H with H
    iapply H
    iexact Hσ

/-- **Absorb a leading update.** The bridge for the value case of `wp_bind`. -/
theorem bupd_wp (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ : Val → IProp GF) :
    (|==> wp (F := F) γ e Φ) ⊢ wp (F := F) γ e Φ :=
  ((BIUpdate.mono (wp_unfold_fwd γ e Φ)).trans (bupd_wpF γ (wp (F := F) γ) e Φ)).trans
    (equiv_iff.mp (wp_unfold γ e Φ)).mpr

/-- `wp` at a value is an update of the postcondition (the inverse of
`wp_value`). -/
theorem wp_value_inv (γ : GName) [HasHeap γ GF F] (v : Val) (Φ : Val → IProp GF) :
    wp (F := F) γ (.val v) Φ ⊢ |==> Φ v := by
  refine (wp_unfold_fwd γ (.val v) Φ).trans ?_
  simp only [wpF, toVal]
  iintro H
  iexact H

/-- The step case of `wp`, exposed as a usable entailment (for non-values). -/
theorem wp_step (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ : Val → IProp GF)
    (hnv : toVal e = none) :
    wp (F := F) γ e Φ ⊢
      ∀ σ, stateInterp γ σ -∗ |==>
        (∀ e' σ' efs, ⌜prim_step e σ e' σ' efs⌝ -∗
          ▷ |==> (stateInterp γ σ' ∗ wp (F := F) γ e' Φ ∗ forkObl (wp (F := F) γ) efs)) := by
  refine (wp_unfold_fwd γ e Φ).trans ?_
  simp only [wpF, hnv]
  iintro H
  iexact H

/-- A step that forks nothing owes no fork obligation: `forkObl wp [] = emp` is
absorbed. Used by every lifting rule whose inversion lemma yields `efs = []`. -/
theorem sep_sep_forkObl_nil (wp : Expr → (Val → IProp GF) → IProp GF) (P Q : IProp GF) :
    iprop(P ∗ Q) ⊢ iprop(P ∗ Q ∗ forkObl wp []) := by
  simp only [forkObl_nil]
  exact sep_mono_r sep_emp.mpr

end LeanliftIris.PhaseA
