/-
Phase A2 (step 2) — the weakest precondition over `λ-conc`.

Defines `wp γ e Φ` as the guarded fixpoint of a contractive functor `wpF`, with
the heap interpreted by the authoritative resource `stateInterp` (from
`HeapRes`). Structure follows the upstream worked example
`Iris/Examples/IProp.lean` (Example 3), adapted to `λ-conc`'s **relational**
`prim_step`.

Scope of this milestone: the wp tracks the **primary thread** only — the step
case quantifies over `prim_step e σ e' σ' efs` but does not yet impose the
forked-thread obligation `[∗ list] ef ∈ efs, wp ef ⊤` (that needs a big-op `ne`
lemma; tracked as the A2.2-fork extension). It also omits the progress
(`reducible`) conjunct, exactly as the upstream template does. Both are additive
extensions that do not change the fixpoint structure. Sorry-free.
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

/-- The weakest-precondition functor, in the standard `match toVal e` shape so
that `wp (val v)` is invertible (`= |==> Φ v`) and a leading update can be
absorbed (`bupd_wp`), which `wp_bind` needs. `wp` recurs only under `▷`, so `wpF`
is contractive. -/
def wpF (γ : GName) [HasHeap γ GF F]
    (wp : Expr → (Val → IProp GF) → IProp GF) (e : Expr) (Φ : Val → IProp GF) :
    IProp GF :=
  match toVal e with
  | some v => iprop(|==> Φ v)
  | none =>
    iprop(∀ σ, stateInterp γ σ -∗ |==>
      (∀ e' σ' efs, ⌜prim_step e σ e' σ' efs⌝ -∗ ▷ |==> (stateInterp γ σ' ∗ wp e' Φ)))

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
      exact HL m Hm e' Φ

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

/-- The step case of `wp`, exposed as a usable entailment (for non-values). -/
theorem wp_step (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ : Val → IProp GF)
    (hnv : toVal e = none) :
    wp (F := F) γ e Φ ⊢
      ∀ σ, stateInterp γ σ -∗ |==>
        (∀ e' σ' efs, ⌜prim_step e σ e' σ' efs⌝ -∗ ▷ |==> (stateInterp γ σ' ∗ wp (F := F) γ e' Φ)) := by
  refine (wp_unfold_fwd γ e Φ).trans ?_
  simp only [wpF, hnv]
  iintro H
  iexact H

end LeanliftIris.PhaseA
