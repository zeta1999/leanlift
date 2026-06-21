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

/-- The weakest-precondition functor. `wp` recurs only under `▷`, so `wpF` is
contractive. -/
def wpF (γ : GName) [HasHeap γ GF F]
    (wp : Expr → (Val → IProp GF) → IProp GF) (e : Expr) (Φ : Val → IProp GF) :
    IProp GF := iprop(
  (∃ v, ⌜toVal e = some v⌝ ∗ |==> Φ v) ∨
  (∀ σ, stateInterp γ σ -∗
    ∀ e' σ' efs, ⌜prim_step e σ e' σ' efs⌝ -∗
      ▷ |==> (stateInterp γ σ' ∗ wp e' Φ)))

instance wpF_contractive (γ : GName) [HasHeap γ GF F] :
    Contractive (wpF (F := F) γ) where
  distLater_dist {n x y HL} e Φ := by
    refine or_ne.ne (.of_eq rfl) ?_
    refine forall_ne (fun σ => ?_)
    refine wand_ne.ne (.of_eq rfl) ?_
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

/-- **Value rule** (smoke test that the `wp` is usable): to verify a value it
suffices to (update-)establish the postcondition. -/
theorem wp_value (γ : GName) [HasHeap γ GF F] (v : Val) (Φ : Val → IProp GF) :
    (|==> Φ v) ⊢ wp (F := F) γ (.val v) Φ := by
  iintro H
  iapply wp_unfold
  simp only [wpF]
  ileft
  iexists v
  isplitl []
  · ipure_intro; rfl
  · iexact H

end LeanliftIris.PhaseA
