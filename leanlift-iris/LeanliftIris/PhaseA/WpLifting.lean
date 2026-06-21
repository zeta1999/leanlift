/-
Phase A2 (step 3) — lifting lemmas for the `wp`.

To verify a concrete operation we must (a) invert `prim_step` — show the only way
a value-argument redex like `load (loc l)` steps is the head rule — and (b) feed
that into the `wp` step case (`wp_lift_step`). Inversion rests on the fact that a
redex plugged into any non-empty evaluation context is never a value
(`fill_toVal_none`), so the context must be empty.

This file establishes the generic lifting rule and the inversion infrastructure,
worked end to end for `load`. Sorry-free.
-/
import LeanliftIris.PhaseA.Wp

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE

/-! ## `prim_step` inversion infrastructure (pure, over `Lang`) -/

/-- A head redex is never a value. -/
theorem head_toVal_none {a σ e' σ' efs} (h : Head a σ e' σ' efs) : toVal a = none := by
  cases h <;> rfl

/-- A redex plugged into any context is never a value. -/
theorem fill_toVal_none {a : Expr} (ha : toVal a = none) :
    ∀ K, toVal (fill K a) = none := by
  intro K
  cases K with
  | nil => simpa [fill] using ha
  | cons fr K' => cases fr <;> simp [fill, List.foldr_cons, fill1, toVal]

/-- **Context inversion for `load`.** If a redex plugs to `load (loc l)`, the
context is empty and the redex is the whole `load`. -/
theorem ctx_nil_of_load {K : List Frame} {a : Expr} {l : Nat} (ha : toVal a = none)
    (h : fill K a = .load (.val (.loc l))) :
    K = [] ∧ a = .load (.val (.loc l)) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

/-- **Step inversion for `load`.** The sole primitive step of `load (loc l)` is
the head read: it yields the stored value, leaves the heap and thread-pool
unchanged. -/
theorem prim_step_load_inv {l : Nat} {σ : Heap} {e' : Expr} {σ' : Heap} {efs : List Expr}
    (h : prim_step (.load (.val (.loc l))) σ e' σ' efs) :
    ∃ v, σ l = some v ∧ e' = .val v ∧ σ' = σ ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_load ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | load hσ => exact ⟨_, hσ, hK', rfl, rfl⟩

/-! ## Generic lifting -/

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-- **Generic step lifting.** Proving the `wp` step body (re-establish the state
interpretation and the continuation `wp` after any primitive step) suffices to
verify a non-value expression. The per-operation rules below are corollaries. -/
theorem wp_lift_step (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ : Val → IProp GF) :
    (∀ σ, stateInterp γ σ -∗
      ∀ e' σ' efs, ⌜prim_step e σ e' σ' efs⌝ -∗ ▷ |==> (stateInterp γ σ' ∗ wp (F := F) γ e' Φ))
    ⊢ wp (F := F) γ e Φ := by
  iintro H
  iapply wp_unfold
  simp only [wpF]
  iright
  iexact H

end LeanliftIris.PhaseA
