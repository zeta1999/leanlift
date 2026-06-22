/-
Phase A2 (step 4) — adequacy for the `λ-conc` weakest precondition.

Adequacy is the trust anchor: a proof `⊢ wp e Φ` in the logic entails an
operational fact about the real `λ-conc` program — closing leanlift's model/code
gap for this lane. We build it from:

  * `wp_step_pres` — one primitive step preserves `stateInterp ∗ wp` (up to the
    `▷`/`|==>` the `wp` carries), the iProp-level heart;
  * the model soundness of `|==> ⌜·⌝` and `▷` (`pure_soundness`, `later_soundness`)
    to extract a meta-level `Prop` after a finite run.

This file currently establishes the preservation step; the meta-level extraction
over `steps` is the remaining piece (tracked in docs/TODO-concurrency.md).
Sorry-free.
-/
import LeanliftIris.PhaseA.WpLifting

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-- **Preservation.** One primitive step of a non-value `e` turns
`stateInterp γ σ ∗ wp γ e Φ` into the interpretation + continuation at the
stepped-to state, modulo the update/later the `wp` carries. -/
theorem wp_step_pres (γ : GName) [HasHeap γ GF F] (e : Expr) (σ : Heap) (e' : Expr)
    (σ' : Heap) (efs : List Expr) (Φ : Val → IProp GF) (hnv : toVal e = none)
    (hstep : prim_step e σ e' σ' efs) :
    stateInterp γ σ ∗ wp (F := F) γ e Φ ⊢
      |==> ▷ |==> (stateInterp γ σ' ∗ wp (F := F) γ e' Φ) := by
  iintro ⟨Hσ, Hwp⟩
  ihave H1 := (wp_step γ e Φ hnv) $$ [Hwp]
  · iexact Hwp
  ihave H2 := H1 $$ [Hσ]
  · iexact Hσ
  imod H2 with H3
  ispecialize H3 $$ %e'
  ispecialize H3 $$ %σ'
  ispecialize H3 $$ %efs
  ispecialize H3 $$ []
  · ipure_intro; exact hstep
  iintro !>
  iexact H3

/-- **Adequacy, base case.** A value verified against a pure postcondition
satisfies it at the meta level. Exercises the soundness path
(`wp_value_inv` → `bupd_elim` → `pure_soundness`). -/
theorem wp_adequacy_val (γ : GName) [HasHeap γ GF F] (v : Val) (φ : Val → Prop)
    (h : ⊢ wp (F := F) γ (.val v) (fun w => iprop(⌜φ w⌝))) : φ v := by
  -- |==> ⌜φ v⌝ ⊢ ⌜φ v⌝ (bupd over a plain pure)
  have hbupd : (iprop(|==> ⌜φ v⌝) : IProp GF) ⊢ iprop(⌜φ v⌝) :=
    (BIUpdate.mono plainly_pure.mpr).trans BIBUpdatePlainly.bupd_plainly
  have hb : (emp : IProp GF) ⊢ iprop(⌜φ v⌝) :=
    (h.trans (wp_value_inv γ v (fun w => iprop(⌜φ w⌝)))).trans hbupd
  have hte : (iprop(True) : IProp GF) ⊢ emp := biaffine_iff_true_emp.1 inferInstance
  exact UPred.pure_soundness (hte.trans hb)

end LeanliftIris.PhaseA
