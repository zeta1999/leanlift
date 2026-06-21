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
open Iris Iris.BI COFE HeapView One DFrac Agree LeibnizO OFE

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

/-- **Context inversion for `store`.** -/
theorem ctx_nil_of_store {K : List Frame} {a : Expr} {l : Nat} {v : Val} (ha : toVal a = none)
    (h : fill K a = .store (.val (.loc l)) (.val v)) :
    K = [] ∧ a = .store (.val (.loc l)) (.val v) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

/-- **Step inversion for `store`.** The sole step writes `v` at the (allocated)
location `l`, returns `unit`, forks nothing. -/
theorem prim_step_store_inv {l : Nat} {v : Val} {σ : Heap} {e' : Expr} {σ' : Heap}
    {efs : List Expr} (h : prim_step (.store (.val (.loc l)) (.val v)) σ e' σ' efs) :
    (∃ w, σ l = some w) ∧ e' = .val .unit ∧ σ' = σ.set l v ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_store ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | store hσ => exact ⟨⟨_, hσ⟩, hK', rfl, rfl⟩

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

/-- **Heap agreement.** Owning the authoritative heap and a points-to forces the
heap to contain that value at that location — the bridge from `stateInterp` to a
concrete `σ l`. -/
theorem stateInterp_pointsTo_agree {γ : GName} [HasHeap γ GF F]
    (σ : Heap) (l : Nat) (v : Val) :
    stateInterp (F := F) γ σ ∗ (l ↦[γ] v) ⊢ (⌜σ l = some v⌝ : IProp GF) := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  obtain ⟨_, _, Hl⟩ := auth_op_frag_one_validN_iff.mp H
  -- Hl : get? (toAgreeHeap σ) l ≡{n}≡ some (toAgree ⟨v⟩); reduce get? (fun-map) + toAgreeHeap
  simp only [Std.PartialMap.get?, Std.instPartialMapFun, toAgreeHeap] at Hl
  -- Hl : (σ l).map (fun w => toAgree ⟨w⟩) ≡{n}≡ some (toAgree ⟨v⟩)
  cases hσ : σ l with
  | none => rw [hσ] at Hl; simp at Hl
  | some w =>
    rw [hσ] at Hl
    simp only [Option.map_some] at Hl
    rw [some_dist_some] at Hl
    rw [LeibnizO.dist_inj (Agree.toAgree_injN Hl)]

/-- **Load rule.** Reading location `l` (owned as `l ↦ v`) returns `v` and gives
the points-to back to the continuation. The first heap operation verified against
the `wp`. -/
theorem wp_load (γ : GName) [HasHeap γ GF F] (l : Nat) (v : Val) (Φ : Val → IProp GF) :
    (l ↦[γ] v) ∗ ((l ↦[γ] v) -∗ |==> Φ v) ⊢
      wp (F := F) γ (.load (.val (.loc l))) Φ := by
  iintro ⟨Hpt, HΦ⟩
  iapply wp_lift_step
  iintro %σ Hsi
  ihave %Hag := stateInterp_pointsTo_agree (γ := γ) σ l v $$ [Hsi, Hpt]
  · isplitl [Hsi] <;> iassumption
  iintro %e' %σ' %efs %Hstep
  obtain ⟨w, hσl, he', hσ', hefs⟩ := prim_step_load_inv Hstep
  have hwv : w = v := by rw [hσl] at Hag; exact Option.some.inj Hag
  subst hwv; subst he'; subst hσ'; subst hefs
  iintro !>
  iintro !>
  isplitl [Hsi]
  · iexact Hsi
  · iapply wp_value
    iapply HΦ
    iexact Hpt

/-- Updating the authoritative map at `l` matches updating the heap there. The
`PartialMap` instance is pinned explicitly (the function-map functor is
higher-order, so it won't infer from `toAgreeHeap σ` alone). -/
theorem insert_toAgreeHeap (σ : Heap) (l : Nat) (v : Val) :
    @Std.PartialMap.insert (Nat → Option ·) Nat (@Std.instPartialMapFun Nat _)
        (Agree (LeibnizO Val)) (toAgreeHeap σ) l (toAgree (⟨v⟩ : LeibnizO Val))
      = toAgreeHeap (σ.set l v) := by
  funext k'
  simp only [Std.PartialMap.insert, toAgreeHeap, Heap.set]
  by_cases h : k' = l <;> simp_all [eq_comm]

/-- **Store rule.** Writing `v_new` to `l` (owned as `l ↦ v_old`) updates the
authoritative heap and the points-to and returns `unit`. The first *mutating*
rule: a frame-preserving ghost update (`HeapView.update_replace`); no heap
agreement is needed (full ownership). -/
theorem wp_store (γ : GName) [HasHeap γ GF F] (l : Nat) (v_old v_new : Val)
    (Φ : Val → IProp GF) :
    (l ↦[γ] v_old) ∗ ((l ↦[γ] v_new) -∗ |==> Φ .unit) ⊢
      wp (F := F) γ (.store (.val (.loc l)) (.val v_new)) Φ := by
  iintro ⟨Hpt, HΦ⟩
  iapply wp_lift_step
  iintro %σ Hsi
  iintro %e' %σ' %efs %Hstep
  obtain ⟨_, he', hσ', hefs⟩ := prim_step_store_inv Hstep
  subst he'; subst hσ'; subst hefs
  have hval : ✓ (toAgree (⟨v_new⟩ : LeibnizO Val)) :=
    CMRA.valid_op_left (toAgree_op_valid_iff_eq.mpr rfl)
  have Hrepl := update_replace (F := F) (H := (Nat → Option ·)) (k := l)
    (m1 := toAgreeHeap σ) (v1 := toAgree (⟨v_old⟩ : LeibnizO Val))
    (v2 := toAgree (⟨v_new⟩ : LeibnizO Val)) hval
  rw [insert_toAgreeHeap] at Hrepl
  -- explicit types ⇒ `iOwn_op`/`iOwn_update` infer their functor/instances
  have Hcomb_lem :
      (stateInterp (F := F) γ σ ∗ (l ↦[γ] v_old))
      ⊢ iOwn (GF := GF) (F := FHeap (F := F)) γ
          (Auth (own one) (toAgreeHeap σ)
            • Frag l (own one) (toAgree (⟨v_old⟩ : LeibnizO Val))) :=
    iOwn_op.mpr
  have Hupd_lem :
      (iOwn (GF := GF) (F := FHeap (F := F)) γ
        (Auth (own one) (toAgreeHeap σ)
          • Frag l (own one) (toAgree (⟨v_old⟩ : LeibnizO Val))))
      ⊢ |==> iOwn (GF := GF) (F := FHeap (F := F)) γ
        (Auth (own one) (toAgreeHeap (σ.set l v_new))
          • Frag l (own one) (toAgree (⟨v_new⟩ : LeibnizO Val))) :=
    iOwn_update Hrepl
  have Hsplit_lem :
      (iOwn (GF := GF) (F := FHeap (F := F)) γ
        (Auth (own one) (toAgreeHeap (σ.set l v_new))
          • Frag l (own one) (toAgree (⟨v_new⟩ : LeibnizO Val))))
      ⊢ (stateInterp (F := F) γ (σ.set l v_new) ∗ (l ↦[γ] v_new)) :=
    iOwn_op.mp
  iintro !>
  ihave Hcomb := Hcomb_lem $$ [Hsi, Hpt]
  · isplitl [Hsi] <;> iassumption
  ihave Hupd := Hupd_lem $$ [Hcomb]
  · iexact Hcomb
  imod Hupd with Hnew
  ihave ⟨HA, HF⟩ := Hsplit_lem $$ [Hnew]
  · iexact Hnew
  iintro !>
  isplitl [HA]
  · iexact HA
  · iapply wp_value
    iapply HΦ
    iexact HF

end LeanliftIris.PhaseA
