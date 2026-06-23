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

/-- **Frame disambiguation.** When the hole content is a non-value, a frame is
determined by the filled expression: `fill1` is injective in both the frame and
the hole. (The basis of `step_by_val` for `wp_bind`.) -/
theorem fill1_inj {fr fr' : Frame} {X Y : Expr} (h : fill1 fr X = fill1 fr' Y)
    (hX : toVal X = none) (hY : toVal Y = none) : fr = fr' ∧ X = Y := by
  cases fr <;> cases fr' <;> simp_all [fill1, toVal] <;> grind

/-- A head redex's frame-hole is always a value: a redex never sits *above* a
non-value subterm (rules out the `K' = []` case in `step_by_val`). -/
theorem head_fill1 {fr : Frame} {X : Expr} {σ : Heap} {e' : Expr} {σ' : Heap}
    {efs : List Expr} (h : Head (fill1 fr X) σ e' σ' efs) : toVal X ≠ none := by
  cases fr <;> simp only [fill1] at h <;> cases h <;> simp [toVal]

/-- **Context decomposition** (the inductive core of `step_by_val`). If a non-value
`e` plugged under `K` equals a head-redex `a` plugged under `K'`, then `a` lies
inside `e`: `K' = K ++ K2` and `e = fill K2 a`. -/
theorem fill_eq_decomp {e a : Expr} (ha : toVal a = none)
    (hHa : ∀ fr X, fill1 fr X = a → toVal X ≠ none) (he : toVal e = none) :
    ∀ (K K' : List Frame), fill K e = fill K' a → ∃ K2, K' = K ++ K2 ∧ e = fill K2 a := by
  intro K
  induction K with
  | nil => intro K' h; exact ⟨K', rfl, by simpa [fill] using h⟩
  | cons fr Krest ih =>
    intro K' h
    cases K' with
    | nil =>
      exfalso
      simp only [fill, List.foldr_cons] at h
      exact hHa fr (fill Krest e) (by simpa [fill] using h) (fill_toVal_none he Krest)
    | cons fr' K'rest =>
      simp only [fill, List.foldr_cons] at h
      obtain ⟨hfr, hfill⟩ :=
        fill1_inj h (fill_toVal_none he Krest) (fill_toVal_none ha K'rest)
      subst hfr
      obtain ⟨K2, hK2, he2⟩ := ih K'rest hfill
      exact ⟨K2, by rw [hK2]; rfl, he2⟩

/-- **`step_by_val`.** A primitive step of `fill K e` (with `e` not a value)
happens *inside* `e`: it decomposes into a step of `e` under the same context. -/
theorem fill_step_inv {K : List Frame} {e : Expr} {σ : Heap} {e'' : Expr} {σ' : Heap}
    {efs : List Expr} (h : prim_step (fill K e) σ e'' σ' efs) (he : toVal e = none) :
    ∃ e', e'' = fill K e' ∧ prim_step e σ e' σ' efs := by
  obtain ⟨K', a, a', hK, hK', hHead⟩ := h
  have ha : toVal a = none := head_toVal_none hHead
  have hHa : ∀ fr X, fill1 fr X = a → toVal X ≠ none := by
    intro fr X hfX
    rw [← hfX] at hHead
    exact head_fill1 hHead
  obtain ⟨K2, hKeq, heq⟩ := fill_eq_decomp ha hHa he K K' hK
  subst hKeq
  refine ⟨fill K2 a', ?_, ⟨K2, a, a', heq, rfl, hHead⟩⟩
  rw [hK', fill_app]

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

/-- **Context inversion for `if`** (scrutinee a boolean value). -/
theorem ctx_nil_of_ite {K : List Frame} {a : Expr} {b : Bool} {e1 e2 : Expr}
    (ha : toVal a = none) (h : fill K a = .ite (.val (.bool b)) e1 e2) :
    K = [] ∧ a = .ite (.val (.bool b)) e1 e2 := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

/-- **Step inversion for `if true`.** The sole step selects the then-branch. -/
theorem prim_step_ite_true_inv {e1 e2 : Expr} {σ : Heap} {e' : Expr} {σ' : Heap}
    {efs : List Expr} (h : prim_step (.ite (.val (.bool true)) e1 e2) σ e' σ' efs) :
    e' = e1 ∧ σ' = σ ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_ite ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | iteT => exact ⟨hK', rfl, rfl⟩

/-- **Context inversion for `cas`** (all three arguments values). -/
theorem ctx_nil_of_cas {K : List Frame} {a : Expr} {l : Nat} {v1 v2 : Val}
    (ha : toVal a = none) (h : fill K a = .cas (.val (.loc l)) (.val v1) (.val v2)) :
    K = [] ∧ a = .cas (.val (.loc l)) (.val v1) (.val v2) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

/-- **Step inversion for `cas`.** A `cas` either succeeds (the cell held the
expected `v1`, writes `v2`, returns `true`) or fails (held something else,
unchanged, returns `false`). -/
theorem prim_step_cas_inv {l : Nat} {v1 v2 : Val} {σ : Heap} {e' : Expr} {σ' : Heap}
    {efs : List Expr} (h : prim_step (.cas (.val (.loc l)) (.val v1) (.val v2)) σ e' σ' efs) :
    ∃ v0, σ l = some v0 ∧
      ((v0 = v1 ∧ e' = .val (.bool true) ∧ σ' = σ.set l v2 ∧ efs = []) ∨
       (v0 ≠ v1 ∧ e' = .val (.bool false) ∧ σ' = σ ∧ efs = [])) := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_cas ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | casS hσ he => exact ⟨_, hσ, Or.inl ⟨he, hK', rfl, rfl⟩⟩
  | casF hσ hne => exact ⟨_, hσ, Or.inr ⟨hne, hK', rfl, rfl⟩⟩

/-- **Context inversion for `faa`** (both arguments values). -/
theorem ctx_nil_of_faa {K : List Frame} {a : Expr} {l : Nat} {n : Int}
    (ha : toVal a = none) (h : fill K a = .faa (.val (.loc l)) (.val (.int n))) :
    K = [] ∧ a = .faa (.val (.loc l)) (.val (.int n)) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

/-- **Step inversion for `faa`.** Fetch-and-add reads the integer `m` at `l`,
writes `m + n`, and returns the old `m`. -/
theorem prim_step_faa_inv {l : Nat} {n : Int} {σ : Heap} {e' : Expr} {σ' : Heap}
    {efs : List Expr} (h : prim_step (.faa (.val (.loc l)) (.val (.int n))) σ e' σ' efs) :
    ∃ m, σ l = some (.int m) ∧ e' = .val (.int m) ∧
      σ' = σ.set l (.int (m + n)) ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_faa ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | faa hσ => exact ⟨_, hσ, hK', rfl, rfl⟩

/-- **Context inversion for `alloc`.** -/
theorem ctx_nil_of_alloc {K : List Frame} {a : Expr} {v : Val} (ha : toVal a = none)
    (h : fill K a = .alloc (.val v)) :
    K = [] ∧ a = .alloc (.val v) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

/-- **Step inversion for `alloc`.** Allocation picks some fresh location. -/
theorem prim_step_alloc_inv {v : Val} {σ : Heap} {e' : Expr} {σ' : Heap} {efs : List Expr}
    (h : prim_step (.alloc (.val v)) σ e' σ' efs) :
    ∃ l, σ l = none ∧ e' = .val (.loc l) ∧ σ' = σ.set l v ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_alloc ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | alloc hσ => exact ⟨_, hσ, hK', rfl, rfl⟩

/-- **Context inversion for `app`** (function and argument both values). -/
theorem ctx_nil_of_app {K : List Frame} {a : Expr} {f x : String} {body : Expr} {w : Val}
    (ha : toVal a = none) (h : fill K a = .app (.val (.clos f x body)) (.val w)) :
    K = [] ∧ a = .app (.val (.clos f x body)) (.val w) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

/-- **Step inversion for β** (application of a closure to a value). -/
theorem prim_step_beta_inv {f x : String} {body : Expr} {w : Val} {σ : Heap}
    {e' : Expr} {σ' : Heap} {efs : List Expr}
    (h : prim_step (.app (.val (.clos f x body)) (.val w)) σ e' σ' efs) :
    e' = substE x w (substE f (.clos f x body) body) ∧ σ' = σ ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_app ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | beta => exact ⟨hK', rfl, rfl⟩

/-- **Context inversion for `pairE`** (both components values). -/
theorem ctx_nil_of_pair {K : List Frame} {a : Expr} {x y : Val} (ha : toVal a = none)
    (h : fill K a = .pairE (.val x) (.val y)) :
    K = [] ∧ a = .pairE (.val x) (.val y) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

/-- **Step inversion for `pairE`.** -/
theorem prim_step_pair_inv {x y : Val} {σ : Heap} {e' : Expr} {σ' : Heap} {efs : List Expr}
    (h : prim_step (.pairE (.val x) (.val y)) σ e' σ' efs) :
    e' = .val (.pair x y) ∧ σ' = σ ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_pair ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | pair => exact ⟨hK', rfl, rfl⟩

theorem ctx_nil_of_fst {K : List Frame} {a : Expr} {x y : Val} (ha : toVal a = none)
    (h : fill K a = .fstE (.val (.pair x y))) :
    K = [] ∧ a = .fstE (.val (.pair x y)) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

theorem prim_step_fst_inv {x y : Val} {σ : Heap} {e' : Expr} {σ' : Heap} {efs : List Expr}
    (h : prim_step (.fstE (.val (.pair x y))) σ e' σ' efs) :
    e' = .val x ∧ σ' = σ ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_fst ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | fst => exact ⟨hK', rfl, rfl⟩

theorem ctx_nil_of_snd {K : List Frame} {a : Expr} {x y : Val} (ha : toVal a = none)
    (h : fill K a = .sndE (.val (.pair x y))) :
    K = [] ∧ a = .sndE (.val (.pair x y)) := by
  cases K with
  | nil => exact ⟨rfl, by simpa [fill] using h⟩
  | cons fr K' =>
    exfalso
    have hnv : toVal (fill K' a) = none := fill_toVal_none ha K'
    simp only [fill, List.foldr_cons] at h hnv
    cases fr <;> simp_all [fill1, toVal]

theorem prim_step_snd_inv {x y : Val} {σ : Heap} {e' : Expr} {σ' : Heap} {efs : List Expr}
    (h : prim_step (.sndE (.val (.pair x y))) σ e' σ' efs) :
    e' = .val y ∧ σ' = σ ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  have ha := head_toVal_none hHead
  obtain ⟨hKnil, haeq⟩ := ctx_nil_of_snd ha hK.symm
  subst hKnil
  subst haeq
  simp only [fill] at hK'
  cases hHead with
  | snd => exact ⟨hK', rfl, rfl⟩

/-! ## Generic lifting -/

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-- **Generic step lifting.** Proving the `wp` step body (re-establish the state
interpretation and the continuation `wp` after any primitive step) suffices to
verify a non-value expression. The per-operation rules below are corollaries. -/
theorem wp_lift_step (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ : Val → IProp GF)
    (hnv : toVal e = none) :
    (∀ σ, stateInterp γ σ -∗ |==>
      (∀ e' σ' efs, ⌜prim_step e σ e' σ' efs⌝ -∗ ▷ |==> (stateInterp γ σ' ∗ wp (F := F) γ e' Φ)))
    ⊢ wp (F := F) γ e Φ := by
  iintro H
  iapply wp_unfold
  simp only [wpF, hnv]
  iexact H

/-- **Pure-step rule.** If every step of `e` is deterministic, heap-preserving,
and fork-free (going to `etgt`), then `▷ wp etgt Φ ⊢ wp e Φ`. The determinism
hypothesis is discharged per-operation by a `prim_step_*_inv` lemma. -/
theorem wp_pure_det (γ : GName) [HasHeap γ GF F] (e etgt : Expr) (Φ : Val → IProp GF)
    (hnv : toVal e = none)
    (hdet : ∀ σ e' σ' efs, prim_step e σ e' σ' efs → e' = etgt ∧ σ' = σ ∧ efs = []) :
    ▷ wp (F := F) γ etgt Φ ⊢ wp (F := F) γ e Φ := by
  iintro H
  iapply wp_unfold
  simp only [wpF, hnv]
  iintro %σ Hsi
  iintro !>
  iintro %e' %σ' %efs %Hstep
  obtain ⟨he, hσ, hefs⟩ := hdet σ e' σ' efs Hstep
  subst he; subst hσ; subst hefs
  iintro !>
  iintro !>
  isplitl [Hsi]
  · iexact Hsi
  · iexact H

/-- **`if true` rule.** -/
theorem wp_if_true (γ : GName) [HasHeap γ GF F] (e1 e2 : Expr) (Φ : Val → IProp GF) :
    ▷ wp (F := F) γ e1 Φ ⊢ wp (F := F) γ (.ite (.val (.bool true)) e1 e2) Φ := by
  apply wp_pure_det (hnv := rfl)
  intro σ e' σ' efs h
  exact prim_step_ite_true_inv h

/-- **Pair rule.** Building a pair of two values. -/
theorem wp_pair (γ : GName) [HasHeap γ GF F] (x y : Val) (Φ : Val → IProp GF) :
    ▷ wp (F := F) γ (.val (.pair x y)) Φ ⊢ wp (F := F) γ (.pairE (.val x) (.val y)) Φ := by
  apply wp_pure_det (hnv := rfl)
  intro σ e' σ' efs h
  exact prim_step_pair_inv h

/-- **First-projection rule.** `fst (x, y)` steps to `x`. -/
theorem wp_fst (γ : GName) [HasHeap γ GF F] (x y : Val) (Φ : Val → IProp GF) :
    ▷ wp (F := F) γ (.val x) Φ ⊢ wp (F := F) γ (.fstE (.val (.pair x y))) Φ := by
  apply wp_pure_det (hnv := rfl)
  intro σ e' σ' efs h
  exact prim_step_fst_inv h

/-- **Second-projection rule.** `snd (x, y)` steps to `y`. -/
theorem wp_snd (γ : GName) [HasHeap γ GF F] (x y : Val) (Φ : Val → IProp GF) :
    ▷ wp (F := F) γ (.val y) Φ ⊢ wp (F := F) γ (.sndE (.val (.pair x y))) Φ := by
  apply wp_pure_det (hnv := rfl)
  intro σ e' σ' efs h
  exact prim_step_snd_inv h

/-- **β rule.** Applying a closure substitutes and steps to the body. -/
theorem wp_beta (γ : GName) [HasHeap γ GF F] (f x : String) (body : Expr) (w : Val)
    (Φ : Val → IProp GF) :
    ▷ wp (F := F) γ (substE x w (substE f (.clos f x body) body)) Φ ⊢
      wp (F := F) γ (.app (.val (.clos f x body)) (.val w)) Φ := by
  apply wp_pure_det (hnv := rfl)
  intro σ e' σ' efs h
  exact prim_step_beta_inv h

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
  simp only [Std.PartialMap.get?, toAgreeHeap] at Hl
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
  iapply wp_unfold
  simp only [wpF, toVal]
  iintro %σ Hsi
  iintro !>
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
  iapply wp_unfold
  simp only [wpF, toVal]
  iintro %σ Hsi
  iintro !>
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

/-- **Fetch-and-add rule.** Owning `l ↦ int m`, `FAA(l, n)` atomically writes
`int (m + n)` and returns the old `int m` — an arithmetic read-modify-write. Like
`wp_store` (frame-preserving ghost update) but it also reads (heap agreement pins
the old value) and returns it. -/
theorem wp_faa (γ : GName) [HasHeap γ GF F] (l : Nat) (m n : Int)
    (Φ : Val → IProp GF) :
    (l ↦[γ] (.int m)) ∗ ((l ↦[γ] (.int (m + n))) -∗ |==> Φ (.int m)) ⊢
      wp (F := F) γ (.faa (.val (.loc l)) (.val (.int n))) Φ := by
  iintro ⟨Hpt, HΦ⟩
  iapply wp_unfold
  simp only [wpF, toVal]
  iintro %σ Hsi
  iintro !>
  ihave %Hag := stateInterp_pointsTo_agree (γ := γ) σ l (.int m) $$ [Hsi, Hpt]
  · isplitl [Hsi] <;> iassumption
  iintro %e' %σ' %efs %Hstep
  obtain ⟨m', hσl, he', hσ', hefs⟩ := prim_step_faa_inv Hstep
  have hmm : m = m' := by
    have h2 := Option.some.inj (Hag.symm.trans hσl)
    injection h2
  subst hmm
  subst he'; subst hσ'; subst hefs
  have hval : ✓ (toAgree (⟨.int (m + n)⟩ : LeibnizO Val)) :=
    CMRA.valid_op_left (toAgree_op_valid_iff_eq.mpr rfl)
  have Hrepl := update_replace (F := F) (H := (Nat → Option ·)) (k := l)
    (m1 := toAgreeHeap σ) (v1 := toAgree (⟨.int m⟩ : LeibnizO Val))
    (v2 := toAgree (⟨.int (m + n)⟩ : LeibnizO Val)) hval
  rw [insert_toAgreeHeap] at Hrepl
  have Hcomb_lem :
      (stateInterp (F := F) γ σ ∗ (l ↦[γ] (.int m)))
      ⊢ iOwn (GF := GF) (F := FHeap (F := F)) γ
          (Auth (own one) (toAgreeHeap σ)
            • Frag l (own one) (toAgree (⟨.int m⟩ : LeibnizO Val))) :=
    iOwn_op.mpr
  have Hupd_lem :
      (iOwn (GF := GF) (F := FHeap (F := F)) γ
        (Auth (own one) (toAgreeHeap σ)
          • Frag l (own one) (toAgree (⟨.int m⟩ : LeibnizO Val))))
      ⊢ |==> iOwn (GF := GF) (F := FHeap (F := F)) γ
        (Auth (own one) (toAgreeHeap (σ.set l (.int (m + n))))
          • Frag l (own one) (toAgree (⟨.int (m + n)⟩ : LeibnizO Val))) :=
    iOwn_update Hrepl
  have Hsplit_lem :
      (iOwn (GF := GF) (F := FHeap (F := F)) γ
        (Auth (own one) (toAgreeHeap (σ.set l (.int (m + n))))
          • Frag l (own one) (toAgree (⟨.int (m + n)⟩ : LeibnizO Val))))
      ⊢ (stateInterp (F := F) γ (σ.set l (.int (m + n))) ∗ (l ↦[γ] (.int (m + n)))) :=
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

/-- **CAS failure rule.** If `l` holds `v_cur ≠ v1`, the compare-and-swap fails:
the heap is unchanged and `false` is returned (load-style, no ghost update). -/
theorem wp_cas_fail (γ : GName) [HasHeap γ GF F] (l : Nat) (v_cur v1 v2 : Val)
    (Φ : Val → IProp GF) (hne : v_cur ≠ v1) :
    (l ↦[γ] v_cur) ∗ ((l ↦[γ] v_cur) -∗ |==> Φ (.bool false)) ⊢
      wp (F := F) γ (.cas (.val (.loc l)) (.val v1) (.val v2)) Φ := by
  iintro ⟨Hpt, HΦ⟩
  iapply wp_unfold
  simp only [wpF, toVal]
  iintro %σ Hsi
  iintro !>
  ihave %Hag := stateInterp_pointsTo_agree (γ := γ) σ l v_cur $$ [Hsi, Hpt]
  · isplitl [Hsi] <;> iassumption
  iintro %e' %σ' %efs %Hstep
  obtain ⟨v0, hσl, hcase⟩ := prim_step_cas_inv Hstep
  have hv0 : v0 = v_cur := by rw [hσl] at Hag; exact Option.some.inj Hag
  rcases hcase with ⟨he, _, _, _⟩ | ⟨_, he', hσ', hefs⟩
  · subst hv0; exact absurd he hne
  · subst he'; subst hσ'; subst hefs
    iintro !>
    iintro !>
    isplitl [Hsi]
    · iexact Hsi
    · iapply wp_value
      iapply HΦ
      iexact Hpt

/-- **CAS success rule.** If `l` holds the expected `v1`, the compare-and-swap
succeeds: writes `v2`, returns `true` (agreement rules out the failure branch;
store-style ghost update). -/
theorem wp_cas_suc (γ : GName) [HasHeap γ GF F] (l : Nat) (v1 v2 : Val)
    (Φ : Val → IProp GF) :
    (l ↦[γ] v1) ∗ ((l ↦[γ] v2) -∗ |==> Φ (.bool true)) ⊢
      wp (F := F) γ (.cas (.val (.loc l)) (.val v1) (.val v2)) Φ := by
  iintro ⟨Hpt, HΦ⟩
  iapply wp_unfold
  simp only [wpF, toVal]
  iintro %σ Hsi
  iintro !>
  ihave %Hag := stateInterp_pointsTo_agree (γ := γ) σ l v1 $$ [Hsi, Hpt]
  · isplitl [Hsi] <;> iassumption
  iintro %e' %σ' %efs %Hstep
  obtain ⟨v0, hσl, hcase⟩ := prim_step_cas_inv Hstep
  have hv0 : v0 = v1 := by rw [hσl] at Hag; exact Option.some.inj Hag
  rcases hcase with ⟨_, he', hσ', hefs⟩ | ⟨hne, _, _, _⟩
  · subst he'; subst hσ'; subst hefs
    have hval : ✓ (toAgree (⟨v2⟩ : LeibnizO Val)) :=
      CMRA.valid_op_left (toAgree_op_valid_iff_eq.mpr rfl)
    have Hrepl := update_replace (F := F) (H := (Nat → Option ·)) (k := l)
      (m1 := toAgreeHeap σ) (v1 := toAgree (⟨v1⟩ : LeibnizO Val))
      (v2 := toAgree (⟨v2⟩ : LeibnizO Val)) hval
    rw [insert_toAgreeHeap] at Hrepl
    have Hcomb_lem :
        (stateInterp (F := F) γ σ ∗ (l ↦[γ] v1))
        ⊢ iOwn (GF := GF) (F := FHeap (F := F)) γ
            (Auth (own one) (toAgreeHeap σ)
              • Frag l (own one) (toAgree (⟨v1⟩ : LeibnizO Val))) :=
      iOwn_op.mpr
    have Hupd_lem :
        (iOwn (GF := GF) (F := FHeap (F := F)) γ
          (Auth (own one) (toAgreeHeap σ)
            • Frag l (own one) (toAgree (⟨v1⟩ : LeibnizO Val))))
        ⊢ |==> iOwn (GF := GF) (F := FHeap (F := F)) γ
          (Auth (own one) (toAgreeHeap (σ.set l v2))
            • Frag l (own one) (toAgree (⟨v2⟩ : LeibnizO Val))) :=
      iOwn_update Hrepl
    have Hsplit_lem :
        (iOwn (GF := GF) (F := FHeap (F := F)) γ
          (Auth (own one) (toAgreeHeap (σ.set l v2))
            • Frag l (own one) (toAgree (⟨v2⟩ : LeibnizO Val))))
        ⊢ (stateInterp (F := F) γ (σ.set l v2) ∗ (l ↦[γ] v2)) :=
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
  · exact absurd hv0 hne

/-- **Alloc rule.** Allocation returns a fresh location holding `v`; the
continuation receives the new points-to for whichever fresh `l` was chosen
(extends the authoritative heap via `update_one_alloc`). -/
theorem wp_alloc (γ : GName) [HasHeap γ GF F] (v : Val) (Φ : Val → IProp GF) :
    (∀ l, (l ↦[γ] v) -∗ |==> Φ (.loc l)) ⊢ wp (F := F) γ (.alloc (.val v)) Φ := by
  iintro Hcont
  iapply wp_unfold
  simp only [wpF, toVal]
  iintro %σ Hsi
  iintro !>
  iintro %e' %σ' %efs %Hstep
  obtain ⟨l, hfresh, he', hσ', hefs⟩ := prim_step_alloc_inv Hstep
  subst he'
  subst hσ'
  subst hefs
  have hval : ✓ (toAgree (⟨v⟩ : LeibnizO Val)) :=
    CMRA.valid_op_left (toAgree_op_valid_iff_eq.mpr rfl)
  have Halloc := update_one_alloc (F := F) (H := (Nat → Option ·)) (k := l)
    (m1 := toAgreeHeap σ) (dq := own one) (v1 := toAgree (⟨v⟩ : LeibnizO Val))
    (by simp [Std.PartialMap.get?, Std.instPartialMapFun, toAgreeHeap, hfresh])
    valid_own_one hval
  rw [insert_toAgreeHeap] at Halloc
  have Hupd_lem :
      (stateInterp (F := F) γ σ)
      ⊢ |==> iOwn (GF := GF) (F := FHeap (F := F)) γ
          (Auth (own one) (toAgreeHeap (σ.set l v))
            • Frag l (own one) (toAgree (⟨v⟩ : LeibnizO Val))) :=
    iOwn_update Halloc
  have Hsplit_lem :
      (iOwn (GF := GF) (F := FHeap (F := F)) γ
        (Auth (own one) (toAgreeHeap (σ.set l v))
          • Frag l (own one) (toAgree (⟨v⟩ : LeibnizO Val))))
      ⊢ (stateInterp (F := F) γ (σ.set l v) ∗ (l ↦[γ] v)) :=
    iOwn_op.mp
  iintro !>
  ihave Hupd := Hupd_lem $$ [Hsi]
  · iexact Hsi
  imod Hupd with Hnew
  ihave ⟨HA, HF⟩ := Hsplit_lem $$ [Hnew]
  · iexact Hnew
  iintro !>
  isplitl [HA]
  · iexact HA
  · iapply wp_value
    iapply Hcont
    iexact HF

/-- A `some` from `toVal` pins the expression to that value. -/
theorem toVal_some_eq {e : Expr} {v : Val} (h : toVal e = some v) : e = .val v := by
  cases e <;> simp_all [toVal]

/-- **Bind rule.** Verify the focused expression `e` first; its postcondition
continues with the refilled evaluation context. The structural rule for
sequencing (e.g. `let x = !s in …`). Proved by Löb induction. -/
theorem wp_bind (γ : GName) [HasHeap γ GF F] (K : List Frame) (e : Expr)
    (Φ : Val → IProp GF) :
    wp (F := F) γ e (fun v => wp (F := F) γ (fill K (.val v)) Φ) ⊢
      wp (F := F) γ (fill K e) Φ := by
  have hcl : ⊢ ∀ ee, wp (F := F) γ ee (fun v => wp (F := F) γ (fill K (.val v)) Φ)
                       -∗ wp (F := F) γ (fill K ee) Φ := by
    iapply BILoeb.loeb_weak
    iintro IH
    iintro %ee Hwp
    cases hv : toVal ee with
    | some v =>
      have hee : ee = .val v := toVal_some_eq hv
      subst hee
      iapply bupd_wp
      iapply (wp_value_inv γ v (fun v => wp (F := F) γ (fill K (.val v)) Φ))
      iexact Hwp
    | none =>
      iapply wp_unfold
      simp only [wpF, fill_toVal_none hv K]
      iintro %σ Hσ
      ihave HwpStep := (wp_step γ ee (fun v => wp (F := F) γ (fill K (.val v)) Φ) hv) $$ [Hwp]
      · iexact Hwp
      ihave HwpBody := HwpStep $$ [Hσ]
      · iexact Hσ
      imod HwpBody with HwpInner
      iintro !>
      iintro %ee2 %σ2 %efs2 %Hstep
      obtain ⟨e', he'', hstep'⟩ := fill_step_inv Hstep hv
      subst he''
      ispecialize HwpInner $$ %e'
      ispecialize HwpInner $$ %σ2
      ispecialize HwpInner $$ %efs2
      ispecialize HwpInner $$ []
      · ipure_intro; exact hstep'
      iintro !>
      imod HwpInner with ⟨Hsi', Hwe⟩
      iintro !>
      isplitl [Hsi']
      · iexact Hsi'
      · iapply IH
        iexact Hwe
    exact true_intro
  iintro Hwp
  iapply hcl
  all_goals first | iexact Hwp | exact true_intro

/-- **Monotonicity.** A pointwise-weaker postcondition gives a weaker `wp`.
Proved by Löb induction (same shape as `wp_bind`). -/
theorem wp_mono (γ : GName) [HasHeap γ GF F] (e : Expr) (Φ Ψ : Val → IProp GF)
    (h : ∀ v, Φ v ⊢ Ψ v) : wp (F := F) γ e Φ ⊢ wp (F := F) γ e Ψ := by
  have hcl : ⊢ ∀ ee, wp (F := F) γ ee Φ -∗ wp (F := F) γ ee Ψ := by
    iapply BILoeb.loeb_weak
    iintro IH
    iintro %ee Hwp
    cases hv : toVal ee with
    | some v =>
      have hee : ee = .val v := toVal_some_eq hv
      subst hee
      iapply wp_value
      ihave HΦ := (wp_value_inv γ v Φ) $$ [Hwp]
      · iexact Hwp
      imod HΦ with HΦ2
      iintro !>
      iapply (h v)
      iexact HΦ2
    | none =>
      iapply wp_unfold
      simp only [wpF, hv]
      iintro %σ Hσ
      ihave HwpS := (wp_step γ ee Φ hv) $$ [Hwp]
      · iexact Hwp
      ihave HwpB := HwpS $$ [Hσ]
      · iexact Hσ
      imod HwpB with HwpI
      iintro !>
      iintro %ee2 %σ2 %efs2 %Hstep
      ispecialize HwpI $$ %ee2
      ispecialize HwpI $$ %σ2
      ispecialize HwpI $$ %efs2
      ispecialize HwpI $$ []
      · ipure_intro; exact Hstep
      iintro !>
      imod HwpI with ⟨Hsi, Hwe⟩
      iintro !>
      isplitl [Hsi]
      · iexact Hsi
      · iapply IH
        iexact Hwe
    exact true_intro
  iintro Hwp
  iapply hcl
  all_goals first | iexact Hwp | exact true_intro

/-- **Let rule.** `let x := e in body` (encoded `(λ_ x. body) e`): verify `e`,
then continue with `body[x := result]`. Combines `wp_bind` + `wp_beta` +
`wp_mono`. -/
theorem wp_let (γ : GName) [HasHeap γ GF F] (x : String) (body e : Expr)
    (Φ : Val → IProp GF) :
    wp (F := F) γ e (fun w => iprop(▷ wp (F := F) γ (substE x w (substE "_" (.clos "_" x body) body)) Φ)) ⊢
      wp (F := F) γ (.app (.val (.clos "_" x body)) e) Φ := by
  refine (wp_mono γ e _
    (fun w => wp (F := F) γ (.app (.val (.clos "_" x body)) (.val w)) Φ) ?_).trans
    (wp_bind γ [Frame.appR (.clos "_" x body)] e Φ)
  intro w
  exact wp_beta γ "_" x body w Φ

/-- **Sequencing rule.** `let _ = e1 in e2` (the result of `e1` discarded): verify
`e1`, then `e2`. A specialization of `wp_let` for a closed continuation `e2` (no
free `_`), packaging the substitution bookkeeping so client proofs compose verified
statements directly. -/
theorem wp_seq (γ : GName) [HasHeap γ GF F] (e1 e2 : Expr) (Φ : Val → IProp GF)
    (hcl : ∀ w : Val, substE "_" w e2 = e2) :
    wp (F := F) γ e1 (fun _ => iprop(▷ wp (F := F) γ e2 Φ)) ⊢
      wp (F := F) γ (.app (.val (.clos "_" "_" e2)) e1) Φ := by
  refine (wp_mono γ e1 _ _ ?_).trans (wp_let γ "_" e2 e1 Φ)
  intro w
  simp only [hcl]
  iintro H; iexact H
