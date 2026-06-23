/-
Phase A2 (fancy-update, piece 5 support) — fresh-name allocation for GenMap.

`inv_alloc` must mint a fresh disabled token `ownD {i}` for an `i` that avoids both the
ambient `γD` frame and the already-allocated invariant names. iris-lean's `GenMap`
exposes that a valid map has *infinitely many* free keys (`Infinite (IsFree car)`, an
injective `Enum`), but there is no lemma "a free key avoiding a finite set exists". We
build it here — which needs a list pigeonhole that, with no Mathlib dependency, must be
proven from Lean-core `List` primitives. Sorry-free.
-/
import Iris.Algebra
import LeanliftIris.PhaseA.Fupd.Masks

namespace LeanliftIris.PhaseA.Fupd
open Iris COFE CMRA OFE

/-! ## List pigeonhole (from Lean core) -/

/-- An injective function maps a `Nodup` list to a `Nodup` list. -/
theorem map_nodup_of_inj {f : Nat → Nat} (hinj : ∀ a b, f a = f b → a = b) :
    ∀ {l : List Nat}, l.Nodup → (l.map f).Nodup
  | [], _ => by simp
  | a :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, map_nodup_of_inj hinj h.2⟩
      rcases List.mem_map.mp hmem with ⟨b, hb, hfb⟩
      have hba : b = a := hinj b a hfb
      subst hba
      exact h.1 hb

/-- A `Nodup` sublist is no longer than its superset. -/
theorem nodup_subset_length :
    ∀ {l X : List Nat}, l.Nodup → l ⊆ X → l.length ≤ X.length
  | [], _, _, _ => by simp
  | a :: l, X, hnd, hsub => by
      rw [List.nodup_cons] at hnd
      have ha : a ∈ X := hsub (List.mem_cons_self ..)
      have hsub' : l ⊆ X.erase a := by
        intro x hx
        have hxa : x ≠ a := by intro h; subst h; exact hnd.1 hx
        exact (List.mem_erase_of_ne hxa).mpr (hsub (List.mem_cons_of_mem _ hx))
      have hle := nodup_subset_length hnd.2 hsub'
      rw [List.length_erase_of_mem ha] at hle
      have := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

/-- **Pigeonhole.** An injective `Nat → Nat` overshoots any finite list. -/
theorem exists_not_mem_of_inj {f : Nat → Nat} (hinj : ∀ a b, f a = f b → a = b)
    (X : List Nat) : ∃ k, f k ∉ X := by
  apply Classical.byContradiction
  intro hc
  have hall : ∀ k, f k ∈ X := fun k =>
    Classical.byContradiction fun hk => hc ⟨k, hk⟩
  have hsub : (List.range (X.length + 1)).map f ⊆ X := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨k, _, rfl⟩
    exact hall k
  have hle := nodup_subset_length (map_nodup_of_inj hinj List.nodup_range) hsub
  rw [List.length_map, List.length_range] at hle
  omega

/-! ## A fresh key for a valid GenMap -/

/-- A valid `GenMap` over `Nat` has a free key avoiding any given finite set. -/
theorem genMap_exists_fresh {n} {mf : GenMap Nat (Excl Unit)}
    (Hv : ✓{n} mf) (X : List Nat) : ∃ i, mf.car i = none ∧ i ∉ X := by
  rcases Hv.2 with ⟨enum, henum⟩
  obtain ⟨k, hk⟩ := exists_not_mem_of_inj (fun _ _ h => henum.inj h) X
  exact ⟨enum k, henum.inc, hk⟩

/-- A singleton exclusive token is a valid `GenMap`. -/
theorem singleton_excl_validN {n} (i : Nat) :
    ✓{n} (GenMap.singleton i (Excl.excl ()) : GenMap Nat (Excl Unit)) := by
  show ✓{n} ((GenMap.empty : GenMap Nat (Excl Unit)).alter i (some (Excl.excl ())))
  exact GenMap.alter_valid Nat (Excl Unit) (by trivial) (UCMRA.unit_valid).validN

/-- **Fresh disabled-token allocation, at the RA level.** From the empty map one can
update to a singleton at a name avoiding any finite set. -/
theorem genMap_alloc_updateP (X : List Nat) :
    (GenMap.empty : GenMap Nat (Excl Unit)) ~~>:
      (fun g => ∃ i, i ∉ X ∧ g = GenMap.singleton i (Excl.excl ())) := by
  intro n mz Hv
  cases mz with
  | none =>
      simp only [op?] at Hv ⊢
      obtain ⟨i, _, hiX⟩ := genMap_exists_fresh (mf := GenMap.empty) Hv X
      exact ⟨GenMap.singleton i (.excl ()), ⟨i, hiX, rfl⟩, singleton_excl_validN i⟩
  | some mf =>
      simp only [op?] at Hv ⊢
      have Hmf : ✓{n} mf := (Dist.validN (UCMRA.unit_left_id (x := mf)).dist).mp Hv
      obtain ⟨i, hi_free, hiX⟩ := genMap_exists_fresh Hmf X
      refine ⟨GenMap.singleton i (.excl ()), ⟨i, hiX, rfl⟩, ?_⟩
      have hcomm := GenMap.op_singleton_comm Nat (Excl Unit) (Excl.excl ()) hi_free
      exact (Dist.validN hcomm.dist).mpr (GenMap.alter_valid Nat (Excl Unit) (by trivial) Hmf)

end LeanliftIris.PhaseA.Fupd
