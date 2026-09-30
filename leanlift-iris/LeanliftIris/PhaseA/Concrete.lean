/-
Phase A — a **concrete instantiation** of the ambient setup, so the closed facts are
unconditional.

Every theorem in the lane is stated under `variable {F} [UFraction F] {GF} [ElemG GF
(FHeap (F := F))]`, and until now nothing in iris-lean or this repository exhibited a
concrete `UFraction` type (iris-lean has only the generic `[NumericFraction α]`
instance and no `NumericFraction` instance). So the "closed" operational facts
(`ex_alloc_load_adequate`, `forkThenFst_result`, `forkThenFst_safe`) were conditional
on a typeclass nothing was known to satisfy — the same shape as an unsatisfiable
premise, one level up (a vacuous theorem type-checks, is sorry-free, prints a clean
axiom set, and proves nothing). This file closes that gap.

`PosNat` (positive naturals, `Proper x := x ≤ 1`) is the *trivial* fraction type: the
whole `1` cannot be split, so fractional ownership is impossible. That is exactly enough
here — the heap camera only ever uses full ownership (`own one`) — and it is genuinely
a `UFraction`. `GF₀` is the functor list holding the heap functor at slot 0, and the
`ElemG` instance is definitional. The three `*_unconditional` theorems below are pure
operational facts about `λ-conc` programs with **no** remaining typeclass or iProp
hypothesis; they are the consumers that keep this instance from drifting into an
unused declaration. Sorry-free.
-/
import LeanliftIris.PhaseA.PoolAdequacy
import LeanliftIris.PhaseA.Examples

namespace LeanliftIris.PhaseA
open Iris

/-! ## The trivial fraction type -/

/-- Positive naturals. -/
def PosNat := { n : Nat // 0 < n }

instance : Add PosNat := ⟨fun a b => ⟨a.1 + b.1, Nat.add_pos_left a.2 _⟩⟩
instance : One PosNat := ⟨⟨1, Nat.one_pos⟩⟩

@[simp] theorem PosNat.add_val (a b : PosNat) : (a + b).1 = a.1 + b.1 := rfl
@[simp] theorem PosNat.one_val : (1 : PosNat).1 = 1 := rfl

theorem PosNat.ext {a b : PosNat} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- `PosNat` with `Proper x := x ≤ 1` is a fraction type with a unique whole element.
Nothing below `1` exists, so no fraction is splittable — the degenerate but honest
instance the full-ownership heap camera needs. -/
instance : UFraction PosNat where
  Proper x := x.1 ≤ 1
  add_comm a b := PosNat.ext (Nat.add_comm _ _)
  add_assoc a b c := PosNat.ext (Nat.add_assoc _ _ _).symm
  add_left_cancel h := PosNat.ext (Nat.add_left_cancel (congrArg Subtype.val h))
  add_ne {a b} h := by
    have h' : a.1 = b.1 + a.1 := congrArg Subtype.val h
    have := b.2
    omega
  proper_add_mono_left {a b} h := Nat.le_trans (Nat.le_add_right _ _) h
  one_whole := by
    refine ⟨Nat.le_refl 1, ?_⟩
    rintro ⟨b, hb⟩
    have := b.2
    simp only [PosNat.add_val, PosNat.one_val] at hb
    omega

/-! ## A concrete functor list holding the heap -/

/-- The functor list: the heap functor over `PosNat` at slot `0`, `Unit` elsewhere. -/
def GF₀ : BundledGFunctors :=
  BundledGFunctors.default.set 0 ⟨FHeap (F := PosNat), inferInstance⟩

instance : ElemG GF₀ (FHeap (F := PosNat)) := ⟨0, rfl⟩

/-! ## Unconditional operational facts -/

/-- **Unconditional.** Any fork-free run of `load (alloc v)` from the empty heap that
reaches a value `r` has `r = v`. No typeclass or iProp hypothesis remains. -/
theorem ex_alloc_load_unconditional (v r : Val) (σ' : Heap)
    (hrun : primSteps (.load (.alloc (.val v))) emptyHeap (.val r) σ') : r = v :=
  ex_alloc_load_adequate (F := PosNat) (GF := GF₀) 0 v r σ' hrun
    (ex_alloc_load_closed_input (F := PosNat) (GF := GF₀) 0 v)

/-- **Unconditional.** Every thread-pool run of `let _ = fork unit in fst (3, 4)` from a
heap with unbounded free space whose primary thread terminates returns `3`. -/
theorem forkThenFst_result_unconditional (σ : Heap) (hinf : Heap.infFree σ) (v : Val)
    (σ' : Heap) (tp' : List Expr) (hrun : steps ⟨[forkThenFst], σ⟩ ⟨.val v :: tp', σ'⟩) :
    v = .int 3 :=
  forkThenFst_result (F := PosNat) (GF₀ := GF₀) σ hinf v σ' tp' hrun

/-- **Unconditional.** No thread of any run of `forkThenFst` from the empty heap is
ever stuck. -/
theorem forkThenFst_safe_unconditional {c : Cfg} (hrun : steps ⟨[forkThenFst], emptyHeap⟩ c) :
    ∀ t ∈ c.tp, toVal t ≠ none ∨ reducible t c.heap :=
  forkThenFst_safe (F := PosNat) (GF₀ := GF₀) hrun

end LeanliftIris.PhaseA
