/-
Phase A2 (fancy-update, piece 1) — mask tokens.

The enabled/disabled invariant-mask tokens that the fancy-update modality
(`Fupd.Fupd`) and `wsat` (`Fupd.Wsat`) consume. We model a mask `E : Iris.Set Nat`
(a predicate on invariant names) by the resource `tok E : GenMap Nat (Excl Unit)` —
the finite-map RA holding an *exclusive* unit token at exactly the names in `E`.
Two ghost names use this one functor: `γE` (enabled) and `γD` (disabled).

The two facts that make this a mask algebra both come for free from `Excl`:
* **splitting** — disjoint masks compose (`ownE_op`), because `tok` is a pointwise
  partial map and disjoint supports `optionOp` to a union; and
* **exclusivity** — overlapping masks are contradictory (`ownE_disjoint`), because
  `excl () • excl () = invalid`.

DESIGN NOTE (the `⊤` limitation). `GenMap Nat _` validity requires *infinitely many*
free keys (`Infinite (IsFree car)`), so `tok ⊤` is invalid and `ownE ⊤ ⊢ False`. The
token algebra therefore models **finite / co-infinite** masks only; this is sound for
the relative `BIFUpdate` laws and for finite-mask invariant access, but is why `fupd`
is not wired into `wp`/adequacy (which would force `ownE ⊤`). See `docs/PLAN-fupd.md`.
Sorry-free.
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra

namespace LeanliftIris.PhaseA.Fupd
open Iris Iris.BI COFE Excl

open scoped Classical

/-- The mask-token functor: a finite map from invariant names to exclusive unit
tokens. Constant in the recursion variable (no stored propositions), so `constOF`. -/
abbrev FTok : OFunctorPre := constOF (GenMap Nat (Excl Unit))

variable {GF} [ElemG GF FTok]

/-- The token resource for a mask `E`: an exclusive unit at every name in `E`. -/
noncomputable def tok (E : Iris.Set Nat) : GenMap Nat (Excl Unit) :=
  ⟨fun i => if E i then some (.excl ()) else none⟩

/-- Ownership of the tokens of mask `E` under ghost name `γ`. `ownE γE` is the
*enabled* tokens; `ownD γD` the *disabled* ones. -/
noncomputable def ownE (γ : GName) (E : Iris.Set Nat) : IProp GF :=
  iOwn (GF := GF) (F := FTok) γ (tok E)

/-- The empty mask carries no tokens — it is the unit of the token RA. -/
theorem tok_empty : tok (fun _ => False) = (GenMap.empty : GenMap Nat (Excl Unit)) := by
  apply congrArg GenMap.mk
  funext i
  simp

/-- Disjoint masks split: their tokens are the `optionOp` union. -/
theorem tok_op {E1 E2 : Iris.Set Nat} (h : Iris.Disjoint E1 E2) :
    tok (Iris.union E1 E2) = tok E1 • tok E2 := by
  apply congrArg GenMap.mk
  funext i
  simp only [CMRA.op, optionOp, tok, Iris.union]
  by_cases h1 : E1 i <;> by_cases h2 : E2 i <;> simp_all
  exact (h i ⟨h1, h2⟩).elim

/-- Overlapping masks are token-invalid: `excl () • excl () = invalid`. -/
theorem tok_validN_disjoint {n} {E1 E2 : Iris.Set Nat}
    (Hv : ✓{n} (tok E1 • tok E2)) : Iris.Disjoint E1 E2 := by
  intro i ⟨h1, h2⟩
  have Hpt := Hv.1 i
  simp only [CMRA.op, optionOp, tok, h1, h2, if_true] at Hpt
  exact Hpt

/-- **Splitting.** Disjoint masks compose to their union under separating
conjunction. -/
theorem ownE_op {γ : GName} {E1 E2 : Iris.Set Nat} (h : Iris.Disjoint E1 E2) :
    ownE (GF := GF) γ (Iris.union E1 E2) ⊣⊢ ownE γ E1 ∗ ownE γ E2 := by
  unfold ownE
  rw [tok_op h]
  exact iOwn_op

/-- **Exclusivity.** Owning the tokens of two masks forces them disjoint. -/
theorem ownE_disjoint {γ : GName} {E1 E2 : Iris.Set Nat} :
    ownE (GF := GF) γ E1 ∗ ownE γ E2 ⊢ (⌜Iris.Disjoint E1 E2⌝ : IProp GF) := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact tok_validN_disjoint H

/-- The empty mask is ownable for free (up to update): it is the token unit. -/
theorem ownE_empty_bupd {γ : GName} :
    ⊢ |==> ownE (GF := GF) γ (fun _ => False) := by
  unfold ownE
  rw [tok_empty]
  haveI : IsUnit (GenMap.empty : GenMap Nat (Excl Unit)) :=
    inferInstanceAs (IsUnit (UCMRA.unit : GenMap Nat (Excl Unit)))
  exact iOwn_unit

end LeanliftIris.PhaseA.Fupd
