/-
Phase A2 (step 1) — the heap resource and the points-to connective for `λ-conc`.

This is the first Iris-dependent Phase-A file. iris-lean ships the resource
*algebra* `HeapView` (authoritative heap with `DFrac` fractions + singleton
fragments) but no program logic; here we instantiate it for our value type `Val`
to obtain a separation-logic points-to `l ↦[γ] v`, embedded into `iProp` via the
ghost-state primitive `iOwn`. This is the heap-ownership foundation the `wp`
(A2 step 2) and the Treiber proof (A4) are built on.

Structure follows the upstream worked example `Iris/Examples/IProp.lean`
(Example 2), specialised from `String` to `λ-conc`'s `Val`. Sorry-free.
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra
import Iris.Std.HeapInstances
import LeanliftIris.PhaseA.Lang

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE HeapView One DFrac Agree LeibnizO

-- Fraction type parameter (kept abstract, as upstream does).
variable {F} [UFraction F]

/-- The heap functor: locations (`Nat`) to agreed-upon `λ-conc` values, with
`DFrac` fractional ownership. The map type is the **plain-function** partial map
`Nat → Option ·` (iris-lean's `instPartialMapFun`), which is exactly `Lang.Heap`
— so the authoritative `state_interp` and the `pointsTo` fragments live in the
same camera, with no finiteness bookkeeping. -/
abbrev FHeap : OFunctorPre :=
  constOF <| HeapView F Nat (Agree (LeibnizO Val)) (Nat → Option ·)

-- The heap functor is present in the global functor list.
variable {GF} [ElemG GF (FHeap (F := F))]

set_option synthInstance.checkSynthOrder false in
/-- A `γ` naming a heap ghost cell, so the points-to notation needs no explicit
type arguments (upstream trick). -/
class abbrev HasHeap (γ : GName) (GF : outParam _) (F : outParam (Type _))
    [UFraction F] := ElemG GF (FHeap (F := F))

/-- The points-to connective: full (`own one`) ownership of location `l` holding
value `v` under heap ghost name `γ`. -/
def pointsTo (γ : GName) [HasHeap γ GF F] (l : Nat) (v : Val) : IProp GF :=
  iOwn (GF := GF) (F := FHeap (F := F)) γ (Frag l (own one) (toAgree ⟨v⟩))

@[inherit_doc] notation l:50 " ↦[" γ:50 "] " v:50 => pointsTo γ l v

/-- **Agreement of points-to.** Two points-to for the same location must hold the
same value — the canonical `gen_heap` agreement lemma. This is what lets a reader
that owns `l ↦ v` conclude a concurrently-held view agrees. -/
theorem pointsTo_agree {γ : GName} [HasHeap γ GF F] (l : Nat) (v w : Val) :
    (l ↦[γ] v) ∗ (l ↦[γ] w) ⊢ (⌜v = w⌝ : IProp GF) := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact LeibnizO.dist_inj <| toAgree_op_validN_iff_dist.mp <|
    (frag_op_validN_iff.mp H).2

end LeanliftIris.PhaseA
