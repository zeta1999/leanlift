/-
Phase A2 (fancy-update, piece 5) — invariants and logical atomicity.

* `inv i P` — the persistent invariant assertion (knowledge that name `i` guards `P`),
  built on `ownI` (`Fupd.InvRes`).
* `bigSep_map_extract` — the reusable world-satisfaction surgery lemma: pull the slot
  for one allocated name out of `wsat`'s iterated separating conjunction. This is the
  enabler for `inv_acc` (opening an invariant).
* `atomic_acc` — the heart of *logical atomicity*. Now that `IProp GF` carries a real
  `fupd` (`Fupd.Fupd`, the registered `BIFUpdate`), the logically-atomic accessor — and
  hence Iris-style logically-atomic triples `<<< α x >>> e @ E <<< β x >>>` — is
  **expressible**: open the public mask `Eo` down to `Ei`, expose the abstract state
  `α x`, and offer to either abort (restore `α x`, recover `Pa`) or commit (consume
  `β x`, deliver `Φ x`), each closing back up to `Eo`.

The remaining proven lemmas `inv_alloc` / `inv_acc` (world-satisfaction open/close) build
directly on `bigSep_map_extract`, the `Fupd.IEq` agreement (`▷ (P ≡ Q)`), and a fresh
disabled-token allocation; they are the last step. Sorry-free.
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra
import LeanliftIris.PhaseA.Fupd.Fupd
import LeanliftIris.PhaseA.Fupd.IEq

namespace LeanliftIris.PhaseA.Fupd
open Iris Iris.BI COFE OFE

variable {GF}

/-- **World-satisfaction surgery.** Pull the element at a known position out of an
iterated separating conjunction over a mapped list — `wsat` opens one invariant slot
with this. -/
theorem bigSep_map_extract {α : Type _} (f : α → IProp GF) (x : α) :
    ∀ pre post : List α,
      ([∗] ((pre ++ x :: post).map f) : IProp GF) ⊣⊢ f x ∗ [∗] ((pre ++ post).map f)
  | [], post => by
      rw [List.nil_append, List.nil_append, List.map_cons]
      exact bigOp_sep_cons
  | a :: pre, post => by
      have IH := bigSep_map_extract f x pre post
      calc ([∗] (((a :: pre) ++ x :: post).map f) : IProp GF)
          ⊣⊢ f a ∗ [∗] ((pre ++ x :: post).map f) := by
            rw [List.cons_append, List.map_cons]; exact bigOp_sep_cons
        _ ⊣⊢ f a ∗ (f x ∗ [∗] ((pre ++ post).map f)) := ⟨sep_mono_r IH.1, sep_mono_r IH.2⟩
        _ ⊣⊢ f x ∗ (f a ∗ [∗] ((pre ++ post).map f)) := sep_left_comm
        _ ⊣⊢ f x ∗ [∗] (((a :: pre) ++ post).map f) := by
            rw [List.cons_append, List.map_cons]
            exact ⟨sep_mono_r bigOp_sep_cons.2, sep_mono_r bigOp_sep_cons.1⟩

variable {F} [UFraction F] [W : WsatG GF F]

/-- The persistent invariant assertion: name `i` guards `P`. -/
noncomputable def inv (i : Nat) (P : IProp GF) : IProp GF := ownI (F := F) W.γI i P

instance instPersistent_inv {i} {P : IProp GF} : BI.Persistent (inv (W := W) i P) := by
  unfold inv
  infer_instance

/-- **Logically-atomic accessor.** Expressible now that `fupd` exists: shift the public
mask `Eo` to the private `Ei`, expose abstract state `α x`, and provide both an abort
(restore `α x`, regain `Pa`) and a commit (give up `β x`, obtain `Φ x`), each shifting
back to `Eo`. -/
noncomputable def atomic_acc (Eo Ei : Iris.Set Nat) {X : Type _}
    (α : X → IProp GF) (Pa : IProp GF) (β Φ : X → IProp GF) : IProp GF :=
  iprop( |={Eo, Ei}=> ∃ x, α x ∗
           ((α x ={Ei, Eo}=∗ Pa) ∧ (β x ={Ei, Eo}=∗ Φ x)) )

/-- Non-expansiveness of the accessor in its abort resource (a sanity check that the
`fupd`-built definition is well-formed). -/
theorem atomic_acc_ne {Eo Ei : Iris.Set Nat} {X : Type _}
    {α β Φ : X → IProp GF} :
    OFE.NonExpansive (atomic_acc (W := W) Eo Ei α · β Φ) := by
  constructor
  intro n Pa Pa' H
  simp only [atomic_acc]
  refine fupd_ne.ne ?_
  refine exists_ne (fun x => ?_)
  refine sep_ne.ne .rfl ?_
  refine and_ne.ne ?_ .rfl
  exact wand_ne.ne .rfl (fupd_ne.ne H)

end LeanliftIris.PhaseA.Fupd
