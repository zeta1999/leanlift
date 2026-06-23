/-
Phase A2 (fancy-update, infra) — internal equality for `IProp`.

iris-lean's BI has no internal-equality connective `≡`. The invariant layer needs it:
opening invariant `i` yields the *stored* body `▷ Q`, but the client holds `ownI i P`;
agreement on the stored `Agree (LaterS ·)` gives `▷ (P ≡ Q)`, which must be reflected
into the logic to transport `▷ Q` to `▷ P` (`Fupd.Inv`'s `inv_acc`).

We define `iEq a b` directly at the `UPred` model: it holds at step `n` iff `a` and `b`
are `n`-equivalent. From this we get the Leibniz elimination (`iEq_elim`), the
agreement bridge from `Agree` validity (`agree_iEq`), and the `LaterS`↔`▷` shift
(`iEq_laterS_fwd`) that turns agreement of stored later-props into `▷ (P ≡ Q)`.
Sorry-free.
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra
import LeanliftIris.PhaseA.Fupd.Functors

namespace LeanliftIris.PhaseA.Fupd
open Iris Iris.BI COFE OFE Agree

variable {GF}

/-- Internal equality: `iEq a b` holds at step `n` iff `a ≡{n}≡ b`. -/
def iEq {α : Type _} [OFE α] (a b : α) : IProp GF where
  holds n _ := a ≡{n}≡ b
  mono H _ Hn := H.le Hn

/-- Internal equality is reflexive. -/
theorem iEq_refl {α : Type _} [OFE α] (a : α) (P : IProp GF) : P ⊢ iEq a a :=
  fun _ _ _ _ => .rfl

/-- Internal equality is symmetric. -/
theorem iEq_sym {α : Type _} [OFE α] {a b : α} : iEq (GF := GF) a b ⊢ iEq b a :=
  fun _ _ _ H => H.symm

/-- **Leibniz elimination.** Equal propositions are interchangeable: from `iEq P Q`
and `P` conclude `Q`. -/
theorem iEq_elim {P Q : IProp GF} : BIBase.and (iEq (GF := GF) P Q) P ⊢ Q :=
  fun n x hv ⟨HE, HP⟩ => (HE n x (Nat.le_refl n) hv).mp HP

/-- **Agreement bridge.** Validity of an `Agree`-product is internal equality of its
arguments. -/
theorem agree_iEq {α : Type _} [OFE α] {a b : α} :
    (UPred.cmraValid (toAgree a • toAgree b) : IProp GF) ⊢ iEq a b :=
  fun _ _ _ H => toAgree_op_validN_iff_dist.mp H

/-- **`LaterS`↔`▷` shift.** Internal equality of `LaterS`-wrapped values is the later
of internal equality. This turns agreement of stored later-propositions into
`▷ (P ≡ Q)`. -/
theorem iEq_laterS_fwd {P Q : IProp GF} :
    iEq (GF := GF) (LaterS.next P) (LaterS.next Q) ⊢ (▷ iEq P Q : IProp GF) := by
  intro n x _ H
  cases n with
  | zero => exact trivial
  | succ n' => exact H n' (Nat.lt_succ_self n')

/-- Internal equality is persistent (its truth is independent of resources). -/
instance instPersistent_iEq {α : Type _} [OFE α] {a b : α} :
    BI.Persistent (iEq (GF := GF) a b) :=
  ⟨fun _ _ _ H => H⟩

/-- Leibniz elimination, other direction: from `iEq P Q` and `Q` conclude `P`. -/
theorem iEq_elim' {P Q : IProp GF} : BIBase.and (iEq (GF := GF) P Q) Q ⊢ P :=
  (and_mono_l iEq_sym).trans iEq_elim

/-- **Transport.** Equal propositions are interchangeable under separating
conjunction. -/
theorem iEq_transport {P Q : IProp GF} : iprop(iEq (GF := GF) P Q ∗ Q) ⊢ P :=
  sep_and.trans iEq_elim'

/-- **Transport under `▷`.** The form `inv_acc` uses to turn the stored body `▷ Q`
into the client's `▷ P` given `▷ (P ≡ Q)`. -/
theorem iEq_later_transport {P Q : IProp GF} :
    iprop(▷ iEq (GF := GF) P Q ∗ ▷ Q) ⊢ (▷ P : IProp GF) :=
  later_sep.mpr.trans (later_mono iEq_transport)

/-- Transport under `▷`, other direction (internal equality is symmetric). -/
theorem iEq_later_transport' {P Q : IProp GF} :
    iprop(▷ iEq (GF := GF) P Q ∗ ▷ P) ⊢ (▷ Q : IProp GF) :=
  (sep_mono_l (later_mono iEq_sym)).trans iEq_later_transport

end LeanliftIris.PhaseA.Fupd
