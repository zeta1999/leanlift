/-
Phase A2 (fancy-update, piece 2) — the invariant-authority resource.

The authoritative finite map from invariant names to the propositions they guard.
Since `Iris/Algebra/Auth.lean` is not built into iris-lean, we use the BUILT
recursive authoritative-map functor `HeapView.HeapViewURF` over the value functor
`FProp = AgreeRF (LaterSOF idOF)` (`Fupd.Functors`): applied to `IProp GF` its value
type is `Agree (LaterS (IProp GF))`, so the map stores *agreed later-propositions*.
(Using the universe-preserving `LaterS` is essential — iris-lean's `Later` bumps the
universe and cannot be stored; see `Fupd.Functors`.)

* `invAuth γ m` — the authority: full (`own one`) ownership of the whole map `m`,
  held inside `wsat`.
* `ownI γ i P` — the *knowledge* that invariant `i` guards `P`. Built from a
  **discarded-fraction** fragment, hence `CoreId`/persistent: it can be freely
  duplicated and shared between `wsat` and any number of clients.

`invAuth_lookup` is the authority↔knowledge bridge: holding `ownI γ i P` against the
authority forces `i ∈ dom m`. (Reflecting the stronger agreement `▷ (P ≡ Q)` into the
logic needs the internal-equality layer, `Fupd.IEq`.) Sorry-free.
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra
import Iris.Std.HeapInstances
import LeanliftIris.PhaseA.Fupd.Functors
import LeanliftIris.PhaseA.Fupd.IEq

namespace LeanliftIris.PhaseA.Fupd
open Iris Iris.BI COFE HeapView One DFrac Agree OFE

/-- The invariant-authority functor: a recursive authoritative map from invariant
names (`Nat`) to agreed later-propositions. -/
abbrev FInv (F : Type _) [UFraction F] : OFunctorPre :=
  HeapView.HeapViewURF (F := F) (H := (Nat → Option ·)) FProp

variable {F} [UFraction F] {GF} [ElemG GF (FInv F)]

/-- The authoritative invariant map (lives inside `wsat`). -/
noncomputable def invAuth (γ : GName) (m : Nat → Option (Agree (LaterS (IProp GF)))) :
    IProp GF :=
  iOwn (GF := GF) (F := FInv F) γ (HeapView.Auth (.own one) m)

/-- Invariant knowledge: name `i` guards `P`. Persistent (discarded fraction). -/
noncomputable def ownI (γ : GName) (i : Nat) (P : IProp GF) : IProp GF :=
  iOwn (GF := GF) (F := FInv F) γ
    (HeapView.Frag i .discard (toAgree (LaterS.next P)))

/-- The agree value is its own core. -/
instance instCoreId_toAgree {α : Type _} [OFE α] (a : α) : CMRA.CoreId (toAgree a) :=
  ⟨.rfl⟩

/-- A discarded fraction is its own core. -/
instance instCoreId_discard : CMRA.CoreId (DFrac.discard : DFrac F) :=
  ⟨.rfl⟩

/-- **Invariant knowledge is persistent.** -/
instance instPersistent_ownI {γ i} {P : IProp GF} :
    BI.Persistent (ownI (F := F) (GF := GF) γ i P) := by
  unfold ownI
  infer_instance

/-- **Authority↔knowledge bridge.** If a client holds `ownI γ i P`, then name `i`
is allocated in the authority's map. -/
theorem invAuth_lookup {γ i} {m : Nat → Option (Agree (LaterS (IProp GF)))} {P : IProp GF} :
    invAuth (F := F) γ m ∗ ownI (F := F) γ i P ⊢ (⌜(m i).isSome⌝ : IProp GF) := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  obtain ⟨v', _, _, Hl, _, _⟩ := HeapView.auth_op_frag_validN_iff.mp H
  have Hmi : m i = some v' := Hl
  simp [Hmi]

/-- **Invariant-knowledge agreement.** Two pieces of knowledge about the same name
agree on the guarded proposition (up to a later) — the agreement of the two
discarded-fraction `Agree (LaterS ·)` fragments. -/
theorem ownI_agree {γ i} {P Q : IProp GF} :
    ownI (F := F) γ i P ∗ ownI (F := F) γ i Q ⊢ (▷ iEq P Q : IProp GF) := by
  refine iOwn_op.mpr.trans (iOwn_cmraValid.trans ?_)
  refine (?step : (UPred.cmraValid _ : IProp GF) ⊢
      UPred.cmraValid (toAgree (LaterS.next P) • toAgree (LaterS.next Q))).trans ?_
  case step => exact fun n x _ H => (HeapView.frag_op_validN_iff.mp H).2
  exact agree_iEq.trans iEq_laterS_fwd

end LeanliftIris.PhaseA.Fupd
