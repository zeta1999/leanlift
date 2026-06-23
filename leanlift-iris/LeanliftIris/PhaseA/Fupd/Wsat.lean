/-
Phase A2 (fancy-update, piece 3) — world satisfaction (`wsat`).

`wsat` is the invariant of invariants: it owns the authoritative invariant map and,
for each allocated name `i` guarding `Q`, the per-name *slot*

  `(▷ Q ∗ ownD {i})  ∨  ownE {i}`

— either the body is stored and the disabled token is held (the invariant is closed),
or the enabled token sits in the world (the invariant is open / available). The
enabled and disabled tokens use the one `FTok` mask algebra (`Fupd.Masks`) under two
ghost names `γE`, `γD`; `ownD γD := ownE γD`.

`WsatG` bundles the three fixed ghost names (`γI` invariants, `γE` enabled,
`γD` disabled) and the two `ElemG` registrations, so the `fupd` modality
(`Fupd.Fupd`) — whose signature `Set Nat → Set Nat → IProp → IProp` has no room for
ghost names — can be a genuine typeclass instance. Sorry-free.
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra
import Iris.Std.HeapInstances
import LeanliftIris.PhaseA.Fupd.Masks
import LeanliftIris.PhaseA.Fupd.InvRes
import LeanliftIris.PhaseA.Fupd.Fresh

namespace LeanliftIris.PhaseA.Fupd
open Iris Iris.BI COFE HeapView One DFrac Agree Excl

variable {F} [UFraction F] {GF} [ElemG GF (FInv F)] [ElemG GF FTok]

/-- The singleton mask `{i}`. -/
def eqset (i : Nat) : Iris.Set Nat := fun j => j = i

/-- Disabled tokens reuse the enabled-token algebra under a separate ghost name. -/
noncomputable abbrev ownD (γ : GName) (D : Iris.Set Nat) : IProp GF := ownE (GF := GF) γ D

/-- The singleton mask's tokens are a singleton GenMap. -/
theorem tok_eqset (i : Nat) :
    tok (eqset i) = GenMap.singleton i (Excl.excl ()) := by
  apply congrArg GenMap.mk
  funext j
  simp only [tok, eqset, GenMap.singleton, GenMap.alter, GenMap.empty, Iris.alter]
  by_cases h : j = i
  · subst h; simp
  · have h' : ¬ i = j := fun heq => h heq.symm
    simp [h, h']

/-- **Fresh token allocation.** A token for a name avoiding any finite set can be
minted (the wsat-side of `inv_alloc`). -/
theorem ownE_alloc (γ : GName) (X : List Nat) :
    ⊢ |==> ∃ i, ⌜i ∉ X⌝ ∗ ownE (GF := GF) γ (eqset i) := by
  haveI : IsUnit (GenMap.empty : GenMap Nat (Excl Unit)) :=
    inferInstanceAs (IsUnit (UCMRA.unit : GenMap Nat (Excl Unit)))
  refine (iOwn_unit (F := FTok) (γ := γ) (ε := GenMap.empty)).trans ?_
  refine (BIUpdate.mono (iOwn_updateP (F := FTok) (γ := γ) (genMap_alloc_updateP X))).trans ?_
  refine BIUpdate.trans.trans (BIUpdate.mono ?_)
  iintro Ha
  icases Ha with ⟨%a', %hP, Hown⟩
  obtain ⟨i, hiX, ha'⟩ := hP
  subst ha'
  iexists i
  isplitl []
  · ipure_intro; exact hiX
  · unfold ownE
    rw [tok_eqset]
    iexact Hown

/-- The authoritative invariant map built from a name/proposition list. -/
noncomputable def toMap : List (Nat × IProp GF) → (Nat → Option (Agree (LaterS (IProp GF))))
  | [] => fun _ => none
  | (i, Q) :: L => fun j => if j = i then some (toAgree (LaterS.next Q)) else toMap L j

/-- If a name is in the authoritative map, it is allocated in the list. -/
theorem toMap_mem : ∀ (L : List (Nat × IProp GF)) {i : Nat},
    (toMap L i).isSome → ∃ Q, (i, Q) ∈ L
  | [], i, h => by simp [toMap] at h
  | (a, Q) :: L, i, h => by
      simp only [toMap] at h
      by_cases hj : i = a
      · exact ⟨Q, by subst hj; exact List.mem_cons_self ..⟩
      · rw [if_neg hj] at h
        obtain ⟨Q', hQ'⟩ := toMap_mem L h
        exact ⟨Q', List.mem_cons_of_mem _ hQ'⟩

/-- A name not among the list's names is unallocated in the authoritative map. -/
theorem toMap_fresh : ∀ (L : List (Nat × IProp GF)) {i : Nat},
    i ∉ L.map Prod.fst → toMap L i = none
  | [], _, _ => rfl
  | (a, Q) :: L, i, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp only [toMap, if_neg h.1]
      exact toMap_fresh L h.2

/-- Consing a name/prop pair onto the list inserts it into the authoritative map
(stated in the `if i = j` orientation that the partial-map `insert` reduces to). -/
theorem toMap_cons_eq_insert (i : Nat) (P : IProp GF) (L : List (Nat × IProp GF)) :
    toMap ((i, P) :: L) =
      (fun j => if i = j then some (toAgree (LaterS.next P)) else toMap L j) := by
  funext j
  simp only [toMap]
  by_cases h : j = i
  · subst h; simp
  · have h' : ¬ i = j := fun e => h e.symm
    simp [h, h']

/-- **Allocate a new invariant in the authority.** For a name fresh in the map, extend
it and hand out the persistent knowledge `ownI`. -/
theorem invAuth_alloc {γ i} {P : IProp GF} {L : List (Nat × IProp GF)}
    (hfresh : toMap L i = none) :
    invAuth (F := F) γ (toMap L) ⊢
      |==> (invAuth (F := F) γ (toMap ((i, P) :: L)) ∗ ownI (F := F) γ i P) := by
  rw [toMap_cons_eq_insert]
  unfold invAuth ownI
  refine (iOwn_update ?_).trans (BIUpdate.mono iOwn_op.mp)
  exact HeapView.update_one_alloc (dq := DFrac.discard) hfresh (by trivial)
    (Agree.valid_def.mpr fun _ => trivial)

/-- The per-invariant slot: body stored & disabled, or enabled token present. -/
noncomputable abbrev invSlot (γE γD : GName) (i : Nat) (Q : IProp GF) : IProp GF :=
  iprop( (▷ Q ∗ ownD (GF := GF) γD (eqset i)) ∨ ownE γE (eqset i) )

/-- The per-name world-satisfaction entry: invariant knowledge plus the slot. -/
noncomputable abbrev slotF (γI γE γD : GName) (p : Nat × IProp GF) : IProp GF :=
  iprop(ownI (F := F) γI p.1 p.2 ∗ invSlot γE γD p.1 p.2)

/-- **World satisfaction.** -/
noncomputable def wsat (γI γE γD : GName) : IProp GF :=
  iprop( ∃ L, invAuth (F := F) γI (toMap L) ∗ [∗] (L.map (slotF (F := F) γI γE γD)) )

/-- The fixed ghost names and registrations the `fupd`/`inv` layer is parametric in.
`F` is an `outParam` (determined by the chosen `WsatG` instance) so the `fupd` /
`BIFUpdate` instances on `IProp GF` resolve without mentioning `F`. -/
class WsatG (GF : BundledGFunctors) (F : outParam (Type _)) [UFraction F] where
  γI : GName
  γE : GName
  γD : GName
  [hInv : ElemG GF (FInv F)]
  [hTok : ElemG GF FTok]

attribute [instance] WsatG.hInv WsatG.hTok

end LeanliftIris.PhaseA.Fupd
