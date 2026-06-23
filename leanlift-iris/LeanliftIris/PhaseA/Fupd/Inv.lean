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

/-- **Open an invariant.** Trading the enable token `ownE {i}` for the stored body
`▷ P` and the disable token `ownD {i}`; `wsat` is handed back with slot `i` now in its
enabled state. The body comes back as `▷ P` (the client's proposition) by agreement
with the stored body. -/
theorem ownI_open {i : Nat} {P : IProp GF} :
    iprop(ownI (F := F) W.γI i P ∗ wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE (eqset i))
      ⊢ iprop(▷ P ∗ wsat (F := F) W.γI W.γE W.γD ∗ ownD W.γD (eqset i)) := by
  simp only [wsat]
  iintro Hin
  icases Hin with ⟨#Hinv, Hw, HEi⟩
  icases Hw with ⟨%L, HA, Hbig⟩
  -- locate the slot for `i`
  ihave Hcomb : iprop(invAuth (F := F) W.γI (toMap L) ∗ ownI (F := F) W.γI i P) $$ [HA]
  · isplitl [HA]
    · iexact HA
    · iexact Hinv
  ihave Hk := (invAuth_lookup_keep (GF := GF) (F := F) (γ := W.γI))
  ispecialize Hk $$ Hcomb
  icases Hk with ⟨%Hsome, HA2, _⟩
  obtain ⟨Q, hmem⟩ := toMap_mem L Hsome
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  ihave Hext := (bigSep_map_extract (slotF (F := F) W.γI W.γE W.γD) (i, Q) pre post).1
  ispecialize Hext $$ Hbig
  icases Hext with ⟨Hslot, Hrest⟩
  icases Hslot with ⟨#HownIQ, Hsl⟩
  icases Hsl with (⟨HQbody, HownD⟩ | HEi_slot)
  · -- slot was disabled: take the body and disable token, re-enable the slot
    ihave Hag := (ownI_agree (F := F) (γ := W.γI) (i := i) (P := P) (Q := Q))
    ihave Hpq : iprop(ownI (F := F) W.γI i P ∗ ownI (F := F) W.γI i Q) $$ []
    · isplitl []
      · iexact Hinv
      · iexact HownIQ
    ispecialize Hag $$ Hpq
    ihave HPlater : iprop(▷ P) $$ [Hag, HQbody]
    · iapply iEq_later_transport
      isplitl [Hag]
      · iexact Hag
      · iexact HQbody
    isplitl [HPlater]
    · iexact HPlater
    · isplitl [HA2 Hrest HEi]
      · iexists (pre ++ (i, Q) :: post)
        isplitl [HA2]
        · iexact HA2
        · ihave Hcomb2 := (bigSep_map_extract (slotF (F := F) W.γI W.γE W.γD) (i, Q) pre post).2
          iapply Hcomb2
          isplitl [HEi]
          · isplitl []
            · iexact HownIQ
            · iright
              iexact HEi
          · iexact Hrest
      · iexact HownD
  · -- slot was enabled: two enable tokens for `i` — impossible
    ihave Hd := (ownE_disjoint (GF := GF) (γ := W.γE) (E1 := eqset i) (E2 := eqset i))
    ihave Hee : iprop(ownE W.γE (eqset i) ∗ ownE W.γE (eqset i)) $$ [HEi, HEi_slot]
    · isplitl [HEi]
      · iexact HEi
      · iexact HEi_slot
    ispecialize Hd $$ Hee
    icases Hd with %Hd
    exact (Hd i ⟨rfl, rfl⟩).elim

/-- **Close an invariant.** Returning the body `▷ P` and the disable token `ownD {i}`
re-disables slot `i` in `wsat` and hands back the enable token `ownE {i}`. -/
theorem ownI_close {i : Nat} {P : IProp GF} :
    iprop(ownI (F := F) W.γI i P ∗ wsat (F := F) W.γI W.γE W.γD ∗ ▷ P ∗ ownD W.γD (eqset i))
      ⊢ iprop(wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE (eqset i)) := by
  simp only [wsat]
  iintro Hin
  icases Hin with ⟨#Hinv, Hw, HPlater, HownD⟩
  icases Hw with ⟨%L, HA, Hbig⟩
  ihave Hcomb : iprop(invAuth (F := F) W.γI (toMap L) ∗ ownI (F := F) W.γI i P) $$ [HA]
  · isplitl [HA]
    · iexact HA
    · iexact Hinv
  ihave Hk := (invAuth_lookup_keep (GF := GF) (F := F) (γ := W.γI))
  ispecialize Hk $$ Hcomb
  icases Hk with ⟨%Hsome, HA2, _⟩
  obtain ⟨Q, hmem⟩ := toMap_mem L Hsome
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  ihave Hext := (bigSep_map_extract (slotF (F := F) W.γI W.γE W.γD) (i, Q) pre post).1
  ispecialize Hext $$ Hbig
  icases Hext with ⟨Hslot, Hrest⟩
  icases Hslot with ⟨#HownIQ, Hsl⟩
  icases Hsl with (⟨HQbody, HownD_slot⟩ | HEi_slot)
  · -- slot already disabled: two disable tokens for `i` — impossible
    ihave Hd := (ownE_disjoint (GF := GF) (γ := W.γD) (E1 := eqset i) (E2 := eqset i))
    ihave Hee : iprop(ownE W.γD (eqset i) ∗ ownE W.γD (eqset i)) $$ [HownD, HownD_slot]
    · isplitl [HownD]
      · iexact HownD
      · iexact HownD_slot
    ispecialize Hd $$ Hee
    icases Hd with %Hd
    exact (Hd i ⟨rfl, rfl⟩).elim
  · -- slot enabled: take the enable token, re-disable with our body + disable token
    ihave Hag := (ownI_agree (F := F) (γ := W.γI) (i := i) (P := P) (Q := Q))
    ihave Hpq : iprop(ownI (F := F) W.γI i P ∗ ownI (F := F) W.γI i Q) $$ []
    · isplitl []
      · iexact Hinv
      · iexact HownIQ
    ispecialize Hag $$ Hpq
    ihave HQlater : iprop(▷ Q) $$ [Hag, HPlater]
    · iapply iEq_later_transport'
      isplitl [Hag]
      · iexact Hag
      · iexact HPlater
    isplitl [HA2 Hrest HQlater HownD]
    · iexists (pre ++ (i, Q) :: post)
      isplitl [HA2]
      · iexact HA2
      · ihave Hcomb2 := (bigSep_map_extract (slotF (F := F) W.γI W.γE W.γD) (i, Q) pre post).2
        iapply Hcomb2
        isplitl [HQlater HownD]
        · isplitl []
          · iexact HownIQ
          · ileft
            isplitl [HQlater]
            · iexact HQlater
            · iexact HownD
        · iexact Hrest
    · iexact HEi_slot

/-- The persistent invariant assertion: name `i` guards `P`. -/
noncomputable def inv (i : Nat) (P : IProp GF) : IProp GF := ownI (F := F) W.γI i P

instance instPersistent_inv {i} {P : IProp GF} : BI.Persistent (inv (W := W) i P) := by
  unfold inv
  infer_instance

/-- **Invariant access.** An invariant `inv i P` can be opened over any mask `E ∋ i`:
shift to `E ∖ {i}`, obtain the body `▷ P`, and receive a closing update that, on return
of `▷ P`, restores the mask to `E`. The Iris invariant-access law, for finite masks. -/
theorem inv_acc {i : Nat} {P : IProp GF} {E : Iris.Set Nat} (hi : E i) :
    inv (W := W) i P ⊢
      fupd (W := W) E (mdiff E (eqset i))
        iprop(▷ P ∗ (▷ P -∗ fupd (W := W) (mdiff E (eqset i)) E (emp : IProp GF))) := by
  have hsub : Iris.Subset (eqset i) E := by
    intro j hj
    simp only [eqset] at hj
    subst hj
    exact hi
  simp only [fupd, inv]
  iintro #Hinv Hin
  icases Hin with ⟨Hw, HE⟩
  -- peel the enable token for `i` off the mask
  ihave Hsplit := (ownE_subset_split (GF := GF) (γ := W.γE) hsub).1
  ispecialize Hsplit $$ HE
  icases Hsplit with ⟨HEi, HE'⟩
  -- open the invariant
  ihave Hpre : iprop(ownI (F := F) W.γI i P ∗ wsat (F := F) W.γI W.γE W.γD
                      ∗ ownE W.γE (eqset i)) $$ [Hw, HEi]
  · isplitl []
    · iexact Hinv
    · isplitl [Hw]
      · iexact Hw
      · iexact HEi
  ihave Hopen := (ownI_open (W := W) (i := i) (P := P))
  ispecialize Hopen $$ Hpre
  icases Hopen with ⟨HPlater, Hw2, HownD⟩
  iapply be_intro
  isplitl [Hw2]
  · iexact Hw2
  · isplitl [HE']
    · iexact HE'
    · isplitl [HPlater]
      · iexact HPlater
      · -- the closing update, capturing the disable token `HownD`
        iintro HP2 Hin2
        icases Hin2 with ⟨Hw3, HE'2⟩
        ihave Hpre2 : iprop(ownI (F := F) W.γI i P ∗ wsat (F := F) W.γI W.γE W.γD
                            ∗ ▷ P ∗ ownD W.γD (eqset i)) $$ [Hw3, HP2, HownD]
        · isplitl []
          · iexact Hinv
          · isplitl [Hw3]
            · iexact Hw3
            · isplitl [HP2]
              · iexact HP2
              · iexact HownD
        ihave Hclose := (ownI_close (W := W) (i := i) (P := P))
        ispecialize Hclose $$ Hpre2
        icases Hclose with ⟨Hw4, HEi2⟩
        iapply be_intro
        isplitl [Hw4]
        · iexact Hw4
        · isplitl [HE'2 HEi2]
          · ihave Hcombw := (ownE_subset_split (GF := GF) (γ := W.γE) hsub).2
            iapply Hcombw
            isplitl [HEi2]
            · iexact HEi2
            · iexact HE'2
          · iemp_intro

/-- **Invariant allocation.** Any `▷ P` can be sealed into a fresh invariant `inv i P`,
under any mask. The Iris invariant-creation law. -/
theorem inv_alloc {P : IProp GF} {E : Iris.Set Nat} :
    (▷ P : IProp GF) ⊢ fupd (W := W) E E iprop(∃ i, inv (W := W) i P) := by
  simp only [fupd, inv, wsat]
  iintro HP Hin
  icases Hin with ⟨Hw, HE⟩
  icases Hw with ⟨%L, HA, Hbig⟩
  -- mint a fresh disabled token avoiding the already-allocated names
  ihave Halloc := (ownE_alloc (GF := GF) W.γD (L.map Prod.fst))
  imod Halloc with Halloc
  icases Halloc with ⟨%i, %hiX, HownD⟩
  -- extend the authority with the fresh invariant
  have hfresh : toMap L i = none := toMap_fresh L hiX
  ihave Hauth := (invAuth_alloc (F := F) (γ := W.γI) (i := i) (P := P) (L := L) hfresh)
  ispecialize Hauth $$ HA
  imod Hauth with Hauth
  icases Hauth with ⟨HA', #HownI⟩
  iapply be_intro
  isplitl [HA' Hbig HP HownD]
  · -- world satisfaction with the new (disabled) slot prepended
    iexists ((i, P) :: L)
    isplitl [HA']
    · iexact HA'
    · rw [List.map_cons]
      iapply bigOp_sep_cons.mpr
      isplitl [HownI HP HownD]
      · isplitl []
        · iexact HownI
        · ileft
          isplitl [HP]
          · iexact HP
          · iexact HownD
      · iexact Hbig
  · isplitl [HE]
    · iexact HE
    · iexists i
      iexact HownI

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
