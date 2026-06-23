/-
Phase A2 (fancy-update, piece 4) — the fancy-update modality and its laws.

`fupd E1 E2 P := wsat ∗ ownE E1 -∗ |==> ◇ (wsat ∗ ownE E2 ∗ P)` (Iris's standard
definition), with the ghost names fixed by `WsatG` (`Fupd.Wsat`). We prove the five
`BIFUpdate` laws and register `instance : BIFUpdate (IProp GF) Nat`.

The laws thread `wsat` opaquely — none of them inspect its structure. They reduce to
(i) algebra of the `|==> ◇` modality (helpers `be_*` below) and (ii) the mask token
algebra (`ownE_op`, `ownE_disjoint`, `ownE_subset_split` from `Fupd.Masks`). The
invariant-allocation/access machinery (`Fupd.Inv`) is what actually uses `wsat`'s
internals. Sorry-free.
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra
import LeanliftIris.PhaseA.Fupd.Wsat

namespace LeanliftIris.PhaseA.Fupd
open Iris Iris.BI COFE OFE

/-! ## Algebra of the `|==> ◇` modality -/

variable {GF}

theorem be_intro {P : IProp GF} : P ⊢ |==> ◇ P :=
  except0_intro.trans BIUpdate.intro

theorem be_mono {P Q : IProp GF} (h : P ⊢ Q) : (|==> ◇ P : IProp GF) ⊢ |==> ◇ Q :=
  BIUpdate.mono (except0_mono h)

theorem be_trans {P : IProp GF} : (|==> ◇ (|==> ◇ P) : IProp GF) ⊢ |==> ◇ P :=
  ((BIUpdate.mono bupd_except0).trans BIUpdate.trans).trans (BIUpdate.mono except0_idemp.1)

theorem be_frame_r {P R : IProp GF} : ((|==> ◇ P) ∗ R : IProp GF) ⊢ |==> ◇ (P ∗ R) :=
  bupd_frame_r.trans (BIUpdate.mono ((sep_mono_r except0_intro).trans except0_sep.2))

/-! ## The fancy-update modality -/

variable {F} [UFraction F] [W : WsatG GF F]

/-- The fancy update: from `wsat ∗ ownE E1` produce `wsat ∗ ownE E2 ∗ P` under a
basic update and an except-0. -/
noncomputable def fupd (E1 E2 : Iris.Set Nat) (P : IProp GF) : IProp GF :=
  iprop( wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE E1 -∗
         |==> ◇ (wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE E2 ∗ P) )

noncomputable instance : FUpd (IProp GF) Nat := ⟨fupd⟩

theorem fupd_eq (E1 E2 : Iris.Set Nat) (P : IProp GF) :
    fupd (W := W) E1 E2 P =
      iprop( wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE E1 -∗
             |==> ◇ (wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE E2 ∗ P) ) := rfl

/-- Non-expansiveness in the postcondition. -/
theorem fupd_ne {E1 E2 : Iris.Set Nat} : OFE.NonExpansive (fupd (W := W) E1 E2) := by
  constructor
  intro n x₁ x₂ H
  simp only [fupd]
  exact wand_ne.ne .rfl
    (BIUpdate.bupd_ne.ne (except0_ne.ne (sep_ne.ne .rfl (sep_ne.ne .rfl H))))

/-! ## The five `BIFUpdate` laws -/

theorem fupd_frame_r (E1 E2 : Iris.Set Nat) (P R : IProp GF) :
    iprop(fupd (W := W) E1 E2 P ∗ R) ⊢ fupd (W := W) E1 E2 iprop(P ∗ R) := by
  simp only [fupd]
  iintro H
  icases H with ⟨Hw, HR⟩
  iintro Hin
  ispecialize Hw $$ Hin
  imod Hw with Hc
  icases Hc with ⟨HW, HE2, HP⟩
  imodintro
  isplitl [HW]
  · iexact HW
  · isplitl [HE2]
    · iexact HE2
    · isplitl [HP]
      · iexact HP
      · iexact HR

theorem fupd_except0 (E1 E2 : Iris.Set Nat) (P : IProp GF) :
    iprop(◇ fupd (W := W) E1 E2 P) ⊢ fupd (W := W) E1 E2 P := by
  simp only [fupd]
  iintro H
  iintro Hin
  -- H : ◇ (𝕎∗OE E1 -∗ |==>◇(...)); Hin : 𝕎∗OE E1
  -- push Hin under ◇ and eliminate
  imod H with Hw
  ispecialize Hw $$ Hin
  iexact Hw

theorem fupd_trans (E1 E2 E3 : Iris.Set Nat) (P : IProp GF) :
    fupd (W := W) E1 E2 (fupd (W := W) E2 E3 P) ⊢ fupd (W := W) E1 E3 P := by
  simp only [fupd]
  apply wand_mono_r
  exact (be_mono (sep_assoc.2.trans wand_elim_r)).trans be_trans

theorem fupd_subset {E1 E2 : Iris.Set Nat} (h : Iris.Subset E2 E1) :
    ⊢ fupd (W := W) E1 E2 (fupd (W := W) E2 E1 (emp : IProp GF)) := by
  simp only [fupd]
  iintro Hin
  icases Hin with ⟨HW, HE1⟩
  ihave Hsplit := (ownE_subset_split (GF := GF) (γ := W.γE) h).1
  ispecialize Hsplit $$ HE1
  icases Hsplit with ⟨HE2, HEd⟩
  iapply be_intro
  isplitl [HW]
  · iexact HW
  · isplitl [HE2]
    · iexact HE2
    · -- inner: 𝕎∗OE E2 -∗ |==>◇(𝕎∗OE E1∗emp), with HEd : OE (mdiff E1 E2) stashed
      iintro Hin2
      icases Hin2 with ⟨HW2, HE2'⟩
      iapply be_intro
      isplitl [HW2]
      · iexact HW2
      · isplitl [HE2' HEd]
        · ihave Hcomb := (ownE_subset_split (GF := GF) (γ := W.γE) h).2
          iapply Hcomb
          isplitl [HE2']
          · iexact HE2'
          · iexact HEd
        · iemp_intro

theorem fupd_mask_frame_r' {E1 E2 Ef : Iris.Set Nat} (P : IProp GF)
    (h : Iris.Disjoint E1 Ef) :
    fupd (W := W) E1 E2 iprop(⌜Iris.Disjoint E2 Ef⌝ → P) ⊢
      fupd (W := W) (Iris.union E1 Ef) (Iris.union E2 Ef) P := by
  -- the modality-free heart: with the framed `ownE Ef`, derive disjointness, recombine
  -- masks, and discharge the implication.
  have step :
      iprop((wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE E2 ∗ (⌜Iris.Disjoint E2 Ef⌝ → P))
              ∗ ownE W.γE Ef)
        ⊢ iprop(wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE (Iris.union E2 Ef) ∗ P) := by
    iintro Hc
    icases Hc with ⟨⟨HW2, HE2, Himp⟩, HEf2⟩
    ihave Hee : iprop(ownE W.γE E2 ∗ ownE W.γE Ef) $$ [HE2, HEf2]
    · isplitl [HE2]
      · iexact HE2
      · iexact HEf2
    ihave Hkeep := (ownE_disjoint_keep (GF := GF) (γ := W.γE))
    ispecialize Hkeep $$ Hee
    icases Hkeep with ⟨%HD, Hee2⟩
    ihave Hpure : iprop(⌜Iris.Disjoint E2 Ef⌝) $$ []
    · ipure_intro
      exact HD
    ispecialize Himp $$ Hpure
    ihave Hcombw := (ownE_op (GF := GF) (γ := W.γE) HD).2
    ispecialize Hcombw $$ Hee2
    isplitl [HW2]
    · iexact HW2
    · isplitl [Hcombw]
      · iexact Hcombw
      · iexact Himp
  simp only [fupd]
  iintro H Hin
  icases Hin with ⟨HW, HEU⟩
  ihave Hsp := (ownE_op (GF := GF) (γ := W.γE) h).1
  ispecialize Hsp $$ HEU
  icases Hsp with ⟨HE1, HEf⟩
  ihave Hwe : iprop(wsat (F := F) W.γI W.γE W.γD ∗ ownE W.γE E1) $$ [HW, HE1]
  · isplitl [HW]
    · iexact HW
    · iexact HE1
  ispecialize H $$ Hwe
  -- thread the stashed `ownE Ef` through the modality, then apply `step`
  iapply (be_mono step)
  iapply be_frame_r
  isplitl [H]
  · iexact H
  · iexact HEf

/-! ## The `BIFUpdate` instance -/

/-- **`IProp GF` is a fancy-update BI over `Nat`-indexed masks.** Assembles the five
laws into the upstream `BIFUpdate` typeclass — logically-atomic triples
`<<< P >>> e @ E <<< Q >>>` are now expressible. -/
noncomputable instance instBIFUpdate : BIFUpdate (IProp GF) Nat where
  ne := fupd_ne
  subset := fupd_subset
  except0 P := fupd_except0 _ _ P
  trans P := fupd_trans _ _ _ P
  mask_frame_r' P := fupd_mask_frame_r' P
  frame_r P R := fupd_frame_r _ _ P R

end LeanliftIris.PhaseA.Fupd
