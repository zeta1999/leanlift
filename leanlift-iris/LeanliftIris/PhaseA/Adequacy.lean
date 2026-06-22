/-
Phase A2 (step 4) — adequacy for the `λ-conc` weakest precondition.

Adequacy is the trust anchor: a proof `⊢ wp e Φ` in the logic entails an
operational fact about the real `λ-conc` program — closing leanlift's model/code
gap for this lane. We build it from:

  * `wp_step_pres` — one primitive step preserves `stateInterp ∗ wp` (up to the
    `▷`/`|==>` the `wp` carries), the iProp-level heart;
  * the model soundness of `|==> ⌜·⌝` and `▷` (`pure_soundness`, `later_soundness`)
    to extract a meta-level `Prop` after a finite run.

This file establishes the one-step preservation, lifts it to a whole fork-free
run via the step-update tower `sfupdN`, collapses that tower over a pure
postcondition at the `UPred` model level (`sfupdN_pure_soundness`), and assembles
the headline **sequential adequacy** `wp_adequacy_seq`: a `wp` proof of a pure
property + a fork-free run reaching a value ⟹ the meta-level fact. (The general
concurrent/thread-pool `steps` adequacy is future work.) Sorry-free.
-/
import LeanliftIris.PhaseA.WpLifting

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-- **Preservation.** One primitive step of a non-value `e` turns
`stateInterp γ σ ∗ wp γ e Φ` into the interpretation + continuation at the
stepped-to state, modulo the update/later the `wp` carries. -/
theorem wp_step_pres (γ : GName) [HasHeap γ GF F] (e : Expr) (σ : Heap) (e' : Expr)
    (σ' : Heap) (efs : List Expr) (Φ : Val → IProp GF) (hnv : toVal e = none)
    (hstep : prim_step e σ e' σ' efs) :
    stateInterp γ σ ∗ wp (F := F) γ e Φ ⊢
      |==> ▷ |==> (stateInterp γ σ' ∗ wp (F := F) γ e' Φ) := by
  iintro ⟨Hσ, Hwp⟩
  ihave H1 := (wp_step γ e Φ hnv) $$ [Hwp]
  · iexact Hwp
  ihave H2 := H1 $$ [Hσ]
  · iexact Hσ
  imod H2 with H3
  ispecialize H3 $$ %e'
  ispecialize H3 $$ %σ'
  ispecialize H3 $$ %efs
  ispecialize H3 $$ []
  · ipure_intro; exact hstep
  iintro !>
  iexact H3

/-- **Adequacy, base case.** A value verified against a pure postcondition
satisfies it at the meta level. Exercises the soundness path
(`wp_value_inv` → `bupd_elim` → `pure_soundness`). -/
theorem wp_adequacy_val (γ : GName) [HasHeap γ GF F] (v : Val) (φ : Val → Prop)
    (h : ⊢ wp (F := F) γ (.val v) (fun w => iprop(⌜φ w⌝))) : φ v := by
  -- |==> ⌜φ v⌝ ⊢ ⌜φ v⌝ (bupd over a plain pure)
  have hbupd : (iprop(|==> ⌜φ v⌝) : IProp GF) ⊢ iprop(⌜φ v⌝) :=
    (BIUpdate.mono plainly_pure.mpr).trans BIBUpdatePlainly.bupd_plainly
  have hb : (emp : IProp GF) ⊢ iprop(⌜φ v⌝) :=
    (h.trans (wp_value_inv γ v (fun w => iprop(⌜φ w⌝)))).trans hbupd
  have hte : (iprop(True) : IProp GF) ⊢ emp := biaffine_iff_true_emp.1 inferInstance
  exact UPred.pure_soundness (hte.trans hb)

/-! ## Multi-step preservation: the step-update tower

A `k`-step run of the `wp` accumulates one `|==> ▷` per primitive step plus the
trailing `|==>` of the base case. We package that modality as a *tower*
`sfupdN k X = (|==> ▷)^k |==> X` and lift one-step preservation along a whole
fork-free run. -/

/-- The step-update tower `(|==> ▷)^k |==> X`. -/
def sfupdN (k : Nat) (X : IProp GF) : IProp GF :=
  match k with
  | 0    => iprop(|==> X)
  | k+1  => iprop(|==> ▷ (sfupdN k X))

/-- Every tower starts with a `|==>`, so a leading `|==>` is absorbed. -/
theorem sfupdN_bupd_absorb (k : Nat) (X : IProp GF) :
    iprop(|==> sfupdN k X) ⊢ sfupdN k X := by
  cases k with
  | zero => exact BIUpdate.trans
  | succ k => exact BIUpdate.trans

/-- The tower is monotone in its payload. -/
theorem sfupdN_mono (k : Nat) {X Y : IProp GF} (h : X ⊢ Y) :
    sfupdN k X ⊢ sfupdN k Y := by
  induction k with
  | zero => exact BIUpdate.mono h
  | succ k ih => exact BIUpdate.mono (later_mono ih)

/-- Towers compose: stacking an `a`-tower over a `b`-tower is an `(a+b)`-tower. -/
theorem sfupdN_compose (a b : Nat) (X : IProp GF) :
    sfupdN a (sfupdN b X) ⊢ sfupdN (a + b) X := by
  induction a with
  | zero =>
      show iprop(|==> sfupdN b X) ⊢ sfupdN (0 + b) X
      rw [Nat.zero_add]
      exact sfupdN_bupd_absorb b X
  | succ k ih =>
      show iprop(|==> ▷ (sfupdN k (sfupdN b X))) ⊢ sfupdN (k + 1 + b) X
      have : (k + 1 + b) = (k + b) + 1 := by omega
      rw [this]
      exact BIUpdate.mono (later_mono ih)

/-- **Fork-free multi-step relation** — the reflexive-transitive closure of a
single-thread, no-fork primitive step. This is the single-thread fragment of the
thread-pool `steps` (each step lifts via `step.single`). -/
inductive primSteps : Expr → Heap → Expr → Heap → Prop where
  | refl {e σ} : primSteps e σ e σ
  | tail {e σ e' σ' e'' σ''} :
      primSteps e σ e' σ' → prim_step e' σ' e'' σ'' [] → primSteps e σ e'' σ''

/-- A stepping expression is not a value. -/
theorem toVal_none_of_prim_step {e : Expr} {σ : Heap} {e' : Expr} {σ' : Heap}
    {efs : List Expr} (h : prim_step e σ e' σ' efs) : toVal e = none := by
  cases e <;> first | rfl | (exfalso; exact val_no_prim_step _ _ _ _ _ h)

/-- **Multi-step preservation.** A `k`-step fork-free run carries
`stateInterp ∗ wp` from the start state to the end state, modulo a `k`-tall
step-update tower. The iProp-level core of sequential adequacy: proved by
induction on the run from the one-step `wp_step_pres`. -/
theorem wp_primSteps_pres (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF)
    {e : Expr} {σ : Heap} {e' : Expr} {σ' : Heap} (h : primSteps e σ e' σ') :
    ∃ k, iprop(stateInterp γ σ ∗ wp (F := F) γ e Φ) ⊢
      sfupdN k iprop(stateInterp γ σ' ∗ wp (F := F) γ e' Φ) := by
  induction h with
  | refl => exact ⟨0, BIUpdate.intro⟩
  | tail _hsteps hstep ih =>
      obtain ⟨k, ih⟩ := ih
      refine ⟨k + 1, ?_⟩
      have hone :
          iprop(stateInterp γ _ ∗ wp (F := F) γ _ Φ) ⊢ sfupdN 1 iprop(stateInterp γ _ ∗ wp (F := F) γ _ Φ) :=
        wp_step_pres γ _ _ _ _ [] Φ (toVal_none_of_prim_step hstep) hstep
      refine ih.trans ((sfupdN_mono k hone).trans ?_)
      exact sfupdN_compose k 1 _

/-! ## The step-update tower over a pure proposition collapses (model level)

The remaining piece the file's header tracked: extracting a meta-level `Prop` from
the tower. A `|==>` over a *pure* proposition is sound (`bupd_plainly` for pure),
and a `▷` over a pure proposition is sound at a high enough step-index
(`later_soundness`'s idea). Threading the two through the tower — evaluating at
step-index `k` and peeling one `▷` per level — collapses `sfupdN k ⌜φ⌝` to `φ`.
This is proved at the `UPred` model level (like `later_soundness`). -/

/-- **Tower collapse.** If `True` entails the `k`-tall tower over a pure `φ`, then
`φ` holds at the meta level. -/
theorem sfupdN_pure_soundness {φ : Prop} (k : Nat)
    (h : (iprop(True) : IProp GF) ⊢ sfupdN k iprop(⌜φ⌝)) : φ := by
  suffices key : ∀ (j m : Nat) (x : IResUR GF), j ≤ m → ✓{m} x →
      (sfupdN j (iprop(⌜φ⌝) : IProp GF)).holds m x → φ by
    exact key k k CMRA.unit (Nat.le_refl k) CMRA.unit_validN
      (h k CMRA.unit CMRA.unit_validN trivial)
  intro j
  induction j with
  | zero =>
      intro m x _ hv hh
      obtain ⟨x', _, hφ⟩ := hh m CMRA.unit (Nat.le_refl m)
        (CMRA.unit_right_id.symm.dist.validN.1 hv)
      exact hφ
  | succ j ih =>
      intro m x hjm hv hh
      cases m with
      | zero => omega
      | succ m' =>
          obtain ⟨x', hx'v, hlater⟩ := hh (m'+1) CMRA.unit (Nat.le_refl _)
            (CMRA.unit_right_id.symm.dist.validN.1 hv)
          have hx'v' : ✓{m'} x' :=
            CMRA.validN_of_le (Nat.le_succ m')
              (CMRA.unit_right_id.dist.validN.1 hx'v)
          exact ih m' x' (by omega) hx'v' hlater

/-! ## Sequential adequacy — the trust anchor

Composing the multi-step preservation with the tower collapse: a `wp` proof of a
pure postcondition, plus a fork-free run that reaches a value, yields a meta-level
operational fact about the real `λ-conc` program. This closes the model/code gap
for every sequential `wp` result in the lane (Treiber `push`/`pop`, the bridge). -/

/-- **Sequential adequacy.** If `stateInterp γ σ ∗ wp γ e ⌜φ⌝` holds and the
program `e` runs fork-free from heap `σ` to a value `v` (at heap `σ'`), then
`φ v` holds at the meta level. -/
theorem wp_adequacy_seq (γ : GName) [HasHeap γ GF F] (e : Expr) (σ : Heap)
    (v : Val) (σ' : Heap) (φ : Val → Prop)
    (hrun : primSteps e σ (.val v) σ')
    (h : (iprop(True) : IProp GF) ⊢
      iprop(stateInterp γ σ ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝)))) : φ v := by
  obtain ⟨k, hpres⟩ := wp_primSteps_pres γ (fun w => iprop(⌜φ w⌝)) hrun
  -- the end payload (state interp + wp at the final value) entails the pure goal
  have bpe : (iprop(|==> ⌜φ v⌝) : IProp GF) ⊢ iprop(⌜φ v⌝) :=
    (BIUpdate.mono plainly_pure.mpr).trans BIBUpdatePlainly.bupd_plainly
  have hwpv : wp (F := F) γ (.val v) (fun w => iprop(⌜φ w⌝)) ⊢ iprop(⌜φ v⌝) :=
    (wp_value_inv γ v (fun w => iprop(⌜φ w⌝))).trans bpe
  have hpayload :
      iprop(stateInterp γ σ' ∗ wp (F := F) γ (.val v) (fun w => iprop(⌜φ w⌝))) ⊢ iprop(⌜φ v⌝) := by
    iintro ⟨_, H⟩
    iapply hwpv
    iexact H
  exact sfupdN_pure_soundness k (h.trans (hpres.trans (sfupdN_mono k hpayload)))

/-! ## Heap-ghost initialization + a fully-closed operational theorem

To *apply* adequacy from nothing we must produce the initial `stateInterp` — the
authoritative heap — out of thin air. `iOwn_alloc` allocates a fresh ghost name
owning the full authoritative heap (valid by `auth_one_valid`). Combined with a
closed `wp` proof and adequacy, this yields a fully-closed meta-level fact about a
real program, with no remaining iProp hypotheses. -/

/-- **Heap-ghost initialization.** The authoritative heap for any `σ` can be
allocated under a fresh ghost name. -/
theorem heap_init (σ : Heap) :
    ⊢ (iprop(|==> ∃ γ : GName, stateInterp (F := F) γ σ) : IProp GF) :=
  iOwn_alloc _ HeapView.auth_one_valid

/-- A length-indexed fork-free run (the step count is explicit, so it is uniform
across a later `∃ γ`). -/
inductive primStepsN : Nat → Expr → Heap → Expr → Heap → Prop where
  | refl {e σ} : primStepsN 0 e σ e σ
  | tail {n e σ e' σ' e'' σ''} :
      primStepsN n e σ e' σ' → prim_step e' σ' e'' σ'' [] →
      primStepsN (n + 1) e σ e'' σ''

/-- A fork-free run has some explicit length. -/
theorem primStepsN_of_primSteps {e : Expr} {σ : Heap} {e' : Expr} {σ' : Heap}
    (h : primSteps e σ e' σ') : ∃ n, primStepsN n e σ e' σ' := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | tail _ hstep ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, hn.tail hstep⟩

/-- **The run relation is the real single-thread semantics.** A fork-free
`primSteps` run is exactly a thread-pool `steps` run of the singleton pool — so the
relation adequacy consumes is not an artificial abstraction but the genuine
operational semantics restricted to one thread. (Each step lifts via
`step.single`; with no forks the pool stays a singleton.) -/
theorem primSteps_imp_steps {e : Expr} {σ : Heap} {e' : Expr} {σ' : Heap}
    (h : primSteps e σ e' σ') : steps ⟨[e], σ⟩ ⟨[e'], σ'⟩ := by
  induction h with
  | refl => exact steps.refl
  | tail _ hstep ih => exact ih.tail (step.single hstep)

/-- **Multi-step preservation, explicit count.** Same as `wp_primSteps_pres` but
the tower height is the run's length `n` — fixed independently of any ghost name. -/
theorem wp_primStepsN_pres (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF)
    {n : Nat} {e : Expr} {σ : Heap} {e' : Expr} {σ' : Heap}
    (h : primStepsN n e σ e' σ') :
    iprop(stateInterp γ σ ∗ wp (F := F) γ e Φ) ⊢
      sfupdN n iprop(stateInterp γ σ' ∗ wp (F := F) γ e' Φ) := by
  induction h with
  | refl => exact BIUpdate.intro
  | @tail n e σ e1 σ1 e2 σ2 _hsteps hstep ih =>
      have hone :
          iprop(stateInterp γ _ ∗ wp (F := F) γ _ Φ) ⊢ sfupdN 1 iprop(stateInterp γ _ ∗ wp (F := F) γ _ Φ) :=
        wp_step_pres γ _ _ _ _ [] Φ (toVal_none_of_prim_step hstep) hstep
      exact ih.trans ((sfupdN_mono n hone).trans (sfupdN_compose n 1 _))

/-- **Closed adequacy.** If — *from nothing* — one can `|==>`-allocate a ghost
heap interpreting `σ` together with a `wp` proof of a pure `φ` (the shape
`heap_init` plus a closed `wp` produce), and the program runs fork-free to a value
`v`, then `φ v` holds. No iProp hypotheses remain — a fully self-contained
meta-level guarantee. The step count is fixed by the run, so it is uniform under
the existential over the freshly-allocated ghost name. -/
theorem wp_adequacy_closed {e : Expr} {σ : Heap} {v : Val} {σ' : Heap}
    {φ : Val → Prop} (hrun : primSteps e σ (.val v) σ')
    (h : (iprop(True) : IProp GF) ⊢
      iprop(|==> ∃ γ : GName,
        stateInterp γ σ ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝)))) : φ v := by
  obtain ⟨n, hn⟩ := primStepsN_of_primSteps hrun
  refine sfupdN_pure_soundness n (h.trans ((BIUpdate.mono ?_).trans (sfupdN_bupd_absorb n _)))
  iintro ⟨%γ, Hpre⟩
  -- per ghost name: preservation to the final value, then the payload collapses
  have bpe : (iprop(|==> ⌜φ v⌝) : IProp GF) ⊢ iprop(⌜φ v⌝) :=
    (BIUpdate.mono plainly_pure.mpr).trans BIBUpdatePlainly.bupd_plainly
  have hpayload :
      iprop(stateInterp γ σ' ∗ wp (F := F) γ (.val v) (fun w => iprop(⌜φ w⌝))) ⊢
        iprop(⌜φ v⌝) := by
    iintro ⟨_, H⟩
    iapply ((wp_value_inv γ v (fun w => iprop(⌜φ w⌝))).trans bpe)
    iexact H
  iapply ((wp_primStepsN_pres γ (fun w => iprop(⌜φ w⌝)) hn).trans (sfupdN_mono n hpayload))
  iexact Hpre

end LeanliftIris.PhaseA
