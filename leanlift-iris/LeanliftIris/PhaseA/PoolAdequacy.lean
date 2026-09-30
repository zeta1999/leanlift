/-
Phase A2 — **concurrent thread-pool adequacy** for the `λ-conc` weakest precondition.

`Adequacy.lean` proves adequacy over the fork-free `primSteps`, and `ForkFree.lean`
lifts that to the real `steps` for programs that cannot fork. This file proves the
fully general theorem: a `wp` proof of a pure postcondition for the *primary*
thread, plus a genuine thread-pool `steps` run (any interleaving, any number of
forked threads) that brings the primary thread to a value, yields the meta-level
fact. The primary thread is the head of the pool: `step` splices the stepped
thread back in place and appends forks at the end, so position 0 is stable.

The argument is the standard Iris one. The pool interpretation
`tpInterp γ Φ (e :: rest) = wp e Φ ∗ forkObl (wp γ) rest` is preserved by every
scheduling step modulo `|==> ▷ |==>` (`tp_step_pres`): stepping the primary thread
is `wp_step_pres`, whose fork obligation is appended to `rest`; stepping a forked
thread is the same lemma at the trivial postcondition inside `forkObl`. The tower
`sfupdN` then collapses exactly as in the sequential case. This is what the
forked-thread obligation in `wpF` buys: without it a forked thread could mutate
the heap with no `wp` to account for it and preservation would fail.

**Safety.** `wpF` carries the progress (`reducible`) conjunct under the pure
free-space invariant `Heap.infFree` (Lang.lean), which every run preserves. So
besides the result theorems (`wp_adequacy_pool*`, partial correctness of the
primary thread) this file proves **`wp_adequacy_safe`**: in every configuration
reachable from a verified program, every thread is a value or can step — no thread
is ever stuck. The `wp` hypotheses are stated under `|==>`: the authoritative heap
is ghost state that can only be allocated (`heap_init`), so `True ⊢ stateInterp ∗ …`
without the update would be unsatisfiable and the theorem vacuous. Both headline
theorems are instantiated on a worked forking program (`forkThenFst_result`,
`forkThenFst_safe`), so neither is a consumer-less statement. Sorry-free.
-/
import LeanliftIris.PhaseA.Adequacy

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-! ## `forkObl` over pool surgery -/

/-- `forkObl` over append (the direction pool re-assembly needs). -/
theorem forkObl_app (wp : Expr → (Val → IProp GF) → IProp GF) (l1 l2 : List Expr) :
    forkObl wp l1 ∗ forkObl wp l2 ⊢ forkObl wp (l1 ++ l2) := by
  induction l1 with
  | nil => exact emp_sep.mp
  | cons a l1 ih => exact sep_assoc.mp.trans (sep_mono_r ih)

/-- Splitting the obligation at a chosen thread. -/
theorem forkObl_split (wp : Expr → (Val → IProp GF) → IProp GF) (t1 t2 : List Expr)
    (e : Expr) :
    forkObl wp (t1 ++ e :: t2) ⊢
      forkObl wp t1 ∗ wp e (fun _ => iprop(True)) ∗ forkObl wp t2 := by
  induction t1 with
  | nil => exact emp_sep.mpr
  | cons a t1 ih => exact (sep_mono_r ih).trans sep_assoc.mpr

/-- Re-joining after the chosen thread stepped to `e'` and forked `efs`. Note
`t1 ++ e' :: t2 ++ efs` parses as `t1 ++ (e' :: (t2 ++ efs))`, the shape `step`
produces. -/
theorem forkObl_join (wp : Expr → (Val → IProp GF) → IProp GF) (t1 t2 efs : List Expr)
    (e' : Expr) :
    forkObl wp t1 ∗ wp e' (fun _ => iprop(True)) ∗ forkObl wp t2 ∗ forkObl wp efs ⊢
      forkObl wp (t1 ++ e' :: t2 ++ efs) := by
  induction t1 with
  | nil => exact emp_sep.mp.trans (sep_mono_r (forkObl_app wp t2 efs))
  | cons a t1 ih => exact sep_assoc.mp.trans (sep_mono_r ih)

/-! ## Head stability

The primary thread is the head of the pool, and `step` keeps it there: a step either
reduces the head itself or leaves it untouched (a non-primary thread stepped; forks
are appended at the end). This is the checked form of the "position 0 is stable"
claim the pool interpretation relies on. -/

/-- One scheduling step of a pool with head `e` yields a pool whose head is either
`e` unchanged or a primitive successor of `e`. -/
theorem step_head {e : Expr} {rest : List Expr} {σ : Heap} {c' : Cfg}
    (h : step ⟨e :: rest, σ⟩ c') :
    ∃ e' rest', c'.tp = e' :: rest' ∧ (e' = e ∨ ∃ efs, prim_step e σ e' c'.heap efs) := by
  obtain ⟨t1, t2, ee, ee', efs, htp, hstep, htp'⟩ := h
  cases t1 with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at htp
      obtain ⟨hee, _⟩ := htp
      subst hee
      exact ⟨ee', t2 ++ efs, by rw [htp']; rfl, Or.inr ⟨efs, hstep⟩⟩
  | cons e0 t1 =>
      simp only [List.cons_append, List.cons.injEq] at htp
      obtain ⟨he0, _⟩ := htp
      exact ⟨e0, t1 ++ ee' :: t2 ++ efs, by rw [htp']; rfl, Or.inl he0.symm⟩

/-! ## The thread-pool interpretation and its preservation -/

/-- The pool interpretation: the primary thread (head) against `Φ`, every other
thread against the trivial postcondition. -/
def tpInterp (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF) : List Expr → IProp GF
  | [] => iprop(emp)
  | e :: rest => iprop(wp (F := F) γ e Φ ∗ forkObl (wp (F := F) γ) rest)

@[simp] theorem tpInterp_cons (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF)
    (e : Expr) (rest : List Expr) :
    tpInterp (F := F) γ Φ (e :: rest) =
      iprop(wp (F := F) γ e Φ ∗ forkObl (wp (F := F) γ) rest) := rfl

/-- Pool preservation, primary-thread case: the head stepped, its forks go to the
end of the pool. -/
theorem tp_step_pres_head (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF)
    {σ σ' : Heap} {e e' : Expr} {t2 efs : List Expr} (hinf : Heap.infFree σ)
    (hstep : prim_step e σ e' σ' efs) :
    stateInterp γ σ ∗ (wp (F := F) γ e Φ ∗ forkObl (wp (F := F) γ) t2) ⊢
      |==> ▷ |==> (stateInterp γ σ' ∗
        (wp (F := F) γ e' Φ ∗ forkObl (wp (F := F) γ) (t2 ++ efs))) := by
  have hnv : toVal e = none := toVal_none_of_prim_step hstep
  iintro ⟨Hsi, Hwp, Hrest⟩
  ihave H := (wp_step_pres γ e σ e' σ' efs Φ hnv hinf hstep) $$ [Hsi, Hwp]
  · isplitl [Hsi]
    · iexact Hsi
    · iexact Hwp
  imod H with H
  iintro !>
  iintro !>
  imod H with ⟨Hsi', Hwe', Hefs⟩
  iintro !>
  isplitl [Hsi']
  · iexact Hsi'
  isplitl [Hwe']
  · iexact Hwe'
  · iapply forkObl_app
    isplitl [Hrest]
    · iexact Hrest
    · iexact Hefs

/-- Pool preservation, forked-thread case: some non-primary thread stepped; the
primary thread is untouched. -/
theorem tp_step_pres_tail (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF)
    {σ σ' : Heap} {e0 e e' : Expr} {t1 t2 efs : List Expr} (hinf : Heap.infFree σ)
    (hstep : prim_step e σ e' σ' efs) :
    stateInterp γ σ ∗ (wp (F := F) γ e0 Φ ∗ forkObl (wp (F := F) γ) (t1 ++ e :: t2)) ⊢
      |==> ▷ |==> (stateInterp γ σ' ∗
        (wp (F := F) γ e0 Φ ∗ forkObl (wp (F := F) γ) (t1 ++ e' :: t2 ++ efs))) := by
  have hnv : toVal e = none := toVal_none_of_prim_step hstep
  iintro ⟨Hsi, Hwp0, Hrest⟩
  ihave ⟨H1, He, H2⟩ := (forkObl_split (wp (F := F) γ) t1 t2 e) $$ [Hrest]
  · iexact Hrest
  ihave H := (wp_step_pres γ e σ e' σ' efs (fun _ => iprop(True)) hnv hinf hstep)
    $$ [Hsi, He]
  · isplitl [Hsi]
    · iexact Hsi
    · iexact He
  imod H with H
  iintro !>
  iintro !>
  imod H with ⟨Hsi', Hwe', Hefs⟩
  iintro !>
  isplitl [Hsi']
  · iexact Hsi'
  isplitl [Hwp0]
  · iexact Hwp0
  · iapply forkObl_join
    isplitl [H1]
    · iexact H1
    isplitl [Hwe']
    · iexact Hwe'
    isplitl [H2]
    · iexact H2
    · iexact Hefs

/-- **Pool preservation.** One scheduling step of the thread pool preserves the
state interpretation and the pool interpretation, modulo `|==> ▷ |==>`. -/
theorem tp_step_pres (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF) {c c' : Cfg}
    (hinf : Heap.infFree c.heap) (h : step c c') :
    stateInterp γ c.heap ∗ tpInterp (F := F) γ Φ c.tp ⊢
      |==> ▷ |==> (stateInterp γ c'.heap ∗ tpInterp (F := F) γ Φ c'.tp) := by
  obtain ⟨t1, t2, e, e', efs, htp, hstep, htp'⟩ := h
  rw [htp, htp']
  cases t1 with
  | nil => exact tp_step_pres_head γ Φ hinf hstep
  | cons e0 t1 => exact tp_step_pres_tail γ Φ hinf hstep

/-! ## Multi-step preservation over the real `steps` -/

/-- A length-indexed thread-pool run (uniform step count under a later `∃ γ`). -/
inductive stepsN : Nat → Cfg → Cfg → Prop where
  | refl {c} : stepsN 0 c c
  | tail {n c c' c''} : stepsN n c c' → step c' c'' → stepsN (n + 1) c c''

/-- Length-indexed runs preserve unbounded free space. -/
theorem stepsN_preserves_infFree {n : Nat} {c c' : Cfg} (h : stepsN n c c')
    (hinf : Heap.infFree c.heap) : Heap.infFree c'.heap := by
  induction h with
  | refl => exact hinf
  | tail _ hstep ih => exact step_preserves_infFree hstep (ih hinf)

/-- Every `steps` run has some explicit length. -/
theorem stepsN_of_steps {c c' : Cfg} (h : steps c c') : ∃ n, stepsN n c c' := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | tail _ hstep ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, hn.tail hstep⟩

/-- **Pool multi-step preservation.** An `n`-step pool run carries
`stateInterp ∗ tpInterp` to the end configuration under an `n`-tall tower. -/
theorem tp_stepsN_pres (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF)
    {n : Nat} {c c' : Cfg} (h : stepsN n c c') (hinf : Heap.infFree c.heap) :
    stateInterp γ c.heap ∗ tpInterp (F := F) γ Φ c.tp ⊢
      sfupdN n iprop(stateInterp γ c'.heap ∗ tpInterp (F := F) γ Φ c'.tp) := by
  induction h with
  | refl => exact BIUpdate.intro
  | @tail n c c1 c2 hsteps hstep ih =>
      have hone :
          iprop(stateInterp γ c1.heap ∗ tpInterp (F := F) γ Φ c1.tp) ⊢
            sfupdN 1 iprop(stateInterp γ c2.heap ∗ tpInterp (F := F) γ Φ c2.tp) :=
        tp_step_pres γ Φ (stepsN_preserves_infFree hsteps hinf) hstep
      exact (ih hinf).trans ((sfupdN_mono n hone).trans (sfupdN_compose n 1 _))

/-! ## Concurrent adequacy — the general theorem -/

/-- The end payload: once the primary thread is a value, the pool interpretation
yields the pure postcondition (the other threads and the heap are dropped). -/
theorem tpInterp_val_pure (γ : GName) [HasHeap γ GF F] (v : Val) (σ' : Heap)
    (tp' : List Expr) (φ : Val → Prop) :
    iprop(stateInterp γ σ' ∗ tpInterp (F := F) γ (fun w => iprop(⌜φ w⌝)) (.val v :: tp')) ⊢
      (iprop(⌜φ v⌝) : IProp GF) := by
  have bpe : (iprop(|==> ⌜φ v⌝) : IProp GF) ⊢ iprop(⌜φ v⌝) :=
    (BIUpdate.mono plainly_pure.mpr).trans BIBUpdatePlainly.bupd_plainly
  simp only [tpInterp_cons]
  iintro ⟨_, H, _⟩
  iapply ((wp_value_inv γ v (fun w => iprop(⌜φ w⌝))).trans bpe)
  iexact H

/-- **Concurrent adequacy.** If `stateInterp γ σ ∗ wp γ e ⌜φ⌝` is obtainable
under an update, and the thread pool `[e]` runs — under any interleaving, forking
freely — to a configuration whose primary thread is the value `v`, then `φ v`
holds at the meta level. Subsumes `wp_adequacy_seq`/`wp_adequacy_steps`: no
fork-freedom is assumed. Partial correctness (see the file header). -/
theorem wp_adequacy_pool (γ : GName) [HasHeap γ GF F] (e : Expr) (σ : Heap)
    (v : Val) (σ' : Heap) (tp' : List Expr) (φ : Val → Prop) (hinf : Heap.infFree σ)
    (hrun : steps ⟨[e], σ⟩ ⟨.val v :: tp', σ'⟩)
    (h : (iprop(True) : IProp GF) ⊢
      iprop(|==> (stateInterp γ σ ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝))))) : φ v := by
  obtain ⟨n, hn⟩ := stepsN_of_steps hrun
  have hinit :
      iprop(stateInterp γ σ ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝))) ⊢
        iprop(stateInterp γ σ ∗ tpInterp (F := F) γ (fun w => iprop(⌜φ w⌝)) [e]) := by
    simp only [tpInterp_cons, forkObl_nil]
    exact sep_mono_r sep_emp.mpr
  exact sfupdN_pure_soundness n
    (h.trans ((BIUpdate.mono (hinit.trans ((tp_stepsN_pres γ _ hn hinf).trans
      (sfupdN_mono n (tpInterp_val_pure γ v σ' tp' φ))))).trans (sfupdN_bupd_absorb n _)))

/-- **Closed concurrent adequacy.** As `wp_adequacy_closed`, but over the real
thread-pool semantics with forking: from nothing, allocate the ghost heap and a
`wp` proof; any pool run bringing the primary thread to `v` gives `φ v`. -/
theorem wp_adequacy_pool_closed {e : Expr} {σ : Heap} {v : Val} {σ' : Heap}
    {tp' : List Expr} {φ : Val → Prop} (hinf : Heap.infFree σ)
    (hrun : steps ⟨[e], σ⟩ ⟨.val v :: tp', σ'⟩)
    (h : (iprop(True) : IProp GF) ⊢
      iprop(|==> ∃ γ : GName,
        stateInterp γ σ ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝)))) : φ v := by
  obtain ⟨n, hn⟩ := stepsN_of_steps hrun
  refine sfupdN_pure_soundness n (h.trans ((BIUpdate.mono ?_).trans (sfupdN_bupd_absorb n _)))
  iintro ⟨%γ, Hpre⟩
  have hinit :
      iprop(stateInterp γ σ ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝))) ⊢
        iprop(stateInterp γ σ ∗ tpInterp (F := F) γ (fun w => iprop(⌜φ w⌝)) [e]) := by
    simp only [tpInterp_cons, forkObl_nil]
    exact sep_mono_r sep_emp.mpr
  iapply (hinit.trans ((tp_stepsN_pres γ _ hn hinf).trans
    (sfupdN_mono n (tpInterp_val_pure γ v σ' tp' φ))))
  iexact Hpre

/-! ## Safety — no reachable thread is stuck -/

/-- The pool interpretation exposes a `wp` (at some postcondition) for every thread. -/
theorem tpInterp_thread (γ : GName) [HasHeap γ GF F] (Φ : Val → IProp GF)
    (t1 t2 : List Expr) (t : Expr) :
    tpInterp (F := F) γ Φ (t1 ++ t :: t2) ⊢ ∃ Ψ, wp (F := F) γ t Ψ := by
  cases t1 with
  | nil =>
      simp only [List.nil_append, tpInterp_cons]
      iintro ⟨H, _⟩
      iexists Φ
      iexact H
  | cons e0 t1 =>
      simp only [List.cons_append, tpInterp_cons]
      iintro ⟨_, H⟩
      ihave ⟨_, Ht, _⟩ := (forkObl_split (wp (F := F) γ) t1 t2 t) $$ [H]
      · iexact H
      iexists (fun _ => iprop(True))
      iexact Ht

/-- **Safety.** In every configuration reachable from a verified program (any
interleaving, any forks), every thread is either a value or can take a step: no
thread is ever stuck. The `wp` hypothesis is the closed form (`heap_init` +
`wp`), as in `wp_adequacy_pool_closed`. -/
theorem wp_adequacy_safe {e : Expr} {σ : Heap} {φ : Val → Prop} (hinf : Heap.infFree σ)
    {c : Cfg} (hrun : steps ⟨[e], σ⟩ c)
    (h : (iprop(True) : IProp GF) ⊢
      iprop(|==> ∃ γ : GName,
        stateInterp γ σ ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝)))) :
    ∀ t ∈ c.tp, toVal t ≠ none ∨ reducible t c.heap := by
  intro t ht
  by_cases hnv : toVal t = none
  · right
    obtain ⟨t1, t2, htp⟩ := List.append_of_mem ht
    obtain ⟨n, hn⟩ := stepsN_of_steps hrun
    have hinf' : Heap.infFree c.heap := stepsN_preserves_infFree hn hinf
    refine sfupdN_pure_soundness (n + 0)
      (h.trans ((BIUpdate.mono ?_).trans (sfupdN_bupd_absorb (n + 0) _)))
    iintro ⟨%γ, Hpre⟩
    have hinit :
        iprop(stateInterp γ σ ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝))) ⊢
          iprop(stateInterp γ σ ∗ tpInterp (F := F) γ (fun w => iprop(⌜φ w⌝)) [e]) := by
      simp only [tpInterp_cons, forkObl_nil]
      exact sep_mono_r sep_emp.mpr
    -- at the end of the run: the thread's wp + the state interp give reducibility
    have hend :
        iprop(stateInterp γ c.heap ∗ tpInterp (F := F) γ (fun w => iprop(⌜φ w⌝)) c.tp) ⊢
          iprop(|==> ⌜reducible t c.heap⌝) := by
      rw [htp]
      iintro ⟨Hsi, Htp⟩
      ihave ⟨%Ψ, Hwp⟩ := (tpInterp_thread γ _ t1 t2 t) $$ [Htp]
      · iexact Htp
      iapply (wp_reducible γ t c.heap Ψ hnv hinf')
      isplitl [Hsi]
      · iexact Hsi
      · iexact Hwp
    iapply (hinit.trans ((tp_stepsN_pres γ _ hn hinf).trans
      ((sfupdN_mono n hend).trans (sfupdN_compose n 0 _))))
    iexact Hpre
  · left; exact hnv

/-! ### Worked example: a program that forks

`let _ = fork unit in fst (3, 4)` is *not* fork-free, so `wp_adequacy_steps` cannot
say anything about it. Concurrent adequacy delivers a closed operational fact: in
**every** thread-pool run (any interleaving of the spawned thread), if the primary
thread reaches a value, that value is `3`. -/

/-- `let _ = fork unit in fst (3, 4)`. -/
def forkThenFst : Expr :=
  .app (.val (.clos "_" "_" (.fstE (.val (.pair (.int 3) (.int 4)))))) (.fork (.val .unit))

/-- Its `wp`: `wp_seq` sequences, `wp_fork` verifies the spawned thread against
`True`, `wp_fst` computes the projection. -/
theorem forkThenFst_wp (γ : GName) [HasHeap γ GF F] :
    ⊢ wp (F := F) γ forkThenFst (fun w => (iprop(⌜w = .int 3⌝) : IProp GF)) := by
  unfold forkThenFst
  iapply (wp_seq γ (.fork (.val .unit)) (.fstE (.val (.pair (.int 3) (.int 4)))) _
    (fun _ => rfl))
  iapply wp_fork
  isplitl []
  · iintro !>
    iapply wp_value
    iintro !>
    ipure_intro; trivial
  · iintro !>
    iintro !>
    iintro !>
    iapply wp_fst
    iintro !>
    iapply wp_value
    iintro !>
    ipure_intro; rfl

/-- **Closed operational fact through a fork.** Every pool run of `forkThenFst`
whose primary thread terminates returns `3`, whatever the spawned thread did and
however the scheduler interleaved it. Obtained from `heap_init` + `forkThenFst_wp`
via `wp_adequacy_pool_closed`, with no fork-freedom side condition. The ghost name
is allocated fresh inside; only the functor setup is assumed. -/
theorem forkThenFst_result {GF₀ : BundledGFunctors.{0, 0, 0}} [ElemG GF₀ (FHeap (F := F))]
    (σ : Heap) (hinf : Heap.infFree σ) (v : Val) (σ' : Heap) (tp' : List Expr)
    (hrun : steps ⟨[forkThenFst], σ⟩ ⟨.val v :: tp', σ'⟩) : v = .int 3 := by
  have hte : (iprop(True) : IProp GF₀) ⊢ (emp : IProp GF₀) :=
    biaffine_iff_true_emp.1 inferInstance
  refine wp_adequacy_pool_closed (F := F) (GF := GF₀) (φ := fun w => w = .int 3) hinf hrun
    (hte.trans ((heap_init (F := F) (GF := GF₀) σ).trans (BIUpdate.mono ?_)))
  iintro ⟨%γ', Hsi⟩
  iexists γ'
  isplitl [Hsi]
  · iexact Hsi
  · exact forkThenFst_wp γ'

/-- **Closed safety fact through a fork.** From the empty heap, no thread of any
run of `forkThenFst` — the primary or the spawned one, under any scheduler — is
ever stuck. Instantiates `wp_adequacy_safe` with the same closed input as
`forkThenFst_result`. -/
theorem forkThenFst_safe {GF₀ : BundledGFunctors.{0, 0, 0}} [ElemG GF₀ (FHeap (F := F))]
    {c : Cfg} (hrun : steps ⟨[forkThenFst], emptyHeap⟩ c) :
    ∀ t ∈ c.tp, toVal t ≠ none ∨ reducible t c.heap := by
  have hte : (iprop(True) : IProp GF₀) ⊢ (emp : IProp GF₀) :=
    biaffine_iff_true_emp.1 inferInstance
  refine wp_adequacy_safe (F := F) (GF := GF₀) (φ := fun w => w = .int 3) emptyHeap_infFree
    hrun (hte.trans ((heap_init (F := F) (GF := GF₀) emptyHeap).trans (BIUpdate.mono ?_)))
  iintro ⟨%γ', Hsi⟩
  iexists γ'
  isplitl [Hsi]
  · iexact Hsi
  · exact forkThenFst_wp γ'

end LeanliftIris.PhaseA
