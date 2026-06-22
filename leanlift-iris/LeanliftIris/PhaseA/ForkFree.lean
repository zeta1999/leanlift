/-
Phase A2 — adequacy over the *real* thread-pool `steps`, for fork-free programs.

Sequential adequacy (`Adequacy.lean`) runs over the bespoke fork-free `primSteps`,
and `primSteps_imp_steps` shows that relation embeds into the genuine thread-pool
`steps`. This file proves the converse for **fork-free** programs: a `steps` run of
a singleton pool whose expression contains no `fork` stays a singleton and *is* a
`primSteps` run — so adequacy holds over the actual operational semantics, not just
the restricted relation. Sorry-free.

The reduction-closure argument needs a fork-free *heap* invariant (`load` reads
heap values, so they must be fork-free too); it holds initially (empty heap) and is
preserved because a fork-free program only ever stores fork-free values.
-/
import LeanliftIris.PhaseA.Adequacy

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE

/-! ## Fork-freedom of values, expressions, frames, and heaps -/

mutual
/-- A value contains no `fork` (recursively, through closure bodies and pairs). -/
def forkFreeV : Val → Prop
  | .unit | .bool _ | .int _ | .loc _ => True
  | .pair a b => forkFreeV a ∧ forkFreeV b
  | .clos _ _ body => forkFreeE body
/-- An expression contains no `fork` subexpression. -/
def forkFreeE : Expr → Prop
  | .val v => forkFreeV v
  | .var _ => True
  | .app a b => forkFreeE a ∧ forkFreeE b
  | .binop _ a b => forkFreeE a ∧ forkFreeE b
  | .ite a b c => forkFreeE a ∧ forkFreeE b ∧ forkFreeE c
  | .pairE a b => forkFreeE a ∧ forkFreeE b
  | .fstE a => forkFreeE a
  | .sndE a => forkFreeE a
  | .alloc a => forkFreeE a
  | .load a => forkFreeE a
  | .store a b => forkFreeE a ∧ forkFreeE b
  | .cas a b c => forkFreeE a ∧ forkFreeE b ∧ forkFreeE c
  | .faa a b => forkFreeE a ∧ forkFreeE b
  | .fork _ => False
end

/-- A heap is fork-free when every stored value is. -/
def forkFreeHeap (σ : Heap) : Prop := ∀ l v, σ l = some v → forkFreeV v

/-! ## Substitution preserves fork-freedom -/

mutual
theorem forkFreeV_substV (x : String) (w : Val) (v : Val)
    (hv : forkFreeV v) (hw : forkFreeV w) : forkFreeV (substV x w v) := by
  cases v with
  | unit => trivial
  | bool => trivial
  | int => trivial
  | loc => trivial
  | pair a b =>
      exact ⟨forkFreeV_substV x w a hv.1 hw, forkFreeV_substV x w b hv.2 hw⟩
  | clos f y body =>
      simp only [substV]
      split
      · exact hv
      · exact forkFreeE_substE x w body hv hw
termination_by sizeOf v
theorem forkFreeE_substE (x : String) (w : Val) (e : Expr)
    (he : forkFreeE e) (hw : forkFreeV w) : forkFreeE (substE x w e) := by
  cases e with
  | val v => exact forkFreeV_substV x w v he hw
  | var y => simp only [substE]; split <;> trivial
  | app a b => exact ⟨forkFreeE_substE x w a he.1 hw, forkFreeE_substE x w b he.2 hw⟩
  | binop op a b => exact ⟨forkFreeE_substE x w a he.1 hw, forkFreeE_substE x w b he.2 hw⟩
  | ite a b c =>
      exact ⟨forkFreeE_substE x w a he.1 hw,
        forkFreeE_substE x w b he.2.1 hw, forkFreeE_substE x w c he.2.2 hw⟩
  | pairE a b => exact ⟨forkFreeE_substE x w a he.1 hw, forkFreeE_substE x w b he.2 hw⟩
  | fstE a => exact forkFreeE_substE x w a he hw
  | sndE a => exact forkFreeE_substE x w a he hw
  | alloc a => exact forkFreeE_substE x w a he hw
  | load a => exact forkFreeE_substE x w a he hw
  | store a b => exact ⟨forkFreeE_substE x w a he.1 hw, forkFreeE_substE x w b he.2 hw⟩
  | cas a b c =>
      exact ⟨forkFreeE_substE x w a he.1 hw,
        forkFreeE_substE x w b he.2.1 hw, forkFreeE_substE x w c he.2.2 hw⟩
  | faa a b => exact ⟨forkFreeE_substE x w a he.1 hw, forkFreeE_substE x w b he.2 hw⟩
  | fork e => exact absurd he id
termination_by sizeOf e
end

/-! ## Fork-freedom of evaluation contexts -/

/-- A frame is fork-free when its non-hole components are. -/
def forkFreeFrame : Frame → Prop
  | .appL e2 => forkFreeE e2
  | .appR v1 => forkFreeV v1
  | .binopL _ e2 => forkFreeE e2
  | .binopR _ v1 => forkFreeV v1
  | .iteC e1 e2 => forkFreeE e1 ∧ forkFreeE e2
  | .pairL e2 => forkFreeE e2
  | .pairR v1 => forkFreeV v1
  | .fstF | .sndF | .allocF | .loadF => True
  | .storeL e2 => forkFreeE e2
  | .storeR v1 => forkFreeV v1
  | .casL e1 e2 => forkFreeE e1 ∧ forkFreeE e2
  | .casM v0 e2 => forkFreeV v0 ∧ forkFreeE e2
  | .casR v0 v1 => forkFreeV v0 ∧ forkFreeV v1
  | .faaL e2 => forkFreeE e2
  | .faaR v1 => forkFreeV v1

/-- Plugging into a frame is fork-free iff the hole and the frame both are. -/
theorem forkFreeE_fill1 (fr : Frame) (e : Expr) :
    forkFreeE (fill1 fr e) ↔ (forkFreeE e ∧ forkFreeFrame fr) := by
  cases fr <;>
    simp only [fill1, forkFreeE, forkFreeFrame, true_and, and_comm, and_assoc, and_left_comm]

/-- Plugging into a nested context is fork-free iff the hole and every frame are. -/
theorem forkFreeE_fill (K : List Frame) (a : Expr) :
    forkFreeE (fill K a) ↔ (forkFreeE a ∧ ∀ fr ∈ K, forkFreeFrame fr) := by
  induction K with
  | nil => simp [fill]
  | cons fr K ih =>
      simp only [fill, List.foldr_cons]
      rw [show K.foldr fill1 a = fill K a from rfl, forkFreeE_fill1, ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨hp, hq⟩, hr⟩; exact ⟨hp, hr, hq⟩
      · rintro ⟨hp, hr, hq⟩; exact ⟨⟨hp, hq⟩, hr⟩

/-- The hole of a fork-free context is fork-free. -/
theorem forkFreeE_fill_hole {K : List Frame} {a : Expr} (h : forkFreeE (fill K a)) :
    forkFreeE a := ((forkFreeE_fill K a).mp h).1

/-- Replacing the hole of a fork-free context with a fork-free expression keeps it
fork-free. -/
theorem forkFreeE_fill_cong {K : List Frame} {a a' : Expr} (h : forkFreeE (fill K a))
    (h' : forkFreeE a') : forkFreeE (fill K a') :=
  (forkFreeE_fill K a').mpr ⟨h', ((forkFreeE_fill K a).mp h).2⟩

/-! ## Reduction preserves fork-freedom -/

/-- Updating a fork-free heap with a fork-free value keeps it fork-free. -/
theorem forkFreeHeap_set {σ : Heap} {l : Nat} {v : Val} (hσ : forkFreeHeap σ)
    (hv : forkFreeV v) : forkFreeHeap (σ.set l v) := by
  intro k w hk
  simp only [Heap.set] at hk
  split at hk
  · cases hk; exact hv
  · exact hσ k w hk

/-- The result of `evalBinop` (an integer or boolean) is fork-free. -/
theorem forkFreeV_evalBinop {op : BinOp} {a b v : Val} (h : evalBinop op a b = some v) :
    forkFreeV v := by
  unfold evalBinop at h
  split at h <;>
    first
      | (injection h with h'; subst h'; trivial)
      | cases h

/-- **Head reduction preserves fork-freedom** (given a fork-free heap), produces a
fork-free heap, and forks nothing. The `fork` redex is excluded since it is not
fork-free. -/
theorem head_preserves_forkFree {a : Expr} {σ : Heap} {a' : Expr} {σ' : Heap}
    {efs : List Expr} (hσ : forkFreeHeap σ) (ha : forkFreeE a)
    (h : Head a σ a' σ' efs) : forkFreeE a' ∧ forkFreeHeap σ' ∧ efs = [] := by
  cases h with
  | @beta f x body w _ =>
      simp only [forkFreeE, forkFreeV] at ha
      refine ⟨?_, hσ, rfl⟩
      exact forkFreeE_substE x w _
        (forkFreeE_substE f (.clos f x body) body ha.1 ha.1) ha.2
  | iteT => exact ⟨ha.2.1, hσ, rfl⟩
  | iteF => exact ⟨ha.2.2, hσ, rfl⟩
  | binop h => exact ⟨forkFreeV_evalBinop h, hσ, rfl⟩
  | pair => exact ⟨ha, hσ, rfl⟩
  | fst => exact ⟨ha.1, hσ, rfl⟩
  | snd => exact ⟨ha.2, hσ, rfl⟩
  | alloc => exact ⟨trivial, forkFreeHeap_set hσ ha, rfl⟩
  | load h => exact ⟨hσ _ _ h, hσ, rfl⟩
  | store h => exact ⟨trivial, forkFreeHeap_set hσ ha.2, rfl⟩
  | casS h he => exact ⟨trivial, forkFreeHeap_set hσ ha.2.2, rfl⟩
  | casF h hne => exact ⟨trivial, hσ, rfl⟩
  | faa h => exact ⟨trivial, forkFreeHeap_set hσ trivial, rfl⟩
  | fork => exact absurd ha id

/-- **Primitive reduction preserves fork-freedom** (given a fork-free heap),
produces a fork-free heap, and forks nothing. -/
theorem prim_step_preserves_forkFree {e : Expr} {σ : Heap} {e' : Expr} {σ' : Heap}
    {efs : List Expr} (hσ : forkFreeHeap σ) (he : forkFreeE e)
    (h : prim_step e σ e' σ' efs) : forkFreeE e' ∧ forkFreeHeap σ' ∧ efs = [] := by
  obtain ⟨K, a, a', hK, hK', hHead⟩ := h
  subst hK; subst hK'
  obtain ⟨ha', hσ', hefs⟩ := head_preserves_forkFree hσ (forkFreeE_fill_hole he) hHead
  exact ⟨forkFreeE_fill_cong he ha', hσ', hefs⟩

/-! ## A fork-free singleton pool stays a singleton; its `steps` run is a `primSteps` -/

/-- One scheduling step of a fork-free singleton pool stays a singleton, and its
step is a fork-free primitive step. -/
theorem step_singleton_forkFree {e : Expr} {σ : Heap} {c' : Cfg}
    (hσ : forkFreeHeap σ) (he : forkFreeE e) (h : step ⟨[e], σ⟩ c') :
    ∃ e', c' = ⟨[e'], c'.heap⟩ ∧ forkFreeE e' ∧ forkFreeHeap c'.heap ∧
      prim_step e σ e' c'.heap [] := by
  obtain ⟨tpc, hpc⟩ := c'
  obtain ⟨t1, t2, ee, ee', efs, htp, hstep, htp'⟩ := h
  -- [e] = t1 ++ ee :: t2 forces t1 = t2 = [] and ee = e
  cases t1 with
  | cons _ _ => simp at htp
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at htp
      obtain ⟨hee, ht2⟩ := htp
      subst hee; subst ht2
      obtain ⟨he', hσ', hefs⟩ := prim_step_preserves_forkFree hσ he hstep
      subst hefs
      simp only [List.nil_append, List.append_nil] at htp'
      subst htp'
      exact ⟨ee', rfl, he', hσ', hstep⟩

/-- **A fork-free singleton run is a `primSteps` run.** A thread-pool `steps` run
of a singleton pool of a fork-free expression over a fork-free heap stays a
singleton pool and corresponds to a `primSteps` run. -/
theorem steps_singleton_forkFree {e : Expr} {σ : Heap} (hσ : forkFreeHeap σ)
    (he : forkFreeE e) : ∀ {c : Cfg}, steps ⟨[e], σ⟩ c →
      ∃ e', c.tp = [e'] ∧ forkFreeE e' ∧ forkFreeHeap c.heap ∧ primSteps e σ e' c.heap := by
  intro c h
  induction h with
  | refl => exact ⟨e, rfl, he, hσ, primSteps.refl⟩
  | @tail c' c'' _hsteps hstep ih =>
      obtain ⟨em, hcm, hem, hσm, hrun⟩ := ih
      have hc'eq : c' = ⟨[em], c'.heap⟩ := by rw [← hcm]
      obtain ⟨e', hc'', he', hσ', hstep'⟩ :=
        step_singleton_forkFree hσm hem (hc'eq ▸ hstep)
      exact ⟨e', by rw [hc''], he', hσ', hrun.tail hstep'⟩

/-- **Adequacy over the real thread-pool `steps`** (fork-free programs). For a
fork-free `e`, a genuine thread-pool run from the empty heap that reaches a value
`v` (with a singleton pool — guaranteed since `e` cannot fork) makes `φ v` hold:
the spec constrains the *actual* operational semantics, not the bespoke
`primSteps`. -/
theorem wp_adequacy_steps {F} [UFraction F] {GF} (γ : GName) [HasHeap γ GF F]
    (e : Expr) (v : Val) (σ' : Heap) (φ : Val → Prop)
    (hff : forkFreeE e) (hrun : steps ⟨[e], emptyHeap⟩ ⟨[.val v], σ'⟩)
    (h : (iprop(True) : IProp GF) ⊢
      iprop(stateInterp γ emptyHeap ∗ wp (F := F) γ e (fun w => iprop(⌜φ w⌝)))) : φ v := by
  have hemp : forkFreeHeap emptyHeap := by intro l w hw; simp [emptyHeap] at hw
  obtain ⟨e', htp, _, _, hps⟩ := steps_singleton_forkFree hemp hff hrun
  -- htp : [.val v] = [e'] ⇒ e' = .val v
  have : e' = .val v := by simpa using htp.symm
  subst this
  exact wp_adequacy_seq γ e emptyHeap v σ' φ hps h
