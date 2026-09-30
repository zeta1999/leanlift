/-
Phase C (step 7) — **erasure: from a real thread-pool run to an interleaving of
abstract traces**, so `linearizable_abstract` applies to executions of `λ-conc`
programs and not only to schedules of pre-computed effect lists.

`Linearize.lean` proves linearizability at the abstract state for an `Interleave`
of abstract traces. The real concurrent semantics is `Lang.step`/`steps` over a
thread pool. This file connects them, honestly: the connection is a theorem with
**two explicit per-program obligations**, not a free lunch.

  * `Trace c tr c'` — a real pool run annotated with, per scheduling step, the
    thread *position* that stepped, the expressions and the heaps before/after
    (`TStep`). Positions are stable across a run: `step` splices the stepped
    thread back in place and appends forks at the end. `Trace.steps`: a trace is
    a `steps` run; `steps_trace`: every `steps` run has a trace.
  * An erasure `er : TStep → Step σ` and an abstraction `abs : Heap → σ`.
    Obligation 1, **commutation** on the recorded steps: what each step did to the
    heap is what its abstract effect does to the abstract state.
  * **`trace_runSteps`** — under commutation, running the erased trace from the
    abstract initial heap lands exactly on the abstract final heap.
  * **`real_run_linearizes`** — add obligation 2, **trace shape**: the erased trace
    is an `Interleave` of a family's abstract traces. Then the abstract final heap
    is the result of the sequential history of LPs, with exactly one LP per
    operation and every LP its operation's commit — `linearizable_abstract`, now
    about a real run.

Obligation 2 is exactly where a CAS-retry loop fails: its steps are not a fixed
effect list, so no family of `AtomicOp`s has it as an interleaving. The theorem
turns that gap into a hypothesis to discharge per program, instead of prose.

  * **`two_incrs`** — the consumer, a real program: two threads each executing
    `FAA(c, 1)` on the `λ-conc` pool. **Every** real run from a heap with `c ↦ k`
    that finishes both threads ends with `c ↦ k + 2`: no lost update, under any
    interleaving. Both obligations are discharged from `prim_step_faa_inv` and the
    fact that each thread steps exactly once (`incr_inv`).

Sorry-free.
-/
import LeanliftIris.PhaseC.Linearize

namespace LeanliftIris.PhaseC
open LeanliftIris.PhaseA

/-! ## Annotated runs -/

/-- One recorded scheduling step: thread position `k` stepped from `e` at heap `σ`
to `e'` at heap `σ'`, forking `efs`. -/
structure TStep where
  k : Nat
  e : Expr
  σ : Heap
  e' : Expr
  σ' : Heap
  efs : List Expr

/-- `step`, with the stepped position and the step data exposed. -/
def stepAt (ts : TStep) (c c' : Cfg) : Prop :=
  ∃ t1 t2 : List Expr, c.tp = t1 ++ ts.e :: t2 ∧ t1.length = ts.k ∧ c.heap = ts.σ ∧
    prim_step ts.e ts.σ ts.e' ts.σ' ts.efs ∧ c'.heap = ts.σ' ∧ c'.tp = t1 ++ ts.e' :: t2 ++ ts.efs

/-- An annotated run: the list of recorded steps, oldest first. -/
inductive Trace : Cfg → List TStep → Cfg → Prop where
  | refl {c} : Trace c [] c
  | snoc {c tr c' ts c''} : Trace c tr c' → stepAt ts c' c'' → Trace c (tr ++ [ts]) c''

/-- A recorded step is a real scheduling step. -/
theorem stepAt.step {ts : TStep} {c c' : Cfg} (h : stepAt ts c c') : step c c' := by
  obtain ⟨t1, t2, htp, _, hσ, hprim, hσ', htp'⟩ := h
  refine ⟨t1, t2, ts.e, ts.e', ts.efs, htp, ?_, htp'⟩
  rw [hσ, hσ']; exact hprim

/-- An annotated run is a real run. -/
theorem Trace.steps {c : Cfg} {tr : List TStep} {c' : Cfg} (h : Trace c tr c') : steps c c' := by
  induction h with
  | refl => exact steps.refl
  | snoc _ hs ih => exact ih.tail hs.step

/-- Every real run has an annotation. -/
theorem steps_trace {c c' : Cfg} (h : steps c c') : ∃ tr, Trace c tr c' := by
  induction h with
  | refl => exact ⟨[], Trace.refl⟩
  | tail _ hs ih =>
      obtain ⟨tr, htr⟩ := ih
      obtain ⟨t1, t2, e, e', efs, htp, hprim, htp'⟩ := hs
      exact ⟨tr ++ [⟨t1.length, e, _, e', _, efs⟩],
        htr.snoc ⟨t1, t2, htp, rfl, rfl, hprim, rfl, htp'⟩⟩

/-! ## Erasure and commutation -/

/-- **Erasure runs the trace.** If every recorded step commutes with its erasure —
`abs σ' = (er ts).eff (abs σ)` — running the erased trace from the abstract initial
heap lands on the abstract final heap. -/
theorem trace_runSteps {σ : Type} (er : TStep → Step σ) (abs : Heap → σ)
    {c : Cfg} {tr : List TStep} {c' : Cfg} (h : Trace c tr c')
    (hcomm : ∀ ts ∈ tr, abs ts.σ' = (er ts).eff (abs ts.σ)) :
    runSteps (tr.map er) (abs c.heap) = abs c'.heap := by
  induction h with
  | refl => rfl
  | snoc _ hs ih =>
      obtain ⟨_, _, _, _, hσ, _, hσ', _⟩ := hs
      have ih' := ih (fun t ht => hcomm t (List.mem_append_left _ ht))
      have hts := hcomm _ (List.mem_append_right _ (List.mem_singleton_self _))
      simp only [List.map_append, List.map_cons, List.map_nil, runSteps, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      simp only [runSteps] at ih'
      rw [ih', hσ', hσ, hts]

/-- **A real run linearizes.** Given a commuting erasure (obligation 1) whose
erased trace is an interleaving of a family's abstract traces (obligation 2), the
abstract final heap is the result of the sequential history of LPs, the history
has exactly one LP per operation, and every LP is its operation's commit. -/
theorem real_run_linearizes {σ : Type} (er : TStep → Step σ) (abs : Heap → σ)
    (os : List (AtomicOp σ)) {c : Cfg} {tr : List TStep} {c' : Cfg} (h : Trace c tr c')
    (hcomm : ∀ ts ∈ tr, abs ts.σ' = (er ts).eff (abs ts.σ))
    (hshape : Interleave (stepsFrom 0 os) (tr.map er)) :
    abs c'.heap = runSteps (lps (tr.map er)) (abs c.heap) ∧
    ((lps (tr.map er)).map (·.op)).Perm (List.range' 0 os.length) ∧
    (∀ x ∈ lps (tr.map er), ∃ k, ∃ hk : k < os.length, x.op = k ∧ x.eff = os[k].t.commit) := by
  obtain ⟨heq, hperm, hcommit⟩ := linearizable_abstract os hshape
  exact ⟨by rw [← trace_runSteps er abs h hcomm, heq], hperm, hcommit⟩

/-! ## Consumer: two concurrent increments on the real pool -/

/-- `FAA(c, 1)`: the increment program. -/
def incr (c : Nat) : Expr := .faa (.val (.loc c)) (.val (.int 1))

/-- The counter's value, read off the heap (`0` if absent or not an integer). -/
def counter (c : Nat) (σ : Heap) : Int :=
  match σ c with
  | some (.int m) => m
  | _ => 0

theorem counter_of_some {c : Nat} {σ : Heap} {m : Int} (h : σ c = some (.int m)) :
    counter c σ = m := by
  simp [counter, h]

theorem counter_set {c : Nat} (σ : Heap) (m : Int) : counter c (σ.set c (.int m)) = m := by
  simp [counter, Heap.set]

/-- The increment as an abstract operation: one LP, effect `+1`. -/
def incrOp : AtomicOp Int where
  P := fun _ => True
  Q := fun _ => True
  t := { pre := [], commit := (· + 1), post := []
         pre_frame := fun _ hf => absurd hf List.not_mem_nil
         post_frame := fun _ hf => absurd hf List.not_mem_nil
         commits := fun _ _ => trivial }

/-- The erasure for increments: every recorded step is its thread's LP, `+1`. -/
def incrEr (ts : TStep) : Step Int := ⟨ts.k, (· + 1), true⟩

/-- A recorded step of `incr c` at a heap holding an integer: what it must be. -/
def IncrStep (c : Nat) (ts : TStep) : Prop :=
  ts.e = incr c ∧ ts.efs = [] ∧ ∃ m : Int, ts.σ c = some (.int m) ∧ ts.σ' = ts.σ.set c (.int (m + 1))

/-- The only step of `incr c` is the fetch-and-add. -/
theorem incr_step_shape {c : Nat} {ts : TStep} (he : ts.e = incr c)
    (hprim : prim_step ts.e ts.σ ts.e' ts.σ' ts.efs) : IncrStep c ts := by
  rw [he] at hprim
  obtain ⟨m, hσ, _, hσ', hefs⟩ := prim_step_faa_inv hprim
  exact ⟨he, hefs, m, hσ, hσ'⟩

/-- Commutation for an increment step: the counter goes up by one. -/
theorem incr_commutes {c : Nat} {ts : TStep} (h : IncrStep c ts) :
    counter c ts.σ' = (incrEr ts).eff (counter c ts.σ) := by
  obtain ⟨_, _, m, hσ, hσ'⟩ := h
  simp only [incrEr]
  rw [hσ', counter_set, counter_of_some hσ]

/-- A thread slot of the two-increment pool: still the program with no step
recorded for it, or finished with exactly one. -/
def SlotOk (c : Nat) (e : Expr) (n : Nat) : Prop :=
  (e = incr c ∧ n = 0) ∨ (∃ v, e = .val v ∧ n = 1)

/-- How many recorded steps belong to position `i`. -/
def countK (i : Nat) (tr : List TStep) : Nat := (tr.filter (·.k = i)).length

theorem countK_append (i : Nat) (tr : List TStep) (ts : TStep) :
    countK i (tr ++ [ts]) = countK i tr + (if ts.k = i then 1 else 0) := by
  simp only [countK, List.filter_append, List.length_append]
  by_cases h : ts.k = i <;> simp [h]

/-- The invariant of the two-increment pool along any trace. -/
def IncrInv (c : Nat) (cfg : Cfg) (tr : List TStep) : Prop :=
  (∃ A B, cfg.tp = [A, B] ∧ SlotOk c A (countK 0 tr) ∧ SlotOk c B (countK 1 tr)) ∧
  (∀ ts ∈ tr, IncrStep c ts) ∧ (∃ m : Int, cfg.heap c = some (.int m)) ∧
  (∀ ts ∈ tr, ts.k = 0 ∨ ts.k = 1)

/-- A finished slot cannot step. -/
theorem slot_val_no_step {c : Nat} {e : Expr} {n : Nat} (h : SlotOk c e n)
    {σ e' σ' efs} (hprim : prim_step e σ e' σ' efs) : e = incr c ∧ n = 0 := by
  rcases h with h | ⟨v, rfl, _⟩
  · exact h
  · exact absurd hprim (val_no_prim_step v σ e' σ' efs)

/-- **The invariant is preserved by every recorded step.** -/
theorem incr_inv_step {c : Nat} {cfg cfg' : Cfg} {tr : List TStep} {ts : TStep}
    (hinv : IncrInv c cfg tr) (hs : stepAt ts cfg cfg') : IncrInv c cfg' (tr ++ [ts]) := by
  obtain ⟨⟨A, B, htp, hA, hB⟩, hall, ⟨m0, hheap⟩, hks⟩ := hinv
  obtain ⟨t1, t2, htp', hk, hσ, hprim, hσ', htp''⟩ := hs
  rw [htp] at htp'
  have hk01 : ts.k = 0 ∨ ts.k = 1 := by
    match t1, htp', hk with
    | [], _, hk => left; simpa using hk.symm
    | [_], _, hk => right; simpa using hk.symm
    | _ :: _ :: _, htp', _ => simp at htp'
  have hks' : ∀ t ∈ tr ++ [ts], t.k = 0 ∨ t.k = 1 := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hks t ht
    · rw [List.mem_singleton.mp ht]; exact hk01
  -- the pool has two slots, so t1 is [] or [A]
  have hshape : IncrStep c ts := by
    -- the stepped expression is A or B, and a stepping slot is still `incr c`
    match t1, htp' with
    | [], htp' =>
        simp only [List.nil_append, List.cons.injEq] at htp'
        obtain ⟨rfl, _⟩ := htp'
        exact incr_step_shape (slot_val_no_step hA hprim).1 hprim
    | [a], htp' =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at htp'
        obtain ⟨rfl, rfl, _⟩ := htp'
        exact incr_step_shape (slot_val_no_step hB hprim).1 hprim
    | _ :: _ :: _, htp' => simp at htp'
  have hall' : ∀ t ∈ tr ++ [ts], IncrStep c t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hall t ht
    · rw [List.mem_singleton.mp ht]; exact hshape
  obtain ⟨he, hefs, m, hσc, hσ'c⟩ := hshape
  refine ⟨?_, hall', ⟨m + 1, by rw [hσ', hσ'c]; simp [Heap.set]⟩, hks'⟩
  match t1, htp', hk with
  | [], htp', hk =>
      simp only [List.nil_append, List.cons.injEq] at htp'
      obtain ⟨rfl, rfl⟩ := htp'
      have hA' := slot_val_no_step hA hprim
      simp only [List.length_nil] at hk
      refine ⟨ts.e', B, by rw [htp'', hefs]; rfl, ?_, ?_⟩
      · rw [countK_append, hA'.2, if_pos hk.symm]
        rw [he] at hprim
        obtain ⟨_, _, he', _, _⟩ := prim_step_faa_inv hprim
        exact Or.inr ⟨_, he', rfl⟩
      · rw [countK_append, if_neg (by omega)]
        simpa using hB
  | [a], htp', hk =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at htp'
      obtain ⟨hAa, rfl, rfl⟩ := htp'
      have hB' := slot_val_no_step hB hprim
      simp only [List.length_singleton] at hk
      refine ⟨A, ts.e', by rw [htp'', hefs, ← hAa]; rfl, ?_, ?_⟩
      · rw [countK_append, if_neg (by omega)]
        simpa using hA
      · rw [countK_append, hB'.2, if_pos hk.symm]
        rw [he] at hprim
        obtain ⟨_, _, he', _, _⟩ := prim_step_faa_inv hprim
        exact Or.inr ⟨_, he', rfl⟩
  | _ :: _ :: _, htp', _ => simp at htp'

/-- The invariant holds along every trace from the initial pool. -/
theorem incr_inv {c : Nat} {σ0 : Heap} {m0 : Int} (h0 : σ0 c = some (.int m0))
    {tr : List TStep} {cfg : Cfg} (h : Trace ⟨[incr c, incr c], σ0⟩ tr cfg) : IncrInv c cfg tr := by
  induction h with
  | refl =>
      exact ⟨⟨incr c, incr c, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩,
        fun _ ht => absurd ht List.not_mem_nil, ⟨m0, h0⟩,
        fun _ ht => absurd ht List.not_mem_nil⟩
  | snoc _ hs ih => exact incr_inv_step ih hs

/-- With every position in `{0, 1}`, the trace length is the sum of the two counts. -/
theorem length_eq_counts : ∀ tr : List TStep, (∀ ts ∈ tr, ts.k = 0 ∨ ts.k = 1) →
    tr.length = countK 0 tr + countK 1 tr := by
  intro tr
  induction tr with
  | nil => intro _; rfl
  | cons ts tr ih =>
      intro hks
      have hrest := ih (fun t ht => hks t (List.mem_cons_of_mem ts ht))
      have hts := hks ts (List.mem_cons_self ..)
      simp only [countK, List.filter_cons, List.length_cons] at hrest ⊢
      rcases hts with h | h <;> simp [h] <;> omega

/-- A finished pool has exactly one step per position, hence a two-step trace with
one step of each position. -/
theorem incr_trace_shape {c : Nat} {tr : List TStep} {v1 v2 : Val} {σ' : Heap}
    (hinv : IncrInv c ⟨[.val v1, .val v2], σ'⟩ tr) :
    ∃ x y, tr = [x, y] ∧ ((x.k = 0 ∧ y.k = 1) ∨ (x.k = 1 ∧ y.k = 0)) := by
  obtain ⟨⟨A, B, htp, hA, hB⟩, _, _, hks⟩ := hinv
  simp only [List.cons.injEq] at htp
  obtain ⟨rfl, rfl, _⟩ := htp
  have h0 : countK 0 tr = 1 := by
    rcases hA with ⟨h, _⟩ | ⟨_, _, h⟩
    · exact absurd h (by simp [incr])
    · exact h
  have h1 : countK 1 tr = 1 := by
    rcases hB with ⟨h, _⟩ | ⟨_, _, h⟩
    · exact absurd h (by simp [incr])
    · exact h
  have hlen : tr.length = 2 := by rw [length_eq_counts tr hks, h0, h1]
  match tr, hlen, h0, h1, hks with
  | [x, y], _, h0, h1, hks =>
      refine ⟨x, y, rfl, ?_⟩
      have hx := hks x (by simp)
      have hy := hks y (by simp)
      simp only [countK, List.filter_cons, List.filter_nil] at h0 h1
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy] at h0 h1 <;> omega

/-- **Two concurrent increments never lose an update.** For the real `λ-conc` pool
`[FAA(c,1), FAA(c,1)]` started at a heap with `c ↦ k`, **every** annotated run that
finishes both threads ends with `c ↦ k + 2` — whatever the scheduler did. Through
`real_run_linearizes`: both obligations discharged. -/
theorem two_incrs {c : Nat} {σ0 : Heap} {m0 : Int} (h0 : σ0 c = some (.int m0))
    {tr : List TStep} {v1 v2 : Val} {σ' : Heap}
    (h : Trace ⟨[incr c, incr c], σ0⟩ tr ⟨[.val v1, .val v2], σ'⟩) :
    σ' c = some (.int (m0 + 2)) := by
  have hinv := incr_inv h0 h
  obtain ⟨x, y, htr, hcase⟩ := incr_trace_shape hinv
  have hcomm : ∀ ts ∈ tr, counter c ts.σ' = (incrEr ts).eff (counter c ts.σ) :=
    fun ts hts => incr_commutes (hinv.2.1 ts hts)
  have hshape : Interleave (stepsFrom 0 [incrOp, incrOp]) (tr.map incrEr) := by
    rw [htr]
    rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · show Interleave [[(⟨0, (· + 1), true⟩ : Step Int)], [(⟨1, (· + 1), true⟩ : Step Int)]]
        [(⟨x.k, (· + 1), true⟩ : Step Int), (⟨y.k, (· + 1), true⟩ : Step Int)]
      rw [hx, hy]
      exact Interleave.step (k := 0) rfl (Interleave.step (k := 1) rfl (Interleave.done (by simp)))
    · show Interleave [[(⟨0, (· + 1), true⟩ : Step Int)], [(⟨1, (· + 1), true⟩ : Step Int)]]
        [(⟨x.k, (· + 1), true⟩ : Step Int), (⟨y.k, (· + 1), true⟩ : Step Int)]
      rw [hx, hy]
      exact Interleave.step (k := 1) rfl (Interleave.step (k := 0) rfl (Interleave.done (by simp)))
  obtain ⟨heq, _, _⟩ := real_run_linearizes incrEr (counter c) [incrOp, incrOp] h hcomm hshape
  obtain ⟨m, hm⟩ := hinv.2.2.1
  have hm' : σ' c = some (.int m) := hm
  have hval : counter c σ' = m0 + 2 := by
    have heq' : counter c σ' = runSteps (lps (tr.map incrEr)) (counter c σ0) := heq
    rw [heq', counter_of_some h0, htr]
    rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [lps, runSteps, incrEr] <;> omega
  have hmv : m = m0 + 2 := by rw [← counter_of_some hm', hval]
  rw [hm', hmv]

/-- The same over the unannotated semantics: every real `steps` run of the pool. -/
theorem two_incrs_steps {c : Nat} {σ0 : Heap} {m0 : Int} (h0 : σ0 c = some (.int m0))
    {v1 v2 : Val} {σ' : Heap}
    (h : steps ⟨[incr c, incr c], σ0⟩ ⟨[.val v1, .val v2], σ'⟩) :
    σ' c = some (.int (m0 + 2)) := by
  obtain ⟨tr, htr⟩ := steps_trace h
  exact two_incrs h0 htr

end LeanliftIris.PhaseC
