/-
Phase C (step 8) — **a future-dependent linearization point on the real pool**:
prophecy resolution attached to a `λ-conc` execution.

`Prophecy.lean`/`ProphMachine.lean` establish the prophecy mechanism abstractly
and on a small resolution machine. The plan's remaining C2 item is to attach a
prophecy-resolved LP to the real execution. With `Erasure.lean` in place this is
now a theorem about `Lang.steps`, for the simplest program whose LP is genuinely
future-dependent: two threads racing `CAS(f, 0, 1)` on a flag.

  * Which thread's CAS succeeds is decided by the schedule — nothing in either
    thread's own code determines it. That is the prophecy: `pv = true` iff thread
    0 wins. Its **resolution** is the real run itself: the first recorded step.
  * The abstract family is **indexed by the prophecy**: the winner is `setOp`
    (`0 ↦ 1`, LP at its CAS), the loser is `noopOp` (observes `1`, LP at its
    failed CAS, no abstract effect). `casFamily pv` picks which thread is which.
  * **`two_cas_linearizes`**: every real run finishing both threads has a
    prophecy value `pv`, resolved by its first step, such that the erased trace is
    an `Interleave` of `stepsFrom 0 (casFamily pv)` — so `real_run_linearizes`
    applies: the flag ends `1`, one LP per thread, each LP its op's commit.
  * **`two_cas_steps`** — the operational payoff, with no abstract vocabulary:
    every `steps` run from `f ↦ 0` that finishes both threads ends with `f ↦ 1`
    and **exactly one** thread returning `true` — the one that stepped first.
    `two_cas_run_exists_0` / `_1` certify both outcomes occur.

What this is: the prophecy phenomenon on the real semantics — the family of
abstract operations a run linearizes against depends on that run, and the
dependency is resolved by the schedule, exactly as `Prophecy.lean` models it in
the small. What it is not: a prophecy *variable* inside `λ-conc` with `NewProph`/
`Resolve` as program steps (that is `ProphMachine.lean`'s machine), nor a `wp`
rule for prophecies; those remain open. Sorry-free.
-/
import LeanliftIris.PhaseC.Erasure

namespace LeanliftIris.PhaseC
open LeanliftIris.PhaseA

/-- `CAS(f, 0, 1)`: claim the flag. -/
def casF (f : Nat) : Expr := .cas (.val (.loc f)) (.val (.int 0)) (.val (.int 1))

/-! ## The two shapes a recorded step of the race can have -/

/-- The winning step: saw `0`, wrote `1`, returned `true`. -/
def WinStep (f : Nat) (ts : TStep) : Prop :=
  ts.e = casF f ∧ ts.efs = [] ∧ ts.σ f = some (.int 0) ∧ ts.e' = .val (.bool true) ∧
    ts.σ' = ts.σ.set f (.int 1)

/-- A losing step: saw `1`, changed nothing, returned `false`. -/
def LoseStep (f : Nat) (ts : TStep) : Prop :=
  ts.e = casF f ∧ ts.efs = [] ∧ ts.σ f = some (.int 1) ∧ ts.e' = .val (.bool false) ∧
    ts.σ' = ts.σ

/-- The only steps of `CAS(f,0,1)`: win on `0`, lose on `1`. -/
theorem cas_step_shape {f : Nat} {ts : TStep} (he : ts.e = casF f)
    (hprim : prim_step ts.e ts.σ ts.e' ts.σ' ts.efs) :
    (ts.σ f = some (.int 0) → WinStep f ts) ∧ (ts.σ f = some (.int 1) → LoseStep f ts) := by
  rw [he] at hprim
  obtain ⟨v0, hσ, hcase⟩ := prim_step_cas_inv hprim
  constructor
  · intro h0
    rw [h0] at hσ
    have hv0 : v0 = .int 0 := Option.some.inj hσ.symm
    rcases hcase with ⟨_, he', hσ', hefs⟩ | ⟨hne, _, _, _⟩
    · exact ⟨he, hefs, h0, he', hσ'⟩
    · exact absurd hv0 hne
  · intro h1
    rw [h1] at hσ
    have hv0 : v0 = .int 1 := Option.some.inj hσ.symm
    rcases hcase with ⟨heq, _, _, _⟩ | ⟨_, he', hσ', hefs⟩
    · subst hv0; simp at heq
    · exact ⟨he, hefs, h1, he', hσ'⟩

/-! ## The invariant of the race -/

/-- A slot: still the CAS with no step recorded, or finished with exactly one. -/
def CSlot (f : Nat) (e : Expr) (n : Nat) : Prop :=
  (e = casF f ∧ n = 0) ∨ (∃ b : Bool, e = .val (.bool b) ∧ n = 1)

/-- The flag and the recorded history agree: nothing happened and the flag is `0`,
or the first step won, every later step lost, and the flag is `1`. -/
def CasHist (f : Nat) (cfg : Cfg) (tr : List TStep) : Prop :=
  (tr = [] ∧ cfg.heap f = some (.int 0)) ∨
  (cfg.heap f = some (.int 1) ∧ ∃ w rest, tr = w :: rest ∧ WinStep f w ∧ ∀ l ∈ rest, LoseStep f l)

def CasInv (f : Nat) (cfg : Cfg) (tr : List TStep) : Prop :=
  (∃ A B, cfg.tp = [A, B] ∧ CSlot f A (countK 0 tr) ∧ CSlot f B (countK 1 tr)) ∧
  (∀ ts ∈ tr, ts.k = 0 ∨ ts.k = 1) ∧
  (∀ ts ∈ tr, cfg.tp[ts.k]? = some ts.e') ∧
  CasHist f cfg tr

theorem cslot_val_no_step {f : Nat} {e : Expr} {n : Nat} (h : CSlot f e n)
    {σ e' σ' efs} (hprim : prim_step e σ e' σ' efs) : e = casF f ∧ n = 0 := by
  rcases h with h | ⟨b, rfl, _⟩
  · exact h
  · exact absurd hprim (val_no_prim_step _ σ e' σ' efs)

theorem countK_zero {i : Nat} {tr : List TStep} (h : countK i tr = 0) : ∀ ts ∈ tr, ts.k ≠ i := by
  intro ts hts hk
  have : ts ∈ tr.filter (·.k = i) := List.mem_filter.mpr ⟨hts, by simp [hk]⟩
  have hlen : 0 < (tr.filter (·.k = i)).length := List.length_pos_of_mem this
  simp only [countK] at h
  omega

/-- The step's own shape, from the history: the first step wins, later ones lose. -/
theorem cas_hist_step {f : Nat} {cfg : Cfg} {tr : List TStep} {ts : TStep}
    (hh : CasHist f cfg tr) (hσ : cfg.heap = ts.σ) (he : ts.e = casF f)
    (hprim : prim_step ts.e ts.σ ts.e' ts.σ' ts.efs) :
    (tr = [] ∧ WinStep f ts) ∨ (tr ≠ [] ∧ LoseStep f ts) := by
  obtain ⟨hwin, hlose⟩ := cas_step_shape he hprim
  rcases hh with ⟨rfl, h0⟩ | ⟨h1, w, rest, rfl, _, _⟩
  · exact Or.inl ⟨rfl, hwin (by rw [hσ] at h0; exact h0)⟩
  · exact Or.inr ⟨by simp, hlose (by rw [hσ] at h1; exact h1)⟩

theorem cas_hist_snoc {f : Nat} {cfg cfg' : Cfg} {tr : List TStep} {ts : TStep}
    (hh : CasHist f cfg tr) (hshape : (tr = [] ∧ WinStep f ts) ∨ (tr ≠ [] ∧ LoseStep f ts))
    (hσ : cfg.heap = ts.σ) (hσ' : cfg'.heap = ts.σ') : CasHist f cfg' (tr ++ [ts]) := by
  rcases hshape with ⟨rfl, hw⟩ | ⟨hne, hl⟩
  · right
    refine ⟨?_, ts, [], rfl, hw, fun _ h => absurd h List.not_mem_nil⟩
    rw [hσ', hw.2.2.2.2]; simp [Heap.set]
  · rcases hh with ⟨rfl, _⟩ | ⟨h1, w, rest, rfl, hw, hrest⟩
    · exact absurd rfl hne
    · right
      refine ⟨by rw [hσ', hl.2.2.2.2, ← hσ]; exact h1, w, rest ++ [ts], rfl, hw, ?_⟩
      intro l hl'
      rcases List.mem_append.mp hl' with h | h
      · exact hrest l h
      · rw [List.mem_singleton.mp h]; exact hl

/-- **The invariant is preserved by every recorded step.** -/
theorem cas_inv_step {f : Nat} {cfg cfg' : Cfg} {tr : List TStep} {ts : TStep}
    (hinv : CasInv f cfg tr) (hs : stepAt ts cfg cfg') : CasInv f cfg' (tr ++ [ts]) := by
  obtain ⟨⟨A, B, htp, hA, hB⟩, hks, hpos, hh⟩ := hinv
  obtain ⟨t1, t2, htp', hk, hσ, hprim, hσ', htp''⟩ := hs
  rw [htp] at htp'
  -- the stepped slot is a live CAS, so its position has no recorded step yet
  have hstep : (ts.e = casF f) ∧ (ts.k = 0 ∧ countK 0 tr = 0 ∧ A = ts.e ∧ B ∈ t2) ∨
      (ts.e = casF f) ∧ (ts.k = 1 ∧ countK 1 tr = 0 ∧ B = ts.e ∧ A ∈ t1) := by
    match t1, htp', hk with
    | [], htp', hk =>
        simp only [List.nil_append, List.cons.injEq] at htp'
        obtain ⟨hAe, ht2⟩ := htp'
        have := cslot_val_no_step hA (hAe ▸ hprim)
        exact Or.inl ⟨by rw [← hAe]; exact this.1, by simpa using hk.symm, this.2, hAe,
          by rw [← ht2]; simp⟩
    | [a], htp', hk =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at htp'
        obtain ⟨hAa, hBe, _⟩ := htp'
        have := cslot_val_no_step hB (hBe ▸ hprim)
        exact Or.inr ⟨by rw [← hBe]; exact this.1, by simpa using hk.symm, this.2, hBe,
          by rw [hAa]; simp⟩
    | _ :: _ :: _, htp', _ => simp at htp'
  have he : ts.e = casF f := by rcases hstep with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
  have hshape := cas_hist_step hh hσ he hprim
  have hefs : ts.efs = [] := by
    rcases hshape with ⟨_, hw⟩ | ⟨_, hl⟩
    · exact hw.2.1
    · exact hl.2.1
  have hval : ∃ b : Bool, ts.e' = .val (.bool b) := by
    rcases hshape with ⟨_, hw⟩ | ⟨_, hl⟩
    · exact ⟨true, hw.2.2.2.1⟩
    · exact ⟨false, hl.2.2.2.1⟩
  refine ⟨?_, ?_, ?_, cas_hist_snoc hh hshape hσ hσ'⟩
  · -- slots
    rcases hstep with ⟨_, hk0, hc0, hAe, _⟩ | ⟨_, hk1, hc1, hBe, _⟩
    · match t1, htp', hk with
      | [], htp', _ =>
          simp only [List.nil_append, List.cons.injEq] at htp'
          obtain ⟨_, ht2⟩ := htp'
          refine ⟨ts.e', B, by rw [htp'', hefs, ← ht2]; rfl, ?_, ?_⟩
          · rw [countK_append, hc0, if_pos hk0]
            obtain ⟨b, hb⟩ := hval
            exact Or.inr ⟨b, hb, rfl⟩
          · rw [countK_append, if_neg (by omega)]; simpa using hB
      | [_], htp', hk => simp at hk; omega
      | _ :: _ :: _, htp', _ => simp at htp'
    · match t1, htp', hk with
      | [], htp', hk => simp at hk; omega
      | [a], htp', _ =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at htp'
          obtain ⟨hAa, _, ht2⟩ := htp'
          refine ⟨A, ts.e', by rw [htp'', hefs, ← hAa, ← ht2]; rfl, ?_, ?_⟩
          · rw [countK_append, if_neg (by omega)]; simpa using hA
          · rw [countK_append, hc1, if_pos hk1]
            obtain ⟨b, hb⟩ := hval
            exact Or.inr ⟨b, hb, rfl⟩
      | _ :: _ :: _, htp', _ => simp at htp'
  · -- positions
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hks t ht
    · rw [List.mem_singleton.mp ht]
      rcases hstep with ⟨_, hk0, _⟩ | ⟨_, hk1, _⟩
      · exact Or.inl hk0
      · exact Or.inr hk1
  · -- every recorded step's slot holds its result
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · -- an old step: its position differs from the new one, and that slot is untouched
      have hkt := hks t ht
      have hpt := hpos t ht
      rw [htp] at hpt
      rcases hstep with ⟨_, hk0, hc0, _, _⟩ | ⟨_, hk1, hc1, _, _⟩
      · have hne := countK_zero hc0 t ht
        match t1, htp', hk with
        | [], htp', _ =>
            simp only [List.nil_append, List.cons.injEq] at htp'
            obtain ⟨_, ht2⟩ := htp'
            rw [htp'', hefs, ← ht2]
            rcases hkt with h | h
            · exact absurd h hne
            · rw [h] at hpt ⊢; simpa using hpt
        | [_], htp', hk => simp at hk; omega
        | _ :: _ :: _, htp', _ => simp at htp'
      · have hne := countK_zero hc1 t ht
        match t1, htp', hk with
        | [], htp', hk => simp at hk; omega
        | [a], htp', _ =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at htp'
            obtain ⟨hAa, _, ht2⟩ := htp'
            rw [htp'', hefs, ← hAa, ← ht2]
            rcases hkt with h | h
            · rw [h] at hpt ⊢; simpa using hpt
            · exact absurd h hne
        | _ :: _ :: _, htp', _ => simp at htp'
    · -- the new step: its slot now holds its result
      rw [List.mem_singleton.mp ht]
      rcases hstep with ⟨_, hk0, _⟩ | ⟨_, hk1, _⟩
      · match t1, htp', hk with
        | [], htp', _ =>
            simp only [List.nil_append, List.cons.injEq] at htp'
            obtain ⟨_, ht2⟩ := htp'
            rw [htp'', hefs, ← ht2, hk0]; rfl
        | [_], htp', hk => simp at hk; omega
        | _ :: _ :: _, htp', _ => simp at htp'
      · match t1, htp', hk with
        | [], htp', hk => simp at hk; omega
        | [a], htp', _ =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at htp'
            obtain ⟨hAa, _, ht2⟩ := htp'
            rw [htp'', hefs, ← hAa, ← ht2, hk1]; rfl
        | _ :: _ :: _, htp', _ => simp at htp'

/-- The invariant holds along every trace from the initial pool. -/
theorem cas_inv {f : Nat} {σ0 : Heap} (h0 : σ0 f = some (.int 0))
    {tr : List TStep} {cfg : Cfg} (h : Trace ⟨[casF f, casF f], σ0⟩ tr cfg) : CasInv f cfg tr := by
  induction h with
  | refl =>
      exact ⟨⟨casF f, casF f, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩,
        fun _ ht => absurd ht List.not_mem_nil, fun _ ht => absurd ht List.not_mem_nil,
        Or.inl ⟨rfl, h0⟩⟩
  | snoc _ hs ih => exact cas_inv_step ih hs

/-- A finished race: two steps, one per position, the first won, the second lost. -/
theorem cas_trace_shape {f : Nat} {tr : List TStep} {v1 v2 : Val} {σ' : Heap}
    (hinv : CasInv f ⟨[.val v1, .val v2], σ'⟩ tr) :
    ∃ x y, tr = [x, y] ∧ ((x.k = 0 ∧ y.k = 1) ∨ (x.k = 1 ∧ y.k = 0)) ∧
      WinStep f x ∧ LoseStep f y ∧ σ' f = some (.int 1) := by
  obtain ⟨⟨A, B, htp, hA, hB⟩, hks, _, hh⟩ := hinv
  simp only [List.cons.injEq] at htp
  obtain ⟨rfl, rfl, _⟩ := htp
  have h0 : countK 0 tr = 1 := by
    rcases hA with ⟨h, _⟩ | ⟨_, _, h⟩
    · exact absurd h (by simp [casF])
    · exact h
  have h1 : countK 1 tr = 1 := by
    rcases hB with ⟨h, _⟩ | ⟨_, _, h⟩
    · exact absurd h (by simp [casF])
    · exact h
  have hlen : tr.length = 2 := by rw [length_eq_counts tr hks, h0, h1]
  match tr, hlen, h0, h1, hks, hh with
  | [x, y], _, h0, h1, hks, hh =>
      refine ⟨x, y, rfl, ?_, ?_⟩
      · have hx := hks x (by simp)
        have hy := hks y (by simp)
        simp only [countK, List.filter_cons, List.filter_nil] at h0 h1
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy] at h0 h1 <;> omega
      · rcases hh with ⟨h, _⟩ | ⟨hf, w, rest, hwr, hw, hrest⟩
        · simp at h
        · simp only [List.cons.injEq] at hwr
          obtain ⟨rfl, rfl⟩ := hwr
          exact ⟨hw, hrest y (by simp), hf⟩

/-! ## The operational payoff -/

/-- **Exactly one winner, and it is whoever stepped first.** Every annotated run
of the race from `f ↦ 0` that finishes both threads ends with `f ↦ 1`, one thread
returning `true` and the other `false`. -/
theorem two_cas {f : Nat} {σ0 : Heap} (h0 : σ0 f = some (.int 0))
    {tr : List TStep} {v1 v2 : Val} {σ' : Heap}
    (h : Trace ⟨[casF f, casF f], σ0⟩ tr ⟨[.val v1, .val v2], σ'⟩) :
    σ' f = some (.int 1) ∧
    ((v1 = .bool true ∧ v2 = .bool false) ∨ (v1 = .bool false ∧ v2 = .bool true)) := by
  have hinv := cas_inv h0 h
  obtain ⟨x, y, htr, hcase, hw, hl, hf⟩ := cas_trace_shape hinv
  obtain ⟨_, _, hpos, _⟩ := hinv
  refine ⟨hf, ?_⟩
  have hx := hpos x (by rw [htr]; simp)
  have hy := hpos y (by rw [htr]; simp)
  rw [hw.2.2.2.1] at hx
  rw [hl.2.2.2.1] at hy
  rcases hcase with ⟨hk0, hk1⟩ | ⟨hk0, hk1⟩
  · rw [hk0] at hx; rw [hk1] at hy
    simp at hx hy
    exact Or.inl ⟨hx, hy⟩
  · rw [hk0] at hx; rw [hk1] at hy
    simp at hx hy
    exact Or.inr ⟨hy, hx⟩

/-- The same over the unannotated semantics. -/
theorem two_cas_steps {f : Nat} {σ0 : Heap} (h0 : σ0 f = some (.int 0)) {v1 v2 : Val} {σ' : Heap}
    (h : steps ⟨[casF f, casF f], σ0⟩ ⟨[.val v1, .val v2], σ'⟩) :
    σ' f = some (.int 1) ∧
    ((v1 = .bool true ∧ v2 = .bool false) ∨ (v1 = .bool false ∧ v2 = .bool true)) := by
  obtain ⟨tr, htr⟩ := steps_trace h
  exact two_cas h0 htr

/-- **Both outcomes occur** (non-vacuity, and the bound is informative): thread 0
first — thread 0 wins. -/
theorem two_cas_run_exists_0 {f : Nat} {σ0 : Heap} (h0 : σ0 f = some (.int 0)) :
    steps ⟨[casF f, casF f], σ0⟩ ⟨[.val (.bool true), .val (.bool false)], σ0.set f (.int 1)⟩ := by
  have h1 : (σ0.set f (.int 1)) f = some (.int 1) := by simp [Heap.set]
  have s1 : step ⟨[casF f, casF f], σ0⟩ ⟨[.val (.bool true), casF f], σ0.set f (.int 1)⟩ :=
    ⟨[], [casF f], casF f, .val (.bool true), [], rfl,
      prim_step.head (Head.casS (l := f) (v1 := .int 0) (v2 := .int 1) h0 rfl), rfl⟩
  have s2 : step ⟨[.val (.bool true), casF f], σ0.set f (.int 1)⟩
      ⟨[.val (.bool true), .val (.bool false)], σ0.set f (.int 1)⟩ :=
    ⟨[.val (.bool true)], [], casF f, .val (.bool false), [], rfl,
      prim_step.head (Head.casF (l := f) (v1 := .int 0) (v2 := .int 1) h1 (by simp)), rfl⟩
  exact (steps.refl.tail s1).tail s2

/-- Thread 1 first — thread 1 wins. -/
theorem two_cas_run_exists_1 {f : Nat} {σ0 : Heap} (h0 : σ0 f = some (.int 0)) :
    steps ⟨[casF f, casF f], σ0⟩ ⟨[.val (.bool false), .val (.bool true)], σ0.set f (.int 1)⟩ := by
  have h1 : (σ0.set f (.int 1)) f = some (.int 1) := by simp [Heap.set]
  have s1 : step ⟨[casF f, casF f], σ0⟩ ⟨[casF f, .val (.bool true)], σ0.set f (.int 1)⟩ :=
    ⟨[casF f], [], casF f, .val (.bool true), [], rfl,
      prim_step.head (Head.casS (l := f) (v1 := .int 0) (v2 := .int 1) h0 rfl), rfl⟩
  have s2 : step ⟨[casF f, .val (.bool true)], σ0.set f (.int 1)⟩
      ⟨[.val (.bool false), .val (.bool true)], σ0.set f (.int 1)⟩ :=
    ⟨[], [.val (.bool true)], casF f, .val (.bool false), [], rfl,
      prim_step.head (Head.casF (l := f) (v1 := .int 0) (v2 := .int 1) h1 (by simp)), rfl⟩
  exact (steps.refl.tail s1).tail s2

/-! ## The prophecy-indexed family and the linearization -/

/-- The winner: `0 ↦ 1`, LP at its CAS. -/
def setOp : AtomicOp Int where
  P := fun s => s = 0
  Q := fun s => s = 1
  t := { pre := [], commit := fun _ => 1, post := []
         pre_frame := fun _ hf => absurd hf List.not_mem_nil
         post_frame := fun _ hf => absurd hf List.not_mem_nil
         commits := fun _ _ => rfl }

/-- The loser: observes `1`, LP at its failed CAS, no abstract effect. -/
def noopOp : AtomicOp Int where
  P := fun s => s = 1
  Q := fun s => s = 1
  t := { pre := [], commit := id, post := []
         pre_frame := fun _ hf => absurd hf List.not_mem_nil
         post_frame := fun _ hf => absurd hf List.not_mem_nil
         commits := fun _ hs => hs }

/-- The family, indexed by the prophecy "thread 0 wins". -/
def casFamily (pv : Bool) : List (AtomicOp Int) :=
  if pv then [setOp, noopOp] else [noopOp, setOp]

/-- The erasure: a step that returned `true` is the `0 ↦ 1` LP, one that returned
`false` is the no-op LP. -/
def casEr (ts : TStep) : Step Int :=
  ⟨ts.k, if ts.e' = .val (.bool true) then fun _ => 1 else id, true⟩

theorem casEr_win {f : Nat} {ts : TStep} (h : WinStep f ts) : casEr ts = ⟨ts.k, fun _ => 1, true⟩ := by
  simp [casEr, h.2.2.2.1]

theorem casEr_lose {f : Nat} {ts : TStep} (h : LoseStep f ts) : casEr ts = ⟨ts.k, id, true⟩ := by
  simp [casEr, h.2.2.2.1]

theorem cas_commutes {f : Nat} {ts : TStep} (h : WinStep f ts ∨ LoseStep f ts) :
    counter f ts.σ' = (casEr ts).eff (counter f ts.σ) := by
  rcases h with hw | hl
  · rw [casEr_win hw, hw.2.2.2.2, counter_set]
  · rw [casEr_lose hl, hl.2.2.2.2]; rfl

/-- **The race linearizes against a prophecy-indexed family.** Every finished run
has a prophecy value `pv` — resolved by the run: `pv = true` iff the first step is
thread 0's — such that the erased trace is an interleaving of `casFamily pv`'s
traces; hence (`real_run_linearizes`) the abstract flag ends at the sequential
history's result `1`, with one LP per thread, each its op's commit. -/
theorem two_cas_linearizes {f : Nat} {σ0 : Heap} (h0 : σ0 f = some (.int 0))
    {tr : List TStep} {v1 v2 : Val} {σ'' : Heap}
    (h : Trace ⟨[casF f, casF f], σ0⟩ tr ⟨[.val v1, .val v2], σ''⟩) :
    ∃ pv : Bool, (∃ x rest, tr = x :: rest ∧ (pv = true ↔ x.k = 0)) ∧
      (pv = true ↔ v1 = .bool true) ∧
      Interleave (stepsFrom 0 (casFamily pv)) (tr.map casEr) ∧
      counter f σ'' = runSteps (lps (tr.map casEr)) (counter f σ0) ∧
      ((lps (tr.map casEr)).map (·.op)).Perm (List.range' 0 2) ∧
      counter f σ'' = 1 := by
  have hinv := cas_inv h0 h
  obtain ⟨x, y, htr, hcase, hw, hl, hf⟩ := cas_trace_shape hinv
  obtain ⟨_, _, hpos, _⟩ := hinv
  have hx := hpos x (by rw [htr]; simp)
  have hy := hpos y (by rw [htr]; simp)
  rw [hw.2.2.2.1] at hx
  rw [hl.2.2.2.1] at hy
  have hcomm : ∀ ts ∈ tr, counter f ts.σ' = (casEr ts).eff (counter f ts.σ) := by
    intro ts hts
    rw [htr] at hts
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hts
    rcases hts with rfl | rfl
    · exact cas_commutes (Or.inl hw)
    · exact cas_commutes (Or.inr hl)
  have hmap : tr.map casEr = [⟨x.k, fun _ => 1, true⟩, ⟨y.k, id, true⟩] := by
    rw [htr]; simp only [List.map_cons, List.map_nil, casEr_win hw, casEr_lose hl]
  rcases hcase with ⟨hk0, hk1⟩ | ⟨hk0, hk1⟩
  · have hv1 : v1 = .bool true := by rw [hk0] at hx; simpa using hx
    refine ⟨true, ⟨x, [y], htr, by simp [hk0]⟩, by simp [hv1], ?_⟩
    have hshape : Interleave (stepsFrom 0 (casFamily true)) (tr.map casEr) := by
      rw [hmap, hk0, hk1]
      show Interleave [[(⟨0, fun _ => 1, true⟩ : Step Int)], [(⟨1, id, true⟩ : Step Int)]] _
      exact Interleave.step (k := 0) rfl (Interleave.step (k := 1) rfl (Interleave.done (by
        intro l hl
        simp only [List.set_cons_zero, List.set_cons_succ, List.mem_cons, List.not_mem_nil,
          or_false] at hl
        rcases hl with rfl | rfl <;> rfl)))
    obtain ⟨heq, hperm, _⟩ :=
      real_run_linearizes casEr (counter f) (casFamily true) h hcomm hshape
    refine ⟨hshape, heq, hperm, ?_⟩
    rw [counter_of_some hf]
  · have hv1 : v1 = .bool false := by rw [hk1] at hy; simpa using hy
    refine ⟨false, ⟨x, [y], htr, by simp [hk0]⟩, by simp [hv1], ?_⟩
    have hshape : Interleave (stepsFrom 0 (casFamily false)) (tr.map casEr) := by
      rw [hmap, hk0, hk1]
      show Interleave [[(⟨0, id, true⟩ : Step Int)], [(⟨1, fun _ => 1, true⟩ : Step Int)]] _
      exact Interleave.step (k := 1) rfl (Interleave.step (k := 0) rfl (Interleave.done (by
        intro l hl
        simp only [List.set_cons_zero, List.set_cons_succ, List.mem_cons, List.not_mem_nil,
          or_false] at hl
        rcases hl with rfl | rfl <;> rfl)))
    obtain ⟨heq, hperm, _⟩ :=
      real_run_linearizes casEr (counter f) (casFamily false) h hcomm hshape
    refine ⟨hshape, heq, hperm, ?_⟩
    rw [counter_of_some hf]

/-- **Both branches of the prophecy are inhabited**, with the erased trace exhibited
as an interleaving of the indexed family: thread 0 first resolves `pv = true`. -/
theorem two_cas_prophecy_0 {f : Nat} {σ0 : Heap} (h0 : σ0 f = some (.int 0)) :
    ∃ tr, Trace ⟨[casF f, casF f], σ0⟩ tr ⟨[.val (.bool true), .val (.bool false)], σ0.set f (.int 1)⟩ ∧
      Interleave (stepsFrom 0 (casFamily true)) (tr.map casEr) := by
  obtain ⟨tr, htr⟩ := steps_trace (two_cas_run_exists_0 h0)
  obtain ⟨pv, _, hpv, hshape, _⟩ := two_cas_linearizes h0 htr
  have : pv = true := hpv.mpr rfl
  subst this
  exact ⟨tr, htr, hshape⟩

/-- Thread 1 first resolves `pv = false`. -/
theorem two_cas_prophecy_1 {f : Nat} {σ0 : Heap} (h0 : σ0 f = some (.int 0)) :
    ∃ tr, Trace ⟨[casF f, casF f], σ0⟩ tr ⟨[.val (.bool false), .val (.bool true)], σ0.set f (.int 1)⟩ ∧
      Interleave (stepsFrom 0 (casFamily false)) (tr.map casEr) := by
  obtain ⟨tr, htr⟩ := steps_trace (two_cas_run_exists_1 h0)
  obtain ⟨pv, _, hpv, hshape, _⟩ := two_cas_linearizes h0 htr
  have : pv = false := by
    cases pv with
    | true => exact absurd (hpv.mp rfl) (by simp)
    | false => rfl
  subst this
  exact ⟨tr, htr, hshape⟩

end LeanliftIris.PhaseC
