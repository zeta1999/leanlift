/-
Phase C (step 6) — **linearizability at the abstract state**, from logical
atomicity, and the remaining structural rules of the triple library.

`LogAtom.lean` packages one operation as a logically-atomic triple `LAT P Q`: a
run with exactly one linearization point (LP). `WpAtomic.lean` grounds such
triples in the real `wp` (`Realizes`, `lat_realized`). This file proves, in core
Lean over the abstract state, what a family of such operations gives under any
schedule of their abstract traces:

  * `Interleave ls h` — `h` is an interleaving of the sequences `ls`: at each
    step take the head of any non-empty sequence. `Interleave.flatten` certifies
    the relation is inhabited; `Interleave.perm_flatten` that an interleaving is
    a permutation of its sources (no step dropped, duplicated or reordered within
    a source).
  * `AtomicOp` — an operation with its own `P`/`Q` and triple; `stepsFrom 0 os` —
    the family's tagged traces; `lps h` — the **sequential history**: the LPs of
    `h`, in order.
  * **`linearizable_abstract`** — for any interleaving `h` of the traces of a
    family `os`: (1) running `h` from any state ends where running the sequential
    history `lps h` ends; (2) the sequential history contains **exactly one LP per
    operation** (its op-indices are a permutation of `0 … |os|-1`); (3) every LP in
    the history **is** its operation's commit. `history_legal` then gives each
    operation's `P → Q` at its LP. `realtime_order` gives that an operation whose
    steps all precede another's has its LP earlier in the history.
  * `two_pushes_linearize` — the consumer, through the general theorem: two
    Treiber pushes, each with framing steps around its LP, under any interleaving,
    end in `v2 :: v1 :: xs` or `v1 :: v2 :: xs`.

**What this is and is not.** It is the abstract-state content of linearizability:
final state, one LP per operation, LPs are the commits, pre/post at the LP, order
preserved. It is *not* Herlihy–Wing linearizability of *programs*: the model has no
invocation/response events, no return values, no pending operations, and each
thread's trace is a fixed list of state-independent effects — a CAS-retry loop
whose continuation depends on another thread is not expressible as an
`AtomicOp`. The repository's real concurrent semantics (`Lang.step`/`steps`,
`PoolAdequacy`) is a different relation; `Erasure.lean` connects the two
(`real_run_linearizes`) under two explicit per-run obligations, and discharges
them uniformly for a real two-thread increment program. The further step — an
Iris-style atomic triple `<<< α >>> e <<< β >>>` letting a client open an
invariant around another thread's LP — needs `fupd` inside `wp`, which
`../docs/PLAN-fupd.md` records as blocked by the `GenMap` mask representation
(`ownE ⊤` unrepresentable); `atomic_acc` (`Fupd/Inv.lean`) makes such triples
expressible only. Sorry-free.
-/
import LeanliftIris.PhaseC.WpAtomic

namespace LeanliftIris.PhaseC
open Iris Iris.BI LeanliftIris.PhaseA

/-! ## Structural rules the triple library was missing -/

namespace LAT
variable {σ : Type}

/-- **Frame, on the right.** Appending framing micro-steps after the LP preserves a
triple. -/
def frameR {P Q : σ → Prop} (t : LAT P Q) (extra : List (σ → σ)) (h : Identities extra) :
    LAT P Q where
  pre := t.pre
  commit := t.commit
  post := t.post ++ extra
  pre_frame := t.pre_frame
  post_frame := by
    intro f hf s
    rcases List.mem_append.mp hf with h1 | h1
    · exact t.post_frame f h1 s
    · exact h f h1 s
  commits := t.commits

/-- **Consequence.** Strengthen the precondition, weaken the postcondition. -/
def conseq {P P' Q Q' : σ → Prop} (t : LAT P Q) (hP : ∀ s, P' s → P s)
    (hQ : ∀ s, Q s → Q' s) : LAT P' Q' where
  pre := t.pre
  commit := t.commit
  post := t.post
  pre_frame := t.pre_frame
  post_frame := t.post_frame
  commits := fun s hs => hQ _ (t.commits s (hP s hs))

end LAT

/-- **Sequential composition realizes the composed effect.** If `e1` realizes `f`
and `e2` realizes `g` on the same representation, then `let _ = e1 in e2` realizes
`g ∘ f` — through the real `wp`, via `wp_seq`. (`e2` must not mention the dummy
binder `"_"`, as `wp_seq` requires; every program in this repository satisfies
that.) Sequential only: this composes effects within one thread. -/
theorem Realizes.seq {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))] {σ : Type}
    (γ : GName) [HasHeap γ GF F] {repr : σ → IProp GF} {f g : σ → σ} {e1 e2 : Expr}
    (h1 : Realizes (F := F) γ repr f e1) (h2 : Realizes (F := F) γ repr g e2)
    (hcl : ∀ w : Val, substE "_" w e2 = e2) :
    Realizes (F := F) γ repr (g ∘ f) (.app (.val (.clos "_" "_" e2)) e1) := by
  intro s
  refine ((h1 s).trans (wp_mono γ e1 _ _ (fun _ => ?_))).trans (wp_seq γ e1 e2 _ hcl)
  exact (h2 (f s)).trans later_intro

/-! ## Tagged micro-steps, operations, and families -/

/-- An abstract micro-step tagged by its operation and by whether it is that
operation's linearization point. -/
structure Step (σ : Type) where
  op : Nat
  eff : σ → σ
  lp : Bool

/-- The step sequence of operation `i` given by a triple: framing prefix, the LP,
framing suffix. -/
def LAT.steps {σ : Type} {P Q : σ → Prop} (i : Nat) (t : LAT P Q) : List (Step σ) :=
  t.pre.map (fun f => ⟨i, f, false⟩) ++ ⟨i, t.commit, true⟩ :: t.post.map (fun f => ⟨i, f, false⟩)

/-- Every non-LP step of an operation is framing. -/
theorem LAT.steps_frame {σ : Type} {P Q : σ → Prop} (i : Nat) (t : LAT P Q) :
    ∀ x ∈ t.steps i, x.lp = false → ∀ s, x.eff s = s := by
  intro x hx hlp s
  simp only [LAT.steps, List.mem_append, List.mem_cons, List.mem_map] at hx
  rcases hx with ⟨f, hf, rfl⟩ | rfl | ⟨f, hf, rfl⟩
  · exact t.pre_frame f hf s
  · simp at hlp
  · exact t.post_frame f hf s

/-- The LP-flagged step of an operation's trace is exactly its commit. -/
theorem LAT.steps_lp {σ : Type} {P Q : σ → Prop} (i : Nat) (t : LAT P Q) :
    ∀ x ∈ t.steps i, x.lp = true → x = ⟨i, t.commit, true⟩ := by
  intro x hx hlp
  simp only [LAT.steps, List.mem_append, List.mem_cons, List.mem_map] at hx
  rcases hx with ⟨f, _, rfl⟩ | rfl | ⟨f, _, rfl⟩
  · simp at hlp
  · rfl
  · simp at hlp

/-- An operation with its own pre/postcondition and triple. -/
structure AtomicOp (σ : Type) where
  P : σ → Prop
  Q : σ → Prop
  t : LAT P Q

/-- The tagged traces of a family, operation `k` of the list tagged `n + k`. -/
def stepsFrom {σ : Type} (n : Nat) : List (AtomicOp σ) → List (List (Step σ))
  | [] => []
  | o :: os => o.t.steps n :: stepsFrom (n + 1) os

/-- The family's commits, tagged the same way: the canonical sequential history. -/
def lpsFrom {σ : Type} (n : Nat) : List (AtomicOp σ) → List (Step σ)
  | [] => []
  | o :: os => ⟨n, o.t.commit, true⟩ :: lpsFrom (n + 1) os

theorem lpsFrom_ops {σ : Type} (n : Nat) (os : List (AtomicOp σ)) :
    (lpsFrom n os).map (·.op) = List.range' n os.length := by
  induction os generalizing n with
  | nil => rfl
  | cons o os ih => simp only [lpsFrom, List.map_cons, List.length_cons, List.range'_succ, ih]

theorem mem_stepsFrom {σ : Type} (n : Nat) (os : List (AtomicOp σ)) :
    ∀ l ∈ stepsFrom n os, ∃ k, ∃ hk : k < os.length, l = os[k].t.steps (n + k) := by
  induction os generalizing n with
  | nil => intro l hl; exact absurd hl List.not_mem_nil
  | cons o os ih =>
      intro l hl
      simp only [stepsFrom, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨0, Nat.zero_lt_succ _, by simp⟩
      · obtain ⟨k, hk, rfl⟩ := ih (n + 1) l hl
        exact ⟨k + 1, Nat.succ_lt_succ hk, by simp [Nat.add_assoc, Nat.add_comm 1 k]⟩

/-! ## Interleavings -/

/-- **Interleaving under any scheduler of the given traces.** `Interleave ls h`:
`h` is obtained from the sequences `ls` by repeatedly picking *any* sequence that
still has steps and taking its head. No fairness, no ordering constraint between
sequences. -/
inductive Interleave {α : Type} : List (List α) → List α → Prop
  | done {ls : List (List α)} (h : ∀ l ∈ ls, l = []) : Interleave ls []
  | step {ls : List (List α)} {k : Nat} {x : α} {rest : List α} {out : List α}
      (hk : ls[k]? = some (x :: rest)) (h : Interleave (ls.set k rest) out) :
      Interleave ls (x :: out)

/-- Every step of an interleaving comes from one of its sources. -/
theorem Interleave.mem {α : Type} {ls : List (List α)} {h : List α} (hi : Interleave ls h) :
    ∀ x ∈ h, ∃ l ∈ ls, x ∈ l := by
  induction hi with
  | done _ => intro x hx; exact absurd hx List.not_mem_nil
  | step hk _ ih =>
      intro y hy
      have hsrc := List.mem_of_getElem? hk
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, hsrc, List.mem_cons_self ..⟩
      · obtain ⟨l, hl, hyl⟩ := ih y hy
        rcases List.mem_or_eq_of_mem_set hl with hl | rfl
        · exact ⟨l, hl, hyl⟩
        · exact ⟨_, hsrc, List.mem_cons_of_mem _ hyl⟩

/-- Taking the head of source `k` is a permutation step on the flattening. -/
theorem flatten_set_perm {α : Type} :
    ∀ (ls : List (List α)) (k : Nat) {x : α} {rest : List α},
      ls[k]? = some (x :: rest) → ls.flatten.Perm (x :: (ls.set k rest).flatten) := by
  intro ls
  induction ls with
  | nil => intro k x rest hk; simp at hk
  | cons l ls ih =>
      intro k x rest hk
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          simp only [List.set_cons_zero, List.flatten_cons, List.cons_append]
          exact List.Perm.refl _
      | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          simp only [List.set_cons_succ, List.flatten_cons]
          exact ((ih k hk).append_left l).trans List.perm_middle

/-- **An interleaving is a permutation of its sources**: no step is dropped,
duplicated, or moved out of its source's order. -/
theorem Interleave.perm_flatten {α : Type} {ls : List (List α)} {h : List α}
    (hi : Interleave ls h) : h.Perm ls.flatten := by
  induction hi with
  | done hd =>
      rw [List.flatten_eq_nil_iff.mpr hd]
  | step hk _ ih =>
      exact (ih.cons _).trans (flatten_set_perm _ _ hk).symm

/-- Adding an exhausted source does not change what can be interleaved. -/
theorem Interleave.cons_nil {α : Type} {ls : List (List α)} {h : List α}
    (hi : Interleave ls h) : Interleave ([] :: ls) h := by
  induction hi with
  | done hd =>
      refine Interleave.done ?_
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · rfl
      · exact hd l hl
  | step hk _ ih =>
      exact Interleave.step (k := _ + 1) (by simpa using hk) (by simpa using ih)

/-- Running one source to completion first is a valid schedule. -/
theorem Interleave.prefix {α : Type} {ls : List (List α)} {h : List α}
    (hi : Interleave ([] :: ls) h) : ∀ l : List α, Interleave (l :: ls) (l ++ h) := by
  intro l
  induction l with
  | nil => simpa using hi
  | cons x l ih =>
      exact Interleave.step (k := 0) (x := x) (rest := l) rfl ih

/-- **Non-vacuity certificate.** Every family of traces has an interleaving: run
the sources one after another. -/
theorem Interleave.flatten {α : Type} : ∀ ls : List (List α), Interleave ls ls.flatten := by
  intro ls
  induction ls with
  | nil => exact Interleave.done (fun _ h => absurd h List.not_mem_nil)
  | cons l ls ih =>
      simp only [List.flatten_cons]
      exact ih.cons_nil.prefix l

/-! ## Runs and sequential histories -/

/-- Run a step sequence from a state. -/
def runSteps {σ : Type} (h : List (Step σ)) (s : σ) : σ := h.foldl (fun a x => x.eff a) s

/-- The **sequential history** of a run: its linearization points, in order. -/
def lps {σ : Type} (h : List (Step σ)) : List (Step σ) := h.filter (·.lp)

theorem lps_append {σ : Type} (h1 h2 : List (Step σ)) : lps (h1 ++ h2) = lps h1 ++ lps h2 :=
  List.filter_append h1 h2

/-- Framing steps drop out of a run: running `h` is running its LPs. This is the
whole content of the state equation; it needs only that every non-LP step is an
identity. -/
theorem runSteps_eq_lps_of_frame {σ : Type} :
    ∀ (h : List (Step σ)), (∀ x ∈ h, x.lp = false → ∀ s, x.eff s = s) →
      ∀ s, runSteps h s = runSteps (lps h) s := by
  intro h
  induction h with
  | nil => intro _ _; rfl
  | cons x h ih =>
      intro hfr s
      have hrest : ∀ y ∈ h, y.lp = false → ∀ s, y.eff s = s :=
        fun y hy => hfr y (List.mem_cons_of_mem x hy)
      simp only [runSteps, lps, List.filter_cons, List.foldl_cons]
      cases hlp : x.lp with
      | true => simpa [runSteps, lps] using ih hrest (x.eff s)
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hfr x (List.mem_cons_self ..) hlp s]
          exact ih hrest s

/-- The LPs of one operation's trace: exactly its commit. -/
theorem lps_steps {σ : Type} {P Q : σ → Prop} (i : Nat) (t : LAT P Q) :
    lps (t.steps i) = [⟨i, t.commit, true⟩] := by
  have hpre : ∀ l : List (σ → σ),
      (l.map (fun f => (⟨i, f, false⟩ : Step σ))).filter (·.lp) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons f l ih => simpa [List.filter_cons] using ih
  simp only [lps, LAT.steps, List.filter_append, hpre, List.filter_cons, List.nil_append]
  rfl

/-- The LPs of a family's traces run in sequence are its canonical history. -/
theorem lps_flatten_stepsFrom {σ : Type} (n : Nat) (os : List (AtomicOp σ)) :
    lps (stepsFrom n os).flatten = lpsFrom n os := by
  induction os generalizing n with
  | nil => rfl
  | cons o os ih =>
      simp only [stepsFrom, List.flatten_cons, lpsFrom]
      rw [lps_append, lps_steps, ih]
      rfl

/-! ## Linearizability at the abstract state -/

/-- **Linearizability at the abstract state.** For a family `os` of logically-atomic
operations and **any** interleaving `h` of their traces:
1. the concurrent run ends where its sequential history `lps h` ends;
2. the sequential history contains **exactly one LP per operation** — its
   op-indices are a permutation of `0 … |os|-1` (no lost, no doubled operation);
3. every LP in the history **is** the commit of the operation it is tagged with. -/
theorem linearizable_abstract {σ : Type} (os : List (AtomicOp σ)) {h : List (Step σ)}
    (hi : Interleave (stepsFrom 0 os) h) :
    (∀ s, runSteps h s = runSteps (lps h) s) ∧
    ((lps h).map (·.op)).Perm (List.range' 0 os.length) ∧
    (∀ x ∈ lps h, ∃ k, ∃ hk : k < os.length, x.op = k ∧ x.eff = os[k].t.commit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    refine runSteps_eq_lps_of_frame h ?_ s
    intro x hx
    obtain ⟨l, hl, hxl⟩ := hi.mem x hx
    obtain ⟨k, hk, rfl⟩ := mem_stepsFrom 0 os l hl
    exact (os[k]).t.steps_frame _ x hxl
  · have hp : (lps h).Perm (lpsFrom 0 os) := by
      have := (hi.perm_flatten).filter (·.lp)
      rw [← lps, ← lps, lps_flatten_stepsFrom] at this
      exact this
    rw [← lpsFrom_ops]
    exact hp.map _
  · intro x hx
    have hxh : x ∈ h := (List.mem_filter.mp hx).1
    have hlp : x.lp = true := (List.mem_filter.mp hx).2
    obtain ⟨l, hl, hxl⟩ := hi.mem x hxh
    obtain ⟨k, hk, rfl⟩ := mem_stepsFrom 0 os l hl
    have := (os[k]).t.steps_lp _ x hxl hlp
    subst this
    exact ⟨k, hk, by simp, rfl⟩

/-- **Legality at the LP.** Each LP of the sequential history takes its operation's
precondition to its postcondition: if `P_k` holds when operation `k`'s LP fires,
`Q_k` holds after it. -/
theorem history_legal {σ : Type} (os : List (AtomicOp σ)) {h : List (Step σ)}
    (hi : Interleave (stepsFrom 0 os) h) :
    ∀ x ∈ lps h, ∃ k, ∃ hk : k < os.length,
      x.op = k ∧ ∀ s, os[k].P s → os[k].Q (x.eff s) := by
  intro x hx
  obtain ⟨k, hk, hop, heff⟩ := (linearizable_abstract os hi).2.2 x hx
  refine ⟨k, hk, hop, fun s hP => ?_⟩
  rw [heff]
  exact (os[k]).t.commits s hP

/-- **Real-time order.** If every step of operation `i` precedes every step of
operation `j` in the run (`h = h1 ++ h2`, no `i`-step in `h2`, no `j`-step in
`h1`), then `i`'s LP precedes `j`'s in the sequential history. -/
theorem realtime_order {σ : Type} (h1 h2 : List (Step σ)) (i j : Nat)
    (hi : ∀ x ∈ h2, x.op ≠ i) (hj : ∀ x ∈ h1, x.op ≠ j) :
    lps (h1 ++ h2) = lps h1 ++ lps h2 ∧
    (∀ x ∈ lps h1, x.op ≠ j) ∧ (∀ x ∈ lps h2, x.op ≠ i) :=
  ⟨lps_append h1 h2,
   fun x hx => hj x (List.mem_filter.mp hx).1,
   fun x hx => hi x (List.mem_filter.mp hx).1⟩

/-! ## Consumer: two Treiber pushes under any interleaving -/

/-- A Treiber push as an abstract operation: read the head and allocate the node
(framing), then the `CAS` that installs it (the LP, effect `v :: ·`). Precondition
trivial; postcondition: `v` is on top right after the LP. -/
def pushOp (v : Val) : AtomicOp (List Val) where
  P := fun _ => True
  Q := fun s => s.head? = some v
  t := { pre := [id, id]
         commit := (v :: ·)
         post := []
         pre_frame := by
           intro f hf s
           simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
           rcases hf with rfl | rfl <;> rfl
         post_frame := fun _ hf => absurd hf List.not_mem_nil
         commits := fun _ _ => rfl }

/-- A history whose op-indices are a permutation of `[0, 1]` is two steps, one of
each op. -/
theorem two_lps {σ : Type} {l : List (Step σ)} (hp : (l.map (·.op)).Perm [0, 1]) :
    ∃ x y, l = [x, y] ∧ ((x.op = 0 ∧ y.op = 1) ∨ (x.op = 1 ∧ y.op = 0)) := by
  have hlen : l.length = 2 := by simpa using hp.length_eq
  match l, hlen with
  | [x, y], _ =>
      refine ⟨x, y, rfl, ?_⟩
      have h0 : 0 ∈ [x.op, y.op] := hp.mem_iff.mpr (by simp)
      have h1 : 1 ∈ [x.op, y.op] := hp.mem_iff.mpr (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h1
      omega

/-- **Two concurrent pushes, through the general theorem.** Whatever the scheduler
does with the two three-step traces, the stack ends as `v2 :: v1 :: xs` (push 1
linearized first) or `v1 :: v2 :: xs` (push 2 first) — never anything else, never
a lost push. -/
theorem two_pushes_linearize (v1 v2 : Val) (xs : List Val) {h : List (Step (List Val))}
    (hi : Interleave (stepsFrom 0 [pushOp v1, pushOp v2]) h) :
    runSteps h xs = v2 :: v1 :: xs ∨ runSteps h xs = v1 :: v2 :: xs := by
  obtain ⟨heq, hperm, hcommit⟩ := linearizable_abstract _ hi
  obtain ⟨x, y, hl, hcase⟩ := two_lps (by simpa using hperm)
  rw [heq, hl]
  obtain ⟨kx, hkx, hopx, heffx⟩ := hcommit x (by rw [hl]; simp)
  obtain ⟨ky, hky, hopy, heffy⟩ := hcommit y (by rw [hl]; simp)
  rcases hcase with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hkx0 : kx = 0 := hopx.symm.trans h0
    have hky1 : ky = 1 := hopy.symm.trans h1
    subst hkx0 hky1
    left
    simp only [runSteps, List.foldl_cons, List.foldl_nil, heffx, heffy]
    rfl
  · have hkx1 : kx = 1 := hopx.symm.trans h0
    have hky0 : ky = 0 := hopy.symm.trans h1
    subst hkx1 hky0
    right
    simp only [runSteps, List.foldl_cons, List.foldl_nil, heffx, heffy]
    rfl

end LeanliftIris.PhaseC
