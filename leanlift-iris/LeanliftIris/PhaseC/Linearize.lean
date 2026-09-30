/-
Phase C (step 6) — **linearizability from logical atomicity**, and the remaining
structural rules of the triple library.

`LogAtom.lean` packages one operation as a logically-atomic triple `LAT P Q`: a
run with exactly one linearization point (LP). `WpAtomic.lean` grounds such
triples in the real `wp` (`Realizes`, `lat_realized`). What neither says is the
thing "logical atomicity" is *for*: that a **concurrent** execution of several
such operations, under **any** scheduler, behaves like a **sequential** history of
their LPs. This file proves it, in core Lean over the abstract state:

  * `Interleave ls h` — `h` is an interleaving of the sequences `ls` (any
    scheduler: at each step pick any non-empty sequence and take its head);
  * `LAT.steps i t` — an operation's micro-steps, tagged by operation index and
    by whether the step is its LP; the non-LP steps are framing (identities);
  * **`linearize`** — for any interleaving `h` of the step sequences of a family
    of logically-atomic operations, running `h` from any state ends in the state
    reached by running **only the LPs, in the order they occur in `h`**. That
    order is the *sequential history*; the concurrent run is indistinguishable
    from it at the abstract state. This is the abstract-state half of
    linearizability for a whole system, generalising `A4`'s single-operation
    skeleton to any number of operations under any interleaving.
  * `two_pushes_linearize` — the day-one consumer: any interleaving of two
    Treiber pushes ends in `v1 :: v2 :: xs` or `v2 :: v1 :: xs`, nothing else.

Structural rules the library was missing: `LAT.frameR` (append framing steps),
`LAT.conseq` (strengthen `P`, weaken `Q`), and `Realizes.seq` (sequential
composition of two realizing programs realizes the composed effect — through the
real `wp`, via `wp_seq`).

**Scope limit, stated:** this is linearizability at the *abstract* state. Tying
the interleaving to the real thread-pool `steps` of *concurrently* running `wp`
proofs — an Iris-style atomic triple `<<< α >>> e <<< β >>>` that lets a client
open an invariant around another thread's LP — needs `fupd` inside `wp`, and
`PLAN-fupd.md` records that `ownE ⊤` is unrepresentable with the `GenMap` mask
tokens, so `fupd` cannot be wired into `wp`/adequacy without changing the mask
representation. `atomic_acc` (`Fupd/Inv.lean`) makes such triples *expressible*;
proving programs against them is blocked on that representation, not on this
library. Sorry-free.
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
binder `"_"`, as `wp_seq` requires.) -/
theorem Realizes.seq {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))] {σ : Type}
    (γ : GName) [HasHeap γ GF F] {repr : σ → IProp GF} {f g : σ → σ} {e1 e2 : Expr}
    (h1 : Realizes (F := F) γ repr f e1) (h2 : Realizes (F := F) γ repr g e2)
    (hcl : ∀ w : Val, substE "_" w e2 = e2) :
    Realizes (F := F) γ repr (g ∘ f) (.app (.val (.clos "_" "_" e2)) e1) := by
  intro s
  refine ((h1 s).trans (wp_mono γ e1 _ _ (fun _ => ?_))).trans (wp_seq γ e1 e2 _ hcl)
  exact (h2 (f s)).trans later_intro

/-! ## Tagged micro-steps and interleavings -/

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

/-- **Interleaving under any scheduler.** `Interleave ls h`: `h` is obtained from
the sequences `ls` by repeatedly picking *any* sequence that still has steps and
taking its head. No fairness, no ordering constraint between sequences: every
schedule is admitted. -/
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

/-! ## Linearizability -/

/-- Run a step sequence from a state. -/
def runSteps {σ : Type} (h : List (Step σ)) (s : σ) : σ := h.foldl (fun a x => x.eff a) s

/-- The **sequential history** of a run: its linearization points, in order. -/
def lps {σ : Type} (h : List (Step σ)) : List (Step σ) := h.filter (·.lp)

/-- Framing steps drop out of a run: running `h` is running its LPs. -/
theorem runSteps_lps {σ : Type} :
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

/-- **Linearizability (abstract state).** Take any family of logically-atomic
operations, given as their tagged step sequences (every non-LP step framing), and
**any** interleaving `h` of them. Running `h` from any state `s` ends exactly where
running the LPs alone, in the order they occur in `h`, ends. So the concurrent
execution is equivalent, at the abstract state, to the sequential history `lps h`:
each operation takes effect at a single instant, its LP, and nowhere else. -/
theorem linearize {σ : Type} (ops : List (List (Step σ)))
    (hfr : ∀ l ∈ ops, ∀ x ∈ l, x.lp = false → ∀ s, x.eff s = s)
    {h : List (Step σ)} (hi : Interleave ops h) (s : σ) :
    runSteps h s = runSteps (lps h) s := by
  refine runSteps_lps h ?_ s
  intro x hx
  obtain ⟨l, hl, hxl⟩ := hi.mem x hx
  exact hfr l hl x hxl

/-- The same, with the operations given as triples. -/
theorem linearize_lat {σ : Type} {P Q : σ → Prop} (ts : List (LAT P Q))
    {h : List (Step σ)} (hi : Interleave (ts.mapIdx fun i t => t.steps i) h) (s : σ) :
    runSteps h s = runSteps (lps h) s := by
  refine linearize _ ?_ hi s
  intro l hl
  obtain ⟨i, hi', hl⟩ := List.mem_mapIdx.mp hl
  subst hl
  exact (ts[i]).steps_frame i

/-! ## Consumer: two Treiber pushes under any interleaving -/

/-- An interleaving of two one-step sequences is one of the two orders. -/
theorem Interleave.two {α : Type} {a b : α} {h : List α}
    (hi : Interleave [[a], [b]] h) : h = [a, b] ∨ h = [b, a] := by
  cases hi with
  | done hd => exact absurd (hd [a] (by simp)) (by simp)
  | @step _ k x rest out hk h2 =>
      match k, hk with
      | 0, hk =>
          simp at hk
          obtain ⟨rfl, rfl⟩ := hk
          cases h2 with
          | done hd => exact absurd (hd [b] (by simp)) (by simp)
          | @step _ k2 y rest2 out2 hk2 h3 =>
              match k2, hk2 with
              | 0, hk2 => simp at hk2
              | 1, hk2 =>
                  simp at hk2
                  obtain ⟨rfl, rfl⟩ := hk2
                  cases h3 with
                  | done _ => exact Or.inl rfl
                  | @step _ k3 _ _ _ hk3 _ =>
                      match k3, hk3 with
                      | 0, hk3 => simp at hk3
                      | 1, hk3 => simp at hk3
                      | k3 + 2, hk3 => simp at hk3
              | k2 + 2, hk2 => simp at hk2
      | 1, hk =>
          simp at hk
          obtain ⟨rfl, rfl⟩ := hk
          cases h2 with
          | done hd => exact absurd (hd [a] (by simp)) (by simp)
          | @step _ k2 y rest2 out2 hk2 h3 =>
              match k2, hk2 with
              | 0, hk2 =>
                  simp at hk2
                  obtain ⟨rfl, rfl⟩ := hk2
                  cases h3 with
                  | done _ => exact Or.inr rfl
                  | @step _ k3 _ _ _ hk3 _ =>
                      match k3, hk3 with
                      | 0, hk3 => simp at hk3
                      | 1, hk3 => simp at hk3
                      | k3 + 2, hk3 => simp at hk3
              | 1, hk2 => simp at hk2
              | k2 + 2, hk2 => simp at hk2
      | k + 2, hk => simp at hk

/-- **Two concurrent pushes.** Whatever the scheduler does, the stack ends as
`v2 :: v1 :: xs` (push 1 linearized first) or `v1 :: v2 :: xs` (push 2 first) —
never anything else, never a lost push. The LP order *is* the sequential history. -/
theorem two_pushes_linearize (v1 v2 : Val) (xs : List Val) {h : List (Step (List Val))}
    (hi : Interleave [(pushAbstract v1 xs).steps 0, (pushAbstract v2 xs).steps 1] h) :
    runSteps h xs = v2 :: v1 :: xs ∨ runSteps h xs = v1 :: v2 :: xs := by
  have hsteps : ∀ (v : Val) (i : Nat),
      (pushAbstract v xs).steps i = [⟨i, (v :: ·), true⟩] := fun _ _ => rfl
  rw [hsteps, hsteps] at hi
  rcases hi.two with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end LeanliftIris.PhaseC
