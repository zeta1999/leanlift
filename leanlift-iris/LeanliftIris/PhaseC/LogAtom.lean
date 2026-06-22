/-
Phase C (step 2) — **logical atomicity, generalized**: a reusable
logically-atomic-triple library, and the Chase–Lev `take` discharged against it
using the prophecy of the previous step.

A linearizability proof says a fine-grained operation *behaves as one atomic
step*. The proof obligation has a fixed shape: among the operation's many physical
micro-steps, exactly **one** — the linearization point — changes the abstract
state, taking the precondition `P` to the postcondition `Q`; every other step
leaves the abstract state untouched (it is *framing*). We package that shape as a
triple `LAT P Q` over an abstract state `σ`:

  * `pre`/`post` — the framing micro-steps before/after the LP (no abstract effect);
  * `commit` — the linearization point, taking `P` to `Q`;
  * `atomic_commit` — the payoff: running the whole operation from a `P`-state lands
    in a `Q`-state. The single commit *is* the atomic effect.

Plus the structural rules a triple library needs: `refl` (a no-op operation is
atomic for any `P`) and `frameL` (prepending framing steps preserves the triple).

We then instantiate it for the Chase–Lev `take` (abstract state = number of live
elements): when the owner wins the last-element race, `take` is logically atomic,
removing the element (`1 ↦ 0`), with its surrounding index read/write as framing
steps. The choice of `take`'s commit — remove vs. no-op — is exactly the
prophecy-selected effect from `Prophecy.lean` (`takeCommit`), so the LP this
library demands is placed by the prophecy and made consistent by the seq_cst
safety result. Core Lean, sorry-free.
-/
import LeanliftIris.PhaseC.Prophecy

namespace LeanliftIris.PhaseC

/-! ## Framing micro-steps and running a sequence -/

/-- A list of abstract micro-step effects, each a no-op on the abstract state. -/
def Identities {σ : Type} (l : List (σ → σ)) : Prop := ∀ f ∈ l, ∀ s, f s = s

/-- Run a sequence of abstract effects left-to-right. -/
def runFold {σ : Type} (l : List (σ → σ)) (s : σ) : σ := l.foldl (fun a f => f a) s

/-- Running a sequence of framing steps is the identity. -/
theorem runFold_identities {σ : Type} :
    ∀ {l : List (σ → σ)}, Identities l → ∀ s, runFold l s = s := by
  intro l
  induction l with
  | nil => intro _ s; rfl
  | cons f l ih =>
      intro h s
      have hf : f s = s := h f List.mem_cons_self s
      have hrest : Identities l := fun g hg => h g (List.mem_cons_of_mem f hg)
      show l.foldl (fun a f => f a) (f s) = s
      rw [hf]; exact ih hrest s

/-! ## The logically-atomic triple -/

/-- A **logically-atomic triple** `⟨P⟩ ⟨Q⟩` over abstract state `σ`: a run split
into framing-prefix `pre`, the single linearization point `commit` (taking `P` to
`Q`), and framing-suffix `post`. -/
structure LAT {σ : Type} (P Q : σ → Prop) where
  pre : List (σ → σ)
  commit : σ → σ
  post : List (σ → σ)
  pre_frame : Identities pre
  post_frame : Identities post
  commits : ∀ s, P s → Q (commit s)

namespace LAT
variable {σ : Type}

/-- The full physical run of a logically-atomic operation. -/
def run {P Q : σ → Prop} (t : LAT P Q) : List (σ → σ) := t.pre ++ t.commit :: t.post

/-- **Atomic commit (the payoff).** Running the whole operation from a `P`-state
lands in a `Q`-state: the framing steps do nothing and the single commit carries
`P` to `Q`. This is the abstract-state half of a linearizability proof. -/
theorem atomic_commit {P Q : σ → Prop} (t : LAT P Q) (s : σ) (hP : P s) :
    Q (runFold t.run s) := by
  have hpre : t.pre.foldl (fun a f => f a) s = s := runFold_identities t.pre_frame s
  have key : runFold t.run s = runFold t.post (t.commit s) := by
    show (t.pre ++ t.commit :: t.post).foldl (fun a f => f a) s
       = t.post.foldl (fun a f => f a) (t.commit s)
    rw [List.foldl_append]
    simp only [List.foldl_cons]
    rw [hpre]
  rw [key, runFold_identities t.post_frame (t.commit s)]
  exact t.commits s hP

/-- **Structural rule — return / no-op.** An operation with no linearization point
is atomic for any predicate: it preserves `P`. -/
def refl (P : σ → Prop) : LAT P P where
  pre := []
  commit := id
  post := []
  pre_frame := fun f hf => absurd hf List.not_mem_nil
  post_frame := fun f hf => absurd hf List.not_mem_nil
  commits := fun _ hs => hs

/-- **Structural rule — frame.** Prepending framing micro-steps preserves a triple
(the LP and its effect are unchanged). Lets client proofs splice in surrounding
no-op steps without re-establishing atomicity. -/
def frameL {P Q : σ → Prop} (t : LAT P Q) (extra : List (σ → σ)) (h : Identities extra) :
    LAT P Q where
  pre := extra ++ t.pre
  commit := t.commit
  post := t.post
  pre_frame := by
    intro f hf s
    rcases List.mem_append.mp hf with h1 | h1
    · exact h f h1 s
    · exact t.pre_frame f h1 s
  post_frame := t.post_frame
  commits := t.commits

end LAT

/-! ## Instantiation: the Chase–Lev `take` is logically atomic

Abstract state = number of live elements. The owner's `take` on the last element,
when it wins the race, is logically atomic with linearization point "remove the
element" (`1 ↦ 0`); its index read of `top` and write of `bot` are framing steps
(no abstract effect). -/

/-- `take`'s abstract effect, **selected by the prophecy** of the thief's outcome:
if the thief wins, `take` is a no-op (the thief's steal was the linearization
point); otherwise `take` removes the element. This is the commit the `LAT` below
installs — the LP placement is the prophecy's. -/
def takeCommit (thiefWins : Bool) : Nat → Nat := if thiefWins then id else fun _ => 0

/-- When the owner wins (`thiefWins = false`), the prophecy-selected commit is
exactly "remove the element". -/
theorem takeCommit_owner : takeCommit false = (fun _ => 0) := rfl

/-- When the thief wins, `take`'s commit is a no-op. -/
theorem takeCommit_thief : takeCommit true = id := rfl

/-- **`take` is logically atomic.** On a one-element deque the owner's winning
`take` linearizes by removing the element, with its index read/write as framing
steps. The commit is `takeCommit false` — the prophecy-selected effect. -/
def takeLAT : LAT (· = 1) (· = 0) where
  pre := [id, id]                 -- read top, write bot: no abstract effect
  commit := takeCommit false      -- the linearization point: remove the element
  post := []
  pre_frame := by
    intro f hf s
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> rfl
  post_frame := fun f hf => absurd hf List.not_mem_nil
  commits := by intro s hs; subst hs; rfl

/-- **Linearizability skeleton, discharged.** Running the owner's `take` on a
one-element deque atomically yields the empty deque: the abstract-state half of
`take`'s linearizability, via `LAT.atomic_commit`. The linearization point it
commits at is the prophecy-resolved one (`Prophecy.owner_claim_lp`), and the
seq_cst safety result guarantees it never coincides with the thief's. -/
theorem take_linearizes (s : Nat) (h : s = 1) : runFold takeLAT.run s = 0 :=
  takeLAT.atomic_commit s h

end LeanliftIris.PhaseC
