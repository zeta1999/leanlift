/-
Phase C (step 5) — bridging the abstract logically-atomic triple to the **real
`wp`**.

`LogAtom.lean` defined a logically-atomic triple `LAT P Q` abstractly (a run of
abstract micro-steps with one commit). The integration obligation
(`PLAN-concurrency.md` C1) is to connect that abstraction to the *actual* program
logic — the iris-lean `wp` over `λ-conc` from Phase A — so the commit is realized
by a verified step of real code, not just an abstract effect.

This file does exactly that for Treiber `push` (`#7`):

  * `HoareTriple` — a wp Hoare triple `{P} e {Q}` over `λ-conc`, with the
    structural rules `hoare_value` / `hoare_mono` / `hoare_conseq` lifted from the
    Phase-A `wp` lemmas (the reusable C1 layer over the real logic).
  * `hoare_push_cas` — the **linearization point** as a Hoare triple: the single
    `CAS` step atomically takes the abstract stack `xs` to `v :: xs`
    (from `push_cas_step`).
  * `pushAbstract` — the abstract LIFO push as a core-Lean `LAT` (commit `v :: ·`).
  * `push_realizes_commit` — **the bridge**: Treiber `push`'s verified `wp` proof
    establishes exactly the abstract `LAT`'s commit on the heap-level stack
    predicate — `{isStack γ s xs} push {isStack γ s ((pushAbstract v xs).commit xs)}`.
    The abstract linearization point of `LAT` is realized by the real program.

So the logically-atomic spec (abstract, core Lean) and the verified `wp` proof
(concrete, iris-lean) name the *same* atomic effect. Sorry-free.
-/
import LeanliftIris.PhaseA.Treiber
import LeanliftIris.PhaseC.LogAtom

namespace LeanliftIris.PhaseC
open Iris Iris.BI COFE LeanliftIris.PhaseA

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-! ## A wp Hoare triple over `λ-conc` and its structural rules -/

/-- A Hoare triple `{P} e {Q}` over `λ-conc`: the precondition resource `P`
entails the weakest precondition of `e` for postcondition `Q`. -/
def HoareTriple (γ : GName) [HasHeap γ GF F] (P : IProp GF) (e : Expr)
    (Q : Val → IProp GF) : Prop :=
  P ⊢ wp (F := F) γ e Q

/-- **Value rule.** `{Q v} (val v) {Q}`. -/
theorem hoare_value (γ : GName) [HasHeap γ GF F] (v : Val) (Q : Val → IProp GF) :
    HoareTriple (F := F) γ (Q v) (.val v) Q := by
  show Q v ⊢ wp (F := F) γ (.val v) Q
  iintro H
  iapply wp_value
  iintro !>
  iexact H

/-- **Rule of consequence on the postcondition** (monotonicity). -/
theorem hoare_mono (γ : GName) [HasHeap γ GF F] {P : IProp GF} {e : Expr}
    {Q Q' : Val → IProp GF} (h : HoareTriple (F := F) γ P e Q)
    (hQ : ∀ v, Q v ⊢ Q' v) : HoareTriple (F := F) γ P e Q' :=
  h.trans (wp_mono γ e Q Q' hQ)

/-- **Full rule of consequence:** strengthen the precondition, weaken the
postcondition. -/
theorem hoare_conseq (γ : GName) [HasHeap γ GF F] {P P' : IProp GF} {e : Expr}
    {Q Q' : Val → IProp GF} (hP : P' ⊢ P) (h : HoareTriple (F := F) γ P e Q)
    (hQ : ∀ v, Q v ⊢ Q' v) : HoareTriple (F := F) γ P' e Q' :=
  hP.trans (h.trans (wp_mono γ e Q Q' hQ))

/-! ## The Treiber `push` linearization point as a Hoare triple -/

/-- **The linearization point, as a Hoare triple.** The single `CAS` of Treiber
`push` atomically takes the abstract stack `xs` to `v :: xs`: owning the cell, the
fresh node, and the list representation, the successful compare-and-swap
re-establishes `isStack` for the extended list. (Repackages `push_cas_step`.) -/
theorem hoare_push_cas (γ : GName) [HasHeap γ GF F] (s : Nat) (v hd : Val) (l : Nat)
    (xs : List Val) :
    HoareTriple (F := F) γ
      iprop((s ↦[γ] hd) ∗ (l ↦[γ] (.pair v hd)) ∗ listRep γ hd xs)
      (.cas (.val (.loc s)) (.val hd) (.val (.loc l)))
      (fun _ => isStack γ s (v :: xs)) :=
  push_cas_step γ s v hd l xs

/-! ## The bridge: the abstract `LAT` commit is realized by the real `wp` -/

/-- The abstract LIFO push as a core-Lean logically-atomic triple: it commits the
abstract stack `xs0` to `v :: xs0`, with no framing micro-steps in this abstract
view (the heap-level read/alloc are realized inside the `wp` proof). -/
def pushAbstract (v : Val) (xs0 : List Val) : LAT (· = xs0) (· = v :: xs0) where
  pre := []
  commit := (v :: ·)
  post := []
  pre_frame := fun _ hf => absurd hf List.not_mem_nil
  post_frame := fun _ hf => absurd hf List.not_mem_nil
  commits := fun _ hs => by rw [hs]

/-- **Realization — the bridge.** Treiber `push`'s verified `wp` proof establishes
exactly the abstract `LAT`'s commit on the heap-level stack predicate: from a heap
representing the stack `xs`, running `push` ends in a heap representing
`(pushAbstract v xs).commit xs` (= `v :: xs`). So the abstract logically-atomic
linearization point and the concrete iris-lean `wp` proof name the *same* atomic
effect — the C1 abstraction is grounded in the real program logic.

(`hclv`/`hclhd`: the pushed value and the old head are closed under substitution —
the standard side-condition of `push_body_spec`, automatic for closed values.) -/
theorem push_realizes_commit (γ : GName) [HasHeap γ GF F] (s : Nat) (v hd : Val)
    (xs : List Val)
    (hclv : ∀ (x : String) (w : Val), substV x w v = v)
    (hclhd : ∀ (x : String) (w : Val), substV x w hd = hd) :
    HoareTriple (F := F) γ
      iprop((s ↦[γ] hd) ∗ listRep γ hd xs)
      (pushBody s v)
      (fun _ => isStack γ s ((pushAbstract v xs).commit xs)) :=
  push_body_spec γ s v hd xs hclv hclhd

/-! ## The general bridge: realizing an abstract commit on a representation

`push_realizes_commit` grounds *one* operation. To generalize beyond `push` we
abstract the pattern: a representation predicate `repr : σ → IProp` reflecting the
abstract state `σ` into the heap, and a program `e` that *realizes* an abstract
effect `f : σ → σ` — from any heap representing `s`, running `e` ends in a heap
representing `f s`. This is the operation-agnostic interface between the abstract
`LAT` library and the real `wp`. -/

/-- **Realization.** Program `e` realizes the abstract effect `f` on
representation `repr`: from any heap representing the abstract state `s`, running
`e` lands in a heap representing `f s`. (Postcondition ignores the return value —
what matters is the abstract-state transformation.) -/
def Realizes {σ : Type} (γ : GName) [HasHeap γ GF F] (repr : σ → IProp GF)
    (f : σ → σ) (e : Expr) : Prop :=
  ∀ s, repr s ⊢ wp (F := F) γ e (fun _ => repr (f s))

/-- **Consequence for realization.** A program realizing `f` on `repr` also
realizes it after weakening the representation pointwise. -/
theorem realizes_mono {σ : Type} (γ : GName) [HasHeap γ GF F]
    {repr repr' : σ → IProp GF} {f : σ → σ} {e : Expr}
    (h : Realizes (F := F) γ repr f e) (hr : ∀ s, repr s ⊢ repr' s)
    (hr' : ∀ s, repr' s ⊢ repr s) : Realizes (F := F) γ repr' f e := by
  intro s
  exact (hr' s).trans ((h s).trans (wp_mono γ e _ _ (fun _ => hr (f s))))

/-- **The general bridge.** Given a logically-atomic triple `t : LAT P Q` and a
program `e` that realizes its commit on a representation `repr`, the real `wp`
establishes the *abstract* postcondition `Q` at the representation level: from a
heap representing a `P`-state, running `e` ends in a heap representing some
`Q`-state. The abstract LP of `LAT` (core Lean) and the verified `wp` proof
(iris-lean) name the same atomic effect — for *any* operation, not just `push`. -/
theorem lat_realized {σ : Type} {P Q : σ → Prop} (t : LAT P Q)
    (γ : GName) [HasHeap γ GF F] (repr : σ → IProp GF) (e : Expr)
    (hreal : Realizes (F := F) γ repr t.commit e) (s : σ) (hP : P s) :
    repr s ⊢ wp (F := F) γ e (fun _ => iprop(∃ s', ⌜Q s'⌝ ∗ repr s')) := by
  refine (hreal s).trans (wp_mono γ e _ _ ?_)
  intro _
  iintro H
  iexists (t.commit s)
  isplitl []
  · ipure_intro; exact t.commits s hP
  · iexact H

/-! ## `push`, through the general bridge -/

/-- `push` realizes the abstract LIFO commit on the heap-level stack predicate
`isStack γ s` (head existentially bound — pushing rebinds it to the fresh node).
`hclosed` is the well-formedness side-condition that heap values are
substitution-closed; it holds for the first-order fragment (locs/ints/unit and
pairs thereof) that a stack actually stores. -/
theorem push_realizes (γ : GName) [HasHeap γ GF F] (s : Nat) (v : Val)
    (hclv : ∀ (x : String) (w : Val), substV x w v = v)
    (hclosed : ∀ (u : Val) (x : String) (w : Val), substV x w u = u) :
    Realizes (F := F) γ (isStack γ s) (v :: ·) (pushBody s v) := by
  intro xs
  show iprop(∃ hd, s ↦[γ] hd ∗ listRep γ hd xs) ⊢
      wp (F := F) γ (pushBody s v) (fun _ => isStack γ s (v :: xs))
  iintro ⟨%hd, Hs, Hrep⟩
  iapply (push_body_spec γ s v hd xs hclv (fun x w => hclosed hd x w))
  isplitl [Hs]
  · iexact Hs
  · iexact Hrep

/-- **End-to-end, through the general bridge.** From a stack holding `xs0`,
running `push` ends in a heap representing some list `ys` satisfying the abstract
postcondition `ys = v :: xs0` — `push`'s abstract `LAT` postcondition discharged
on the real `wp` via `lat_realized`. -/
theorem push_establishes_post (γ : GName) [HasHeap γ GF F] (s : Nat) (v : Val)
    (xs0 : List Val)
    (hclv : ∀ (x : String) (w : Val), substV x w v = v)
    (hclosed : ∀ (u : Val) (x : String) (w : Val), substV x w u = u) :
    isStack γ s xs0 ⊢
      wp (F := F) γ (pushBody s v)
        (fun _ => iprop(∃ ys, ⌜ys = v :: xs0⌝ ∗ isStack γ s ys)) :=
  lat_realized (pushAbstract v xs0) γ (isStack γ s) (pushBody s v)
    (push_realizes γ s v hclv hclosed) xs0 rfl

/-! ## A second operation through the bridge: Treiber `pop`

`pop` is *partial* — it removes the head, defined only on a non-empty stack — so
it does not fit the total `∀`-quantified `Realizes` wrapper the way `push` does.
It bridges through the per-state `LAT` + `HoareTriple` interface instead,
demonstrating the machinery handles a state-*shrinking* operation and validating
that the bridge is not push-specific. -/

/-- The abstract LIFO pop as a core-Lean logically-atomic triple: on a non-empty
abstract stack `x :: xs0` it commits to `xs0`, its linearization point being
`List.tail` (the head node's unlink). -/
def popAbstract (x : Val) (xs0 : List Val) : LAT (· = x :: xs0) (· = xs0) where
  pre := []
  commit := List.tail
  post := []
  pre_frame := fun _ hf => absurd hf List.not_mem_nil
  post_frame := fun _ hf => absurd hf List.not_mem_nil
  commits := fun _ hs => by subst hs; rfl

/-- **Realization — the bridge for `pop`.** Treiber `pop`'s verified `wp` proof
establishes exactly the abstract `LAT`'s commit on the heap-level stack predicate:
from a heap whose head node is `l ↦ (x, nxt)` over a tail representing `xs`,
running `pop` returns `x` and ends in a heap representing
`(popAbstract x xs).commit (x :: xs)` (= `List.tail (x :: xs)` = `xs`). The
abstract pop LP and the concrete iris-lean proof name the same atomic effect.
(Repackages `pop_body_spec`.) -/
theorem pop_realizes_commit (γ : GName) [HasHeap γ GF F] (s : Nat) (x nxt : Val)
    (l : Nat) (xs : List Val)
    (hclx : ∀ (y : String) (w : Val), substV y w x = x)
    (hclnxt : ∀ (y : String) (w : Val), substV y w nxt = nxt) :
    HoareTriple (F := F) γ
      iprop((s ↦[γ] (.loc l)) ∗ (l ↦[γ] (.pair x nxt)) ∗ listRep γ nxt xs)
      (popBody s)
      (fun r => iprop(⌜r = x⌝ ∗ isStack γ s ((popAbstract x xs).commit (x :: xs)))) :=
  pop_body_spec γ s x nxt l xs hclx hclnxt

end LeanliftIris.PhaseC
