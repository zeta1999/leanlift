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

end LeanliftIris.PhaseC
