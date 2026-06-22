/-
Phase A4 — Treiber lock-free stack (#7), the end-to-end demonstration.

The objective of this lane: take real lock-free code + annotations and prove
useful properties. Here we do exactly that for Treiber's `push`:

  * **code** — `push` encoded in `λ-conc` (the same `head = !s; node = alloc(v,
    head); CAS(s, head, node)` retry loop as the C++ corpus' `treiber_hazard.cpp`);
  * **annotation** — the separation-logic stack predicate `isStack γ s xs`
    (`s` points to a singly-linked list representing the Lean list `xs`);
  * **property** — `push` prepends: `isStack γ s xs ⊢ wp (push s v) {isStack γ s
    (v :: xs)}`, proved by composing the `wp` rules.

This is a *sequentially-consistent, single-owner* proof: owning `isStack` means
no other thread races, so the `CAS` succeeds on the first try (the retry branch
is dead). It establishes the full pipeline; the concurrent/linearizable version
is logical-atomicity work (Phase C). Sorry-free.
-/
import LeanliftIris.PhaseA.WpLifting

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-! ## Annotation: the stack representation predicate -/

/-- `listRep γ hd xs`: the heap from `hd` is a singly-linked list of nodes
`(value, next)` spelling out `xs`. The empty list is the `unit` sentinel (null);
a cons is a node `l ↦ (x, nxt)` with `hd = loc l` and `nxt` the tail. -/
def listRep (γ : GName) [HasHeap γ GF F] : Val → List Val → IProp GF
  | hd, []       => iprop(⌜hd = .unit⌝)
  | hd, (x :: xs) =>
      iprop(∃ (l : Nat) (nxt : Val), ⌜hd = .loc l⌝ ∗ l ↦[γ] (.pair x nxt) ∗ listRep γ nxt xs)

/-- `isStack γ s xs`: the stack cell `s` holds the head of a list representing
`xs`. -/
def isStack (γ : GName) [HasHeap γ GF F] (s : Nat) (xs : List Val) : IProp GF :=
  iprop(∃ hd, s ↦[γ] hd ∗ listRep γ hd xs)

/-! ## Code: `push` in `λ-conc`

`pushV` is the recursive closure; `pushBody s v` is its body with the location
`s` and value `v` already plugged in (what one beta-reduction of `pushV (loc s)
v` produces). We prove the spec of the body — the interesting part — directly. -/

/-- The recursive `push` closure (`push s v`, curried). -/
def pushV : Val :=
  .clos "push" "s" (.val (.clos "self" "v"
    (.app (.val (.clos "_" "head"
      (.app (.val (.clos "_" "node"
        (.ite (.cas (.var "s") (.var "head") (.var "node"))
              (.val .unit)
              (.app (.app (.var "self") (.var "s")) (.var "v")))))
        (.alloc (.pairE (.var "v") (.var "head"))))))
      (.load (.var "s")))))

/-- `push`'s body with `s := loc s` and `v := v` substituted in (and the retry
inlined as `unit`, which the single-owner proof never reaches). -/
def pushBody (s : Nat) (v : Val) : Expr :=
  .app (.val (.clos "_" "head"
    (.app (.val (.clos "_" "node"
      (.ite (.cas (.val (.loc s)) (.var "head") (.var "node"))
            (.val .unit)
            (.val .unit))))
      (.alloc (.pairE (.val v) (.var "head"))))))
    (.load (.val (.loc s)))

/-! ## Property: the linking CAS establishes the stack invariant

The heart of `push`: after reading the old head `hd` and allocating a node
`l ↦ (v, hd)`, the `CAS(s, hd, loc l)` (which succeeds because we own `s ↦ hd`)
re-establishes `isStack` for the extended list `v :: xs`. This is the lock-free
reasoning step + the annotation discharging the useful property. -/
theorem push_cas_step (γ : GName) [HasHeap γ GF F] (s : Nat) (v hd : Val) (l : Nat)
    (xs : List Val) :
    (s ↦[γ] hd) ∗ (l ↦[γ] (.pair v hd)) ∗ listRep γ hd xs ⊢
      wp (F := F) γ (.cas (.val (.loc s)) (.val hd) (.val (.loc l)))
        (fun _ => isStack γ s (v :: xs)) := by
  iintro ⟨Hs, Hnode, Hrep⟩
  iapply (wp_cas_suc γ s hd (.loc l) (fun _ => isStack γ s (v :: xs)))
  isplitl [Hs]
  · iexact Hs
  · iintro Hs'
    iintro !>
    simp only [isStack]
    iexists (.loc l)
    isplitl [Hs']
    · iexact Hs'
    · simp only [listRep]
      iexists l, hd
      isplitl []
      · ipure_intro; rfl
      · isplitl [Hnode]
        · iexact Hnode
        · iexact Hrep

end LeanliftIris.PhaseA
