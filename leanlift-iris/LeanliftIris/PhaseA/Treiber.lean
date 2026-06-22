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

/-- `push`'s body with `s := loc s` and `v := v` plugged in, in A-normal form
(every operation bound by a `let`, so the proof is a clean chain of `wp_let`s).
`let head = !s in let p = (v, head) in let node = alloc p in
 let b = CAS(s, head, node) in if b then () else ()`. The retry is inlined as
`()` (dead in the single-owner proof). -/
def pushBody (s : Nat) (v : Val) : Expr :=
  .app (.val (.clos "_" "head"
    (.app (.val (.clos "_" "p"
      (.app (.val (.clos "_" "node"
        (.app (.val (.clos "_" "b"
          (.ite (.var "b") (.val .unit) (.val .unit))))
          (.cas (.val (.loc s)) (.var "head") (.var "node")))))
        (.alloc (.var "p")))))
      (.pairE (.val v) (.var "head")))))
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

/-! ## Property: full `push` body — *push prepends*

The single end-to-end theorem: running `push`'s body (`head = !s; node =
alloc(v, head); CAS(s, head, node)`) on a stack holding `xs` yields a stack
holding `v :: xs`. Composes every rule: `wp_let`/`wp_bind` (sequencing),
`wp_load`, `wp_pair`, `wp_alloc`, `wp_cas_suc`, `wp_if_true`, `wp_value`. -/
theorem push_body_spec (γ : GName) [HasHeap γ GF F] (s : Nat) (v hd : Val) (xs : List Val)
    (hclv : ∀ (x : String) (w : Val), substV x w v = v)
    (hclhd : ∀ (x : String) (w : Val), substV x w hd = hd) :
    (s ↦[γ] hd) ∗ listRep γ hd xs ⊢
      wp (F := F) γ (pushBody s v) (fun _ => isStack γ s (v :: xs)) := by
  simp only [pushBody]
  iintro ⟨Hs, Hrep⟩
  -- let head = !s   (head ↦ hd)
  iapply wp_let
  iapply (wp_load γ s hd)
  isplitl [Hs]
  · iexact Hs
  · iintro Hs2
    iintro !>
    iintro !>
    simp [substE, substV, hclv, hclhd]
    -- let p = (v, hd)
    iapply wp_let
    iapply wp_pair
    iintro !>
    iapply wp_value
    iintro !>
    iintro !>
    simp [substE, substV, hclv, hclhd]
    -- let node = alloc (v, hd)
    iapply wp_let
    iapply (wp_alloc γ (.pair v hd))
    iintro %l Hnode
    iintro !>
    iintro !>
    simp [substE, substV, hclv, hclhd]
    -- let b = CAS(s, hd, loc l)
    iapply wp_let
    iapply (wp_cas_suc γ s hd (.loc l))
    isplitl [Hs2]
    · iexact Hs2
    · iintro Hs3
      iintro !>
      iintro !>
      simp [substE, substV, hclv, hclhd]
      -- if b (= true) then () else ()
      iapply wp_if_true
      iintro !>
      iapply wp_value
      iintro !>
      -- reassemble isStack γ s (v :: xs)
      simp only [isStack]
      iexists (.loc l)
      isplitl [Hs3]
      · iexact Hs3
      · simp only [listRep]
        iexists l, hd
        isplitl []
        · ipure_intro; rfl
        · isplitl [Hnode]
          · iexact Hnode
          · iexact Hrep

/-! ## Code + property: `pop` — *pop removes the head and returns it*

The dual of `push`: read the head `head = !s` (a node `loc l`), load the node
`node = !head` to get `(v, nxt)`, project out the value `v = fst node` and the
next pointer `nxt = snd node`, then `CAS(s, head, nxt)` to unlink it (succeeds in
the single-owner proof), returning `v`. On a stack holding `x :: xs` this returns
`x` and leaves a stack holding `xs`. The retry branch is inlined as `v` (dead).
This is the second lock-free operation, exercising the projection rules
`wp_fst`/`wp_snd` and validating the `wp` layer on a read-modify-return op. -/

/-- `pop`'s body with `s := loc s` plugged in, in A-normal form:
`let head = !s in let node = !head in let v = fst node in let nxt = snd node in
 let b = CAS(s, head, nxt) in if b then v else v`. -/
def popBody (s : Nat) : Expr :=
  .app (.val (.clos "_" "head"
    (.app (.val (.clos "_" "node"
      (.app (.val (.clos "_" "v"
        (.app (.val (.clos "_" "nxt"
          (.app (.val (.clos "_" "b"
            (.ite (.var "b") (.var "v") (.var "v"))))
            (.cas (.val (.loc s)) (.var "head") (.var "nxt")))))
          (.sndE (.var "node")))))
        (.fstE (.var "node")))))
      (.load (.var "head")))))
    (.load (.val (.loc s)))

/-- **`pop` removes the head and returns it.** From a stack whose head node is
`l ↦ (x, nxt)` and whose tail from `nxt` represents `xs`, running `pop` returns
`x` and re-establishes `isStack γ s xs`. Composes `wp_load` (twice), the new
projection rules `wp_fst`/`wp_snd`, `wp_cas_suc`, `wp_if_true`, `wp_value`.
(`hclx`/`hclnxt`: the popped value and the next pointer are substitution-closed —
the standard side-condition, automatic for the first-order heap fragment.) -/
theorem pop_body_spec (γ : GName) [HasHeap γ GF F] (s : Nat) (x nxt : Val) (l : Nat)
    (xs : List Val)
    (hclx : ∀ (y : String) (w : Val), substV y w x = x)
    (hclnxt : ∀ (y : String) (w : Val), substV y w nxt = nxt) :
    (s ↦[γ] (.loc l)) ∗ (l ↦[γ] (.pair x nxt)) ∗ listRep γ nxt xs ⊢
      wp (F := F) γ (popBody s) (fun r => iprop(⌜r = x⌝ ∗ isStack γ s xs)) := by
  simp only [popBody]
  iintro ⟨Hs, Hnode, Hrep⟩
  -- let head = !s   (head ↦ loc l)
  iapply wp_let
  iapply (wp_load γ s (.loc l))
  isplitl [Hs]
  · iexact Hs
  · iintro Hs2
    iintro !>
    iintro !>
    simp [substE, substV, hclx, hclnxt]
    -- let node = !head   (node ↦ (x, nxt))
    iapply wp_let
    iapply (wp_load γ l (.pair x nxt))
    isplitl [Hnode]
    · iexact Hnode
    · iintro Hnode2
      iintro !>
      iintro !>
      simp [substE, substV, hclx, hclnxt]
      -- let v = fst node   (= x)
      iapply wp_let
      iapply (wp_fst γ x nxt)
      iintro !>
      iapply wp_value
      iintro !>
      iintro !>
      simp [substE, substV, hclx, hclnxt]
      -- let nxt = snd node   (= nxt)
      iapply wp_let
      iapply (wp_snd γ x nxt)
      iintro !>
      iapply wp_value
      iintro !>
      iintro !>
      simp [substE, substV, hclx, hclnxt]
      -- let b = CAS(s, loc l, nxt)
      iapply wp_let
      iapply (wp_cas_suc γ s (.loc l) nxt)
      isplitl [Hs2]
      · iexact Hs2
      · iintro Hs3
        iintro !>
        iintro !>
        simp [substE, substV, hclx, hclnxt]
        -- if b (= true) then v else v
        iapply wp_if_true
        iintro !>
        iapply wp_value
        iintro !>
        -- postcondition: ⌜x = x⌝ ∗ isStack γ s xs
        isplitl []
        · ipure_intro; rfl
        · simp only [isStack]
          iexists nxt
          isplitl [Hs3]
          · iexact Hs3
          · iexact Hrep

end LeanliftIris.PhaseA
