/-
Phase A1 — `λ-conc`: a tiny concurrent imperative core with a heap and atomics,
plus a *sequentially-consistent* small-step operational semantics.

This is a deliberately minimal HeapLang-style language: values, (recursive)
functions, pairs, integer/boolean operations, a mutable heap with
`alloc`/`load`/`store`, the atomics `CAS`/`FAA`, and `fork`. The semantics is
given as

  * `Head`      — head reduction (pure rules + heap/atomic rules + fork),
  * `prim_step` — head reduction under an evaluation context (`fill K`),
  * `step`      — the thread-pool interleaving relation over configurations.

SC is the *interleaving* of per-thread primitive steps over a single shared
heap: there is no per-location memory order, no buffering — every `load` sees the
last `store` in the global order. That is exactly leanlift's existing model
assumption; Phase B will replace `Head`/`step` with a weak-memory version.

Core Lean only (no Iris yet): this file is the object language A2's `wp` and A4's
Treiber proof will be defined over. Sorry-free.
-/
namespace LeanliftIris.PhaseA

/-- Binary primitive operators. -/
inductive BinOp where
  | add | sub | eq | le
deriving Repr, DecidableEq

mutual

/-- Values (closed runtime data). `clos f x e` is a recursive closure; an
ordinary λ is `clos "_" x e` with `f` unused. (Named `clos`, not `rec`, to avoid
colliding with the auto-generated `Val.rec` recursor.) -/
inductive Val where
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | loc (l : Nat)
  | pair (a b : Val)
  | clos (f x : String) (body : Expr)

/-- Expressions. A `clos`/λ literal is a value, written `val (.clos ..)`. -/
inductive Expr where
  | val (v : Val)
  | var (x : String)
  | app (e1 e2 : Expr)
  | binop (op : BinOp) (e1 e2 : Expr)
  | ite (e0 e1 e2 : Expr)
  | pairE (e1 e2 : Expr)
  | fstE (e : Expr)
  | sndE (e : Expr)
  | alloc (e : Expr)
  | load (e : Expr)
  | store (e1 e2 : Expr)
  | cas (e0 e1 e2 : Expr)
  | faa (e1 e2 : Expr)
  | fork (e : Expr)

end

deriving instance Repr for Val, Expr
deriving instance DecidableEq for Val, Expr

/-- The heap: a total map from locations to optionally-allocated values. -/
abbrev Heap := Nat → Option Val

/-- The empty heap (nothing allocated). -/
def emptyHeap : Heap := fun _ => none

/-- Point update of the heap. -/
def Heap.set (σ : Heap) (l : Nat) (v : Val) : Heap :=
  fun j => if j = l then some v else σ j

/-! ## Substitution

Substitute a (closed) value `w` for the free variable `x`. `rec`/λ binders
shadow, so we stop under a binder that rebinds `x`. -/

mutual

def substV (x : String) (w : Val) : Val → Val
  | .unit       => .unit
  | .bool b     => .bool b
  | .int n      => .int n
  | .loc l      => .loc l
  | .pair a b   => .pair (substV x w a) (substV x w b)
  | .clos f y body =>
      if x = f ∨ x = y then .clos f y body else .clos f y (substE x w body)

def substE (x : String) (w : Val) : Expr → Expr
  | .val v        => .val (substV x w v)
  | .var y        => if x = y then .val w else .var y
  | .app a b      => .app (substE x w a) (substE x w b)
  | .binop op a b => .binop op (substE x w a) (substE x w b)
  | .ite a b c    => .ite (substE x w a) (substE x w b) (substE x w c)
  | .pairE a b    => .pairE (substE x w a) (substE x w b)
  | .fstE a       => .fstE (substE x w a)
  | .sndE a       => .sndE (substE x w a)
  | .alloc a      => .alloc (substE x w a)
  | .load a       => .load (substE x w a)
  | .store a b    => .store (substE x w a) (substE x w b)
  | .cas a b c    => .cas (substE x w a) (substE x w b) (substE x w c)
  | .faa a b      => .faa (substE x w a) (substE x w b)
  | .fork a       => .fork (substE x w a)

end

/-- Operator evaluation. `eq` compares any two values (decidable); `add`/`sub`/
`le` are integer operations. -/
def evalBinop : BinOp → Val → Val → Option Val
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .le,  .int a, .int b => some (.bool (decide (a ≤ b)))
  | .eq,  a,      b      => some (.bool (decide (a = b)))
  | _,    _,      _      => none

/-! ## Head reduction

The redex rules. Atomicity is structural: `cas`/`faa` consume the heap cell and
produce the new heap in a single `Head` step, so no other thread can interleave
mid-operation. -/

inductive Head : Expr → Heap → Expr → Heap → List Expr → Prop where
  | beta {f x body w σ} :
      Head (.app (.val (.clos f x body)) (.val w)) σ
           (substE x w (substE f (.clos f x body) body)) σ []
  | iteT {e1 e2 σ} : Head (.ite (.val (.bool true))  e1 e2) σ e1 σ []
  | iteF {e1 e2 σ} : Head (.ite (.val (.bool false)) e1 e2) σ e2 σ []
  | binop {op v1 v2 v σ} (h : evalBinop op v1 v2 = some v) :
      Head (.binop op (.val v1) (.val v2)) σ (.val v) σ []
  | pair {a b σ} : Head (.pairE (.val a) (.val b)) σ (.val (.pair a b)) σ []
  | fst {a b σ} : Head (.fstE (.val (.pair a b))) σ (.val a) σ []
  | snd {a b σ} : Head (.sndE (.val (.pair a b))) σ (.val b) σ []
  | alloc {v σ l} (h : σ l = none) :
      Head (.alloc (.val v)) σ (.val (.loc l)) (σ.set l v) []
  | load {l v σ} (h : σ l = some v) :
      Head (.load (.val (.loc l))) σ (.val v) σ []
  | store {l v w σ} (h : σ l = some w) :
      Head (.store (.val (.loc l)) (.val v)) σ (.val .unit) (σ.set l v) []
  | casS {l v1 v2 v0 σ} (h : σ l = some v0) (he : v0 = v1) :
      Head (.cas (.val (.loc l)) (.val v1) (.val v2)) σ (.val (.bool true)) (σ.set l v2) []
  | casF {l v1 v2 v0 σ} (h : σ l = some v0) (he : v0 ≠ v1) :
      Head (.cas (.val (.loc l)) (.val v1) (.val v2)) σ (.val (.bool false)) σ []
  | faa {l m n σ} (h : σ l = some (.int m)) :
      Head (.faa (.val (.loc l)) (.val (.int n))) σ (.val (.int m)) (σ.set l (.int (m + n))) []
  | fork {e σ} : Head (.fork e) σ (.val .unit) σ [e]

/-! ## Evaluation contexts (left-to-right, call-by-value) -/

/-- A single evaluation-context frame: a redex position with a hole. -/
inductive Frame where
  | appL (e2 : Expr) | appR (v1 : Val)
  | binopL (op : BinOp) (e2 : Expr) | binopR (op : BinOp) (v1 : Val)
  | iteC (e1 e2 : Expr)
  | pairL (e2 : Expr) | pairR (v1 : Val)
  | fstF | sndF
  | allocF | loadF
  | storeL (e2 : Expr) | storeR (v1 : Val)
  | casL (e1 e2 : Expr) | casM (v0 : Val) (e2 : Expr) | casR (v0 v1 : Val)
  | faaL (e2 : Expr) | faaR (v1 : Val)
deriving Repr, DecidableEq

/-- Plug an expression into a frame. -/
def fill1 : Frame → Expr → Expr
  | .appL e2,      e => .app e e2
  | .appR v1,      e => .app (.val v1) e
  | .binopL op e2, e => .binop op e e2
  | .binopR op v1, e => .binop op (.val v1) e
  | .iteC e1 e2,   e => .ite e e1 e2
  | .pairL e2,     e => .pairE e e2
  | .pairR v1,     e => .pairE (.val v1) e
  | .fstF,         e => .fstE e
  | .sndF,         e => .sndE e
  | .allocF,       e => .alloc e
  | .loadF,        e => .load e
  | .storeL e2,    e => .store e e2
  | .storeR v1,    e => .store (.val v1) e
  | .casL e1 e2,   e => .cas e e1 e2
  | .casM v0 e2,   e => .cas (.val v0) e e2
  | .casR v0 v1,   e => .cas (.val v0) (.val v1) e
  | .faaL e2,      e => .faa e e2
  | .faaR v1,      e => .faa (.val v1) e

/-- Plug into a nested context (head of the list is the outermost frame). -/
def fill (K : List Frame) (e : Expr) : Expr :=
  K.foldr fill1 e

/-- A primitive step: head reduction under some evaluation context. -/
def prim_step (e : Expr) (σ : Heap) (e' : Expr) (σ' : Heap) (efs : List Expr) : Prop :=
  ∃ K a a', e = fill K a ∧ e' = fill K a' ∧ Head a σ a' σ' efs

/-! ## Thread-pool semantics (SC interleaving) -/

/-- A configuration: a pool of threads and the shared heap. -/
structure Cfg where
  tp   : List Expr
  heap : Heap

/-- One scheduling step: pick a thread, take a primitive step, splice the result
back and append any forked threads to the end of the pool. The single shared
`heap` threaded through every step is what makes this sequentially consistent. -/
def step (c c' : Cfg) : Prop :=
  ∃ (t1 t2 : List Expr) (e e' : Expr) (efs : List Expr),
    c.tp = t1 ++ e :: t2 ∧
    prim_step e c.heap e' c'.heap efs ∧
    c'.tp = t1 ++ e' :: t2 ++ efs

/-- Reflexive-transitive closure of `step`. -/
inductive steps : Cfg → Cfg → Prop where
  | refl {c} : steps c c
  | tail {c c' c''} : steps c c' → step c' c'' → steps c c''

/-! ## Sanity metatheory -/

/-- `fill []` is the identity (empty context). -/
@[simp] theorem fill_nil (e : Expr) : fill [] e = e := rfl

/-- A value is not a head redex (progress: stuck only at values / genuine errors). -/
theorem head_not_val (v : Val) (σ : Heap) (e' : Expr) (σ' : Heap) (efs : List Expr) :
    ¬ Head (.val v) σ e' σ' efs := by
  intro h; cases h

/-- Head reduction lifts to a primitive step (empty context). -/
theorem prim_step.head {a σ a' σ' efs} (h : Head a σ a' σ' efs) :
    prim_step a σ a' σ' efs :=
  ⟨[], a, a', rfl, rfl, h⟩

/-- A primitive step lifts to a single thread-pool step for a one-thread pool. -/
theorem step.single {e σ e' σ' efs} (h : prim_step e σ e' σ' efs) :
    step ⟨[e], σ⟩ ⟨e' :: efs, σ'⟩ :=
  ⟨[], [], e, e', efs, rfl, h, rfl⟩

/-! ### Worked example

`let r = ref 7 in !r` reduces to `7`. With `r` bound, we model it directly as
`load (alloc 7)`: alloc picks a fresh cell, then load reads it back. -/

/-- `alloc 7` allocates cell `0` in the empty heap. -/
theorem ex_alloc :
    prim_step (.alloc (.val (.int 7))) emptyHeap
              (.val (.loc 0)) (emptyHeap.set 0 (.int 7)) [] :=
  prim_step.head (Head.alloc rfl)

/-- Reading back the freshly-allocated cell yields `7`. -/
theorem ex_load_after_alloc :
    prim_step (.load (.val (.loc 0))) (emptyHeap.set 0 (.int 7))
              (.val (.int 7)) (emptyHeap.set 0 (.int 7)) [] :=
  prim_step.head (Head.load (by simp [Heap.set]))

/-- A successful CAS flips `0 ↦ 1 ⇒ 0 ↦ 2` and reports `true`; the heap is
updated atomically in one step. -/
theorem ex_cas_success :
    prim_step (.cas (.val (.loc 0)) (.val (.int 1)) (.val (.int 2)))
              (emptyHeap.set 0 (.int 1))
              (.val (.bool true)) ((emptyHeap.set 0 (.int 1)).set 0 (.int 2)) [] :=
  prim_step.head (Head.casS (by simp [Heap.set]) rfl)

/-- `fork e` schedules a new thread: a singleton pool becomes a two-thread pool
(`unit` for the parent, `e` appended). -/
theorem ex_fork (e : Expr) (σ : Heap) :
    step ⟨[.fork e], σ⟩ ⟨[.val .unit, e], σ⟩ :=
  step.single (prim_step.head Head.fork)

end LeanliftIris.PhaseA
