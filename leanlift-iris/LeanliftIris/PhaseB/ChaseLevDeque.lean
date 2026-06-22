/-
Phase B (step 9) — the Chase–Lev deque's **structure**: the fixed-capacity
circular array with wrap-around.

`ChaseLev.lean` proved the *weak-memory* heart (the last-element take/steal race is
store buffering, so it needs a `seq_cst` fence). This file is the complementary
*sequential* layer: the backing store is a fixed-capacity ring buffer addressed by
absolute indices `top ≤ bot` modulo `cap`, and we prove it really behaves as a
double-ended queue, **including slot reuse across the wrap-around boundary**.

  * the owner pushes/pops at the **bottom** (LIFO),
  * a thief steals from the **top** (FIFO),
  * absolute index `i` lives in slot `i % cap`, so once an index passes `cap` the
    slots are reused.

Proved (sorry-free): `popBottom_pushBottom_val` (owner LIFO returns its last push),
`popTop_pushBottom_singleton` (a lone element is stealable), `size_*` accounting,
the `top ≤ bot` invariant preserved by every op, and a concrete `cap = 2`
execution (`wrap_*`) where a stolen slot is **reused** by a later push and the
thief still reads every element back in FIFO order — wrap-around done right.
-/

namespace LeanliftIris.PhaseB

/-- A fixed-capacity circular-array deque (the Chase–Lev backing store, sequential
semantics). `buf i` is slot `i` (only `i < cap` is ever live); absolute indices
`top ≤ bot` address slots through `i % cap`, so indices past `cap` reuse slots. -/
structure Deque (α : Type) where
  cap : Nat
  buf : Nat → α
  top : Nat
  bot : Nat

namespace Deque
variable {α : Type}

/-- Number of live elements. -/
def size (d : Deque α) : Nat := d.bot - d.top

/-- Owner pushes at the bottom: write slot `bot % cap`, advance `bot`. -/
def pushBottom (d : Deque α) (v : α) : Deque α :=
  { d with buf := fun i => if i = d.bot % d.cap then v else d.buf i, bot := d.bot + 1 }

/-- Owner pops from the bottom (LIFO): retreat `bot`, read its slot. `none` if empty. -/
def popBottom (d : Deque α) : Deque α × Option α :=
  if d.bot ≤ d.top then (d, none)
  else ({ d with bot := d.bot - 1 }, some (d.buf ((d.bot - 1) % d.cap)))

/-- Thief steals from the top (FIFO): read slot `top % cap`, advance `top`. `none`
if empty. -/
def popTop (d : Deque α) : Deque α × Option α :=
  if d.bot ≤ d.top then (d, none)
  else ({ d with top := d.top + 1 }, some (d.buf (d.top % d.cap)))

/-! ## Size accounting -/

theorem size_pushBottom (d : Deque α) (v : α) (h : d.top ≤ d.bot) :
    (d.pushBottom v).size = d.size + 1 := by
  show (d.bot + 1) - d.top = (d.bot - d.top) + 1
  omega

theorem size_popTop (d : Deque α) (h : d.top < d.bot) :
    (d.popTop).1.size = d.size - 1 := by
  unfold popTop
  rw [if_neg (by omega)]
  show (d.bot) - (d.top + 1) = (d.bot - d.top) - 1
  omega

theorem size_popBottom (d : Deque α) (h : d.top < d.bot) :
    (d.popBottom).1.size = d.size - 1 := by
  unfold popBottom
  rw [if_neg (by omega)]
  show (d.bot - 1) - d.top = (d.bot - d.top) - 1
  omega

/-! ## The `top ≤ bot` invariant is preserved by every operation -/

theorem inv_pushBottom (d : Deque α) (v : α) (h : d.top ≤ d.bot) :
    (d.pushBottom v).top ≤ (d.pushBottom v).bot := by
  show d.top ≤ d.bot + 1; omega

theorem inv_popTop (d : Deque α) (h : d.top ≤ d.bot) :
    (d.popTop).1.top ≤ (d.popTop).1.bot := by
  unfold popTop; split
  · exact h
  · show d.top + 1 ≤ d.bot; omega

theorem inv_popBottom (d : Deque α) (h : d.top ≤ d.bot) :
    (d.popBottom).1.top ≤ (d.popBottom).1.bot := by
  unfold popBottom; split
  · exact h
  · show d.top ≤ d.bot - 1; omega

/-! ## Owner LIFO: a push is undone by the next bottom pop -/

/-- **Owner LIFO.** Popping the bottom right after pushing returns the just-pushed
value — the same slot (`bot % cap`) is written and read back. -/
theorem popBottom_pushBottom_val (d : Deque α) (v : α) (h : d.top ≤ d.bot) :
    ((d.pushBottom v).popBottom).2 = some v := by
  simp only [popBottom, pushBottom]
  rw [if_neg (by omega)]
  simp [Nat.add_sub_cancel]

/-- The push/pop-bottom round trip restores the index window (`top`, `bot`). -/
theorem popBottom_pushBottom_window (d : Deque α) (v : α) (h : d.top ≤ d.bot) :
    ((d.pushBottom v).popBottom).1.top = d.top ∧ ((d.pushBottom v).popBottom).1.bot = d.bot := by
  simp only [popBottom, pushBottom]
  rw [if_neg (by omega)]
  refine ⟨rfl, ?_⟩
  show d.bot + 1 - 1 = d.bot
  omega

/-! ## A lone element is stealable -/

/-- **Single-element steal.** A value pushed onto an empty deque can be stolen from
the top — the bottom write and the top read hit the same slot. -/
theorem popTop_pushBottom_singleton (d : Deque α) (v : α) (hempty : d.bot = d.top) :
    ((d.pushBottom v).popTop).2 = some v := by
  simp only [popTop, pushBottom]
  rw [if_neg (by omega)]
  rw [hempty]
  simp

/-! ## Concrete wrap-around: a reused slot is read back in FIFO order

`cap = 2`. Push `10,20` (slots 0,1); steal `10` (frees slot 0); push `30` — index
`2`, slot `2 % 2 = 0`, **reusing the slot `10` vacated**; then steal the rest. The
thief reads `20` then `30` — every element back, in order, across the boundary. -/

/-- The empty `cap = 2` deque (sentinel fill `0`). -/
def d2 : Deque Nat := { cap := 2, buf := fun _ => 0, top := 0, bot := 0 }

/-- After `push 10; push 20; steal`, then `push 30` (which wraps into slot 0). -/
def d2wrapped : Deque Nat := ((d2.pushBottom 10).pushBottom 20).popTop.1.pushBottom 30

/-- The first steal returns the oldest element `10` (slot 0). -/
theorem wrap_steal0 : ((d2.pushBottom 10).pushBottom 20).popTop.2 = some 10 := by decide

/-- After the wrap, the next steal returns `20` (slot 1). -/
theorem wrap_steal1 : d2wrapped.popTop.2 = some 20 := by decide

/-- And the final steal returns `30` — read back from the **reused** slot 0. -/
theorem wrap_steal2 : d2wrapped.popTop.1.popTop.2 = some 30 := by decide

/-- The deque is then empty: a fourth steal returns `none`. -/
theorem wrap_steal3 : d2wrapped.popTop.1.popTop.1.popTop.2 = none := by decide

end Deque

end LeanliftIris.PhaseB
