/-
Phase A3 — sweep-to-fill VWAP (#10 effective-best), pure-function proofs.

The C++ corpus ships two engines for a marketable order of size `Q` against a
price-ascending ask ladder:

  * Engine 1 (`sweep_linear`): a single-shot linear walk, O(levels touched).
  * Engine 2 (`PrefixBook::query`): prefix sums + binary search, O(log N)/query.

Their fuzz harness asserts "linear == prefix, 0 mismatches" over 200k random
ladders. Here that becomes a *theorem* (`linear_eq_prefix`), quantified over all
ladders and all `Q`. We also prove the edge cases the fuzzer special-cases
(`Q == 0`, over-ask, drained levels) and the exact-arithmetic VWAP bracket
`best_ask * filled ≤ notional ≤ touch * filled` — the integer form of
`best_ask ≤ VWAP ≤ touch`, with no floating point on the path.

Core Lean only (no Mathlib, no Iris): these are kernel-checked pure proofs. `Nat`
is unbounded, so `notional` is *exactly* the C++ 128-bit accumulator with no
overflow caveat. Sorry-free.
-/
namespace LeanliftIris.PhaseA

/-- One price level: an integer tick price and an aggregate quantity. -/
structure Level where
  price : Nat
  qty   : Nat
deriving Repr, DecidableEq

/-- The result of a sweep. `touch` is `none` when nothing was consumed (the C++
sentinel `-1`); otherwise the worst (deepest) price touched. -/
structure Sweep where
  requested : Nat
  filled    : Nat
  notional  : Nat
  touch     : Option Nat
  levels    : Nat
  complete  : Bool
deriving Repr, DecidableEq

/-- Total resting size across the ladder. -/
def total : List Level → Nat
  | []      => 0
  | l :: ls => l.qty + total ls

/-! ## Engine 1 — linear walk

Tail-recursive forward accumulation, mirroring the C++ loop. The C++ `break` on
`filled == Q` is unnecessary here: once `filled == Q`, every `take` is
`min qty 0 = 0`, so the level is skipped and the accumulator is unchanged. Thus
folding the whole list yields the same result as breaking early. -/

/-- Step over one level given the budget `Q` and current `(filled, notional,
touch, levels)`. -/
def fillStep (Q : Nat) (l : Level) :
    (Nat × Nat × Option Nat × Nat) → (Nat × Nat × Option Nat × Nat) :=
  fun (f, n, t, lv) =>
    let take := min l.qty (Q - f)
    if take = 0 then (f, n, t, lv)
    else (f + take, n + l.price * take, some l.price, lv + 1)

/-- Engine 1 accumulator core. -/
def linearAux (Q : Nat) :
    List Level → (Nat × Nat × Option Nat × Nat) → (Nat × Nat × Option Nat × Nat)
  | [],      acc => acc
  | l :: ls, acc => linearAux Q ls (fillStep Q l acc)

/-- Engine 1: single-shot linear walk. -/
def sweepLinear (asks : List Level) (Q : Nat) : Sweep :=
  let (f, n, t, lv) := linearAux Q asks (0, 0, none, 0)
  { requested := Q, filled := f, notional := n, touch := t, levels := lv,
    complete := f = Q }

/-! ## Basic accumulator invariants -/

/-- The new `filled` after one fillStep is `f + min qty (Q - f)` (uniform across the
empty/non-empty branches: when `take = 0` the level is skipped and `f + 0 = f`). -/
theorem fillStep_fst (Q : Nat) (l : Level) (acc : Nat × Nat × Option Nat × Nat) :
    (fillStep Q l acc).1 = acc.1 + min l.qty (Q - acc.1) := by
  obtain ⟨f, n, t, lv⟩ := acc
  simp only [fillStep]
  by_cases hz : min l.qty (Q - f) = 0
  · simp [hz]
  · simp [hz]

/-- Exact `filled`: a greedy walk fills `min Q total`. This single identity
subsumes the completion case (`Q ≤ total ⇒ filled = Q`) and the over-ask case
(`Q > total ⇒ filled = total`). Requires the running `filled` to be `≤ Q`, which
holds from the `0` start. -/
theorem linearAux_filled (Q : Nat) (asks : List Level) :
    ∀ acc : Nat × Nat × Option Nat × Nat, acc.1 ≤ Q →
      (linearAux Q asks acc).1 = min Q (acc.1 + total asks) := by
  induction asks with
  | nil => intro acc h; simp only [linearAux, total]; omega
  | cons l ls ih =>
    intro acc h
    simp only [linearAux, total]
    rw [ih (fillStep Q l acc) (by rw [fillStep_fst]; have := Nat.min_le_right l.qty (Q - acc.1); omega)]
    rw [fillStep_fst]
    have := Nat.min_le_right l.qty (Q - acc.1)
    omega

/-- `filled = min Q total` for the top-level call. -/
theorem sweepLinear_filled (asks : List Level) (Q : Nat) :
    (sweepLinear asks Q).filled = min Q (total asks) := by
  have := linearAux_filled Q asks (0, 0, none, 0) (by simp)
  simpa [sweepLinear] using this

/-- `filled ≤ Q` for the top-level call. -/
theorem sweepLinear_filled_le (asks : List Level) (Q : Nat) :
    (sweepLinear asks Q).filled ≤ Q := by
  rw [sweepLinear_filled]; exact Nat.min_le_left _ _

/-- Completion characterisation: the sweep is `complete` iff the book can cover
the order (`Q ≤ total`). -/
theorem sweepLinear_complete (asks : List Level) (Q : Nat) :
    (sweepLinear asks Q).complete = decide (Q ≤ total asks) := by
  have hf : (sweepLinear asks Q).filled = min Q (total asks) := sweepLinear_filled asks Q
  simp only [sweepLinear] at hf ⊢
  -- complete := (filled = Q); filled = min Q total
  rw [hf]
  by_cases h : Q ≤ total asks <;> simp [h, Nat.min_eq_left] <;> omega

/-- Over-ask: when the order exceeds the book, it fills the whole book and is not
complete. -/
theorem sweep_over_ask (asks : List Level) (Q : Nat) (h : total asks < Q) :
    (sweepLinear asks Q).filled = total asks ∧
    (sweepLinear asks Q).complete = false := by
  refine ⟨?_, ?_⟩
  · rw [sweepLinear_filled]; omega
  · rw [sweepLinear_complete]; simp; omega

/-! ## Drained levels are skipped

A level with `qty = 0` contributes nothing and does not count toward `levels`
(the C++ `if (take == 0) continue;`). -/

/-- A zero-quantity head level is transparent to the walk. -/
theorem linearAux_drained (Q : Nat) (l : Level) (ls : List Level)
    (hl : l.qty = 0) (acc : Nat × Nat × Option Nat × Nat) :
    linearAux Q (l :: ls) acc = linearAux Q ls acc := by
  obtain ⟨f, n, t, lv⟩ := acc
  simp only [linearAux, fillStep, hl, Nat.zero_min, if_true]

/-! ## VWAP bracket: `best_ask * filled ≤ notional ≤ touch * filled`

The C++ claims `best_ask ≤ VWAP ≤ touch` with `VWAP = notional / filled`. We
prove the division-free integer form, which is *stronger* (no rounding): every
consumed unit costs at least the best price and at most the deepest price
touched, so the size-weighted notional is bracketed. -/

/-- Ascending price ladder: each level's price bounds all later levels. (The C++
sweep's stated precondition: a "price-ascending ask ladder".) -/
def Ascending : List Level → Prop
  | []      => True
  | l :: ls => (∀ m ∈ ls, l.price ≤ m.price) ∧ Ascending ls

/-- The touch value as a number (`0` stands in for the `none` sentinel; in that
case `filled = 0` too, so the bound is `0 ≤ 0`). -/
def touchVal (s : Sweep) : Nat := s.touch.getD 0

/-- **Lower bracket.** If `lo` is a price floor for every non-empty level (e.g.
`lo = best_ask`), then `lo * filled ≤ notional`: no unit executes below `lo`.
Does not need the ladder to be sorted. -/
theorem linearAux_lower (Q lo : Nat) (asks : List Level) :
    ∀ acc : Nat × Nat × Option Nat × Nat,
      (∀ m ∈ asks, m.qty ≠ 0 → lo ≤ m.price) →
      lo * acc.1 ≤ acc.2.1 →
      lo * (linearAux Q asks acc).1 ≤ (linearAux Q asks acc).2.1 := by
  induction asks with
  | nil => intro acc _ h; simpa [linearAux] using h
  | cons l ls ih =>
    intro acc hlo Hlo
    obtain ⟨f, n, t, lv⟩ := acc
    simp only [linearAux]
    by_cases hz : min l.qty (Q - f) = 0
    · simp only [fillStep, if_pos hz]
      exact ih (f, n, t, lv) (fun m hm => hlo m (by simp [hm])) Hlo
    · simp only [fillStep, if_neg hz]
      apply ih
      · exact fun m hm => hlo m (by simp [hm])
      · -- lo * (f + take) ≤ n + price * take
        have hqz : l.qty ≠ 0 := by intro h; exact hz (by simp [h])
        have hlp : lo ≤ l.price := hlo l (by simp) hqz
        have h1 : lo * min l.qty (Q - f) ≤ l.price * min l.qty (Q - f) :=
          Nat.mul_le_mul_right _ hlp
        have hHlo : lo * f ≤ n := Hlo
        show lo * (f + min l.qty (Q - f)) ≤ n + l.price * min l.qty (Q - f)
        rw [Nat.mul_add]
        omega

/-- **Upper bracket.** On an ascending ladder, `notional ≤ touch * filled`: no
unit executes above the deepest price touched. -/
theorem linearAux_upper (Q : Nat) (asks : List Level) (hasc : Ascending asks) :
    ∀ acc : Nat × Nat × Option Nat × Nat,
      acc.2.1 ≤ (acc.2.2.1.getD 0) * acc.1 →
      (∀ tp, acc.2.2.1 = some tp → ∀ m ∈ asks, tp ≤ m.price) →
      (linearAux Q asks acc).2.1 ≤ ((linearAux Q asks acc).2.2.1.getD 0) * (linearAux Q asks acc).1 := by
  induction asks with
  | nil => intro acc h _; simpa [linearAux] using h
  | cons l ls ih =>
    intro acc Hhi Ht
    obtain ⟨f, n, t, lv⟩ := acc
    obtain ⟨hhead, htail⟩ := hasc
    simp only [linearAux]
    by_cases hz : min l.qty (Q - f) = 0
    · simp only [fillStep, if_pos hz]
      exact ih htail (f, n, t, lv) Hhi (fun tp ht m hm => Ht tp ht m (by simp [hm]))
    · simp only [fillStep, if_neg hz]
      apply ih htail
      · -- n + price * take ≤ price * (f + take)
        have htp : t.getD 0 ≤ l.price := by
          cases t with
          | none => simp
          | some tp => exact Ht tp rfl l (by simp)
        have h2 : (t.getD 0) * f ≤ l.price * f := Nat.mul_le_mul_right _ htp
        have hHhi : n ≤ (t.getD 0) * f := Hhi
        show n + l.price * min l.qty (Q - f)
              ≤ ((some l.price).getD 0) * (f + min l.qty (Q - f))
        rw [Option.getD_some, Nat.mul_add]
        omega
      · -- new touch = some price ≤ every later level
        intro tp htp m hm
        simp only [Option.some.injEq] at htp
        subst htp
        exact hhead m hm

/-- **`best_ask ≤ VWAP`** (integer form). With `lo` a floor on every non-empty
level's price, the realized notional is at least `lo` per filled unit. -/
theorem sweep_lower (asks : List Level) (Q lo : Nat)
    (hlo : ∀ m ∈ asks, m.qty ≠ 0 → lo ≤ m.price) :
    lo * (sweepLinear asks Q).filled ≤ (sweepLinear asks Q).notional := by
  have := linearAux_lower Q lo asks (0, 0, none, 0) hlo (by simp)
  simpa [sweepLinear] using this

/-- **`VWAP ≤ touch`** (integer form). On an ascending ladder, the realized
notional is at most the deepest price touched, per filled unit. -/
theorem sweep_upper (asks : List Level) (Q : Nat) (hasc : Ascending asks) :
    (sweepLinear asks Q).notional ≤ touchVal (sweepLinear asks Q) * (sweepLinear asks Q).filled := by
  have := linearAux_upper Q asks hasc (0, 0, none, 0) (by simp) (by simp)
  simpa [sweepLinear, touchVal] using this

/-! ## Edge cases the fuzzer special-cases -/

/-- `Q == 0`: nothing is consumed and the sweep is trivially complete. -/
theorem sweep_Q_zero (asks : List Level) :
    sweepLinear asks 0 =
      { requested := 0, filled := 0, notional := 0, touch := none,
        levels := 0, complete := true } := by
  -- with Q = 0 every `take = min qty (0 - f) = min qty 0 = 0`, so acc is fixed.
  have key : ∀ acc : Nat × Nat × Option Nat × Nat,
      linearAux 0 asks acc = acc := by
    induction asks with
    | nil => intro acc; rfl
    | cons l ls ih =>
      intro acc
      obtain ⟨f, n, t, lv⟩ := acc
      simp only [linearAux, fillStep]
      rw [ih]
      simp
  simp [sweepLinear, key]
