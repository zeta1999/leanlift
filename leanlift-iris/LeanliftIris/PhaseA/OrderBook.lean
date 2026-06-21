/-
Phase A3 — L2 order book (#9 l2-order-book), pure-function proofs.

The C++ keeps a dense price ladder `qty[tick]` and a 3-level hierarchical
occupancy bitmap, so `best_bid`/`best_ask` are O(1) bit-scans rather than an
O(N) walk. The headline correctness claims are:

  * `best = max occupied level` (resp. min for the ask), and
  * "the fall-back after the top level is cancelled is free" — when the current
    best level is set to zero, the next best is the highest/lowest *remaining*
    occupied level.

Here we model the ladder as `q : Nat → Nat` (aggregate size per tick) over a
bounded index range `[0, N)`, with `best_bid = maxOcc` / `best_ask = minOcc`
(exactly what `clz`/`ctz` over the bitmap compute), and prove both the invariant
and fall-back. We also prove the microprice (size-weighted fair value) is
bracketed in `[best_bid, best_ask]`. Core Lean only, sorry-free.

The hierarchical *bitmap* itself (the clz/ctz refinement of `maxOcc`/`minOcc`)
is a separate bit-vector obligation; here we pin the specification it must meet.
-/
namespace LeanliftIris.PhaseA

/-- A price ladder: aggregate resting quantity per integer tick. A tick is
"occupied" iff its quantity is non-zero. -/
abbrev Ladder := Nat → Nat

/-- Feed update: set the aggregate size at `tick` to `v` (the C++ `update`; the
occupancy bit flips implicitly with the 0↔non-zero transition). -/
def upd (q : Ladder) (tick v : Nat) : Ladder :=
  fun j => if j = tick then v else q j

/-- Highest occupied tick strictly below `n` (the C++ `best_bid = max_set`).
`none` when `[0, n)` is empty. -/
def maxOcc : Nat → Ladder → Option Nat
  | 0,     _ => none
  | n + 1, q => if q n ≠ 0 then some n else maxOcc n q

/-- Scan `[i, i+f)` upward for the lowest occupied tick. -/
def minFrom (q : Ladder) : Nat → Nat → Option Nat
  | 0,     _ => none
  | f + 1, i => if q i ≠ 0 then some i else minFrom q f (i + 1)

/-- Lowest occupied tick in `[0, n)` (the C++ `best_ask = min_set`). -/
def minOcc (n : Nat) (q : Ladder) : Option Nat := minFrom q n 0

/-! ## `best_bid = max occupied` -/

/-- `maxOcc` only depends on the ladder over its scan range. -/
theorem maxOcc_congr (n : Nat) (q q' : Ladder) (h : ∀ j, j < n → q j = q' j) :
    maxOcc n q = maxOcc n q' := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [maxOcc]
    rw [h m (by omega), ih (fun j hj => h j (by omega))]

/-- Dropping a zero top tick. -/
theorem maxOcc_skip (m : Nat) (q : Ladder) (h : q m = 0) :
    maxOcc (m + 1) q = maxOcc m q := by
  show (if q m ≠ 0 then some m else maxOcc m q) = maxOcc m q
  rw [if_neg (by simp [h])]

/-- Dropping a contiguous block of zero top ticks `[m, n)`. -/
theorem maxOcc_drop (q : Ladder) :
    ∀ n m, m ≤ n → (∀ j, m ≤ j → j < n → q j = 0) →
      maxOcc n q = maxOcc m q := by
  intro n
  induction n with
  | zero => intro m hm _; have : m = 0 := by omega
            subst this; rfl
  | succ k ih =>
    intro m hm hz
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · have hk0 : q k = 0 := hz k (by omega) (by omega)
      rw [maxOcc_skip k q hk0]
      exact ih m (by omega) (fun j hj hjk => hz j hj (by omega))
    · have : m = k + 1 := by omega
      subst this; rfl

/-- **Specification of `best_bid`.** `maxOcc n q = some k` exactly captures: `k`
is occupied, in range, and every higher in-range tick is empty — i.e. `k` is the
greatest occupied tick. -/
theorem maxOcc_some_iff (n : Nat) (q : Ladder) (k : Nat) :
    maxOcc n q = some k ↔
      (k < n ∧ q k ≠ 0 ∧ ∀ j, k < j → j < n → q j = 0) := by
  induction n with
  | zero => simp [maxOcc]
  | succ m ih =>
    by_cases htop : q m = 0
    · rw [maxOcc_skip m q htop, ih]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, fun j hj hjm => ?_⟩
        rcases Nat.lt_or_ge j m with h | h
        · exact h3 j hj h
        · have : j = m := by omega
          rw [this]; exact htop
      · rintro ⟨h1, h2, h3⟩
        have hkm : k < m := by
          rcases Nat.lt_or_ge k m with h | h
          · exact h
          · exfalso; have : k = m := by omega
            rw [this] at h2; exact h2 htop
        exact ⟨hkm, h2, fun j hj hjm => h3 j hj (by omega)⟩
    · have hstep : maxOcc (m + 1) q = some m := by
        show (if q m ≠ 0 then some m else maxOcc m q) = some m
        rw [if_pos htop]
      rw [hstep]
      constructor
      · intro h
        rw [Option.some.injEq] at h; subst h
        exact ⟨by omega, htop, fun j hj hjm => by omega⟩
      · rintro ⟨h1, h2, h3⟩
        by_cases hkm : k = m
        · rw [hkm]
        · exact absurd (h3 m (by omega) (by omega)) htop

/-- **Fall-back correctness (bid side).** When the current best bid `k` is
cancelled (`upd q k 0`), the new best bid is the highest occupied tick *below*
`k` — computed for free, since all ticks above `k` were already empty. -/
theorem maxOcc_fallback (n : Nat) (q : Ladder) (k : Nat)
    (hk : maxOcc n q = some k) :
    maxOcc n (upd q k 0) = maxOcc k q := by
  rw [maxOcc_some_iff] at hk
  obtain ⟨hkn, _, hhi⟩ := hk
  have hzero : ∀ j, k ≤ j → j < n → upd q k 0 j = 0 := by
    intro j hjk hjn
    by_cases hjeq : j = k
    · simp [upd, hjeq]
    · simp only [upd, if_neg hjeq]
      exact hhi j (by omega) hjn
  rw [maxOcc_drop (upd q k 0) n k (by omega) hzero]
  exact maxOcc_congr k _ q (fun j hj => by simp [upd, Nat.ne_of_lt hj])

/-! ## `best_ask = min occupied` (symmetric) -/

/-- Specification of `minFrom` over its scan window `[i, i+f)`. -/
theorem minFrom_some_iff (q : Ladder) :
    ∀ f i k, minFrom q f i = some k ↔
      (i ≤ k ∧ k < i + f ∧ q k ≠ 0 ∧ ∀ j, i ≤ j → j < k → q j = 0) := by
  intro f
  induction f with
  | zero =>
    intro i k
    constructor
    · intro h; exact absurd h (by simp [minFrom])
    · rintro ⟨h1, h2, _, _⟩; omega
  | succ g ih =>
    intro i k
    by_cases hqi : q i = 0
    · have hstep : minFrom q (g + 1) i = minFrom q g (i + 1) := by
        show (if q i ≠ 0 then some i else minFrom q g (i + 1)) = minFrom q g (i + 1)
        rw [if_neg (by simp [hqi])]
      rw [hstep, ih (i + 1)]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨by omega, by omega, h3, fun j hj hjk => ?_⟩
        rcases Nat.lt_or_ge j (i + 1) with h | h
        · have : j = i := by omega
          rw [this]; exact hqi
        · exact h4 j h hjk
      · rintro ⟨h1, h2, h3, h4⟩
        have hik : i < k := by
          rcases Nat.lt_or_ge i k with h | h
          · exact h
          · exfalso; have : i = k := by omega
            rw [this] at hqi; exact h3 hqi
        exact ⟨by omega, by omega, h3, fun j hj hjk => h4 j (by omega) hjk⟩
    · have hstep : minFrom q (g + 1) i = some i := by
        show (if q i ≠ 0 then some i else minFrom q g (i + 1)) = some i
        rw [if_pos hqi]
      rw [hstep]
      constructor
      · intro h
        rw [Option.some.injEq] at h; subst h
        exact ⟨by omega, by omega, hqi, fun j hj hjk => by omega⟩
      · rintro ⟨h1, h2, h3, h4⟩
        by_cases hik : i = k
        · rw [hik]
        · have hik' : i < k := by omega
          exact absurd (h4 i (by omega) hik') hqi

/-- **Specification of `best_ask`.** `minOcc n q = some k` ⇔ `k` is the least
occupied tick in range. -/
theorem minOcc_some_iff (n : Nat) (q : Ladder) (k : Nat) :
    minOcc n q = some k ↔ (k < n ∧ q k ≠ 0 ∧ ∀ j, j < k → q j = 0) := by
  unfold minOcc
  rw [minFrom_some_iff]
  constructor
  · rintro ⟨_, h2, h3, h4⟩; exact ⟨by omega, h3, fun j hj => h4 j (by omega) hj⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h2, fun j _ hj => h3 j hj⟩

/-- **Fall-back correctness (ask side).** Cancelling the current best ask `k`
reveals a strictly higher occupied tick, with everything below it empty. -/
theorem minOcc_fallback (n : Nat) (q : Ladder) (k k' : Nat)
    (hk : minOcc n q = some k)
    (hk' : minOcc n (upd q k 0) = some k') :
    k < k' ∧ q k' ≠ 0 ∧ ∀ j, j < k' → upd q k 0 j = 0 := by
  rw [minOcc_some_iff] at hk hk'
  obtain ⟨hkn, hkq, hlo⟩ := hk
  obtain ⟨hk'n, hk'q, hlo'⟩ := hk'
  have hk_le : k ≤ k' := by
    rcases Nat.lt_or_ge k' k with h | h
    · have hz : upd q k 0 k' = 0 := by simp [upd, Nat.ne_of_lt h, hlo k' h]
      exact absurd hz hk'q
    · exact h
  have hk_ne : k' ≠ k := by
    intro h; rw [h] at hk'q; simp [upd] at hk'q
  have hupd : upd q k 0 k' = q k' := by simp [upd, hk_ne]
  exact ⟨by omega, by rw [← hupd]; exact hk'q, hlo'⟩

/-! ## Microprice bracket

`microprice = (bb·qa + ba·qb) / (qb + qa)` is claimed to lie in `[bb, ba]`. We
prove the division-free integer form (no FP, no rounding) given a non-crossed
book `bb ≤ ba`. -/

/-- **`best_bid ≤ microprice ≤ best_ask`** (integer form): the size-weighted fair
value is bracketed by the touch prices. `qb`, `qa` are the resting sizes at the
best bid/ask. -/
theorem microprice_bracket (bb ba qb qa : Nat) (hcross : bb ≤ ba) :
    bb * (qb + qa) ≤ bb * qa + ba * qb ∧ bb * qa + ba * qb ≤ ba * (qb + qa) := by
  refine ⟨?_, ?_⟩
  · have : bb * qb ≤ ba * qb := Nat.mul_le_mul_right _ hcross
    rw [Nat.mul_add]; omega
  · have : bb * qa ≤ ba * qa := Nat.mul_le_mul_right _ hcross
    rw [Nat.mul_add]; omega
