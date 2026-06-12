-- Proof obligation for `isqrt` (SPEC §10 level L3), over the Aeneas-extracted
-- binary-search LOOP (isqrt_loop / isqrt_loop.body via the `loop` combinator).
-- The engine prepends `import Aeneas`, the opens, `namespace kernel`, and the
-- freshly-EXTRACTED defs, then appends `end kernel`.
--
-- The postcondition `r*r ≤ n < (r+1)^2` is proved by `loop.spec_decr_nat` with
--   measure  : hi - lo                              (well-founded; strictly drops)
--   invariant: lo^2 ≤ n ∧ n < (hi+1)^2 ∧ lo ≤ hi ∧ hi ≤ 65535
-- The `hi ≤ 65535` conjunct is what bounds `mid` so `mid*mid` can't overflow u32.
-- Developed via the propose→kernel→repair loop; sorry-free.
theorem isqrt_correct (n : Std.U32) :
    isqrt n ⦃ r => r.val * r.val ≤ n.val ∧ n.val < (r.val + 1) * (r.val + 1) ⦄ := by
  unfold isqrt isqrt_loop
  apply loop.spec_decr_nat
    (measure := fun x => x.2.val - x.1.val)
    (inv := fun x => x.1.val * x.1.val ≤ n.val ∧ n.val < (x.2.val + 1) * (x.2.val + 1)
            ∧ x.1.val ≤ x.2.val ∧ x.2.val ≤ 65535)
  · -- hBody
    rintro ⟨lo, hi⟩ ⟨hlo, hhi, hle, hcap⟩
    simp only [isqrt_loop.body]
    split
    · -- lo < hi
      rename_i hlt
      progress as ⟨i, hi_i⟩
      progress as ⟨i1, hi_i1⟩
      progress as ⟨mid, hi_mid⟩
      progress as ⟨i2, hi_i2⟩
      case hmax =>
        -- mid*mid ≤ U32.max, since mid ≤ 65535 and 65535² < 2³²
        have hm : mid.val ≤ 65535 := by scalar_tac
        have h2 := Nat.mul_le_mul hm hm
        scalar_tac
      split_ifs with hb
      · -- i2 = mid*mid ≤ n : continue with (mid, hi)
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨?_, hhi, ?_, hcap, ?_⟩
        · -- mid² ≤ n
          have : i2.val ≤ n.val := by scalar_tac
          rw [hi_i2] at this; exact this
        · scalar_tac           -- mid ≤ hi
        · scalar_tac           -- measure: hi - mid < hi - lo
      · -- mid*mid > n : continue with (lo, mid-1)
        progress as ⟨hi1, hi_hi1⟩
        refine ⟨hlo, ?_, ?_, ?_, ?_⟩
        · -- n < (hi1+1)² = mid²
          have hgt : n.val < i2.val := by scalar_tac
          rw [hi_i2] at hgt
          have hmid1 : hi1.val + 1 = mid.val := by scalar_tac
          rw [hmid1]; exact hgt
        · scalar_tac           -- lo ≤ hi1
        · scalar_tac           -- hi1 ≤ 65535
        · scalar_tac           -- measure decreases
    · -- ¬ lo < hi : done lo, and lo = hi
      rename_i hge
      refine ⟨hlo, ?_⟩
      have heq : lo.val = hi.val := by scalar_tac
      rw [heq]; exact hhi
  · -- hInv at (0, 65535)
    exact ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
#print axioms isqrt_correct
