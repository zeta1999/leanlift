-- Proof obligation for `bisect_sqrt` (SPEC §10 level L3) — the bisection METHOD,
-- over the Aeneas-extracted loop. Engine prepends import/opens/namespace + the
-- freshly-EXTRACTED defs, appends `end kernel`.
--
-- Same recipe as isqrt (loop.spec_decr_nat; measure hi-lo; invariant
-- lo²≤n ∧ n<(hi+1)² ∧ lo≤hi ∧ hi≤65535) plus the ε-termination: the loop exits
-- when hi-lo ≤ eps, and the postcondition's upper bound widens to (lo+eps+1)²
-- via squaring-monotonicity (Nat.mul_le_mul on hi+1 ≤ lo+eps+1). See
-- docs/PLAN-proofs.md Appendix A. Sorry-free.
theorem bisect_correct (n eps : Std.U32) :
    bisect_sqrt n eps ⦃ r =>
      r.val * r.val ≤ n.val ∧ n.val < (r.val + eps.val + 1) * (r.val + eps.val + 1) ⦄ := by
  unfold bisect_sqrt bisect_sqrt_loop
  apply loop.spec_decr_nat
    (measure := fun x => x.2.val - x.1.val)
    (inv := fun x => x.1.val * x.1.val ≤ n.val ∧ n.val < (x.2.val + 1) * (x.2.val + 1)
            ∧ x.1.val ≤ x.2.val ∧ x.2.val ≤ 65535)
  · -- hBody
    rintro ⟨lo, hi⟩ ⟨hlo, hhi, hle, hcap⟩
    simp only [bisect_sqrt_loop.body]
    progress as ⟨i, hi_i⟩          -- i = hi - lo
    split_ifs with he
    · -- i > eps  ⇒  hi - lo > eps  ⇒  lo < hi : one bisection step
      progress as ⟨i1, hi_i1⟩      -- i1 = lo + hi
      progress as ⟨i2, hi_i2⟩      -- i2 = i1 + 1
      progress as ⟨mid, hi_mid⟩    -- mid = i2 / 2
      progress as ⟨i3, hi_i3⟩      -- i3 = mid * mid
      case hmax =>
        have hm : mid.val ≤ 65535 := by scalar_tac
        have h2 := Nat.mul_le_mul hm hm
        scalar_tac
      split_ifs with hb
      · -- mid² ≤ n : continue with (mid, hi)
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨?_, hhi, ?_, hcap, ?_⟩
        · have : i3.val ≤ n.val := by scalar_tac
          rw [hi_i3] at this; exact this
        · scalar_tac
        · scalar_tac
      · -- mid² > n : continue with (lo, mid-1)
        progress as ⟨hi1, hi_hi1⟩
        refine ⟨hlo, ?_, ?_, ?_, ?_⟩
        · have hgt : n.val < i3.val := by scalar_tac
          rw [hi_i3] at hgt
          have hmid1 : hi1.val + 1 = mid.val := by scalar_tac
          rw [hmid1]; exact hgt
        · scalar_tac
        · scalar_tac
        · scalar_tac
    · -- i ≤ eps  ⇒  hi - lo ≤ eps : done lo, within the ε-bracket
      refine ⟨hlo, ?_⟩
      -- n < (hi+1)² ≤ (lo+eps+1)²  since hi ≤ lo + eps
      have hb : hi.val + 1 ≤ lo.val + eps.val + 1 := by scalar_tac
      calc n.val < (hi.val + 1) * (hi.val + 1) := hhi
        _ ≤ (lo.val + eps.val + 1) * (lo.val + eps.val + 1) := Nat.mul_le_mul hb hb
  · -- hInv at (0, 65535)
    exact ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
#print axioms bisect_correct
