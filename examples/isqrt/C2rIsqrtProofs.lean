-- Proof obligation for `isqrt` (SPEC §10 level L3) over the extraction of the
-- MACHINE-TRANSLATED Rust: cpp2rust renders C++ unsigned arithmetic with
-- `wrapping_*` ops, so unlike `IsqrtProofs.lean` (checked `+ * -`, side goals
-- of the no-overflow kind) the obligations here are of the mod-vanishes kind —
-- the invariant's `hi ≤ 65535` bound makes every wrap a no-op:
--   lo + hi + 1 ≤ 131071 < 2³²  and  mid² ≤ 65535² < 2³²  and  1 ≤ mid.
-- The engine prepends `import Aeneas`, the opens, `namespace kernel`, and the
-- freshly-EXTRACTED defs, then appends `end kernel`.
set_option maxHeartbeats 1000000 in
theorem isqrt_correct (n : Std.U32) :
    isqrt n ⦃ r => r.val * r.val ≤ n.val ∧ n.val < (r.val + 1) * (r.val + 1) ⦄ := by
  unfold isqrt isqrt_loop
  apply loop.spec_decr_nat
    (measure := fun x => x.2.val - x.1.val)
    (inv := fun x => x.1.val * x.1.val ≤ n.val ∧ n.val < (x.2.val + 1) * (x.2.val + 1)
            ∧ x.1.val ≤ x.2.val ∧ x.2.val ≤ 65535)
  · -- hBody
    rintro ⟨lo, hi⟩ ⟨hlo, hhi, hle, hcap⟩
    simp only [isqrt_loop.body, lift]
    split
    · -- lo < hi
      rename_i hlt
      progress as ⟨mid, hmid⟩
      -- mid = (((lo+hi) % 2³²) + 1) % 2³² / 2 = (lo+hi+1)/2 — the wraps vanish
      have hmid' : mid.val = (lo.val + hi.val + 1) / 2 := by
        simp only [core.num.U32.wrapping_add_val_eq] at hmid
        scalar_tac
      have hmlo : lo.val < mid.val := by scalar_tac
      have hmhi : mid.val ≤ hi.val := by scalar_tac
      have hm65 : mid.val ≤ 65535 := by scalar_tac
      have hsq : (core.num.U32.wrapping_mul mid mid).val = mid.val * mid.val := by
        have h2 := Nat.mul_le_mul hm65 hm65
        simp only [core.num.U32.wrapping_mul_val_eq]
        scalar_tac
      split_ifs with hb
      · -- mid² ≤ n : continue with (mid, hi)
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨?_, hhi, ?_, hcap, ?_⟩
        · rw [← hsq]; scalar_tac
        · scalar_tac
        · scalar_tac
      · -- mid² > n : continue with (lo, mid-1)
        simp only [Aeneas.Std.WP.spec_ok]
        have hsub : (core.num.U32.wrapping_sub mid 1#u32).val = mid.val - 1 := by
          simp only [core.num.U32.wrapping_sub_val_eq]
          scalar_tac
        refine ⟨hlo, ?_, ?_, ?_, ?_⟩
        · -- n < ((mid-1)+1)² = mid²
          have hgt : n.val < mid.val * mid.val := by rw [← hsq]; scalar_tac
          rw [hsub]
          have : mid.val - 1 + 1 = mid.val := by scalar_tac
          rw [this]; exact hgt
        · rw [hsub]; scalar_tac
        · rw [hsub]; scalar_tac
        · rw [hsub]; scalar_tac
    · -- ¬ lo < hi : done lo, and lo = hi
      rename_i hge
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨hlo, ?_⟩
      have heq : lo.val = hi.val := by scalar_tac
      rw [heq]; exact hhi
  · -- hInv at (0, 65535)
    exact ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
#print axioms isqrt_correct
