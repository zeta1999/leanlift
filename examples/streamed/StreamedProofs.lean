-- Proof obligations for `streamed` (SPEC §10 level L3), over the Aeneas-extracted
-- `Result Std.U64` model. The engine prepends `import Aeneas`, `open …`,
-- `namespace kernel`, and the freshly-EXTRACTED `def streamed …`, then appends
-- `end kernel`; these theorems are proved about that exact extracted definition.
--
-- They discharge the `Result`-monad obligations (each u64 -/+/* is fallible) and
-- prove the I2 (bounded) / I3 (monotone, clamped) facts — the same properties the
-- spike's recovery.hpp consteval checks assume of the real arithmetic. Proofs are
-- hand-written (the `step as`/`scalar_tac` structure follows the 4-bind ramp); the
-- agent-assisted closing path (claude -p proposes tactics, the kernel disposes) is
-- the generalization (see docs/PLAN-proofs.md).

-- I3, low clamp: at or below start, nothing is recognised.
theorem streamed_low (deposit start stop t : Std.U64) (h : t.val ≤ start.val) :
    streamed deposit start stop t ⦃ r => r.val = 0 ⦄ := by
  unfold streamed
  have hle : t ≤ start := by scalar_tac
  simp [hle]

-- I2, high clamp / completion: at or past stop, fully vested.
theorem streamed_high (deposit start stop t : Std.U64)
    (hss : start.val < stop.val) (h : stop.val ≤ t.val) :
    streamed deposit start stop t ⦃ r => r.val = deposit.val ⦄ := by
  unfold streamed
  have h1 : ¬ (t ≤ start) := by scalar_tac
  have h2 : t ≥ stop := by scalar_tac
  simp [h1, h2]

-- I2, boundedness: GIVEN no overflow in deposit*(t-start), streamed succeeds and
-- never exceeds the deposit — the obligation the `Result` monad forces and the
-- differential test discovered empirically (`deposit*(t-start) ≤ U64.max`).
theorem streamed_bounded (deposit start stop t : Std.U64)
    (hss : start.val < stop.val)
    (hov : deposit.val * (t.val - start.val) ≤ Std.U64.max) :
    streamed deposit start stop t ⦃ r => r.val ≤ deposit.val ⦄ := by
  unfold streamed
  split
  · simp
  · split
    · simp
    · rename_i h1 h2
      step as ⟨ i, hi ⟩
      step as ⟨ i1, hi1 ⟩
      step as ⟨ i2, hi2 ⟩
      step as ⟨ q, hq ⟩
      have hle : i.val ≤ i2.val := by rw [hi, hi2]; scalar_tac
      have hb  : i1.val ≤ deposit.val * i2.val := by
        rw [hi1]; exact Nat.mul_le_mul (Nat.le_refl _) hle
      rw [hq]
      exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hb)

-- I3, monotonicity: a ≤ b ⇒ streamed(a) ≤ streamed(b) (the no-underflow fact).
theorem streamed_mono (deposit start stop a b : Std.U64)
    (hss : start.val < stop.val) (hab : a.val ≤ b.val)
    (hova : deposit.val * (a.val - start.val) ≤ Std.U64.max)
    (hovb : deposit.val * (b.val - start.val) ≤ Std.U64.max) :
    streamed deposit start stop a ⦃ ra =>
      streamed deposit start stop b ⦃ rb => ra.val ≤ rb.val ⦄ ⦄ := by
  unfold streamed
  split
  · split
    · simp
    · split
      · simp
      · step as ⟨ i, hi ⟩; step as ⟨ i1, hi1 ⟩; step as ⟨ i2, hi2 ⟩
        step as ⟨ q, hq ⟩; simp
  · split
    · rename_i h1 h2
      have hb1 : ¬ b ≤ start := by scalar_tac
      have hb2 : b ≥ stop := by scalar_tac
      simp [hb1, hb2]
    · rename_i h1 h2
      step as ⟨ ia, hia ⟩; step as ⟨ i1a, hi1a ⟩; step as ⟨ i2a, hi2a ⟩
      step as ⟨ qa, hqa ⟩
      split
      · scalar_tac
      · split
        · have hle : ia.val ≤ i2a.val := by rw [hia, hi2a]; scalar_tac
          have hb : i1a.val ≤ ia.val.succ * 0 + deposit.val * i2a.val := by
            simp; rw [hi1a]; exact Nat.mul_le_mul (Nat.le_refl _) hle
          simp; rw [hqa]
          exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; rw [hi1a] at *; omega)
        · step as ⟨ ib, hib ⟩; step as ⟨ i1b, hi1b ⟩; step as ⟨ i2b, hi2b ⟩
          step as ⟨ qb, hqb ⟩
          rw [hqa, hqb, hi2a, hi2b]
          apply Nat.div_le_div_right
          rw [hi1a, hi1b, hia, hib]
          exact Nat.mul_le_mul (Nat.le_refl _) (by scalar_tac)

#print axioms streamed_low
#print axioms streamed_high
#print axioms streamed_bounded
#print axioms streamed_mono
