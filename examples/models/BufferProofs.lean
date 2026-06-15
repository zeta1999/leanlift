-- Proof obligation for `admit` (PLAN-perf-demo, L3): the CODE mirror of the link
-- model's buffer safety, over the Aeneas-EXTRACTED `Result Std.U32` def. The
-- engine prepends `import Aeneas`, the opens, `namespace kernel`, and the
-- freshly-extracted `def admit …`, then appends `end kernel`.
--
-- This is the code-level twin of the model→Lean qualitative bound
-- (`lift model prove link`: buf ≤ K): the Rust the sender would actually run is
-- proved to keep the buffer in range — `admit` never exceeds K, so the `u32`
-- add never overflows. (The sibling `release` no-underflow proof is analogous.)
theorem admit_le (buf k : Std.U32) (h : buf.val ≤ k.val) :
    admit buf k ⦃ r => r.val ≤ k.val ⦄ := by
  unfold admit
  split
  · step as ⟨ r, hr ⟩      -- buf + 1  (buf < k ≤ U32.max ⇒ no overflow)
    scalar_tac
  · simp; scalar_tac        -- ¬(buf < k) ∧ buf ≤ k ⇒ buf = k

#print axioms admit_le
