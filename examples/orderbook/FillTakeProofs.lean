-- Proof obligation for `fill_take` (PLAN-concurrency E1: the #10 sweep's
-- per-level fill in safe Rust, Charon+Aeneas extracted). The engine prepends
-- `import Aeneas`, the opens, `namespace kernel`, and the extracted def.
--
-- `fill_take filled qty q` is the body of the sweep loop: with `filled` of the
-- requested `q` already taken, take `min(qty, q − filled)` from the level. This
-- is `fillStep`'s `take` in leanlift-iris `PhaseA/Sweep.lean`. The premise
-- `filled ≤ q` is the loop invariant the sweep maintains (`filled ≤ Q`), and it
-- is exactly what makes the u32 subtraction total.

theorem fill_take_spec (filled qty q : Std.U32) (h : filled.val ≤ q.val) :
    fill_take filled qty q ⦃ r =>
      r.val = min qty.val (q.val - filled.val) ∧ filled.val + r.val ≤ q.val ⦄ := by
  unfold fill_take
  progress as ⟨rem, hrem⟩
  split <;> (simp only [Aeneas.Std.WP.spec_ok]; constructor <;> scalar_tac)

/-- **Premise inhabited, answer pinned.** 3 of 7 filled, a level of 10: take
    exactly 4, and the sweep is then complete. -/
theorem fill_take_3_10_7 : fill_take 3#u32 10#u32 7#u32 ⦃ r => r.val = 4 ⦄ := by
  apply WP.spec_mono (fill_take_spec 3#u32 10#u32 7#u32 (by decide))
  rintro r ⟨h, _⟩
  simp at h
  omega

#print axioms fill_take_spec
#print axioms fill_take_3_10_7
