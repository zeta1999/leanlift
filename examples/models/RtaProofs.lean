-- Proof for `rta_term` (PLAN-qnet-rta §A, L3) — the DEDUCTIVE, unbounded
-- companion to the R2 Kani proof, over the Aeneas-EXTRACTED `Result Std.U32`
-- model of leanlift's OWN RTA interference term `⌈r/tj⌉·cj`. The engine prepends
-- `import Aeneas`, the opens, `namespace kernel`, and the extracted `def
-- rta_term …`, then appends `end kernel`.
--
-- We prove the extracted code computes exactly the spec `((r+tj−1)/tj)·cj`
-- (under the no-overflow premises the `Result` monad forces). Monotonicity in r
-- — what makes the RTA fixed-point iteration converge to the TRUE worst-case
-- response time — then follows from the spec by Nat.div/mul monotonicity
-- (`rta_term_mono_nat`, a pure-Nat corollary needing no extraction).

theorem rta_term_spec (r cj tj : Std.U32)
    (htj : 1 ≤ tj.val)
    (hsum : r.val + tj.val ≤ Std.U32.max)
    (hmul : ((r.val + tj.val - 1) / tj.val) * cj.val ≤ Std.U32.max) :
    rta_term r cj tj ⦃ res => res.val = ((r.val + tj.val - 1) / tj.val) * cj.val ⦄ := by
  unfold rta_term
  step as ⟨ i, hi ⟩      -- i = r + tj
  step as ⟨ i1, hi1 ⟩    -- i1 = i - 1
  step as ⟨ i2, hi2 ⟩    -- i2 = i1 / tj
  step as ⟨ res, hres ⟩  -- res = i2 * cj  (no-overflow side goals auto-discharged)
  rw [hres, hi2, hi1, hi]

/-- Monotonicity of the RTA term in the window `r` (pure Nat, the soundness fact:
    a non-decreasing recurrence ⇒ its iteration converges to the least fixed
    point = the true WCRT). `tj ≥ 1`. -/
theorem rta_term_mono_nat (r r' cj tj : Nat) (htj : 1 ≤ tj) (hrr : r ≤ r') :
    ((r + tj - 1) / tj) * cj ≤ ((r' + tj - 1) / tj) * cj := by
  apply Nat.mul_le_mul_right
  apply Nat.div_le_div_right
  omega

#print axioms rta_term_spec
#print axioms rta_term_mono_nat
