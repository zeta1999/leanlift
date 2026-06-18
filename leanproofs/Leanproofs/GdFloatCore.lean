/-
  Phase B (core) — the axiom-free analytic backbone of the f64 transport.

  A floating-point gd step is a (1+δ)-perturbation of the exact-ℝ step plus a
  tiny absolute (subnormal) term. Abstract that away: model the displacement
  magnitude of ANY such perturbed iteration as a sequence `w : ℕ → ℝ` obeying

      |w (k+1)| ≤ q · |w k| + s        (q = |ρ|·(1+c·u),  s = rounding floor)

  and prove, with NO custom axioms, the discrete input-to-state envelope:

      |w K| ≤ q^K · |w 0| + s · Σ_{i<K} q^i          (`perturbed_envelope`)
            ≤ q^K · |w 0| + s / (1 − q)   (for q < 1)  (`perturbed_bound`)

  and that the envelope converges to the `s/(1−q)` neighborhood
  (`envelope_tendsto`). Instantiated by the FloatModel bridge (next sub-step,
  axiom-gated) with `q = |1−2η|·(1+c·u)` and `s = O(η_sub)`, this is exactly the
  "f64 gd converges to an O(u) neighborhood of the true minimum" headline (B2/B3).

  This file is the part that is *proved*; the rounding model it will be applied
  to is the part that is *trusted* (`FloatModel.lean`, not yet added).
-/
import Mathlib

namespace Leanproofs.GdFloatCore

open Filter Topology Finset

/-- **B-core / envelope.** Any nonneg-rate perturbed contraction is bounded by the
geometric envelope plus the accumulated additive floor. No assumption `q < 1`. -/
theorem perturbed_envelope (q s : ℝ) (hq0 : 0 ≤ q) (w : ℕ → ℝ)
    (hrec : ∀ k, |w (k + 1)| ≤ q * |w k| + s) (K : ℕ) :
    |w K| ≤ q ^ K * |w 0| + s * ∑ i ∈ Finset.range K, q ^ i := by
  induction K with
  | zero => simp
  | succ k ih =>
      calc |w (k + 1)| ≤ q * |w k| + s := hrec k
        _ ≤ q * (q ^ k * |w 0| + s * ∑ i ∈ Finset.range k, q ^ i) + s := by
              have := mul_le_mul_of_nonneg_left ih hq0
              linarith
        _ = q ^ (k + 1) * |w 0| + s * ∑ i ∈ Finset.range (k + 1), q ^ i := by
              rw [geom_sum_succ]; ring

/-- **B-core / uniform bound.** For a genuine contraction `q < 1`, the geometric
sum collapses to `1/(1−q)`, giving a single closed envelope. -/
theorem perturbed_bound (q s : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hs : 0 ≤ s)
    (w : ℕ → ℝ) (hrec : ∀ k, |w (k + 1)| ≤ q * |w k| + s) (K : ℕ) :
    |w K| ≤ q ^ K * |w 0| + s / (1 - q) := by
  have henv := perturbed_envelope q s hq0 w hrec K
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hsum : ∑ i ∈ Finset.range K, q ^ i ≤ 1 / (1 - q) := by
    have hmul : (∑ i ∈ Finset.range K, q ^ i) * (1 - q) = 1 - q ^ K := by
      linear_combination -geom_sum_mul q K
    rw [le_div_iff₀ h1q, hmul]
    nlinarith [pow_nonneg hq0 K]
  have hsterm : s * ∑ i ∈ Finset.range K, q ^ i ≤ s / (1 - q) := by
    calc s * ∑ i ∈ Finset.range K, q ^ i ≤ s * (1 / (1 - q)) := by gcongr
      _ = s / (1 - q) := by ring
  linarith

/-- **B-core / neighborhood.** The closed envelope `q^K·|w₀| + s/(1−q)` converges
to the `s/(1−q)` rounding-floor neighborhood as `K → ∞`. With `perturbed_bound`,
the perturbed iteration is eventually trapped in `[0, s/(1−q)+ε]` for every ε. -/
theorem envelope_tendsto (q s w0 : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun K => q ^ K * w0 + s / (1 - q)) atTop (𝓝 (s / (1 - q))) := by
  have hpow : Tendsto (fun K => q ^ K * w0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const w0
  simpa using hpow.add_const (s / (1 - q))

end Leanproofs.GdFloatCore
