/-
  Phase A — exact-ℝ convergence of fixed-step gradient descent (`opt-gd`).

  Mirrors `examples/opt/gd.cpp` / `Gd.lean` over the reals:
    minimize  f(x,y) = (x-1)² + (y-2)²,  ∇f = (2(x-1), 2(y-2)),
    step  p ← p − η·∇f(p),  return f(x_K, y_K) after K steps.

  The iteration decouples and linearises exactly: with ρ = 1 − 2η,
    (x_K − 1) = ρ^K (x₀ − 1),   (y_K − 2) = ρ^K (y₀ − 2),
  hence the closed form  f(x_K,y_K) = ρ^{2K} · f(x₀,y₀)  (`gd_objective_closed`).
  From it: descent for η ∈ [0,1] (`gd_descent`) and convergence to 0 for
  η ∈ (0,1) (`gd_converges`). Sorry-free; the reference the f64 proof transports.
-/
import Mathlib

namespace Leanproofs.GdReal

open Filter Topology

/-- The objective `f(x,y) = (x-1)² + (y-2)²`. -/
def fObj (x y : ℝ) : ℝ := (x - 1) ^ 2 + (y - 2) ^ 2

/-- One gradient-descent step with step size `η` (exact reals). -/
def gdStep (η : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 - η * (2 * (p.1 - 1)), p.2 - η * (2 * (p.2 - 2)))

/-- The state after `K` steps from `(x₀,y₀)`. -/
def gdReal (η : ℝ) (K : ℕ) (x0 y0 : ℝ) : ℝ × ℝ :=
  (gdStep η)^[K] (x0, y0)

/-- The displacement contracts by exactly `ρ = 1 − 2η` per step (both coords). -/
theorem gd_displacement (η : ℝ) (K : ℕ) (x0 y0 : ℝ) :
    (gdReal η K x0 y0).1 - 1 = (1 - 2 * η) ^ K * (x0 - 1) ∧
    (gdReal η K x0 y0).2 - 2 = (1 - 2 * η) ^ K * (y0 - 2) := by
  induction K with
  | zero => simp [gdReal]
  | succ k ih =>
      obtain ⟨ihx, ihy⟩ := ih
      have hstep : gdReal η (k + 1) x0 y0 = gdStep η (gdReal η k x0 y0) := by
        simp only [gdReal, Function.iterate_succ', Function.comp_apply]
      rw [hstep]
      refine ⟨?_, ?_⟩
      · simp only [gdStep, pow_succ]
        linear_combination (1 - 2 * η) * ihx
      · simp only [gdStep, pow_succ]
        linear_combination (1 - 2 * η) * ihy

/-- **A1 — closed form.** `f(x_K,y_K) = ρ^{2K} · f(x₀,y₀)`, `ρ = 1 − 2η`. -/
theorem gd_objective_closed (η : ℝ) (K : ℕ) (x0 y0 : ℝ) :
    fObj (gdReal η K x0 y0).1 (gdReal η K x0 y0).2
      = (1 - 2 * η) ^ (2 * K) * fObj x0 y0 := by
  obtain ⟨hx, hy⟩ := gd_displacement η K x0 y0
  have h2 : (1 - 2 * η) ^ (2 * K) = ((1 - 2 * η) ^ K) ^ 2 := by
    rw [show 2 * K = K * 2 from Nat.mul_comm 2 K, pow_mul]
  simp only [fObj]
  rw [hx, hy, h2]; ring

/-- **A2 — descent.** For `η ∈ [0,1]` the objective never increases. -/
theorem gd_descent (η : ℝ) (K : ℕ) (x0 y0 : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    fObj (gdReal η K x0 y0).1 (gdReal η K x0 y0).2 ≤ fObj x0 y0 := by
  rw [gd_objective_closed]
  have hf : 0 ≤ fObj x0 y0 := by simp only [fObj]; positivity
  have hsq : (1 - 2 * η) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hρ : (1 - 2 * η) ^ (2 * K) ≤ 1 := by
    rw [pow_mul]; exact pow_le_one₀ (sq_nonneg _) hsq
  exact mul_le_of_le_one_left hf hρ

/-- **A3 — convergence.** For `η ∈ (0,1)` the objective tends to `0`. -/
theorem gd_converges (η x0 y0 : ℝ) (h0 : 0 < η) (h1 : η < 1) :
    Tendsto (fun K => fObj (gdReal η K x0 y0).1 (gdReal η K x0 y0).2) atTop (𝓝 0) := by
  have hfun : (fun K => fObj (gdReal η K x0 y0).1 (gdReal η K x0 y0).2)
            = fun K => (1 - 2 * η) ^ (2 * K) * fObj x0 y0 := by
    funext K; exact gd_objective_closed η K x0 y0
  rw [hfun]
  have hbase : (1 - 2 * η) ^ 2 < 1 := by
    nlinarith [mul_pos h0 (show (0:ℝ) < 1 - η by linarith)]
  have hpow : Tendsto (fun K => (1 - 2 * η) ^ (2 * K)) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (1 - 2 * η)) hbase
    simpa [pow_mul] using this
  simpa using hpow.mul_const (fObj x0 y0)

end Leanproofs.GdReal
