# examples/opt — float optimization kernels

Numerical-optimization kernels in `double` (and `float`), each **lifted into a
Lean model and verified bit-exactly** against the C++ oracle, **and** backed by
machine-checked **convergence theory** over ℝ.

| kernel | source / model | L1 (bit-exact) | convergence proof (ℝ + float) |
|---|---|---|---|
| golden-section (1D) | `gss.cpp` / `Gss.lean` | `lift verify opt-gss` | `Opt.Real.Gss.gss_golden_converges` |
| gradient descent (multi-D) | `gd.cpp` / `Gd.lean` | `lift verify opt-gd` | `Opt.Real.Gd.gd_converges` + `Opt.Compose.gd_error_bound` |
| Hooke–Jeeves (derivative-free) | `hj.cpp` / `Hj.lean` | `lift verify opt-hj` | `Opt.Real.Hj.hj_converges` + `hj_stall` |

The proofs live in
[`../../numerical-algorithms/lean-opt/proofs`](../../../numerical-algorithms/lean-opt/proofs)
(separate Mathlib toolchain). Three honest layers — (1) the idealized **ℝ**
algorithm converges; (2) a parametric **float** model rounds within ½·ulp (f32
prec 24 vs f64 prec 53); (3) **compose** → `|fl_xₙ − x*| ≤ ρⁿ·|e₀| + ½ulp/(1−ρ)`.

**Seam:** native Lean `Float` is opaque, so these kernels' *native* models stay
L1 bit-exact; the convergence/rounding theorems are about the ℝ algorithm and the
parametric float model. `fadd`/`fadd32` are the f64/f32 smoke twins (real
binary32-vs-binary64 divergence).

All kernels use only `+ − × ÷ √` and comparisons (bit-exact-safe under
`-ffp-contract=off`), bounded loops (`Float.iterate`), and compute irrational
constants via `Float.sqrt` so C++ and Lean share the exact bits.
