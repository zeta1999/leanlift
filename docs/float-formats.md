# Float & low-precision (DNN) formats — requirement, landscape, plan

> Researched 2026-06-13. Companion to `docs/PLAN-proofs.md` §II (the float track).
> leanlift today is **integer-only** (`sig.rs::IntType` = U8/U16/U32/U64, bit-exact
> comparator, checked-integer support lib). This is the plan to add floats.

## 0. Requirement

Support **f32, f64**, and the low-precision formats used in DNNs: **bf16, fp16**
(IEEE half), **fp8** (E4M3, E5M2), **fp4** (E2M1), and the **P3109** family. These
differ only in `(exponent bits, precision/mantissa bits, bias, special-value
encoding, rounding mode, saturation)`. So the model must be **parametric over a
format config** — one model + a config table — not N hand-written types.

## 1. The two error notions (why floats are the hard part)

- **Method / discretization error** — e.g. trapezoidal `|I_h − ∫f| ≤ C·h²·max|f''|`.
  A theorem over **ℝ**, nothing to do with floats; provable in Mathlib real-analysis.
- **Rounding error** — how the float implementation deviates from the real
  computation (≤ k ulp, or `|fl(x)−x| ≤ u·|x|` per op, propagated). Needs an
  IEEE-754 / low-precision model **with rounding**. Lean's native `Float` is
  **opaque to the kernel** (`@[extern]` binary64) → *no theorems are provable about
  it*. So a certified rounding bound needs a real formalization, not `Float`.

## 2. Lean float-library landscape (the earlier "nothing mature" was too pessimistic)

Three active Lean 4 efforts as of mid-2026:

| project | what | formats | error proofs | maturity | Mathlib |
|---|---|---|---|---|---|
| **FloatSpec** (Beneficial-AI-Foundation) | Flocq port to Lean 4 | IEEE-754, generic radix/format (f32/f64) | `Plus_error`/`Relative`/`Sterbenz`/`ulp` **stated but largely `sorry`** | early — v0.7.0, Lean v4.27.0-rc1 | yes |
| **Flean** (J. McKinsey) | from-scratch *parametric* float | `FloatCfg(prec, emin, emax)` → any binary format | error bounds **proven sorry-free**; **computable over ℚ** | "mostly done", not production (single NaN, no normal/subnormal unification) | yes |
| **FLoPS** (Rutgers) | the **P3109** low-precision standard | **parametric**: bitwidth, precision, signedness, domain — 3-bit upward (the ML-hardware target) | **sorry-free core**: rounding incl **stochastic**, saturation, FastTwoSum error (Thm 4.4–4.7); ~15k LOC | research-grade (arXiv 2602.15965) | yes (EReal) |

Takeaways:
- **Parametric is the right shape.** FLoPS (P3109) and Flean both parametrize the
  format ⇒ f32/f64/bf16/fp16/fp8/fp4 are *config instances*. Exactly the "shitload
  of DNN formats" requirement, as one model.
- **FLoPS is closest to the DNN world** — P3109 *is* the ML-hardware low-precision
  standard; it covers stochastic rounding + saturation (what fp8 training needs)
  and is sorry-free on its core.
- **Flean is computable over ℚ** ⇒ fits leanlift's exact-arithmetic + `#eval`
  differential-testing model (L1) *and* proves error bounds (L3). Lighter weight.
- **FloatSpec** is the most faithful IEEE-754 *structure*, but its error proofs are
  mostly `sorry` ⇒ **not usable for "accurate error estimates" yet**.

## 3. How it maps onto leanlift

- **Model.** Add a parametric `FloatFmt { exp_bits, prec, bias, rounding,
  saturating }` (mirrors Flean's `FloatCfg` / P3109's 4 params). Operations round
  via a *proven* rounder computable over ℚ. DNN formats = config instances.
- **L1 (testing).** Evaluate the model over ℚ via `#eval`; difftest against the
  oracle (hardware/library float). Needs the comparator's `ulp/rel/abs` modes +
  NaN canonicalization + signed-zero handling (SPEC §6, **currently unimplemented**).
- **L3 (proof).** Reuse the chosen library's proven rounding-error theorems for the
  rounding bound; Mathlib real-analysis for the method bound; compose.
- **The hard oracle problem.** The reference impl must match the target's rounding
  **bit-exactly per format**: f32/f64 are native C++/hardware; bf16/fp16 are
  library/intrinsic; **fp8 E4M3/E5M2 and fp4 vary by framework** (PyTorch / CUDA /
  etc.) incl. saturation and RNE-vs-stochastic. The oracle must pin *which*
  implementation it certifies against — a fidelity-profile question (SPEC §11).

## 4. Risks / decisions

- **Toolchain pinning.** Our Lean is **4.28.0** and the Aeneas backend pins it too;
  FloatSpec targets 4.27.0-rc1, FLoPS/Flean pin specific Mathlib versions. Bringing
  a float lib + Mathlib alongside the Aeneas-pinned toolchain may conflict — likely
  the float track lives in a **separate lake project** from the Aeneas/integer one.
- **Which library:** FLoPS (P3109, DNN-first, sorry-free, research code) vs Flean
  (parametric, sorry-free, lighter) vs wait on FloatSpec (faithful IEEE, proofs
  incomplete). Recommend evaluating **FLoPS + Flean** first.
- **Vendor** (git submodule / lake dep) vs reimplement the minimal slice needed.

## 5. TODO

- [ ] Evaluate **FLoPS** and **Flean** as a lake dependency; check Lean/Mathlib
      version compatibility against our 4.28 + Aeneas pin (isolate if needed).
- [ ] Add a parametric `FloatFmt` to `sig.rs` and instantiate **f32, f64, bf16,
      fp16, fp8-e4m3, fp8-e5m2, fp4** (+ the P3109 params: signedness, domain).
- [ ] Implement comparator float modes (`ulp` / `rel` / `abs`, NaN canonicalization,
      signed-zero, rounding-mode divergence reporting) — SPEC §6.
- [ ] Float **oracle** per format: native for f32/f64; library/bit-twiddle for the
      low-precision ones; pin the rounding/saturation profile (SPEC §11), forbid
      `-ffast-math` / FMA-contraction unless modeled.
- [ ] First float example end-to-end at **L1** (testing): e.g. an fp8 dot-product /
      GEMM tile vs the model under `ulp`/`rel`.
- [ ] First float **L3**: a per-op rounding bound (`fl(a+b)` within `u·|a+b|`) from
      the chosen library; then a method-error bound (trapezoidal) over ℝ in Mathlib;
      then compose for an end-to-end "implementation within ε of the true value".
- [ ] Honesty gate: keep the Mathlib-heavy float track isolated from the light,
      fast integer track; never report a `sorry`-backed bound as proven.

## Sources

- [FloatSpec (Reservoir)](https://reservoir.lean-lang.org/@Beneficial-AI-Foundation/FloatSpec)
- [Flean — Floating point numbers in Lean](https://josephmckinsey.com/flean2.html)
- [FLoPS: P3109 Floating-Point in Lean (arXiv 2602.15965)](https://arxiv.org/html/2602.15965)
- [Flocq (the Coq original)](https://flocq.gitlabpages.inria.fr/)
- [Lean Zulip — IEEE floats](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/IEEE.20floats.html)

## 6. Spike result (2026-06-13) — parametric quantizer, fp8 → f64

First float example landed at **L1**, validating the parametric-config approach
*before* any rounding-bound proof: `quantize_rne(prec, n)` — round `n` to `prec`
mantissa bits, round-to-nearest-even. **One function; the format is the `prec`
argument** (2=fp8-E5M2, 3=fp8-E4M3, 7=bf16, 10=fp16, **23=f32, 52=f64**).

- `lift verify quant` — the hand-written Lean model is **bit-exact vs the C++
  oracle on 894 vectors** spanning all six formats (small ints exact at high prec;
  large ints exercise f32/f64 rounding — e.g. `52, 2⁵³+1 → 2⁵³`, the textbook
  round-to-even).
- The **rounding-error bound `|q−n| ≤ ulp/2` holds 894/894** (checked empirically
  by `Profile::Quant`) — a real per-element error estimate at L1.
- `lift verify cpp-quant` — the LLM (`claude -p`) translated it **conformantly,
  staying inside the audited support-library API**: it synthesized the shifts and
  `log2` from checked `*`/`/` + bounded loops (`1<<<s` → repeated `*2`,
  `n>>>s` → `/2^s`, tie-to-even via quotient parity) rather than reaching for raw
  `Nat` bit-ops. Encouraging for the eventual L3 path (proofs need the audited lib).

Caveats (deliberately out of scope for this first test, tracked in §5): this is the
*significand-rounding core* only — exponent/bias/**subnormal**/NaN/Inf encoding and
saturation are not yet modeled, and the comparison is integer bit-exact (the
`ulp/rel/abs`/NaN comparator modes are still unimplemented). The L3 rounding-bound
*proof* still needs one of the libraries in §2.
