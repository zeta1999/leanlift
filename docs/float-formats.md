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
      *Partial (§7): a vendor seam `Opt/Float/Vendor.lean` with a `RoundingModel`
      interface is built so FLoPS/Flean drop in behind it; the actual dep eval /
      drop-in is still pending.*
- [ ] Add a parametric `FloatFmt` to `sig.rs` and instantiate **f32, f64, bf16,
      fp16, fp8-e4m3, fp8-e5m2, fp4** (+ the P3109 params: signedness, domain).
      *Partial: `sig.rs` has native `FloatType` F32/F64 (§7) and the §6 parametric
      `quantize_rne(prec, ·)` covers the significand for fp8/bf16/fp16/f32/f64; the
      full `FloatFmt{exp_bits,prec,bias,rounding,saturating}` config + fp8/fp4
      exponent/bias/subnormal instances are not yet in `sig.rs`.*
- [x] **Implement comparator float modes** (`ulp` / `rel` / `abs`, NaN
      canonicalization, signed-zero, rounding-mode divergence reporting) — SPEC §6.
      Done in `compare.rs` (`FloatTol`, `float_match`, `Class::ToleranceDivergence`),
      wired through `lift verify --float-tol exact|ulp:N|rel:E|abs:E` (float kernels
      only; default exact preserves every bit-exact path). 14 comparator unit tests
      + brutal review (fixed a Rel/Abs overflow-to-Inf false-CONFORM). See §8.
- [ ] Float **oracle** per format: native for f32/f64; library/bit-twiddle for the
      low-precision ones; pin the rounding/saturation profile (SPEC §11), forbid
      `-ffast-math` / FMA-contraction unless modeled.
      *Partial (§7): native f32/f64 oracle with `-ffp-contract=off` + NaN/−0
      canonicalization; low-precision (fp8/fp4) library oracle still TODO.*
- [ ] First float example end-to-end at **L1** (testing): e.g. an fp8 dot-product /
      GEMM tile vs the model under `ulp`/`rel`.
      *Partial: §6 did per-element fp8 `quantize_rne` (894 vectors, bit-exact) and §7
      `fadd`/`fadd32`/`opt-*`; a low-precision dot-product/GEMM tile exercising the new
      `--float-tol ulp/rel` modes is the natural next step now that the comparator
      supports them.*
- [x] First float **L3**: a per-op rounding bound (`fl(a+b)` within `u·|a+b|`) — done
      in §7 (`Opt/Float/Fmt.lean::roundTo_le_half`, f32 2⁻²³ / f64 2⁻⁵²), composed with
      the Mathlib ℝ convergence rate into an end-to-end ε bound, sorry-free.
- [x] Honesty gate: the Mathlib-heavy float track lives in a separate offline lake
      project (`../numerical-algorithms/lean-opt`), built sorry-free with a documented
      vendor seam; native `Float` results are labelled **L1 only** (kernel-opaque, no
      theorem stated). Never report a `sorry`-backed bound as proven.

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

## 7. Result (2026-06-16) — native f64/f32 path + convergence proofs

The float track advanced on three fronts (see `../numerical-algorithms/lean-opt`):

- **Native `Float`/`Float32` end-to-end.** `sig.rs` gained `FloatType` (F32/F64);
  the oracle emits a bit-pattern runner (`-ffp-contract=off`, NaN/`-0.0`
  canonical) and the Lean runner uses native `Float`/`Float32`. `lift verify`
  `fadd`/`opt-gss`/`opt-gd`/`opt-hj` (f64) and `fadd32` (f32) are **bit-exact** —
  Lean's native binary64/binary32 ≡ C++ `double`/`float`. This is L1 only:
  native `Float` is `@[extern]`, opaque to the kernel (no theorem statable).
- **Convergence proved over ℝ** (Mathlib, sorry-free): `gd_converges`,
  `gss_golden_converges`, `hj_converges` + `hj_stall` — the §1 *method-error*
  notion, finally machine-checked for the optimizer kernels.
- **A parametric rounding model** (`Opt/Float/Fmt.lean`): the §1 *rounding-error*
  notion — `roundTo_le_half : |fl(x)−x| ≤ ½·ulp`, f32 (2⁻²³) vs f64 (2⁻⁵²) —
  composed with the ℝ rate (`perturbed_contraction`) into an end-to-end ε bound
  `|fl_xₙ − x*| ≤ ρⁿ·|e₀| + ½ulp/(1−ρ)`. Built in-repo (offline, sorry-free) with
  a documented **vendor seam** (`Opt/Float/Vendor.lean`) so FLoPS/Flean (§2) can
  drop in behind the `RoundingModel` interface without touching the proofs.

## 8. Result (2026-06-17) — comparator float modes (SPEC §6, TODO item 3)

The difftest comparator was integer/bit-exact only: `lean_val == cpp_val` string
equality. That is exactly right for native f32/f64 (Lean's binary64/binary32 ≡ C++
`double`/`float` bit-for-bit) but cannot express the **bounded** divergence a
low-precision or vendor-pinned oracle legitimately produces. Now implemented in
`src/compare.rs`:

- **`FloatTol`** = `Exact | Ulp(n) | Rel(eps) | Abs(eps)`, parsed from the CLI spec
  `exact | ulp:N | rel:E | abs:E`.
- **`float_match(a_bits, b_bits, {tol,width})`** decodes the result bit patterns at
  the kernel's float width and classifies `BitExact / WithinTolerance / Diverge`
  with **NaN canonicalization** (any NaN ≡ any NaN; NaN vs finite always diverges),
  **signed-zero** (−0 ≡ +0), **Inf-by-sign**, and a sign-magnitude → monotone-order
  transform for exact integer ULP distance.
- **`Class::ToleranceDivergence`** — a within-tolerance float difference is REPORTED
  (human `tol-div:` line + `report.json` `tolerance_divergence` count + a
  per-divergence record) and counts as conformant; an out-of-tolerance one is a
  `Mismatch` (real bug), exactly as before.
- Wired through **`lift verify <kernel> --float-tol <spec>`**; the flag is rejected
  on a non-float example (fail-closed), and `None` (the default) leaves every
  existing bit-exact path byte-identical. `fadd --float-tol ulp:2` stays
  209/209 Conform (native f64 is already bit-exact).

**Soundness.** `Exact` accepts only bit-identical-or-canonical pairs, so it can
never mask a divergence; the tolerance modes only ever *widen* (and report) the
accepted set. A brutal review found and fixed one false-CONFORM: in `Rel`/`Abs`
mode the difference of two far-apart finite values can overflow to `±Inf`, and
`Inf ≤ Inf` would have conformed the *maximal* divergence (`+MAX` vs `−MAX`) — now
guarded by requiring a finite difference. 14 comparator unit tests (ULP across the
sign/zero boundary, NaN/±0/Inf, rel/abs, f32 width, the overflow teeth, and the
`compare()` classification path). `ci.sh` GREEN.

Still on the integer/bit-exact default until a low-precision kernel (item 5) ships
that needs a non-`exact` tolerance against its vendor oracle — the comparator is now
ready for it.
