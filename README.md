<p align="center">
  <img src="assets/logo.svg" alt="leanlift" width="160"/>
</p>

<h1 align="center">leanlift</h1>

<p align="center">
  <strong>Lift a function into a Lean 4 model and prove it's the same function — by bit-exact differential execution.</strong>
</p>

<p align="center">
  <img src="https://img.shields.io/badge/status-WIP-yellow.svg" alt="WIP">
  <img src="https://img.shields.io/badge/Lean4-4.28-blueviolet.svg" alt="Lean4">
  <img src="https://img.shields.io/badge/oracle-bit--exact-green.svg" alt="bit-exact">
  <img src="https://img.shields.io/badge/sound%20path-Charon%2BAeneas-orange.svg" alt="Aeneas">
  <img src="https://img.shields.io/badge/trust-LLM%20proposes%2C%20algorithm%20disposes-lightgrey.svg" alt="trust model">
</p>

> **⚠ Work in progress.** The validation spine is complete end to end; float kernels are L1 (testing) only — native `Float` is opaque, so float *proofs* are future work. See [`SPEC.md`](./SPEC.md) and [`docs/`](./docs) for the design and open tracks.

---

The trust model is **"LLM proposes, algorithm disposes."** A candidate Lean
translation is *never trusted*: the differential oracle and the Lean kernel
discharge or refute it. A wrong candidate produces unexplained mismatches, drops
to L0, and exits nonzero. See [`SPEC.md`](./SPEC.md) for the full design.

## The validation ladder

```
L0  typechecks         the candidate elaborates and runs
L1  conformant         bit-exact vs the source oracle on a deterministic vector set
L3  proved             a theorem on the extracted model, certified sorry-free
```

## Front-ends — how a candidate is obtained

| front-end | source | how the Lean candidate is produced | trust |
|---|---|---|:-:|
| **Prewritten** | C++ | hand-written model (ground truth for tests) | oracle-checked |
| **Sound (Rust)** | Rust | **extracted** by Charon + Aeneas (no hand-writing) | by construction |
| **LLM** | C++ / Go / Solidity | an agent translates it, then propose→difftest→repair | oracle-checked |
| **cpp2rust** | C++ | [cpp2rust](https://github.com/Cpp2Rust/cpp2rust) machine-translates C++→Rust, then Charon + Aeneas extract the Rust | oracle-checked, deterministic (no LLM) |

## What it verifies

| domain | examples | the lesson |
|---|---|---|
| **Integer** (checked `UInt`) | `streamed`, `avg`, `dot2` | the unsigned-overflow `wrap` boundary — C++ wraps, the checked model fails |
| **Integer loops / methods** | `isqrt`, `bisect` | a proven postcondition over a bounded loop / ε-bracket method |
| **Low-precision** | `quant` | one parametric quantizer, fp8 → f64; `\|q−n\| ≤ ulp/2` |
| **Float** (IEEE-754 binary64) | `fadd`, `opt-gss`, `opt-gd`, `opt-hj` | numerical **optimization**, bit-exact vs C++ `double` |

### Float optimization kernels ([`lean-opt`](../numerical-algorithms/lean-opt))

A ladder of `double` optimizers — Lean's native binary64 `Float` matches C++
`double` **bit-for-bit** on `+ − × ÷ √` under `-ffp-contract=off`, so the oracle
is exact (NaN/`-0.0` canonicalized):

| kernel | algorithm | property checked (L1) |
|---|---|---|
| `opt-gss` | golden-section search (1D) | `a ≤ x ≤ b ∧ \|x−3\| ≤ ½·tol + √ε` |
| `opt-gd`  | gradient descent (multi-D) | `0 ≤ f(x_K) ≤ f(x_0)` (descent, η ≤ 1) |
| `opt-hj`  | Hooke–Jeeves (derivative-free, à la NLOpt) | `0 ≤ f(best) ≤ f(start)` |

The `√ε` floor in the `opt-gss` bound is real: a derivative-free search on a
quadratic can only locate the minimizer to ≈`1e-8` — the tool *measures* it.

**Convergence is proved, not just tested.** Beyond L1 bit-exact faithfulness,
[`lean-opt/proofs`](../numerical-algorithms/lean-opt/proofs) carries machine-checked
(Lean 4 + Mathlib, **sorry-free**) convergence theory, in three honest layers:

| layer | result |
|---|---|
| **ℝ** | `gd_converges` (geometric `(1-2η)^{2n}→0`), `gss_golden_converges` (bracket `→ x*`), `hj_converges` + `hj_stall` (monotone ↓, stalls only near-optimally) |
| **float** | a parametric rounding model with a proven `\|fl(x)−x\| ≤ ½·ulp`, instantiated f32 (2⁻²³) vs f64 (2⁻⁵²) — `f64_finer_than_f32` |
| **compose** | `perturbed_contraction` ⇒ `\|fl_xₙ − x*\| ≤ ρⁿ·\|e₀\| + ½ulp/(1−ρ)` (method error + a precision-shrinking rounding floor) |

The **honesty seam**: native Lean `Float` is `@[extern]` (opaque), so the *native*
kernel stays L1 bit-exact; the convergence/rounding theorems are proved for the
idealized ℝ algorithm and a faithful parametric float model. The `Float32` path
(`fadd32`) gives real binary32-vs-binary64 differential runs.

## Four C++→Lean translation lanes

The LLM front-end is **agent-swappable** — any backend may propose; the oracle
disposes identically. The lanes double as a model-quality comparison
(`lift verify --lane <name> cpp-*`):

| lane | backend | where |
|---|---|---|
| `claude` | `claude -p` (reference) | local |
| `skill`  | same, driven from [`SKILL.md`](./SKILL.md) — proves the doc is self-sufficient | local |
| `gemma`  | `gemma4:e4b` via ollama (16 GB class) | local |
| `qwen`   | Qwen3 on an OpenAI-compatible endpoint | remote (env-configured, skipped until set) |
| `lh`     | [le-harnais](https://github.com/) `lh model chat` (optional; model via `LEANLIFT_LH_MODEL`) | local (skipped unless `lh` is on PATH) |

Responses are content-addressed under `.leanlift-cache/`, keyed by lane + prompt,
so reruns don't re-query. See [`SKILL.md`](./SKILL.md) for the portable skill the
lanes follow.

The `lh` lane is **optional** — le-harnais is a separate (closed-source) tool. leanlift has **no
build dependency** on it: the lane is a runtime shell-out that self-skips when `lh` isn't installed,
so a le-harnais-free checkout builds and runs identically. It's the "pluggable LLM client" mode
(le-harnais proposes a translation; leanlift's own differential oracle still decides L1).

## Quick start

```bash
cargo build --release

./target/release/lift verify avg               # integer: the midpoint-overflow bug
./target/release/lift verify opt-gss           # float: golden-section, bit-exact
./target/release/lift verify cpp-opt-gss --lane gemma   # LLM translates it (local model)
./target/release/lift prove  rust-isqrt        # L3: r·r ≤ n < (r+1)², sorry-free
./tests/run.sh                                 # positive + negative + sound suite

# the optimization ladder + lane-quality report:
cd ../numerical-algorithms/lean-opt && ./ci.sh
```

The engine compiles the Lean support libraries (`LeanLift.Checked`,
`LeanLift.Float`) to `.olean` on first run. The **sound Rust path**
(`rust-streamed`, `rust-isqrt`, `rust-bisect`) needs Charon + Aeneas built —
`scripts/build_aeneas.sh`.

### The cpp2rust lane (`c2r-*`) — deterministic C++ → Lean

[cpp2rust](https://github.com/Cpp2Rust/cpp2rust) (MIT, PLDI 2026) machine-translates
C++ to Rust from the clang AST; leanlift then runs the generated crate through the
same Charon + Aeneas extraction as the Rust path:

```
C++ ──cpp2rust──▶ Rust ──Charon+Aeneas──▶ Lean  (vs. the C++ binary, bit-exact)
```

Unlike the LLM lanes this chain is **deterministic and offline** — but the
translation is still *untrusted*: the differential oracle compares the extracted
Lean against the original C++ binary on the same vectors, so a mistranslation
shows up as an L1 divergence, never as silent trust. Build the tool with
`scripts/build_cpp2rust.sh` (fetches clang/LLVM 22 automatically if the system
toolchain is older; no sudo needed); locate it with `LEANLIFT_CPP2RUST`. Like the
`lh` lane, the `c2r-*` examples **self-skip** (exit 0) when the tool isn't built:

```bash
./target/release/lift verify c2r-avg      # C++ midpoint-overflow, via cpp2rust
./target/release/lift verify c2r-isqrt    # C++ loop kernel, via cpp2rust
./target/release/lift verify c2r-dot2     # C++ wrap-on-mul kernel, via cpp2rust
./target/release/lift prove  c2r-isqrt    # L3: r·r ≤ n < (r+1)² over the MACHINE-TRANSLATED kernel
```

The `c2r-isqrt` proof is the full ladder on a C++ source: cpp2rust renders the
C++ as wrapping-ops Rust, Aeneas extracts it, and
[`C2rIsqrtProofs.lean`](./examples/isqrt/C2rIsqrtProofs.lean) discharges the
same postcondition as `rust-isqrt` — with mod-vanishes obligations (the
invariant's `hi ≤ 65535` bound makes every wrap a no-op) in place of the
checked path's no-overflow side goals. Sorry-free, kernel-checked.

leanlift generates the crate from `cpp2rust --model=unsafe` output (scalar Rust,
`wrapping_*` ops — the faithful C++ unsigned semantics; the safe model's
`Rc<RefCell<_>>` cells are not extractable by Aeneas) and rejects any output that
needs the libcc2rs pointer runtime — the lane is for pointer-free kernels.

## L3 — proof (`lift prove`)

Beyond L1 conformance, `lift prove` discharges a theorem on the *extracted* model
and certifies it **sorry-free** (`#print axioms` shows no `sorryAx`):

```
lift prove rust-isqrt    # isqrt_correct: r·r ≤ n < (r+1)²              (a LOOP)
lift prove rust-bisect   # bisect_correct: lo² ≤ n < (lo+eps+1)²   (bisection METHOD)
  → level: L3 proved  (Lean theorems closed, sorry-free)
    axioms: propext, Classical.choice, Quot.sound
```

A false theorem fails to elaborate and exits nonzero — the Lean kernel is the
gate. (Float kernels stay at L1: native `Float` is `@[extern]`, opaque to the
kernel; a certified rounding-bound track is in [`docs/float-formats.md`](docs/float-formats.md).)

## Behavioural models (`lift model`)

A **dual axis**: author one behavioural model and generate, from a single source
of truth, a Lean proof (qualitative), a PRISM model (quantitative), and runnable
code. Seven families (FSM, Petri, behaviour tree, coloured PN, stochastic GSPN,
queueing net, real-time). See [`docs/SPEC-models.md`](docs/SPEC-models.md),
[`docs/TUTORIAL.md`](docs/TUTORIAL.md), [`docs/TESTING.md`](docs/TESTING.md).

```
lift model check    examples/models/dock.model.toml    # M1 BFS: reachability + safety
lift model prove    examples/models/mcl.model.toml      # M3 Lean: safety, sorry-free
lift model prism    examples/models/link.model.toml     # M2 CTMC: throughput/delay/overflow
```

The **M-ladder** mirrors the code ladder: M1 checked (native BFS), M2
model-checked (PRISM/CTMC), M3 proved (Lean). Each example ships a `*.recipe.md`;
all are exercised by `tests/run.sh`.

## Project structure

```
src/
  sig.rs        machine value types (int + float) & signatures
  oracle.rs     C++/Go oracle: compile source + a typed runner (float = bit-pattern)
  harness.rs    the LLM front-end: 4 lanes + propose→difftest→repair loop
  frontend.rs   how a candidate is obtained (prewritten / Charon+Aeneas / LLM / cpp2rust)
  compare.rs    bit-exact comparator + divergence classifier + postconditions
  prove.rs      L3: assemble model + theorems, certify sorry-free
  models/       the behavioural-model axis (lift model)
lean/LeanLift/
  Checked.lean  audited checked-integer library (the wrap-vs-fail semantics)
  Float.lean    audited IEEE-754 float library (bounded iteration, bit-exact)
examples/
  {streamed,avg,dot2,isqrt,bisect,quant}/   integer + low-precision kernels
  opt/{gss,gd,hj}.{cpp,lean}                float optimization kernels
  rust-kernels/                             the sound Rust path + proof obligations
SKILL.md        the portable C++→Lean translation skill (the lanes follow it)
```

## Next

Signed/float L3 proofs (FloatSpec/Flean/FLoPS), a proof kernel for the support
library, structs/arrays, annotation ingestion → Contract IR (SPEC §7). The path
toward numerical algorithms (isqrt → bisection → float error-bounds → optimizers)
is in [`docs/PLAN-proofs.md`](docs/PLAN-proofs.md).
