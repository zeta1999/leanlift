# `leanlift` — preliminary specification (v0.1, draft)

> Working name. CLI: `lift`. Status: **preliminary** — written to be argued with.
> Grounded in the C++/Rust/Lean verification spike (see
> `../../tutor-tech/cpp-day44-constexpr-recovery/REPRODUCE_VERIFICATION.md`).

## 1. One-line pitch

Lift a function from **C++, Go, Solidity, or Rust** into a **Lean 4** model, and
**prove it's the same function** — automatically, by bit-exact differential
execution and (optionally) a machine-checked property — with a one-command CLI.

## 2. The core idea (the trust model)

There is exactly one mature source→Lean path (Rust, via Charon+Aeneas). For C++,
Go, and Solidity there is **no sound transpiler**, so we use an **LLM agent** to
translate. An LLM translation is **never trusted**. It is a *hypothesis*, and the
tool's job is to **discharge or refute it with an algorithm**:

```
            ┌─────────────┐   candidate Lean    ┌──────────────────────────────┐
 source  ─► │ front-end   │ ──────────────────► │ VALIDATION (the trust anchor)│
 + specs    │ (Aeneas OR  │ ◄────── repair ──── │  1. typechecks in Lean?       │
            │  LLM agent) │   (errors fed back) │  2. bit-exact vs source on    │
            └─────────────┘                     │     generated vectors?        │
                                                │  3. (opt) property proved?    │
                                                └──────────────────────────────┘
```

**LLM proposes, algorithm disposes.** The deliverable is not "the LLM's Lean" —
it is "Lean that *typechecks* and is *empirically conformant to the source on N
vectors* (and optionally carries a proof)". The agent can be wrong; the
differential oracle and the Lean kernel cannot rubber-stamp it.

This is the lesson of the spike: an LLM (or even a sound tool) can produce Lean
whose *semantics drift* from the source — the canonical case being `u64` overflow
(C++ wraps, Rust panics, Lean's `Result` fails). The tool must **surface and
classify** such divergences, never hide them.

## 3. Scope

**In (v1):** single pure-ish functions and small modules over machine integers,
floats, structs, and fixed arrays; value semantics. The "kernel" shape:
`f(a,b,c,…) -> r`.

**In (later):** stateful code (mutation, heap) — needs a memory model; only Rust
gets this "for free" via Aeneas's borrow-derived functional translation. For
C++/Go a restricted no-alias subset first (see §13).

**Out:** concurrency, unbounded I/O, FFI-heavy code, full STL/stdlib semantics,
proving deep functional-correctness theorems automatically (the tool *sets up*
the proof obligation; closing it may stay human/agent-assisted).

## 4. Architecture

```
lift/
  frontends/
    rust/      → wraps Charon (`charon cargo --preset aeneas`) + Aeneas (`-backend lean`)   [SOUND]
    cpp/       → LLM agent + clang AST/LLVM-IR context                                       [LLM]
    go/        → LLM agent + go/types + AST context                                          [LLM]
    solidity/  → LLM agent + solc AST / Slither context                                      [LLM]
  semantics/   → per-language "fidelity profile" (int width/overflow, float, UB) → Lean model choice
  annotations/ → ingest SV-COMP / Gobra / Scribble → unified Contract IR
  oracle/      → build source as shared lib (.so/.dylib) or EVM; run vectors; capture results
  vectors/     → vector generation (from Contract IR + fuzzing + edge heuristics)
  leanrt/      → run candidate Lean (compiled `lake exe` or `#eval`); collect results
  compare/     → bit-exact / float-tolerance comparator (deterministic)
  harness/     → LLM harness abstraction (Claude, Codex, …) with the propose→repair loop
  report/      → verdict, divergence classes, coverage, certificate
  cli/         → `lift`
```

## 5. Front-ends

| language | mechanism | trust | notes |
|---|---|---|---|
| **Rust** | Charon + Aeneas (the proven pipeline) | **sound** | `Result`-monad model; `--preset aeneas`; partial extraction degrades stdlib to `axiom` |
| **C++** | LLM agent, fed clang AST + types (templates already instantiated) | LLM | prefer feeding clang AST/LLVM-IR over raw text for fidelity |
| **Go** | LLM agent, fed `go/types` + AST | LLM | |
| **Solidity** | LLM agent, fed `solc --ast-compact-json` / Slither IR | LLM | oracle is EVM, not dlopen (see §6) |

All front-ends emit the **same artifact**: a `Candidate` = `{ lean_source,
entrypoint, signature, semantics_profile }`. Rust's is sound by construction;
the others enter the validation loop.

## 6. The validation oracle (ground truth)

The source implementation is the oracle. We execute it natively and compare.

- **C++** → `clang++ -shared -fPIC` with an `extern "C"` ABI shim → `.so`/`.dylib`;
  `dlopen`/`dlsym` from a small runner; call with each vector.
- **Go** → `go build -buildmode=c-shared` → `.so`/`.dylib` + header; same `dlopen`.
- **Rust** → `crate-type=["cdylib"]` (or call the real fn from a harness bin, as the
  spike does).
- **Solidity** → **no dlopen**: deploy+call on an embedded EVM (`revm`/`evmone`);
  the "vector" is calldata, the "result" is return data. This asymmetry is
  first-class, not a hack.
- **Lean side** → compile the candidate to a native `lake exe` reading vectors
  (preferred at scale), or `#eval` for small runs. *Validated feasible in the
  spike:* extracted Lean is computable; build a machine int from a runtime `Nat`
  via `{ bv := BitVec.ofNat W x }`.

Each side emits a normalized line `args => RESULT`; the comparator joins by input.

### Comparison modes (per output type)

- **integers / structs of integers** — **bit-exact**.
- **`f32`/`f64`** — configurable: `exact-bits` (reinterpret as `u32/u64`, compare),
  `ulp <= k`, `rel <= ε`, `abs <= ε`. **NaN** canonicalized (any-NaN == any-NaN,
  configurable); **signed zero** and **rounding-mode** divergences reported, not
  silently equated.
- **error / trap** — a distinguished `OVERFLOW`/`TRAP`/`REVERT` token. The
  comparator knows that source semantics differ here (C++ wrap vs Rust panic vs
  Lean `Result.fail` vs Solidity revert) and classifies the line as a
  **semantic-divergence class**, not a flat pass/fail (see §12).

## 7. Annotation ingestion → Contract IR

Annotations do double duty: **constrain vector generation** (preconditions) and
**become Lean proof obligations** (postconditions). All forms normalize to one
**Contract IR**: `{ requires: [Expr], ensures: [Expr], nondet_inputs: [Var:Type] }`.

| source dialect | precond | postcond | nondet |
|---|---|---|---|
| **SV-COMP** (C/C++) | `__VERIFIER_assume(e)` | `assert(e)` / `reach_error` unreachable | `__VERIFIER_nondet_T()` |
| **Go** | `// @requires e` (Gobra `requires`) | `// @ensures e` (Gobra) | typed `nondet_T()` shim, or `testing/quick`/gopter generators |
| **Solidity** | `/// @custom:requires` or Scribble `if_succeeds`/`require` | Scribble `if_succeeds`, SMTChecker invariants | calldata fuzzing |
| **Rust** | (none needed for translation) | optional `#[ensures]`-style for the Lean theorem | — |

- `requires` → input-domain constraints handed to the **vector generator** (e.g.
  `assume(start < stop)` excludes ill-formed windows; the no-overflow
  side-condition `deposit*(t-start) < 2^W` restricts the *safe* domain).
- `ensures` → a Lean `theorem` skeleton the proof stage (or the agent) must close.
- `nondet` → the free, universally-quantified inputs.

> Go has no single standard; **Gobra** (Viper-based Go verifier) annotations are
> the "cool" target, with `testing/quick`/`gopter` as the property-generator
> fallback. Solidity's idiomatic forms are **Scribble** and **SMTChecker**.

## 8. LLM harness abstraction

```
trait LlmHarness {
  fn translate(source, context, semantics_profile, contract) -> Candidate
  fn repair(candidate, failure: TypeError | Counterexample | ProofGoal) -> Candidate
}
```

- Implementations v1: **Claude**, **Codex**. Selected by `--harness`. Later: a
  custom harness following an extra spec (TBD — plug-in point reserved).
- The loop is **propose → typecheck → difftest → (repair) → …**, bounded by
  `--max-iters`. Every failure is fed back *structured*: Lean type errors, the
  **minimal counterexample** vector from the comparator (shrunk), or the open
  proof goal. The agent never sees a bare "it failed".
- **Determinism / audit:** every prompt, candidate, and verdict is logged;
  `temperature=0` by default; a candidate is content-addressed so a passing run
  is reproducible without re-querying the LLM.

## 9. CLI / UX (must be trivial)

```bash
# zero-config: detect language, find the function, generate vectors, validate
lift verify ./vesting.cpp --fn streamed

# with a contract (drives vector domain + the Lean theorem)
lift verify ./vesting.go --fn Streamed --contract gobra

# float tolerance
lift verify ./dsp.cpp --fn lowpass --float ulp:2

# Rust takes the sound path automatically (no LLM)
lift verify ./crate --fn streamed            # uses Charon+Aeneas

# pick the agent
lift verify ./Vault.sol --fn previewRedeem --harness codex
```

- One config file `leanlift.toml` for repeatable runs (targets, profile,
  tolerance, vector budget, harness). CLI flags override.
- Exit code: `0` = conformant (and proof closed if requested), nonzero otherwise.
- Output is a human report **and** a machine `report.json`.

## 10. Verdict / certificate (the certification ladder)

The tool reports a **level**, never a bare boolean:

| level | meaning |
|---|---|
| **L0 typechecks** | candidate Lean compiles against the model library |
| **L1 conformant/N** | bit-exact (or in-tolerance) vs source on **N** vectors, divergences only in declared semantic classes |
| **L2 bounded-proved** | a model checker (CBMC for C/C++, …) confirms a property ∀ over a bounded domain |
| **L3 proved** | a Lean `theorem` (the `ensures`) is closed (by `decide`/`scalar_tac`/agent), no `sorry` |

`report.json` carries: level, vector count + seed, coverage (which branches/edge
classes hit), the **divergence table** (e.g. "40/450 vectors: source wraps, Lean
fails — `deposit*(t-start) ≥ 2^64`"), and the content hash of the candidate.

## 11. Semantic-fidelity profiles (first-class, not an afterthought)

Per (language × type) the tool pins how the source behaves and which Lean model
to extract against:

- **integer overflow**: `wrap` (C/C++ unsigned, Rust release, Go) | `trap/panic`
  (Rust debug) | `fail` (Aeneas `Result`) | `revert` (Solidity). The comparator
  uses this to decide whether a divergence is **expected** (declared) or a **bug**.
- **signed overflow / shifts / UB** (C/C++): flagged; the safe domain excludes UB
  inputs unless the profile says "model UB as X".
- **float**: rounding mode, FMA contraction, `-ffast-math` (forbidden by default),
  NaN payload, x87 vs SSE. Lean `Float` = IEEE-754 binary64; `f32` needs an
  explicit single-precision model.
- **Solidity**: `uint256` (not native — Lean model via `BitVec 256` / `Nat` mod
  2^256), checked arithmetic (0.8+ reverts on overflow → maps cleanly to a
  `Result`-style model), gas ignored.

## 12. MVP milestones

1. **M0 — Rust path, end to end.** Wrap Charon+Aeneas; oracle via `cdylib`/bin;
   compiled-Lean runner; bit-exact comparator; `report.json`. (≈ the spike,
   productized.)
2. **M1 — C++ via Claude.** LLM front-end + propose/typecheck/difftest/repair
   loop; SV-COMP annotation ingestion; counterexample shrinking; semantic
   profiles for int overflow. Demo: `streamed`.
3. **M2 — floats + Go.** Float tolerance modes; `go:buildmode=c-shared` oracle;
   Gobra/`gopter` annotations.
4. **M3 — Solidity.** EVM oracle (`revm`); `uint256` model; Scribble ingestion;
   L2 via SMTChecker/CBMC-style.
5. **M4 — L3 proofs + pluggable harness.** Theorem skeletons from `ensures`;
   agent-assisted closing; Codex + custom-harness plug-in.

## 13. Open questions / risks

- **Stateful C++/Go**: no borrow checker ⇒ no free functional model. v1 restricts
  to value semantics; a no-alias subset + a heap monad is a research-grade step
  (see the spike's "Aeneas-for-C++" analysis). **Punt to a Rust re-expression**
  where possible.
- **Coverage ≠ proof.** L1 is *testing*; "conformant/N" must never be reported as
  "verified". The report wording and the level taxonomy must keep this honest.
- **Vector generation reaching rare branches** (deep `if`s, narrow domains):
  combine contract-guided generation + coverage-feedback fuzzing; **log what was
  *not* covered** (no silent truncation).
- **Lean library coverage**: Aeneas's model lacks stdlib combinators (extraction
  goes partial → `axiom`). For C++/Go the agent must target a *fixed, audited*
  Lean support library; unknown ops become explicit holes, not silent axioms.
- **Float determinism across build flags**: pin compiler flags; forbid
  `-ffast-math`; record the toolchain in the certificate.
- **LLM nondeterminism / cost**: cache by content hash; `temperature=0`; cap
  iterations; the validation is the gate so a flaky agent only costs retries, not
  correctness.
- **Solidity ≠ dlopen**: the oracle abstraction must cover "execute on EVM" as a
  peer of "dlopen a native lib".

## 14. Non-goals (v1)

- Not a general C++→Lean compiler. Not a substitute for hand proofs of deep
  theorems. Not a soundness oracle for the LLM (the *differential test + Lean
  kernel* are the oracle; the LLM is untrusted throughout).
- No claim of equivalence beyond the tested domain unless an L2/L3 artifact backs
  it.

## 15. Addendum — behavioural models (FSM · BT · CPN · SPN)

A dual axis to the code→Lean path above: author one **behavioural model** (FSM,
behaviour tree, coloured Petri net, or stochastic PN with token loss) in an easy
text format and generate, from that single source of truth, a **Lean proof**
(qualitative), a **PRISM model** (quantitative), and **runnable code**. Same
trust model (mechanical exporter, kernel/checker as anchor), same simple one-
command UX (`lift model check <file>`). See [`docs/SPEC-models.md`](docs/SPEC-models.md)
(spec) and [`docs/PLAN-models.md`](docs/PLAN-models.md) (phased plan).

---

### Appendix A — why differential testing is the right anchor (from the spike)

Four independent methods on the same kernel all converged on the **same**
`deposit*(t-start)` overflow side-condition: the EXPLAINER's hand-wave, the Lean
`Result` obligation (`streamed_bounded`'s `hov`), CBMC's intractable bit-blast,
and the differential test's 40/450 divergent vectors. The differential oracle is
cheap, language-agnostic, and *finds the boundary empirically* — which is exactly
what makes it the trust floor for an untrusted LLM translation.
