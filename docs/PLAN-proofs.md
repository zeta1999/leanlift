# Plan — from conformance (L1) to proof (L3), toward a numerical algorithm

> Status: planning doc. Companion to `SPEC.md`. Written 2026-06; to be argued with.

## 0. Where we are

The engine does **L0/L1** end to end across C++, Rust (sound), Go, and Solidity:
a candidate Lean model is obtained (hand / Aeneas / LLM) and **validated by
bit-exact differential execution** against the source oracle, classifying
declared overflow divergences. We do **not yet prove anything** about the code —
L1 is *testing on N vectors*, not a theorem. The certification ladder (SPEC §10)
goes further:

| level | meaning | status |
|---|---|---|
| L0 | candidate typechecks against the model library | ✅ |
| L1 | bit-exact vs source on N vectors, declared divergences only | ✅ |
| **L2** | a property holds ∀ over a **bounded** domain (model checker) | ▢ |
| **L3** | a Lean **theorem** (the `ensures`) is closed, no `sorry` | ▢ |

This plan is about **L2/L3**: *extract → state a property → prove it → certify →
document the recipe*, and then about applying that machinery to a **numerical
algorithm** where correctness is the whole point.

---

## Part I — The proof procedure (L2/L3)

### I.1 The recipe (the documented procedure)

For one function the loop is:

1. **Lift** — obtain the Lean model (existing front-ends: Aeneas for Rust, LLM
   for C++/Go/Solidity, or hand-written). This already happens for L1.
2. **State** — turn a *property* into a Lean proof obligation. Sources, in order
   of preference:
   - a `Contract IR` `ensures` clause (SPEC §7), once annotation ingestion exists;
   - for now, a **hand-stated theorem skeleton** attached to the example.
   The statement is over the model's types (checked `UInt`/`Res`, or Aeneas's
   `Std.U64`/`Result`), typically *guarded by the no-overflow precondition* the
   differential test already discovered empirically (e.g.
   `deposit*(t-start) < 2^64`).
3. **Discharge L1 first** — never attempt a proof the difftest already refutes.
   L1 is the cheap filter; L3 is the expensive certificate.
4. **Prove** — close the goal with the proof backend matched to the candidate
   kind (§I.2). Allow a bounded fallback (L2) when the full ∀ is out of reach.
5. **Certify** — re-elaborate with `sorry`/axiom detection; record the level,
   the theorem statement, its hypotheses (the precondition), and the content
   hash in `report.json`. An L3 claim must be **kernel-checked and sorry-free**.
6. **Document** — emit a worked `*.recipe.md` per example: source → model →
   statement → tactic → certificate, so the procedure is reproducible.

The honesty rule (SPEC §13) carries over: an L2 (bounded) result must never be
reported as L3 (universal), and a proof guarded by a precondition must surface
that precondition in the certificate.

### I.2 Two proof backends, matched to the two model kinds

- **Aeneas-extracted models** (`Result` monad over `Std.U64`): use Aeneas's Lean
  tactic library — `progress` to step the monad, `scalar_tac`/`omega` for the
  integer side-conditions. The spike already closed the canonical theorems on
  this exact `streamed` extraction:
  - `streamed_mono` (I3): non-decreasing in `t`;
  - `streamed_bounded` (I2): result ∈ `[0, deposit]`, carrying the overflow
    hypothesis `hov : deposit*(t-start) < 2^64`.
  These are the **first L3 targets** — reproduce them under `lift prove`.
- **Support-library models** (`LeanLift.Checked`, used by the LLM/hand
  candidates): plain Lean 4, Mathlib-free. Properties close with `omega`,
  `decide`, `bv_decide`, and structural induction over the checked ops. The
  support lib will need small **lemmas** about `UInt.add/mul/sub/div` (monotone,
  bounded, `ofNat` round-trips) — an audited proof kernel that candidate proofs
  build on.

The **agent stays in the loop**: just as the LLM proposes a *translation* that
the oracle disposes, it can propose a *tactic block* that the **Lean kernel**
disposes. `claude -p` writes the proof; sorry-free kernel acceptance is the gate
(same trust model, now for proofs). This is the L3-"by agent" path.

### I.3 Engine integration

- New `lift prove <example>` (or `--prove` on `verify`): runs L1, then attaches
  the theorem skeleton, invokes the proof backend, and reports the level.
- Add to the `Example`: an optional `theorem: { statement, precondition }`.
- Extend `report.json`: `level: "L3_proved"`, the statement, the discharged
  hypotheses, sorry-free = true.
- **L2 bridge** (optional, cheaper): wire CBMC for C/C++ (`cbmc --function …
  --unwind k`) as the bounded backend — the spike already did this for the
  recovery properties; it slots in as the L2 producer where L3 is intractable.

### I.4 First milestone (Part I done)

`lift prove rust-streamed` closes `streamed_mono` and `streamed_bounded`
(sorry-free) on the Aeneas extraction and emits an **L3 certificate**, with a
`streamed.recipe.md` documenting every step. This is the smallest end-to-end
"prove something on real code" deliverable, and it reuses artifacts that already
exist from the spike.

---

## Part II — Toward a numerical algorithm (Numerical Recipes)

> "Analysis and proof of correctness is fundamental here."

### II.1 The float problem, stated honestly

Numerical Recipes is float-heavy, and **IEEE-754 proofs are hard**: Lean's
`Float` is opaque-ish, and real error analysis needs Mathlib's real-analysis.
But the tool already has the right escape hatches:

- **Differential testing still works on floats** — the comparator has the
  float modes (`exact-bits`/`ulp`/`rel`/`abs`, SPEC §6) already specified. So L1
  conformance for a float kernel is reachable now (it's just testing).
- **Proof needs one of two tracks:**
  - **(A) exact / integer / fixed-point kernels** — bit-exact *and* provable
    today, Mathlib-free. Start here.
  - **(B) float kernels with an error-bound spec** — correctness is "output is
    within a proven bound of the true value", not bit-exactness. Needs a Lean
    real-analysis layer (Mathlib). This is the research-grade endpoint.

### II.2 A progression of targets (increasing difficulty)

**Tier 0 — exact, integer, provable now** (warm-ups that build the proof kernel):
- **Horner** polynomial evaluation: prove `horner cs x = Σ cᵢ·xⁱ` by induction.
  Straight recursion, pure algebra — the cleanest first induction proof.
- **isqrt**: prove the *exact* postcondition `r·r ≤ n < (r+1)·(r+1)`. Introduces
  a loop/recursion with a real numerical postcondition.
- **gcd** (Euclid): `gcd a b ∣ a ∧ gcd a b ∣ b ∧` greatest. Termination + number
  theory.

**Tier 1 — numerical, integer/fixed-point** (the first true "numerical method"):
- **Bisection** on a monotone integer function `f`. The correctness story is the
  whole point and is provable without floats:
  - *invariant*: the root stays bracketed — `f(lo) ≤ 0 ≤ f(hi)` is preserved;
  - *termination*: `hi − lo` strictly halves each step (a decreasing measure);
  - *postcondition*: on exit `hi − lo ≤ ε ⇒ a root lies within ε of `lo``.
  This exercises **loops + termination + a numerical guarantee** — the new
  ingredients beyond the straight-line kernels we have. Fixed-point arithmetic
  keeps it exact.

**Tier 2 — float, error-bound** (where Part II is "fundamental"):
- **Trapezoidal / Simpson integration**: prove the error bound
  `|I_h − ∫f| ≤ C·h²·max|f''|` (trapezoid) on the Lean side, and difftest the C++
  implementation in `rel`/`ulp` mode. Requires Mathlib real-analysis and a spec
  of `f`. This is the first genuinely *numerical-analysis* proof; treat it as a
  research milestone, not a sprint.

### II.3 Recommended first numerical kernel: **bisection** (with **isqrt** as warm-up)

Rationale: small; the correctness property *is* the reason the algorithm exists;
integer/fixed-point ⇒ end-to-end provable with the tools we have; and it forces
the engine to handle **loops/termination**, which the current straight-line
kernels never did. Do `isqrt` first (single postcondition, simpler loop), then
`bisection` (invariant + termination + ε-guarantee).

### II.4 What each tier demands from the engine

- **Loops/recursion in the model.** Aeneas turns Rust loops into structural
  recursion / well-founded defs for free — so the **Rust front-end is the path
  of least resistance for numerical kernels**. For LLM C++/Go, the candidate must
  encode the loop as a Lean recursive def or `fold`; the support lib likely needs
  a small bounded-iteration combinator, and the prompt must teach it.
- **Contract IR (SPEC §7).** Pre/postconditions stop being hand-stated and start
  driving both vector domains *and* the theorem skeleton. `isqrt`/`bisection`
  are good first Contract-IR customers (`requires n ≥ 0`, `ensures r·r ≤ n …`).
- **Float-tolerance comparator.** Finish the `ulp/rel/abs` modes in `compare.rs`
  for Tier 2; pin compiler flags (forbid `-ffast-math`, SPEC §11).
- **Mathlib gate.** Keep the exact/integer track Mathlib-free (fast, audited);
  put float real-analysis behind an explicit Mathlib-backed support module so the
  light track stays light.

---

## Part III — Ordered next steps

1. **L3 on existing code.** `lift prove rust-streamed` → close `streamed_mono` +
   `streamed_bounded` (Aeneas + `scalar_tac`), emit L3 cert + `streamed.recipe.md`.
   *Proves the procedure on code we already have.* (Part I.4)
2. **Proof kernel for the support lib.** Audited lemmas about `UInt.*` so
   support-lib candidates (LLM/hand) can carry proofs too; close a property on
   `avg`/`dot2` (e.g. `avg a b ≤ max a b` under no-overflow).
3. **`isqrt` example** (C++ + Rust) → extract → prove `r·r ≤ n < (r+1)²`. First
   numerical postcondition; first loop. Document the recipe.
4. **`bisection` example** (integer/fixed-point) → prove bracketing invariant +
   termination + ε-guarantee. First real numerical method.
5. **Float-tolerance comparator + trapezoidal rule** with an error-bound theorem
   (Mathlib). Research milestone — where numerical analysis proof is fundamental.

## Open questions / risks

- **Loop encoding for LLM front-ends.** Without a borrow checker the model has no
  free functional form; the agent must produce structural-recursion Lean and the
  support lib must offer the combinators. Rust (Aeneas) sidesteps this — prefer it
  for numerical kernels, or re-express C++ in Rust (SPEC §13).
- **Proof automation ceiling.** `omega`/`scalar_tac`/`decide` close arithmetic
  side-conditions but not deep functional theorems; expect agent-assisted tactic
  search (claude -p proposes, the kernel disposes) for Tier 1+.
- **Float determinism + Mathlib weight.** Real-analysis proofs pull in Mathlib
  (heavy) and pin the toolchain/flags; keep it isolated from the light integer
  track.
- **Termination obligations.** Well-founded recursion measures (e.g. `hi−lo`)
  must be supplied; for LLM models this is another thing the prompt/agent must
  get right and the kernel will check.
