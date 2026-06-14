# Plan — formally testing the **models tooling** (not just the models)

> Companion to `PLAN-models.md`. Where that plan certifies each *user model*
> (Lean M3, PRISM M2), this plan is about assuring the **tool** — the Rust code
> that does the checking, unfolding, solving, and code generation.

## 0. Two different things to assure

| | what is certified | by what |
|---|---|---|
| **the model** (output) | "this FSM is safe", "P(freed)=…" | the Lean kernel (M3), PRISM/the CTMC solver (M2) — *already done* |
| **the tool** (TCB) | "the checker/unfolder/solver/exporter is correct" | this plan |

The output guarantees are only as good as the tool that produces them. The
sharp risk: **a tool bug yields a wrong-but-self-consistent model**, which then
gets "proved" — proving the wrong theorem. The unfolder is the prime suspect
(unfold a CPN incorrectly → the Lean proof certifies the *wrong* PT-net), as is
the CTMC builder (vanishing elimination already had a `P[i][i]` bug that only an
*independent* cross-check caught).

The defense is **independent oracles + tool verification**, layered by cost.

## 1. Tier 0 — what exists today

- Unit tests (`src/models/gspn.rs`): the CTMC solver vs day49 closed forms
  (`P=1`, `E=1/μd`, `1−e^{−μd T}`, `1−p^{K+1}`), the arithmetic evaluator, the
  immediate-cycle detector.
- Integration sweep + teeth (`ci.sh`): every verb/family/format; a wrong model
  goes red in **both** the checker and the Lean proof.
- **Exhaustive loop closure**: generated code difftested against the native model
  over every reachable `(state, action)` edge (a complete equivalence check for
  deterministic models — see §5).

Gaps Tier 0 cannot cover: adversarial parser input, "self-consistent wrong"
tool bugs (where checker and proof share the bug), and any property over the
*space* of models rather than the six fixed examples.

## 2. Tier 1 — property-based + differential testing (dependency-free, cheap)

Hand-rolled (seeded PRNG, no Cargo dep — keeps the build offline-safe like the
rest of the engine). Generate random models and assert relations that must hold
for *every* model. **Highest payoff per hour.**

**Metamorphic properties** (the result is invariant under a transformation):
- *Determinism*: `check(m)` twice ⇒ identical report (also: stable across hash
  seeds — guards the HashMap-ordering trap).
- *Rename-invariance*: a bijective renaming of states/places preserves the
  verdict and the reachable-set size.
- *Product commutativity*: `product(A,B) ≅ product(B,A)` up to state renaming.
- *Dead-state addition*: adding an unreachable state/transition never changes
  the verdict.
- *Petri loss monotonicity*: adding a pure-loss transition never *raises* an
  upper-bound count (the Rust analogue of `Petri.le_preserved`).

**Oracle / differential properties** (two independent computations agree):
- *Reachability soundness*: every state the BFS reports is reproducible by
  replaying its witness trace through `step` (no phantom states).
- **CPN unfold ≡ coloured simulation** — the deferred `PLAN-models.md` §4.3.
  Build a native *coloured* occurrence-graph simulator and assert it is
  isomorphic to the unfolded PT-net's reachable graph. This directly guards the
  prime-suspect unfolder. *(Needs the coloured simulator — ~half a day.)*
- *Two-algorithm agreement*: BFS reachable set == DFS reachable set.
- *Native CTMC vs PRISM*: already wired in `prism` when the binary is present;
  make it a CI gate where PRISM is installed.
- *M1 ↔ M3 agreement*: over random FSMs, `check` says safe **iff** the generated
  Lean proof elaborates. (Systematizes the teeth across the model space.)

Deliverable: `src/models/proptest.rs` (`#[cfg(test)]`), a seeded model generator
+ the properties above, run by `cargo test`. A starter landing with this plan
covers determinism, rename-invariance, and reachability soundness.

## 3. Tier 2 — fuzzing the parsers (external tool: `cargo-fuzz` / libFuzzer)

The hand-rolled `toml`/`xml`/`pnml`/`scxml` parsers index and `unwrap` in places;
adversarial bytes are the likeliest panic source. A libFuzzer target per parser
asserts **no panic, no hang** on arbitrary input:

```rust
fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = leanlift::models::toml::parse(s);   // must return Result, never panic
    }
});
```

`cargo-fuzz` is an external tool (not a shipped dependency — same status as
`lean`/`forge`/`aeneas`). Run in CI nightly with a time budget; seed the corpus
with `examples/models/*`. Payoff: turns "probably doesn't panic" into "fuzzed N
CPU-hours clean".

## 4. Tier 3 — bounded model checking (external tool: **Kani**)

Kani proves the *absence of panics* and bounded assertions for Rust — a great
fit for the integer/array logic here. Harnesses (`#[kani::proof]`, behind a
`cfg(kani)`):
- *Petri `fire` never underflows*: `assume(enabled(m,t)); fire(m,t)` — prove no
  `u32` subtraction overflow for bounded markings. (Proves the safety the code
  relies on implicitly.)
- *`vid`/`ctor` always produce a valid identifier*: non-empty, first char a
  letter, all chars alphanumeric — for any input string up to length k. (Guards
  exactly the bug class fixed in the review.)
- *CTMC outputs are finite and in range*: for a bounded generator `Q`,
  `prob_reach ∈ [0,1]`, `transient` rows sum to ≤ 1, no `NaN`/`inf`.
- *`solve` does not panic* on any k×k input within bounds.

Kani is unwind-bounded, so these are "correct up to size k" — strong for the
small dimensions these models hit.

## 5. Tier 4 — deductive verification / **dogfooding leanlift on itself**

The on-brand endgame: leanlift already extracts Rust → Lean via Charon+Aeneas
and proves theorems (the engine's L3). **Point that at the models substrate.**
Extract the core, integer-only functions — `PtNet::fire`, `enabled`, the
conserved-sum step — to Lean and prove they satisfy the very theory the export
relies on (`LeanLift/Models/Petri.lean`: `fire_le`, `le_preserved`). Then the
tool that produces proofs is *itself* proved by the same tool — the circle
closes.

- **Aeneas** (already built for the engine): best for the pure functional core
  (markings as arrays, `fire`/`enabled`). Reuses `scripts/build_aeneas.sh`.
- **Creusot** (alternative, Pearlite contracts → Why3/SMT): good for SMT-friendly
  integer invariants; **poor** for floats/`HashMap`/deep recursion, so *not* for
  the CTMC solver. Candidate: annotate `check::check`'s loop invariant (the
  reachable set is closed under `step`).
- Out of scope for deductive tools: the float CTMC solver (measure theory /
  numerical error — stays at Tier 1 differential vs PRISM + closed forms, exactly
  the day49 division of labour).

## 6. Tool-fit summary

| component | Tier-1 (prop/diff) | Tier-2 (fuzz) | Tier-3 (Kani) | Tier-4 (Aeneas/Creusot) |
|---|---|---|---|---|
| `toml`/`xml`/`scxml`/`pnml` parse | round-trip | **yes** | no-panic | — |
| `check` BFS | reach soundness, det. | — | no-panic | Creusot loop-invariant |
| `format::product` | commutativity | — | — | — |
| `cpn::unfold` | **unfold ≡ coloured** | — | — | — |
| `PtNet::fire/enabled` | loss monotonicity | — | **no underflow** | **Aeneas vs Petri.lean** |
| `gspn` CTMC solver | vs PRISM + closed forms | — | finite/in-range | — (floats) |
| `lean`/`codegen` emit | M1↔M3, loop closure | — | `vid`/`ctor` valid | — |

## 7. The loop-closure coverage policy (the "why 300?" resolution)

300 was an arbitrary magic number, and random sampling is the wrong tool for a
finite transition system. Policy now:

- **Default: exhaustive.** A BFS witness path to every reachable state, each
  extended by every action ⇒ every reachable `(state, action)` edge is exercised
  exactly once. For a deterministic model this is a *complete* equivalence check
  — any single-edge codegen bug is guaranteed to surface, not just likely.
  Bounded by `check::DEFAULT_BOUND`; if hit, the verdict says "coverage partial".
- **Param for scale: `--samples N [--seed S]`.** When the reachable space is
  unbounded or too large to enumerate, supplement the (truncated) exhaustive
  frontier with `N` random traces to probe deeper.
- **Rule of thumb for `N`** (sampled mode, coupon-collector): to hit all `E`
  reachable edges with high probability using traces of length `L ≈ 3·diameter`,
  take **`N ≈ 10 · E / L · ln E`**, i.e. an order of magnitude over the
  coupon-collector expectation `E·ln E / L`. Concretely default `N = 10 ·
  edges_explored` when exhaustive truncates; log what was left uncovered (never
  silently claim total — the §0.2 honesty rule).

## 8. Ordered next steps

1. **Tier 1 starter** (lands with this plan): `proptest.rs` — determinism,
   rename-invariance, reachability soundness, over a seeded random-FSM generator.
2. **CPN unfold ≡ coloured simulator** (Tier 1, highest-risk component).
3. **`--samples`/`--seed`** loop-closure param (lands with this plan) + the
   rule-of-thumb default for truncated nets.
4. **Kani** harnesses for `fire` no-underflow and `vid`/`ctor` validity (the
   fixed-bug regression guards).
5. **cargo-fuzz** targets for the four parsers; nightly CI budget.
6. **Aeneas dogfood**: extract `PtNet::fire`/`enabled` → Lean, prove against
   `Petri.lean`. The headline: leanlift verifies its own models substrate.
