# Plan — formally testing the **models tooling** (phased)

> Companion to `PLAN-models.md`. That plan certifies each *user model* (Lean M3,
> PRISM M2); this plan assures the **tool** — the Rust code that checks, unfolds,
> solves, and generates. Phased like `PLAN-models.md`; cornerstones are **Kani**
> (Phase V1, bounded model checking) and **Aeneas** (Phase V3, deductive proof —
> leanlift verifying its own substrate).

## 0. Two different things to assure

| | what is certified | by what |
|---|---|---|
| **the model** (output) | "this FSM is safe", "P(freed)=…" | the Lean kernel (M3), PRISM / the CTMC solver (M2) — *already done* |
| **the tool** (TCB) | "the checker/unfolder/solver/exporter is correct" | this plan |

The sharp risk: a tool bug yields a **wrong-but-self-consistent** model, which
then gets "proved" — proving the wrong theorem. The unfolder and the CTMC builder
are the prime suspects (the latter already had a `P[i][i]` bug an *independent*
cross-check caught). Defense = independent oracles + tool verification.

## What exists (Tier 0)

Unit tests (CTMC vs day49 closed forms; evaluator; cycle detector), the
integration sweep + teeth (`ci.sh`), and the **exhaustive loop closure** (codegen
vs native over every reachable edge). Cannot cover: adversarial parser input,
self-consistent tool bugs, or properties over the *space* of models.

---

## Phase V0 — property-based + differential harness (no deps) ✅ mostly done

Hand-rolled, seeded (no Cargo dep — keeps the build offline-safe). Assert
relations true for *every* model, and cross-check independent computations.

- **V0.1 coloured CPN simulator.** ✅ `cpn::occurrence_graph` — computes
  enabling/firing directly over coloured `(place,value)` multisets, sharing
  nothing with the unfolder but the parse.
- **V0.2 unfold ≡ coloured differential.** ✅ `cpn` tests: the unfolded PT-net's
  reachable graph must equal the coloured occurrence graph (the prime-suspect
  unfolder). Verified non-vacuous: an injected multiplicity bug fails it.
- **V0.3 metamorphic properties.** ✅ (`proptest.rs`) determinism,
  rename-invariance, reachable-count vs independent BFS, **product
  commutativity** (A∥B ≡ B∥A up to `a|b`↔`b|a`), **dead-state-addition
  invariance** (an unreachable forbidden state perturbs neither count nor
  verdict), and **Petri loss monotonicity** (the Rust analogue of
  `Petri.le_preserved`: non-increasing transitions keep every reachable marking
  ≤ the initial total; non-vacuity guarded).
- **V0.4 random CPN generator** feeding V0.2 (today the differential runs on the
  `resource` example + two synthetic nets; randomize for breadth).
- **V0.5 M1 ↔ M3 agreement** over random FSMs: `check` says safe **iff** the
  generated Lean proof elaborates (systematizes the teeth; gated on `lean`).
- **V0.6 native CTMC vs PRISM** as a CI gate where the `prism` binary is present.

---

## Phase V1 — Kani: bounded model checking (no-panic + invariants)

Kani proves panic-freedom and bounded assertions for Rust — the right tool for
this integer/array logic. Harnesses behind `#[cfg(kani)]`, run by `cargo kani`
(an external tool, like `lean`/`forge`/`aeneas` — not a shipped dependency).

- **V1.1 scaffold.** A `#[cfg(kani)] mod kani_harness` per target module; a
  `verify-kani.sh` that runs `cargo kani` if installed, SKIPs otherwise.
- **V1.2 `PtNet::fire` never underflows.** `kani::assume(enabled(m,t))` over a
  bounded marking ⇒ prove no `u32` subtraction overflow in `fire`. Proves the
  safety the production code relies on implicitly.
- **V1.3 `vid`/`ctor` always emit a valid identifier.** For any input up to
  length k: non-empty, first char a letter, all chars alphanumeric — exactly the
  bug class fixed in the review, now a proof.
- **V1.4 CTMC outputs finite & in range.** For a bounded generator `Q`:
  `prob_reach ∈ [0,1]`, transient rows sum ≤ 1, no `NaN`/`inf`; `solve` does not
  panic on any k×k input. (Bounded k — strong for these small dimensions.)
- **V1.5 parser no-panic** for bounded inputs (complements V2 fuzzing with a
  bounded *proof*).
- **V1.6 CI.** `ci.sh` calls `verify-kani.sh` (SKIP when Kani absent), so the
  bounded proofs run wherever Kani is installed.

---

## Phase V2 — fuzzing the parsers (cargo-fuzz / libFuzzer)

The hand-rolled `toml`/`xml`/`pnml`/`scxml` parsers index and `unwrap`;
adversarial bytes are the likeliest panic. One libFuzzer target per parser
asserting **no panic, no hang**:

```rust
fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) { let _ = toml::parse(s); } // never panics
});
```

- **V2.1** four `fuzz/` targets; **V2.2** seed the corpus with
  `examples/models/*`; **V2.3** a nightly CI time budget. External tool, not a
  shipped dep.

---

## Phase V3 — Aeneas: deductive proof of the functional core (dogfood) ★

The on-brand capstone: the engine already extracts Rust → Lean via Charon+Aeneas
and proves theorems (L3). **Point it at the models substrate** — then the tool
that produces proofs is itself proved by the same tool.

- **V3.1 carve a pure core.** Factor the marking arithmetic (`fire`, `enabled`,
  the conserved-sum step) into a small, panic-free, `HashMap`-free crate
  (`examples/models-core/`, arrays/slices only) Charon+Aeneas can ingest — the
  same shape as `examples/rust-kernels`.
- **V3.2 extract to Lean** via `scripts/build_aeneas.sh` (already built for the
  engine): `fire`/`enabled` → a `Result` model.
- **V3.3 prove against `Petri.lean`.** Discharge that the extracted `fire`
  satisfies the theory the export relies on — `fire_le` / `le_preserved` (firing
  a non-increasing transition preserves an upper bound), sorry-free.
- **V3.4 wire as `lift prove models-core`** (a `proof_frag` in `examples.rs`):
  leanlift certifies its own Petri kernel L3, in the same CI as the user models.
- **V3.5 Creusot alternative** for SMT-friendly integer code: contract
  `check::check`'s loop invariant ("the reachable set is closed under `step`").
  *Not* for the float CTMC solver — that stays at V0.6 differential-vs-PRISM
  (the day49 division of labour: floats/measure theory are the wrong job for a
  proof assistant).

---

## Phase V4 — coverage policy (the "why 300?" resolution) ✅ done

- **V4.1 exhaustive by default.** ✅ The loop closure covers every reachable
  `(state, action)` edge via BFS witness paths — a *complete* equivalence check
  for deterministic models, not a sample.
- **V4.2 `--samples N [--seed S]`.** ✅ Supplements the (truncated) exhaustive
  frontier with random traces for unbounded/huge nets.
- **V4.3 rule of thumb for `N`** (sampled mode, coupon-collector): to hit all `E`
  reachable edges w.h.p. with traces of length `L ≈ 3·diameter`, take
  **`N ≈ 10·E/L·ln E`**; default `10·edges_explored` when exhaustive truncates;
  always log what was left uncovered (never silently claim total).

---

## Phase V5 — consolidation

- **V5.1 `verify.sh`** orchestrator: property tests always; Kani / Aeneas /
  cargo-fuzz when their tools are present; one pass/fail summary.
- **V5.2 CI tiers**: `ci.sh` = fast (build, test, integration, teeth, exhaustive
  loop closure); `verify.sh` = deep (Kani + Aeneas + fuzz), nightly.

---

## Tool-fit summary

| component | V0 prop/diff | V1 Kani | V2 fuzz | V3 Aeneas/Creusot |
|---|---|---|---|---|
| `toml`/`xml`/`scxml`/`pnml` parse | round-trip | no-panic (bounded) | **yes** | — |
| `check` BFS | reach soundness, det. | no-panic | — | Creusot loop-invariant |
| `format::product` | commutativity | — | — | — |
| `cpn::unfold` | **unfold ≡ coloured** ✅ | — | — | — |
| `PtNet::fire/enabled` | loss monotonicity | **no underflow** | — | **Aeneas vs Petri.lean** ★ |
| `gspn` CTMC solver | vs PRISM + closed forms | finite/in-range | — | — (floats) |
| `lean`/`codegen` emit | M1↔M3, loop closure ✅ | `vid`/`ctor` valid | — | — |

## Ordered next steps

1. ✅ V0.1–V0.3 (coloured sim, unfold≡coloured differential, FSM proptests:
   determinism, rename, BFS-count, product commutativity, dead-state-addition,
   loss monotonicity) + V4 coverage policy + `--samples`.
2. **V1.2/V1.3 Kani** — `fire` no-underflow and `vid`/`ctor` validity (the
   fixed-bug regression guards), behind `verify-kani.sh`.
3. **V3.1–V3.4 Aeneas dogfood** — extract the Petri core and prove it against
   `Petri.lean` (the headline: leanlift verifies its own substrate).
4. V0.4–V0.6 (random CPNs, M1↔M3, CTMC-vs-PRISM gate); V2 parser fuzzing.
5. V5 consolidation (`verify.sh`, nightly deep tier).
