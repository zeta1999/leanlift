# PLAN — extensions: qnet family · EDF demand-bound · Aeneas RTA · shared workload

> Extends `PLAN-perf-demo.md` with four capabilities, then a hardening pass.
> **Quality bar: this is for an app where bugs are not an option.** Every
> implementation step ends with BOTH:
>   1. `./ci.sh` GREEN (and `verify.sh` where a proved kernel is touched), and
>   2. a **brutally-honest code-review subagent** over that step's diff — its
>      findings triaged and fixed before moving on.
> Principle unchanged: useful > perfect; cross-check every number against a
> closed form, an analysis, AND a simulation.

## Phase Q — queueing-network family (`kind = "qnet"`)

The multi-station generalization of the single-server `link`. Open Jackson
networks: product-form, solved exactly and cheaply (no state space).

- **Q1 spec + parse.** `[[station]]` (name, `mu`, `servers`=1, external `lambda`),
  `[[route]]` (from, to, `prob`). Auto-detect (`[[station]]`); validate μ>0,
  out-probs ≤ 1, rates ≥ 0.
- **Q2 analyzer.** Traffic equations `(I − Pᵀ)λ = λ⁰` ⇒ per-station `λᵢ`,
  `ρᵢ = λᵢ/(cᵢμᵢ)`, M/M/1 `Lᵢ = ρᵢ/(1−ρᵢ)`, `Wᵢ = 1/(μᵢ−λᵢ)`; network `L=ΣLᵢ`,
  `W=L/Σλ⁰`; **stability** `max ρᵢ < 1`, **bottleneck** `argmax ρᵢ`.
  `lift model check qnet`. (M/M/c Erlang-C: noted extension.)
- **Q3 validation.** Closed forms (single M/M/1, tandem, feedback), flow
  balance, network Little; bottleneck **phase transition** (scale λ⁰ ⇒ divergence
  at closed-form `λ*`).
- **Q4 simulation cross-check.** Open-network DES (Poisson in, exp service,
  prob routing) ⇒ empirical `Lᵢ` vs analytic; `lift model simulate qnet`.
- **Q5 sweep + example + recipe.** `qnet.model.toml` (3-station feedback),
  `scripts/qnet-sweep.sh`, `qnet.recipe.md`.

## Phase E — EDF demand-bound analysis (constrained deadlines `D ≤ T`)

Today `rt.rs` does EDF only via `U ≤ 1` (exact for `D = T`). Extend to the EXACT
**processor-demand** test so `D < T` works:

- **E1 demand-bound function.** `dbf(t) = Σᵢ max(0, ⌊(t−Dᵢ)/Tᵢ⌋ + 1)·Cᵢ`;
  EDF-schedulable iff `U ≤ 1` AND `dbf(t) ≤ t` for every deadline point
  `t = kTᵢ + Dᵢ` up to a bound `L` (hyperperiod, or the busy-period bound
  `L = (Σ(Tᵢ−Dᵢ)Uᵢ)/(1−U)`). Pseudo-polynomial, exact.
- **E2 wire + example.** `policy="EDF"` routes to the demand test; report the
  first failing `t` if any. Teaching case: a set that passes `U ≤ 1` but a tight
  `D` makes `dbf(t) > t` ⇒ unschedulable (the EDF analogue of RTA-beats-bound).
- **E3 validation.** Tests: implicit-deadline EDF agrees with `U ≤ 1`; a
  constrained-deadline counterexample; demand-bound ↔ a busy-period simulation.

## Phase A — Aeneas RTA proof (deductive companion to the R2 Kani proof)

The unbounded deductive proof via leanlift's own Charon+Aeneas pipeline (dogfood,
as `models-fire` / `link-buffer`).

- **A1 carve.** `rta_term(r,cj,tj) = div_ceil(r,tj)·cj` in `examples/rust-kernels`.
- **A2 extract + prove.** Charon+Aeneas → Lean; `RtaProofs.lean` proves
  **monotonicity in `r`** (with the `Result`-monad no-overflow premises),
  sorry-free — the LFP-soundness fact.
- **A3 wire.** `rta-kernel` example (`lift prove rta-kernel` → L3); tests/run.sh.

## Phase C — connecting the two demos on a shared workload

The capstone: the SAME workload analyzed both ways. A periodic job `(C, T)` is a
task (deterministic RTA) AND a queue (`μ = 1/C`, `λ = 1/T`, stochastic). Sweep the
shared load and show **both** boundaries on one axis: the hard schedulability
step (RTA) and the soft queueing delay / deadline-miss (CTMC/sim).

- **C1 bridge + sweep.** `scripts/shared-workload-sweep.sh`: from one `(C,T,load)`
  emit the task model (→ `lift model check`, hard) and the queue model (→
  `lift model prism/simulate`, soft); tabulate hard verdict + soft mean-delay /
  miss vs load; mark both boundaries.
- **C2 recipe.** `shared-workload.recipe.md`: one workload, two safe-region
  boundaries (provably-safe hard ⊆ probably-safe soft); the unified picture.

## Phase M — the manual testing manual

`docs/TESTING.md`: a copy-pasteable, unambiguous manual — every verb on every
example, EXPECTED output/verdict, sweeps, proofs, Kani/Aeneas deep checks —
executable by a person *or an agent*.

## Phase F — finalize (hardening)

- **F1 refresh all docs** (README verbs incl. `simulate`/`--set`/`--scale`,
  `qnet`/`tasks` families, EDF; `docs/FORMATS-models.md`; `SPEC.md` pointer).
- **F2 manual-test subagent.** Run `docs/TESTING.md` end-to-end in a subagent;
  capture transcript; fix deviations.
- **F3 final brutal review subagent** over the whole-branch diff (numeric edge
  cases, overflow, off-by-one, parser robustness); triage + fix.
- **F4 mini tutorial** `docs/TUTORIAL.md`: a short worked walkthrough for the
  stochastic (`link`/`qnet`) and deterministic (`tasks`) sides + the shared
  workload.

## Ordered execution (CI + brutal review at each ★ step) — ✅ COMPLETE

1. ✅ Q1+Q2 (+ brutal review → 2 CRITICAL fixed)  2. ✅ Q3  3. ✅ Q4  4. ✅ Q5
5. ✅ E1+E2 (+ brutal review → CRITICAL overflow + D>T fixed)  6. ✅ E3
7. ✅ A1–A3 (`lift prove rta-kernel`, L3 sorry-free)  8. ✅ C1+C2
9. ✅ M (`docs/TESTING.md`)  10. ✅ F1 (README + FORMATS)  11. ✅ F2 (manual-test
subagent: 28/28 PASS incl. live Kani+Aeneas)  12. ✅ F3 (final review subagent →
2 CRITICAL + 2 HIGH + 2 MEDIUM in the simulators/knobs, all fixed)  13. ✅ F4
(`docs/TUTORIAL.md`).

Every step ended CI-green; `verify.sh` (Kani + Aeneas) green. The whole plan is
done — qnet family, EDF demand-bound, the Aeneas RTA proof, the shared-workload
connection, the testing manual, and the tutorial — all under "bugs are not an
option" with brutal-review hardening.
