# PLAN — the performance + correctness showcase (the "phase-change" demo)

> Sibling to `PLAN-models.md` (the model axis), `PLAN-verification.md` (assuring
> the tool), and `PLAN-proofs.md` (the L3 path). This plan is the **end-to-end
> demo** that ties them together for the target user: **someone designing code
> that is both performance- and correctness-critical.**

## 0. Operating principle — useful > perfect

The tool earns its keep by being *useful first*, not by being a perfection
exercise. Two rules, already the de-facto pattern in `PLAN-verification.md`:

1. **Cheapest tool that actually bites, per obligation.** Deductive proof where
   it converges cheaply (Aeneas `fire_place`, Kani `fire_no_underflow`);
   exhaustive/property test where a proof is intractable (V1.3 identifiers, V1.4
   floats, V2 parsers); carve + property-test + *gate the prover* where the tool
   isn't installed yet (V3.5 Creusot). A feature never blocks on a proof that
   won't converge.
2. **The verification ladder travels with the feature.** Adding a model feature
   means extending — in the same change — its M1 check, Lean/PRISM obligation,
   codegen loop-closure, and Kani/Creusot/Aeneas hook, each **gated so an absent
   tool SKIPs (never red)**. That is what keeps *code ↔ models consistent* as the
   surface grows, without a perfection tax.

Everything below is in service of those two rules.

## 1. The demo, in one line

**One authored model of a 1→1 network protocol → Lean proof (qualitative) +
PRISM/CTMC performance (quantitative) + simulation (empirical), exhibiting a
designer-visible PHASE TRANSITION** at a loss/latency threshold, with every
layer cross-checked against the others.

### The physics (so the "phase change" is real, not hand-waved)

Stop-and-wait ARQ (alternating-bit), one sender → one receiver, lossy link, fed
by a message queue at rate `λ`:

- attempt succeeds w.p. `1−p`; each attempt+timeout cycle costs `τ ≈ RTT` ⇒
  mean service `S = τ/(1−p)`, effective rate `μ_eff = (1−p)/τ`.
- offered load `ρ = λτ/(1−p)`; **stable iff `ρ < 1`, i.e. `p < p* = 1 − λτ`.**
- order parameter `W = L/λ`, `L = ρ/(1−ρ)` → **diverges as `p → p*⁻`**.

Honest framing: a finite-state CTMC has **no true singularity** — the divergence
lives in the `K→∞` (unbounded-buffer) limit. So the demo is a **finite-size
scaling** story: finite-`K` CTMCs show a knee that **sharpens as `K` grows**
(`K = 2,4,8,16…`) toward a step at `p*`; the `K→∞` closed form gives the exact
threshold; simulation shows the empirical cliff. The triangulation
**closed-form `p*` ↔ exact finite-CTMC knee ↔ empirical cliff** *is* the leanlift
cross-check ethos applied to a phase transition.

## 2. Method → piece (efficiency-aware; see `PLAN-verification` tool-fit)

| Demo piece | Method | Why efficient |
|---|---|---|
| per-message `P(deliver)`, `E[delay]`, `P(≤deadline)` | exact CTMC / closed form | tiny chain; `dock-gspn` already does `1−p^(K+1)` |
| queued `W`, `P(overflow)`, throughput vs `p` | exact CTMC, finite `K` | `~K` states/point — sweep is cheap |
| `K→∞` divergence + exact `p*` | product-form `M/M/1` / matrix-geometric | closed form / per-block — no state space |
| empirical cliff + validation | discrete-event simulation | cost independent of state space |
| qualitative correctness | Lean (Petri→Lean M3) + Aeneas (code→Lean L3) | the must/cannot, sorry-free |

## 3. Phased plan (each phase ships its own rung of the ladder)

| Phase | Deliverable | Reuse / New | Ladder rung added |
|---|---|---|---|
| **D0 Spec** | stop-and-wait + bounded queue; params `(λ,μ,p,τ,K,budget)`; properties (safety: buffer-bound, no-dup; perf: `W`, overflow, throughput, `P(≤T)`) | new doc | — |
| **D1 steady-state solver** | `gspn.rs`: `πQ=0` via **GTH** (stable) + sparse Gauss–Seidel; the one missing numeric (today: transient + absorption only) | new (small, drop-in) | unit tests vs `M/M/1/K` closed form; property test (rows sum, π≥0, Σπ=1) |
| **D2 model→Lean+PRISM** | `link.model.toml` (GSPN: source + buffer + `dock-gspn` link); `lift model prove` (M3 safety) + `lift model prism` (CTMC + CSL: throughput, overflow, delay-via-Little, `P(≤T)`) | reuse `emit_petri`, `gspn.rs`, `prism.rs`; new arrival/buffer GSPN + queries | M1↔M3 agreement; CTMC-vs-PRISM gate |
| **D3 sweep + threshold** | driver sweeps `p` and `K∈{2,4,8,16}`; tabulates metric; extracts knee; compares to closed-form `p*=1−λτ`; ASCII curve in report | new (thin loop over `gspn.rs`) | closed-form vs measured-knee teeth |
| **D4 empirical cross-check** | DES of the same protocol; per-`p` empirical `W`/overflow; overlay on CTMC; assert agreement + visible cliff | reuse codegen executor + V0.6 diff; new small DES | sim-vs-CTMC cross-check |
| **D5 narrative** | `*.recipe.md`: "dial latency/error → works to `p*`, then collapses"; finite-size-scaling plot; the 4-way triangulation | reuse recipe writer | — |
| **D1 Aeneas kernel** | Rust kernel = alternating-bit toggle / retransmit-budget counter → Aeneas → Lean L3, invariant sorry-free | reuse `models-fire` dogfood | L3 self-proof of the protocol kernel |

(D1 steady-state is the critical-path enabler — without `πQ=0` there is no `W`/
throughput for the *queued* model.)

## 4. Cross-checks (the teeth)

closed-form `p*` ↔ measured knee · CTMC ↔ simulation (D4) · CTMC ↔ PRISM
(existing `run_prism_and_diff`) · Lean M3 ↔ M1 `check` · finite-`K` curves → step
as `K↑`. A wrong model must go red in *more than one* of these.

## 5. Numerical-efficiency stance (the designer's lens)

Every sweep point is a tiny **exact CTMC** (cheap); the limit divergence uses the
**closed-form `M/M/1`** (no state space); the empirical layer is **simulation**
(state-space-free). So the one demo showcases three efficiency regimes. The only
new numeric the demo *needs* is **steady-state mode** (D1, GTH) — which is also
the highest-value `gspn.rs` upgrade independent of this demo.

## 6. Scope honesty / deferred

- Full ABP correctness in Lean is heavy → qualitative Lean scoped to a
  place-invariant safety bound (`emit_petri`) + eventual-delivery skeleton
  (`Ctmc.lean`); the **code→Lean L3** scoped to a *kernel*, not the whole
  protocol.
- "Phase transition" = finite-size scaling toward the `K→∞` singularity — framed
  as such, never sold as a singular finite chain.
- Real-time / deadline / **schedulability** is the deterministic worst-case
  sibling of this average-case story — a natural follow-on family, planned in §8.

## 7. Ordered start

1. ✅ **D1 steady-state (GTH)** in `gspn.rs` — enabler + standalone win.
2. ✅ **D2** `link.model.toml` (ergodic stop-and-wait + buffer) + steady-state
   metrics `mean`/`throughput`/`full` in the evaluator, validated vs M/M/1/K
   closed form + Little; `prism link` in `ci.sh`. Manual `p`-sweep already shows
   the collapse (X: 0.40→0.21, Pblock: 0.0003→0.48 as p: 0.3→0.95).
3. ✅ **D3 sweep** — `--set name=value` param override + `scripts/link-sweep.sh`:
   ASCII curve of L/X/Pblock vs `p`, closed-form `p* = R/(1+R)`, empirical knee,
   self-check (`--check`) wired into `ci.sh`. Knee p≈0.88 ≈ p*=0.882.
4. ✅ **D4 sim cross-check** — SSA (Gillespie) simulator in `gspn.rs` +
   `lift model simulate` (empirical vs analytic vs Δ); `simulation_matches_
   analytic_link` test (sim ≈ CTMC, stable & congested). Δ ≈ 0.1–3%.
5. **D5 narrative**, **Aeneas kernel** (code→Lean), **model→Lean qualitative** — next.

## 8. Real-time / schedulability — the natural deterministic intersection

The perf demo is the **average-case, stochastic** side ("how *likely* / how *fast*").
Real-time schedulability (Cheng, *Real-Time Systems*) is the **worst-case,
deterministic** side ("does it *ever* miss"). They are the **same designer
question — "what is my safe operating region?" — on the same model**, one a soft
sigmoid, the other a hard step. leanlift can host both and, crucially, **draw
both boundaries on one task/load model**:

- queueing stability `ρ < 1`  ↔  RM bound `U ≤ n(2^{1/n}−1)` / EDF `U ≤ 1`
- soft: `P(miss deadline)` rising sigmoid (CTMC, §1–5)  ↔  hard: schedulable yes/no (a step)

Same `useful > perfect` rules (§0): cheapest test that bites; the ladder travels
with the feature. Methods are *cheaper* than the CTMC (deterministic, no state
space) — the efficient complement.

| Phase | Deliverable | Reuse / New | Ladder rung |
|---|---|---|---|
| **R0 Spec** | task-set model family `kind="tasks"` (`*.model.toml`): per task `C,T,D`, policy `RM`/`EDF`; properties = schedulable?, per-task WCRT, utilization headroom | reuse the TOML parser/family auto-detect | — |
| **R1 Native analysis (M1-analog)** | utilization-bound test `O(n)` (sufficient) + **response-time analysis** fixed point `Rᵢ = Cᵢ + Σⱼ∈hp ⌈Rᵢ/Tⱼ⌉Cⱼ` (exact, pseudo-poly) + EDF demand-bound; `lift model check` → schedulable + WCRT table | new `rt.rs`; reuse report/CLI | unit tests vs textbook task sets; property test (util-pass ⇒ RTA-pass) |
| **R2 Kernel proof (L3/Kani-analog)** | carve the **RTA iteration** (the `⌈·⌉`/sum step) as a Rust kernel → prove **monotone & overflow-free fixed point** (Kani no-overflow; Aeneas/Lean: the step is monotone ⇒ least fixed point exists & RTA is sound) | reuse `models-fire` dogfood + `fire_no_underflow` Kani pattern | L3/Kani proof of the analysis kernel |
| **R3 Empirical cross-check** | discrete-event **RM/EDF scheduler** over the hyperperiod; assert observed max response `≤` RTA WCRT; small sets vs exhaustive schedule | reuse codegen executor + V0.6 diff pattern | sim-vs-RTA teeth (a missed bound goes red) |
| **R4 The intersection demo ★** | one task/load model → **hard** schedulability boundary (RTA/util, step) **and** **soft** deadline-miss probability (CTMC, sigmoid), both plotted vs load → the unified "safe operating region" | reuse D1–D5 CTMC path + R1 RTA | hard-⊆-soft consistency check (deterministic boundary is conservative) |
| **R5 Narrative** | `*.recipe.md`: "here's where it's *provably* safe (hard), and here's where it's *probably* safe (soft) — pick your margin" | reuse recipe writer | — |

**Cross-checks (teeth):** util-bound (sufficient) ⇒ RTA (exact) must agree;
RTA WCRT ≥ simulated max response; **hard boundary ⊆ soft boundary** (if it's
hard-schedulable it can't be over the stochastic stability knee). A wrong
analyzer goes red in more than one.

**Efficiency note:** util test `O(n)`; RTA pseudo-polynomial; both far cheaper
than building a CTMC — so R-phases give designers an *instant* worst-case answer,
with the stochastic CTMC reserved for the soft-degradation picture. R2's kernel
proof is the on-brand payoff: leanlift proving its *own* schedulability analyzer
sound, the same way it already proves its Petri firing kernel (V3).
