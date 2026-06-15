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
  sibling of this average-case story (utilization bound, response-time analysis)
  — a natural follow-on family (see Cheng, *Real-Time Systems*): same designer
  question ("what's my safe operating region?"), a sharp boundary, but worst-case
  rather than stochastic. Deferred to its own plan.

## 7. Ordered start

1. **D1 steady-state (GTH + sparse GS)** in `gspn.rs` — enabler + standalone win.
2. **D2 `link.model.toml`** + the queued CSL queries (reuses the most).
3. **D3 sweep** — fastest path to *seeing* the phase change.
4. **D4 sim cross-check**, **D5 narrative**, **Aeneas kernel** — in any order.
