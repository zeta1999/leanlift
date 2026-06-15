# Recipe — `link`: a phase transition you can dial (perf-demo)

A worked, end-to-end showcase (PLAN-perf-demo): **one model of a 1→1 network
protocol → quantitative performance (CTMC/PRISM) + an empirical cross-check
(simulation), exhibiting a designer-visible PHASE TRANSITION.** The question it
answers: *given my latency and loss rate, up to what load does this link keep
up — and where does it fall off a cliff?*

## The model

`examples/models/link.model.toml` — stop-and-wait ARQ, one sender → one
receiver, lossy link, fed by message arrivals into a bounded buffer (K=8),
written as an **ergodic GSPN** so steady-state performance is well-defined.

Designer knobs (`--set name=value`, no file edits):
- `lam`  — offered load (arrival rate)
- `p`    — per-attempt loss probability
- `mu_r` — retransmit rate ≈ 1/timeout (the latency knob)

Invariants: `buf+slot = K` (waiting buffer), `idle+tx+wait = 1` (one message in
flight — stop-and-wait).

## The physics (why there's a cliff, not a slope)

Each delivery needs `Geometric(1−p)` attempts, so mean service time
`S(p) = 1/μ_d + p/((1−p)·μ_r)` and offered load `ρ = λ·S(p)`. The buffer is
stable **iff `ρ < 1`**, which gives an exact threshold

```
p* = R/(1+R),   R = (1 − λ/μ_d)·μ_r / λ.
```

As `p → p*⁻` the queue length `L = ρ/(1−ρ)` (and delay `W = L/λ`) diverges; for a
finite buffer K the divergence becomes a **knee that sharpens as K grows**
(finite-size scaling toward the K→∞ singularity). For the defaults
(`λ=0.4, μ_d=1, μ_r=5`): **`p* = 0.882`.**

## What you run

```
# the phase-transition curve (ASCII), with closed-form p* and the empirical knee
./scripts/link-sweep.sh

# one operating point: empirical (simulation) vs analytic (CTMC), self-checked
lift model simulate examples/models/link.model.toml --set p=0.9 --time 200000

# the raw quantitative metrics + PRISM export
lift model prism examples/models/link.model.toml --set p=0.9
```

## What you see — the cliff

`link-sweep.sh` (throughput `X` bar, full bar = λ):

```
p              L         X    Pblock   throughput X (full bar = λ)
0.30      0.3358    0.3999    0.0003   ████████████████████████████████████████
0.70      0.8147    0.3984    0.0039   ████████████████████████████████████████
0.85      2.4633    0.3810    0.0475   ██████████████████████████████████████
0.88      3.5020    0.3609    0.0979   ████████████████████████████████████
0.90      4.4493    0.3355    0.1613   ██████████████████████████████████
0.95      6.8979    0.2080    0.4801   █████████████████████
0.98      7.6938    0.0926    0.7685   █████████

empirical knee (first p with X < 0.95·λ): p ≈ 0.88     closed-form p* = 0.882
```

Below `p*` the link delivers everything (`X ≈ λ`, short queue); above it the
buffer saturates (`L → K`), throughput **collapses**, and blocking explodes.

## The triangulation (why you can trust it)

The same threshold falls out of three independent computations — the leanlift
cross-check ethos applied to a phase transition:

1. **Closed form** — `p* = 0.882` from the stability algebra above.
2. **Exact CTMC** — the sweep's empirical knee, `p ≈ 0.88` (GTH steady-state
   solver over the tangible marking chain). `ci.sh` asserts `|knee − p*| ≤ 0.06`.
3. **Simulation** — SSA/Gillespie, e.g. at `p=0.9`: empirical `L=4.48, X=0.335,
   Pblock=0.163` vs analytic `4.45 / 0.335 / 0.161` (Δ ≈ 0.1–3%).

## Designer takeaway

You get a **safe operating region** with a sharp boundary, the *exact* knob that
moves it (`p* = R/(1+R)` — raise `μ_r`/lower latency to push it out), and an
empirical sanity check that the analysis isn't lying. The deterministic
worst-case twin of this (hard schedulability) is PLAN-perf-demo §8.

*Pending (the correctness leg): the qualitative Lean safety of the buffer
invariant (model→Lean) and a code→Lean L3 proof of the protocol kernel — see
PLAN-perf-demo §3 (D1-Aeneas) and §6.*
