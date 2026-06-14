# Model recipe — `dock-gspn` (stochastic, M2 + the division of labour)

The dock release of `dock.model.toml`, now a **Generalized Stochastic Petri
net** (day49). `send` is immediate (instant retransmit, so `holding` markings
are vanishing and eliminated); `deliver` (rate μd) and `lose` (rate μl) are
timed and race. The reachability graph is a **CTMC** over the tangible markings,
solved numerically — numpy-free, in Rust.

## 1. Model (`dock-gspn.model.toml`, authored)

```toml
kind = "gspn"
mode = "lease"
initial = "holding:1, budget:3"        # K = 3

[[param]]
name = "p"
value = "0.5"
[[param]]
name = "mu_l"
value = "mu_d * p / (1 - p)"            # ⇒ p = μl/(μd+μl)

[[transition]]
name = "send"
kind = "immediate"                     # holding is vanishing
pre = "holding:1"
post = "inflight:1"

[[transition]]
name = "lose"
kind = "timed"
rate = "mu_l"
pre = "inflight:1, budget:1"           # spends a budget token
post = "holding:1"                     # instant resend

[[query]]
compute = "prob"
target = "freed"
# … etime, transient …
```

## 2. Measure (M2 — the native CTMC solver)

```
$ lift model prism examples/models/dock-gspn.model.toml
  level : M2 measured  (quantitative CTMC analysis)
  tangible states : 8
    P(freed)            = 1.000000
    E[time]             = 1.000000
    P(freed by T=5)     = 0.993262
  PRISM : not on PATH — self-checked against the native CTMC solver
```

Every number matches a closed form — the validation anchor:

| query | computed | closed form |
|-------|----------|-------------|
| `P(freed)` (lease) | 1.000000 | 1 (absorbs in `freed` w.p. 1) |
| `E[time]` (lease)  | 1.000000 | 1/μd — *independent of K, p* (the day49 surprise) |
| `P(freed ≤ 5)`     | 0.993262 | 1 − e^(−μd·5) = 0.993262 |

The eight tangible states are `inflight` and `freed`, each carrying the leftover
budget (0..3) — `freed` is a *class* of markings, aggregated exactly as CSL
`P=?[F "freed"]` labels a set. The solver uses the embedded jump chain for
`P(freed)`/`E[time]` and **uniformization** for the transient.

`lift model prism` also writes `dock-gspn.prism` (the tangible CTMC as an
explicit-state PRISM `ctmc` module, with the concrete rates we solved) and
`dock-gspn.props` (the CSL queries). If a `prism` binary is on PATH it is run
and its `Result:` lines are diffed against the native solver (machine-checked);
otherwise the native solver is the self-check.

## 3. Teeth — lease vs giveup

Switch to **giveup** mode (at budget 0 a loss `abort`s to a `stuck` sink:
add a timed `abort` with `inhibit = "budget"`, `post = "stuck:1"`):

```
  mode: giveup        tangible states : 9
    P(freed)            = 0.937500          # = 1 − p^(K+1) = 1 − 0.5^4
    E[time]             = 0.937500
```

`P(freed)` drops from 1 to **1 − p^(K+1)** — the day48 Part-3 "coverage". And the
*qualitative* picture flips with it: `stuck` is now reachable, so `AF freed`
(inevitability) is **false**. That is the division of labour, made sharp:

> **Lean says it must; PRISM says how fast.** In lease mode the inevitability
> skeleton is a kernel-checked theorem (`LeanLift/Models/Ctmc.lean`,
> `inevitably_freed`, sorry-free); PRISM/this solver refine it to `P=1`,
> `E[time]=1/μd`, `P(freed≤T)=1−e^(−μd·T)`. In giveup mode the proof no longer
> holds (`stuck` reachable) and the number is `1−p^(K+1)` — the two tools agree
> on *which* event matters and disagree only on the regime, exactly as they
> should. CSL `P=?[F freed]` is the quantitative refinement of CTL `AF freed`.

## Scope note

The PRISM model is exported over the *tangible* CTMC (vanishing pre-eliminated),
which is fully general and reproduces our numbers. Auto-generating the per-model
Lean qualitative proof (beyond the worked lease skeleton in `Ctmc.lean`), MDP/
CTMDP policy synthesis, and bursty (Gilbert–Elliott) loss are deferred (§5.7).
