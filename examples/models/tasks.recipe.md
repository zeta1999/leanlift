# Recipe — `tasks`: provably safe vs probably safe (the hard/soft intersection)

The deterministic **worst-case** sibling of `link.recipe.md` (which is the
stochastic average-case story). Same designer question — *what is my safe
operating region?* — but answered two ways on **one task model**:

- **HARD** (real-time schedulability): does it *ever* miss a deadline? A sharp
  step, proved by exact response-time analysis (RTA).
- **SOFT** (stochastic): how *often* does it miss when execution is typically
  lighter than worst-case? A graceful sigmoid, by Monte-Carlo simulation.

## The model

`examples/models/tasks.model.toml` — three periodic tasks under Rate-Monotonic
scheduling (`kind = "tasks"`). The classic teaching case: utilization
`U = 1/3 + 1/5 + 2/8 = 0.783` **exceeds** the RM bound `3(2^{1/3}−1) = 0.780`, so
the cheap `O(n)` sufficient test *fails* — yet exact RTA proves every task meets
its deadline.

## What you run

```
# HARD: the schedulability certificate (utilization bound + exact RTA)
lift model check examples/models/tasks.model.toml

# the HARD/SOFT intersection, swept over load scale
./scripts/tasks-sweep.sh

# one operating point, both verdicts
lift model simulate examples/models/tasks.model.toml --scale 1.6
```

## What you see — RTA beats the bound

```
  utilization : U = 0.7833   bound = 0.7798   (FAIL — sufficient)
  response-time analysis (exact):
    sensor     R =    1  ≤  D = 3     ✓
    filter     R =    2  ≤  D = 5     ✓
    control    R =    5  ≤  D = 8     ✓
  level : SCHEDULABLE
```

RTA is *exact* (and tighter than the bound): worst-case response times computed
by the fixed point `Rᵢ = Cᵢ + Σⱼ∈hp ⌈Rᵢ/Tⱼ⌉Cⱼ`.

## The intersection — `tasks-sweep.sh`

```
scale    hard (RTA)        soft miss  P(miss) bar
1.0      SCHED             0.0000
1.3      UNSCHED           0.1305     █████
1.6      UNSCHED           0.1515     ██████
2.2      UNSCHED           0.4666     ███████████████████
3.5      UNSCHED           0.6509     ██████████████████████████

hard boundary (first UNSCHED): scale ≈ 1.3   soft miss there: 0.1305
```

The **hard** boundary trips at scale ≈ 1.3 — but the **soft** reality (typical
execution `∈ [0.5C, C]`) still misses only ~13% there, climbing to a sigmoid as
load grows. The hard boundary is **conservative**: it says "stop" well before
deadlines actually start dropping.

## The triangulation (why you can trust it)

1. **Utilization bound** — sufficient `O(n)` screen (here it's pessimistic).
2. **Exact RTA** — the fixed point; its per-term kernel is **proved monotone &
   overflow-free by Kani** (`verify-kani.sh`: `div_ceil_safe`, `term_monotone`),
   so the iteration provably converges to the true worst-case — leanlift proving
   its OWN analyzer sound.
3. **Simulation** — a fixed-priority scheduler from the critical instant produces
   exactly the RTA worst-case (`rta_matches_simulation`); the stochastic version
   gives the soft miss curve.

## Designer takeaway

You get **two boundaries** on one model: a *provably-safe* region (hard, RTA) and
a *probably-safe* region (soft, miss probability) — and the gap between them is
your **margin**. Tighten to the hard line for certifiable systems; ride into the
soft region (with a known miss rate) where best-effort is acceptable.

The stochastic average-case twin of all this is `link.recipe.md`.
