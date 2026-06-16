# Recipe — `qnet`: the bottleneck phase transition (open queueing network)

The multi-station generalization of `link.recipe.md`. An **open Jackson network**
solved exactly in closed form (product-form — no state space), cross-checked by
simulation. The designer question: *where is my bottleneck, and how much load
until it saturates?*

## The model

`examples/models/qnet.model.toml` — three stations: requests arrive at `frontend`,
flow to `worker`, which completes (70% exit) or bounces to `retry` and back — a
feedback loop the traffic equations resolve.

## What you run

```
lift model check examples/models/qnet.model.toml      # per-station ρ/L/W + bottleneck
./scripts/qnet-sweep.sh                                # bottleneck divergence vs load
lift model simulate examples/models/qnet.model.toml    # empirical L vs analytic
```

## What you see

```
station        λ        ρ          L          W
frontend     2.0000   0.4000     0.6667     0.3333
worker       2.8571   0.7143     2.5000     0.8750 ◀ bottleneck
retry        0.8571   0.1429     0.1667     0.1944
network L = 3.3333   W = 1.6667   throughput = 2.0000   level : STABLE
```

The feedback inflates the worker's load: `λ_worker = 2/(1−0.3) = 2.857`, so it's
the bottleneck at ρ=0.714 even though external arrivals are only 2.

## The phase transition — `qnet-sweep.sh`

```
scale    verdict     bottleneck  L(bottleneck)
1.0      STABLE      worker      2.5000
1.2      STABLE      worker      6.0000
1.3      STABLE      worker      13.0000
1.4      UNSTABLE    worker      NaN

empirical instability: scale ≈ 1.4   closed-form scale* = 1.400
```

Since ρ is linear in the external rate, the network goes unstable at
`scale* = 1 / max ρ(1) = 1/0.714 = 1.4` — the worker's queue diverges as load
approaches it. Closed form and the swept verdict agree exactly.

## The triangulation

1. **Closed form** — traffic equations + per-station M/M/1 (product-form, exact).
2. **Stability boundary** — `scale* = 1/max ρ`, matched by the swept verdict.
3. **Simulation** — open-network DES; empirical per-station L matches analytic
   to ~0.01 (`simulation_matches_analytic`).

## Designer takeaway

The product-form solution names your **bottleneck** and the exact **load margin**
to saturation — instantly, with no state space — and the simulation confirms it.
Push load past `scale*` and that one station's queue blows up while the rest sit
idle. (The single-server special case is `link`; the worst-case real-time twin
is `tasks`.)

Honest scope: single-server stations (M/M/1) today; M/M/c (Erlang-C) is refused
at parse rather than approximated — a known gap, not a silent wrong.
