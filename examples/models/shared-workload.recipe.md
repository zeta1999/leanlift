# Recipe — shared workload: provably safe ⊊ probably safe

The capstone tying the two demos together. The SAME server under load is analyzed
**both** ways — deterministic real-time (worst-case) and stochastic queueing
(average-case) — and the two safe-operating regions are shown on one load axis.

## The two views of one workload

- `examples/models/shared-tasks.model.toml` — the **deterministic** view: two
  periodic jobs with tight deadlines (D = T/2) on the server, judged by exact
  response-time analysis (RTA, the critical-instant worst case).
- `examples/models/shared-queue.model.toml` — the **stochastic** view: the same
  server as an M/M/1 with the matching base utilization (0.5), judged by queueing
  stability and mean delay.

`--scale ℓ` raises the load on both.

## What you run

```
./scripts/shared-workload-sweep.sh
```

```
load ℓ  HARD (RT/RTA)     SOFT (queue)    queue mean delay W
1.0     SCHEDULABLE       STABLE          2.0000
1.3     SCHEDULABLE       STABLE          2.8571
1.4     UNSCHEDULABLE     STABLE          3.3333
1.8     UNSCHEDULABLE     STABLE          10.0000
1.9     UNSCHEDULABLE     STABLE          20.0000
2.0     UNSCHEDULABLE     UNSTABLE        NaN

provably-safe boundary (HARD): ℓ ≈ 1.4
probably-safe boundary (SOFT): ℓ ≈ 2.0
```

## The point

- **Provably safe** (HARD, RTA): every deadline is *certifiably* met only up to
  ℓ ≈ 1.4. Past that, a deadline provably misses in the worst case (simultaneous
  releases).
- **Probably safe** (SOFT, queue): the server is *stable on average* up to
  ℓ ≈ 2.0; in the margin [1.4, 1.9] the mean delay is finite but climbing
  (3.3 → 20) — it usually keeps up, but offers no per-job guarantee.

So **provably-safe ⊊ probably-safe**, and the gap is the designer's margin:
certify to ℓ ≈ 1.4 for hard-real-time guarantees, or ride into [1.4, 1.9] if a
best-effort average (with a known, growing delay) is acceptable.

## Why one tool

This is the whole thesis: a single modeling tool gives a designer of
performance- AND correctness-critical code *both* boundaries from *one* workload
— the worst-case proof (`tasks`/RTA, Kani- and Aeneas-checked kernels) and the
average-case performance (`qnet`/`link` CTMC, simulation-validated) — instead of
two disconnected analyses. The stochastic single-server special case is `link`;
the multi-station generalization is `qnet`; the worst-case twin is `tasks`.
