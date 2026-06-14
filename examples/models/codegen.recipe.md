# Model recipe — code export + the loop closure (Phase 6)

`lift model export` turns a model into a runnable executor in **C++ / Rust / Go**,
and `--verify` closes the loop: the generated code is difftested against the
native model semantics over random action traces. This is the model-axis
analogue of leanlift's L1 — *"the exporter proposes, the algorithm disposes"* —
and it is where the two halves of leanlift meet (the code→Lean engine and the
model→artifacts axis).

## 1. Export

```
$ lift model export examples/models/mcl.model.toml --lang rust --emit mcl_exec.rs
  leanlift code export — fsm `examples/models/mcl.model.toml` → rust
  source : mcl_exec.rs
```

The executor is an idiomatic state machine: `enum State`, `enum Event`, a `step`
match returning `Option<State>`, a `forbidden` predicate (the §6.2 **runtime
monitor** — the proved safety property compiled to a guard), and a driver. FSMs
and behaviour trees both export (a BT compiles to an LTS first).

All three languages share one **trace protocol** so their output is directly
comparable: read traces from stdin (one per line, space-separated event names);
for each, print the visited state names, a `!` after any forbidden state, and
`BLOCKED` when an event is refused.

```
$ printf 'start converged kidnapped\n' | ./mcl_exec
Boot|Delocalized Localize|Delocalized Navigate|Localized Recover|Delocalized
```

## 2. The loop closure (`--verify`)

```
$ lift model export examples/models/mcl.model.toml --lang rust --verify
  loop closure : L1 conformant — 21/21 reachable edges match the native model
  (generated code ≡ model semantics — the two halves of leanlift meet)

$ lift model export examples/models/mission.model.toml --lang go --verify
  loop closure : L1 conformant — 7/7 reachable edges match the native model
```

`--verify` compiles the generated executor (`rustc` / `c++` / `go build`), runs
it over **exhaustive (state, action)-edge coverage** — a witness path to every
reachable state, each extended by every action — and compares its output
line-by-line to the native simulator. For a deterministic model this is a
*complete* equivalence check, not a sample: every reachable edge is exercised
(`mcl`: 21 = 5 states × 4 events + 1). Conformant ⇒ the generated code *is* the
model. Rust, C++, and Go all conform on `mcl` (FSM) and `mission` (BT).

## 3. Teeth

A code-generator bug is caught as an edge divergence. Corrupt one transition in
the emitted Rust — point `Localize|Delocalized --converged-->` at `Recover`
instead of `Navigate`:

```
  loop closure : FAILED — edge trace N diverges:
      trace   : start converged …
      native  : … Navigate|Localized …
      codegen : … Recover|Delocalized …
```

Because coverage is exhaustive over reachable edges, *any* single-edge codegen
bug is guaranteed to surface (not just statistically likely). The native model
is the oracle; this is the same difftest discipline as the engine's bit-exact
L1, applied to state traces instead of numeric vectors.

## Petri / CPN executors

Code export also covers the Petri families: a PT-net (or an unfolded CPN)
becomes a marking-array executor (`enabled`/`fire`/`forbidden` over `[u32; N]`),
and the loop closure difftests **marking** traces instead of state names.

```
$ lift model export examples/models/dock.model.toml --lang go --verify
  loop closure : L1 conformant — 49/49 reachable edges match the native model
$ lift model export examples/models/resource.model.toml --lang rust --verify
  loop closure : L1 conformant — 25/25 reachable edges match the native model
```

(dock: 49 = 6 reachable markings × 8 transitions + 1; resource: 25 = 4 × 6 + 1.
On an unbounded net the BFS is capped and the verdict says "coverage partial".)
`--lang dot` emits a place/transition Petri diagram (places as circles with
token counts, transitions as boxes).

## Scope note

Code export covers FSM, BT, Petri, and CPN (the last via unfolding). GSPN
executors, the networked Go coordinator (the dock's signed/sequence-numbered
lease protocol, §6.4/§2.7), and proving the Rust export back through Aeneas to
re-derive M3 on the code (§6.3) are deferred further steps.
