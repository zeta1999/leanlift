# Formats reference — `lift model`

The behavioural-models axis (see [`SPEC-models.md`](./SPEC-models.md) and
[`PLAN-models.md`](./PLAN-models.md)). One easy text format, five families, one
auto-detected one-command path. This page is the authoring reference.

## The verbs

| Verb | Level | What it does |
|------|-------|--------------|
| `lift model check <file>` | M1 | bounded-BFS reachability + safety; deadlocks; family-specific findings |
| `lift model prove <file>` | M3 | export a Lean model + proof, certify sorry-free (FSM/BT/Petri/CPN) |
| `lift model prism <file>` | M2 | GSPN → tangible CTMC: solve quantitative queries + export PRISM |
| `lift model export <file>` | L1 | generate a Rust/C++/Go executor; `--verify` difftests it vs the model |

The **family is auto-detected from the file** — no `--kind` needed. Every flag
*refines, never enables*: the bare verb on the bare file always does something
useful. Each run writes a human verdict to stdout and a `model-report.json`;
exit code is `0` iff the claimed level was reached.

Detection precedence: explicit `kind = "…"`, else `[[colour]]` ⇒ cpn, `tree` ⇒
bt, `places` ⇒ petri (or `kind="gspn"` for stochastic), `states`/`machines` ⇒
fsm.

## FSM — finite-state machines

Flat machine, or a synchronous product of named component machines.

```toml
kind = "fsm"
machines = ["supervisor", "belief"]   # omit for a single flat FSM (use `states`)
initial  = ["Boot", "Delocalized"]    # flat: initial = "Boot"; states = [...]

[[transition]]
machine = "supervisor"                # omit `machine` for a flat FSM
from = "Boot"
on   = "start"
to   = "Localize"

[[forbid]]                            # safety: this (product) state is unreachable
supervisor = "Navigate"               # flat: state = "Error"
belief     = "Delocalized"
```

A product is composed synchronously (shared event ⇒ both move; private event ⇒
owner moves, other self-loops) and flattened. `prove` exports `inductive State`/
`Event`, `step`, `safeB`, and a `safety` theorem via `invariant_of_preserved`.

## BT — behaviour trees

A reactive tree over a finite boolean blackboard; compiles to an LTS.

```toml
kind    = "bt"
vars    = ["lost", "atGoal", "moving"]
initial = ["lost"]                    # vars true initially; others false

tree = """
fallback(
  sequence( cond:atGoal, act:idle ),
  sequence( cond:lost,   act:recover ),
  act:navigate
)
"""

[[action]]
name   = "navigate"
guard  = "lost=false"                 # precondition (literals: v=true/v=false/v/!v)
effect = "moving=true, atGoal=true"   # blackboard literals to establish

[[forbid]]                            # safety: never (lost ∧ moving)
true = ["lost", "moving"]
```

Nodes: `seq(…)`/`sequence`, `fallback(…)`/`sel`/`fb`, `cond:v` / `cond:!v`,
`act:name`. Tick: an action returns Success if its effect already holds, Running
(applying it) if its guard holds, else Failure; the first Running halts the tick.

## Petri — place/transition nets (with token loss)

```toml
kind      = "petri"
places    = ["free", "csA", "csB", "relA", "relB"]
initial   = "free:1"                  # a marking: place:count, comma-separated
conserved = ["free", "csA", "csB", "relA", "relB"]  # optional: place-invariant subset

[[transition]]
name = "acqA"
pre  = "free:1"
post = "csA:1"

[[transition]]
name = "lossA"
pre  = "relA:1"
post = ""                             # pure loss: empty post

[[bound]]                             # safety: sum(places) ≤ max
name   = "mutex"
places = ["csA", "csB"]
max    = "1"
```

`prove` strengthens to the inductive invariant `Σ_conserved ≤ B` (default: all
places) and derives each bound by `omega`. Upper-bound safety survives loss;
the loss-induced deadlock is reported by `check`.

## CPN — coloured Petri nets

Finite colour sets; unfolds to a PT-net (so check/prove reuse the Petri backends).

```toml
kind      = "cpn"
conserved = ["crit", "lock"]          # place-invariant subset (top-level)

[[colour]]
name   = "Proc"
values = ["p1", "p2", "p3"]

[[place]]
name   = "idle"
colour = "Proc"
init   = "p1, p2, p3"                 # multiset of colour values

[[transition]]
name = "acquire"
var  = "p:Proc"                       # one bound variable per transition
pre  = "idle(p), lock(lk)"            # single-token arcs: var or constant value
post = "crit(p)"

[[bound]]
name  = "mutex"
place = "crit"                        # summed over all colours
max   = "1"
```

## GSPN — stochastic nets (→ CTMC → PRISM)

```toml
kind    = "gspn"
mode    = "lease"                     # documentation; transitions present decide behaviour
places  = ["holding", "inflight", "freed", "budget"]
initial = "holding:1, budget:3"

[[param]]                             # named scalars; value is an arithmetic expr
name  = "p"
value = "0.5"
[[param]]
name  = "mu_l"
value = "mu_d * p / (1 - p)"          # may reference earlier params

[[transition]]
name   = "send"
kind   = "immediate"                  # zero-time; chosen by weight; makes markings vanishing
weight = "1.0"
pre    = "holding:1"
post   = "inflight:1"

[[transition]]
name = "deliver"
kind = "timed"                        # exponential; `rate` is an expression
rate = "mu_d"
pre  = "inflight:1"
post = "freed:1"

[[transition]]
name    = "abort"                     # giveup mode: enabled only when budget is empty
kind    = "timed"
rate    = "mu_l"
pre     = "inflight:1"
inhibit = "budget"
post    = "stuck:1"

[[query]]                             # compute = prob | etime | transient
name    = "P(freed)"
compute = "prob"
target  = "freed"
[[query]]
name    = "P(freed by T=5)"
compute = "transient"
target  = "freed"
time    = "5"
```

`prism` builds the tangible CTMC (vanishing eliminated), solves the queries
(numpy-free), and writes `<stem>.prism` + `<stem>.props`. With a `prism` binary
on PATH it runs and diffs; otherwise the native solver is the self-check.

## Code export

```
lift model export <file> --lang rust|c++|go [--emit <out>] [--verify]
```

Emits an executor for FSM/BT (enum state machine + a `forbidden` runtime
monitor). `--verify` compiles it and difftests against the native model over 300
deterministic traces → L1 conformance. The trace protocol: stdin traces (one per
line, space-separated events) → visited state names, `!` after a forbidden
state, `BLOCKED` on a refused event.

## Interop — standard formats as input

Standard formats are detected from content and handled with no conversion step
(the UX bar: "standard formats just work as input").

- **SCXML** (W3C statecharts) → FSM. `lift model check mission.scxml`,
  `lift model prove mission.scxml`, `lift model export mission.scxml` all work
  directly — the `<scxml>` root is auto-detected. Subset: `<state id>`/`<final
  id>` (flattened) and `<transition event= target=>`; the safety property is
  authored in-file as `forbid="true"` on a `<state>`. (PNML for Petri and
  BehaviorTree.CPP/Groot XML for BTs are further steps.)

```xml
<scxml initial="locked">
  <state id="locked"><transition event="coin" target="unlocked"/></state>
  <state id="unlocked"><transition event="push" target="locked"/></state>
  <state id="broken" forbid="true"/>   <!-- safety: must be unreachable -->
</scxml>
```

- **DOT** (Graphviz) export for visualization: `lift model export <file> --lang
  dot` emits a digraph (initial double-circled, forbidden states filled red,
  edges labelled by event). Render with `dot -Tpng model.dot -o model.png`.

## The worked examples

`examples/models/`: `tiny` (FSM), `mcl` (FSM product), `dock` (Petri + loss),
`mission` (BT), `resource` (CPN), `dock-gspn` (GSPN). Each has a `*.recipe.md`
(model → check → prove/measure/export → certificate). All are exercised by
`tests/run.sh`.
