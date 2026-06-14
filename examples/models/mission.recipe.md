# Model recipe — `mission` (behaviour tree, M1 → M3)

A robot-mission behaviour tree (PLAN-models §3). The payoff (§3.3): a BT
**compiles to an LTS**, so `check` and `prove` reuse the Phase-1 FSM machinery
*unchanged* — the same exporter, the same Lean theory, the same teeth.

## 1. Model (`mission.model.toml`, authored)

A priority fallback over a boolean blackboard `{lost, atGoal, moving}`: idle if
at the goal, else recover if lost, else navigate. Actions carry a guard
(precondition) and an effect (blackboard literals to establish).

```toml
kind    = "bt"
vars    = ["lost", "atGoal", "moving"]
initial = ["lost"]

tree = """
fallback(
  sequence( cond:atGoal, act:idle ),
  sequence( cond:lost,   act:recover ),
  act:navigate
)
"""

[[action]]
name   = "recover"
guard  = "lost=true"
effect = "lost=false"

[[action]]
name   = "navigate"
guard  = "lost=false"                 # only move once localized
effect = "moving=true, atGoal=true"

[[forbid]]                            # safety: never moving while lost
true = ["lost", "moving"]
```

Tick semantics: a leaf Action returns Success if its effect already holds,
Running (applying the effect) if its guard holds, else Failure; a Sequence fails
on the first Failure, a Fallback succeeds on the first Success, and the first
Running halts the tick. One tick ⇒ one executing action ⇒ one LTS transition.

## 2. Check (M1) and prove (M3)

```
$ lift model check examples/models/mission.model.toml
  level : M1 checked      reachable : 3 state(s)
  deadlocks : atGoal_moving           # mission complete (quiescent)
  safety    : ok (no forbidden state reachable)

$ lift model prove examples/models/mission.model.toml
  level : M3 proved  (Lean safety theorem closed, sorry-free)
  theorem   : Mission.safety
```

The three reachable blackboard states are `lost → none → atGoal_moving`; the
robot relocalizes *before* it ever moves, so `lost ∧ moving` is never reached.
The proof is the exact FSM safety theorem from Phase 1 — BT → LTS → `emit_fsm`.

## 3. Teeth

Safety here is *defence in depth*: navigate is guarded by `lost=false` **and**
the recover branch out-prioritizes it. Defeat both — put an **unguarded**
navigate first in the fallback:

```toml
tree = "fallback( act:navigate, sequence(cond:lost, act:recover) )"
# navigate with no guard
```

Now from the initial `lost` state navigate runs immediately:

- **M1** goes red: `lost_atGoal_moving` reachable and forbidden (exit 1).
- **M3** goes red: the generated Lean proof fails to elaborate (exit 1).

(Conversely, merely deleting the recover branch leaves the robot safely *stuck*
when lost — M1 reports one reachable state and M3 still proves: a quiescent BT
is a one-state LTS.)

## Scope note

The native `*.model.toml` tree DSL is authored here; importing the de-facto
**BehaviorTree.CPP / Groot XML** (§3.1) and code export (§3.5 → Phase 6) are
deferred further steps. Decorators and Parallel are not yet modelled — the
reactive Sequence/Fallback core covers this example.
