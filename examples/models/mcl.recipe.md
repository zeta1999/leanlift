# Model recipe — `mcl` (M1 → M3)

The behavioural-models analogue of `rust-isqrt.recipe.md`: author one model,
check it, prove it. The system is the Day-45 MCL robot — a mission `supervisor`
composed in lock-step with a `belief` (localization) estimator, sharing the
events `{converged, kidnapped}`. Safety property: **never navigate while
delocalized** — the product must never reach `(Navigate, Delocalized)`.

## 1. Model (`mcl.model.toml`, authored)

Two FSMs and a forbidden product state. The tool computes the synchronous
(alphabetised) product — a shared event fires iff both machines accept it; a
private event (`start`, `goal_reached`) moves its owner and self-loops the
other.

```toml
machines = ["supervisor", "belief"]
initial  = ["Boot", "Delocalized"]

[[transition]]            # supervisor: Boot -start-> Localize -converged-> Navigate …
machine = "supervisor"
from = "Boot"
on   = "start"
to   = "Localize"
# … (see mcl.model.toml)

[[transition]]            # belief: Delocalized <-kidnapped- / -converged-> Localized
machine = "belief"
from = "Delocalized"
on   = "converged"
to   = "Localized"

[[forbid]]                # the safety property, as a product state
supervisor = "Navigate"
belief     = "Delocalized"
```

## 2. Check (M1 — native BFS)

```
$ lift model check examples/models/mcl.model.toml
  level : M1 checked  (reachable set explored, safety holds)
  reachable : 5 state(s)
  deadlocks : Done|Localized          # the terminal mission state
  safety    : ok (no forbidden state reachable)
```

The five reachable product states are `Boot|Delocalized`, `Localize|Delocalized`,
`Navigate|Localized`, `Recover|Delocalized`, `Done|Localized` — note
`Navigate|Delocalized` is **not** among them. `Done|Localized` is reported as a
deadlock: the mission has ended, which is legitimate termination (a declared
liveness property — Phase 2.5 — is what would turn a deadlock red).

## 3. Prove (M3 — Lean, sorry-free)

```
$ lift model prove examples/models/mcl.model.toml
  level : M3 proved  (Lean safety theorem closed, sorry-free)
  theorem   : Mcl.safety  (every reachable state satisfies safeB)
  axioms    : 'Mcl.safety' depends on axioms: [propext]
```

`lift model prove` emits a self-contained Lean file (the flattened product as an
`inductive State`, the `step` function, and `safeB`) and elaborates it. The
theorem is closed by `LeanLift.Models.Fsm.invariant_of_preserved` + an
exhaustive finite case split — the kernel re-derives, with a proof object, what
the M1 BFS checked. `propext` is a standard Lean axiom; the absence of `sorryAx`
is the sorry-free certificate.

## 4. Teeth

Break the model — make `belief` fail to re-localize on `converged`
(`Delocalized --converged--> Delocalized`) — and the robot can enter `Navigate`
while still `Delocalized`:

- **M1** goes red: `safety : VIOLATED — Navigate|Delocalized` (exit 1).
- **M3** goes red: the generated Lean proof *fails to elaborate* (exit 1) —
  `simp_all` can no longer discharge the `navigateDelocalized` arm because that
  state is now reachable with `safeB = false`.

That a wrong model fails in *both* the checker and the proof is the trust model
(PLAN-models §0 invariant 2): the generator is mechanical, the kernel disposes.
