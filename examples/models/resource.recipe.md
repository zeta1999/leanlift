# Model recipe — `resource` (coloured Petri net, M1 → M3)

A coloured resource-mutex (PLAN-models §4, Jensen LNCS 803 in miniature): N
processes, coloured by identity, compete for ONE shared lock. The payoff (§4.3):
the CPN **unfolds to a PT-net**, so `check` (M1) and `prove` (M3) reuse the
Phase-2 Petri machinery unchanged.

## 1. Model (`resource.model.toml`, authored)

Colour set `Proc = {p1,p2,p3}`; a one-element `Lock`. One coloured `acquire`/
`release` schema stands for one PT transition *per process* (the compactness).

```toml
kind = "cpn"
conserved = ["crit", "lock"]          # the place-invariant subsystem

[[colour]]
name = "Proc"
values = ["p1", "p2", "p3"]

[[place]]
name = "idle"
colour = "Proc"
init = "p1, p2, p3"

[[place]]
name = "lock"
colour = "Lock"
init = "lk"

[[transition]]
name = "acquire"
var  = "p:Proc"                       # |Proc| bindings, one schema
pre  = "idle(p), lock(lk)"
post = "crit(p)"

[[bound]]
name  = "mutex"
place = "crit"                        # summed over all colours
max   = "1"
```

## 2. Check (M1) and prove (M3)

```
$ lift model check examples/models/resource.model.toml
  level : M1 checked      reachable : 4 state(s)
  safety    : ok (no forbidden state reachable)
  note      : CPN compactness: 3 coloured place(s) / 2 transition(s)
              → unfolded 7 PT place(s) / 6 PT transition(s)

$ lift model prove examples/models/resource.model.toml
  level : M3 proved  (Lean safety theorem closed, sorry-free)
  theorem   : Resource.safety
```

The unfolded reachability graph **is** the coloured occurrence graph (the
unfolding is semantics-preserving). The four reachable markings are "all idle"
plus one per process holding the lock — `crit` never exceeds 1.

The M3 proof is the Phase-2 exporter with a **place invariant**: the conserved
subsystem `lock + Σ crit` starts at 1 and every transition keeps it (acquire:
lock → crit; release: crit → lock), so `Σ crit ≤ 1` follows by `omega`. This is
exactly Jensen's place-invariant argument — the global token total (here 4) is
*too weak*; the conserved subsystem is what proves mutual exclusion.

## 3. Teeth

Give the lock two tokens (`init = "lk, lk"`):

- **M1** goes red: `crit_p1+crit_p2+crit_p3 = 2 > 1` reachable (exit 1).
- **M3** goes red: the conserved mass now starts at 2, so `omega` can no longer
  derive `Σ crit ≤ 1` (exit 1).

## Scope note

This delivers the coloured-mutex (colour sets, typed places, a bound variable,
unfolding, occurrence graph, place invariant) end to end. The full Jensen
**distributed-database** net needs *broadcast multiset* arcs (`Mes(s) = {(s,r) |
r≠s}`), guards, and tuple/product colours — deferred further steps, as are PNML
high-level interop (§4.6) and code export (§4.7).
