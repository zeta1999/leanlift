# Model recipe — `dock` (M1 → M3, PT-net with loss)

Two distant rovers (A, B) share ONE charging dock over a **lossy** release
channel (day48 Part 2). Asynchronous / interleaving Petri-net semantics: a
release message in flight can be dropped. The lesson, made formal: **safety
survives loss; liveness does not.**

## 1. Model (`dock.model.toml`, authored)

Places `free, csA, csB, relA, relB`; one dock token initially (`free:1`). Each
rover acquires (`acq*: free→cs*`), releases (`rel*: cs*→rel*`), the message is
delivered (`deliver*: rel*→free`) — or **lost** (`loss*: rel*→∅`, a pure-loss
transition: `post = ""`).

```toml
kind    = "petri"
places  = ["free", "csA", "csB", "relA", "relB"]
initial = "free:1"

[[transition]]            # acqA: grab the dock
name = "acqA"
pre  = "free:1"
post = "csA:1"
# … acqB, relA/relB, deliverA/deliverB …

[[transition]]            # lossA: release message DROPPED
name = "lossA"
pre  = "relA:1"
post = ""

[[bound]]                 # safety: at most one rover charging
name   = "mutex"
places = ["csA", "csB"]
max    = "1"
```

## 2. Check (M1 — native BFS)

```
$ lift model check examples/models/dock.model.toml
  level : M1 checked  (reachable set explored, safety holds)
  reachable : 6 state(s)
  deadlocks : 0,0,0,0,0
  safety    : ok (no forbidden state reachable)
  note      : marking vector order: free,csA,csB,relA,relB
  note      : net is LOSSY: declared upper-bound safety is monotone under loss …
  note      : the reachable deadlock(s) above include the loss-induced sink …
```

Mutual exclusion holds across all 6 reachable markings. The reported deadlock
`0,0,0,0,0` (read with the legend: every place empty) is the **loss-induced
sink**: fire `acqA; relA; lossA` and the dock token is gone forever — no rover
can ever charge again. The checker surfaces this as a first-class finding (the
safety-survives-loss / liveness-doesn't split).

## 3. Prove (M3 — Lean, sorry-free)

```
$ lift model prove examples/models/dock.model.toml
  level : M3 proved  (Lean safety theorem closed, sorry-free)
  theorem   : Dock.safety  (every reachable state satisfies safeB)
  axioms    : 'Dock.safety' depends on axioms: [propext, Quot.sound]
```

The exporter proves the **inductive strengthening** `total m ≤ 1` (every
transition conserves the token total, or — under loss — decreases it), then
derives `csA + csB ≤ 1` by `omega`. Mutual exclusion is a corollary of the
upper bound, *not* of a conservation equality — which is exactly why it survives
loss. The kernel re-derives, with a proof object, what the M1 BFS checked.

## 4. Teeth

Set `initial = "free:2"` (two dock tokens — mutual exclusion should break):

- **M1** goes red: `csA+csB = 2 > 1` reachable at `0,0,2,0,0` / `0,1,1,0,0` /
  `0,2,0,0,0` (exit 1).
- **M3** goes red: the proof fails to elaborate — `omega` cannot derive
  `csA + csB ≤ 1` from the now-weaker `total ≤ 2` (exit 1).

A wrong model fails in *both* the checker and the proof (PLAN-models §0
invariant 2). Conversely, leaving `free:1` but keeping the loss transitions
shows safety holds *with* loss present — the headline result.
