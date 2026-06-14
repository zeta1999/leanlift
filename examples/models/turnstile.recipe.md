# Model recipe — `turnstile` (SCXML import + DOT export)

A standard **W3C SCXML** statechart, handled with no conversion step — the
"standard formats just work as input" UX bar. The same coin-operated turnstile
flows through every verb; the family is auto-detected from the `<scxml>` root.

## 1. The file (`turnstile.scxml`, standard SCXML)

```xml
<scxml initial="locked">
  <state id="locked">
    <transition event="coin" target="unlocked"/>
    <transition event="push" target="locked"/>
  </state>
  <state id="unlocked">
    <transition event="push" target="locked"/>
    <transition event="coin" target="unlocked"/>
  </state>
  <state id="broken" forbid="true"/>   <!-- safety: must be unreachable -->
</scxml>
```

The only leanlift-specific addition is `forbid="true"` on a `<state>` — the
safety property authored in-file (keeping the one-command, one-file path).

## 2. Every verb, on the .scxml directly

```
$ lift model check  examples/models/turnstile.scxml
  level : M1 checked      reachable : 2 state(s)      safety : ok
$ lift model prove  examples/models/turnstile.scxml
  level : M3 proved  (Lean safety theorem closed, sorry-free)
$ lift model export examples/models/turnstile.scxml --lang rust --verify
  loop closure : L1 conformant — 300/300 traces match the native model
$ lift model export examples/models/turnstile.scxml --lang dot --emit turnstile.dot
  source : turnstile.dot     # dot -Tpng turnstile.dot -o turnstile.png
```

`broken` is unreachable, so M1 is safe and M3 closes; the SCXML parser feeds the
same `Lts` the native `.model.toml` FSM path uses, so check / prove / export and
the loop closure are all reused unchanged. The DOT export double-circles the
initial state and fills forbidden states red.

## Scope note

SCXML import covers flat `<state>`/`<final>` + evented `<transition>`. Compound/
parallel hierarchy, eventless transitions, datamodel/executable content, and the
PNML (Petri) and BehaviorTree.CPP (BT) importers are further steps.
