# `leanlift` — SPEC addendum: behavioural **models** (FSM · BT · CPN · SPN)

> Addendum to `SPEC.md` (v0.1). Status: **preliminary** — written to be argued with.
> Grounded in the FSM/Petri → Lean export spike (`../../propaganda/tutor-tech/
> formal-day48-fsm-lean-export`), the GSPN → CTMC → PRISM spike (`…/formal-day49-
> gspn-ctmc`), and Jensen, *An Introduction to the Theoretical Aspects of Coloured
> Petri Nets* (LNCS 803, 1994; `~/Downloads/sds,+PB-476.pdf`).

## 1. One-line pitch

Author a **behavioural model** — a finite-state machine, a behaviour tree, a
coloured Petri net, or a stochastic Petri net with token/message loss — in **one
easy text format**, and from that single source of truth **prove its qualitative
properties in Lean 4, measure its quantitative properties in PRISM/Storm, and
generate a runnable implementation in C++/Rust/Go** — with a one-command CLI.

## 2. Why this is a *leanlift* feature, not a separate tool

`SPEC.md` describes one direction: **source code → Lean model, validated by
bit-exact differential execution**. The front-end (Aeneas / LLM) is *untrusted*;
the differential oracle and the Lean kernel are the trust anchor —
"LLM proposes, algorithm disposes."

This addendum adds the **dual** direction: **one text model → many artifacts**
(a Lean proof, a PRISM model, executable code). The same trust philosophy
applies, sharpened:

- the exporter is **deliberately mechanical** (like `export_petri.py`): it is
  auditable by inspection, and the Lean kernel / model-checker re-derives what it
  emitted. A wrong model produces a Lean proof that **fails to compile** and a
  checker that goes **red** — the generator is not trusted, it is *checked*
  (the "teeth", `EXPLAINER_PETRI.md` §8/§9).
- the model is the **single source of truth**; every artifact is generated, never
  hand-edited.

The two directions **meet** (SPEC-models §7, and Plan Phase 6): the code this
addon *emits* (C++/Rust/Go) can be fed back through the existing `lift verify` /
`lift prove` to certify that the implementation **conforms to** the model. One
half generates the implementation from the model; the other half proves the
implementation matches it.

> **The thesis, in slogan form** (after `formal-day49 §1`): *Lean says it **must**
> happen; PRISM says **how likely / how fast**; codegen makes it **run**; and the
> existing lift engine checks the code is **the same** model.*

## 3. Scope

**In (v1):** four model families, all *finite-state or bounded*:

| family | what it is | standard text format | analysis spike |
|---|---|---|---|
| **FSM** | finite-state machines, synchronous (alphabetised) product | SCXML (W3C) / DOT | day48 Part 1 (`fsm.py`, `export_lean.py`) |
| **BT** | behaviour trees (Sequence/Fallback/Parallel/Decorator/Action/Condition) | BehaviorTree.CPP / Groot XML | new (compiles to an LTS for analysis) |
| **PT-net** | place/transition Petri nets, interleaving, with **token loss** | PNML (ISO/IEC 15909-2) | day48 Part 2 (`petri.py`, `export_petri.py`) |
| **CPN** | **coloured** Petri nets: typed tokens, arc expressions, guards | PNML high-level / symmetric | new (Jensen) |
| **SPN/GSPN** | **stochastic** PN: exponential-rate + immediate transitions → CTMC | PRISM language | day49 (`gspn.py`, `export_prism.py`) |

**Out (v1):** unbounded nets (infinite reachable set; we *detect and refuse*,
not diverge — `petri.py PetriNet.reachable` raises past a per-place bound); full
LTL/CTL liveness under fairness (we do safety + *bounded* liveness via a variant;
unbounded-fairness liveness is a seam, `EXPLAINER_PETRI.md` §8); measure-theoretic
*proof* of probabilities (we *compute* them in PRISM and *prove the qualitative
skeleton* in Lean — the division of labour of `formal-day49 §1/§6`).

## 4. The unifying abstraction — the Discrete Transition System IR (DTS-IR)

Every family lowers to one core, because **all of them are transition systems**
— the central reuse of the spike: a Petri net *is* a transition system, an FSM
*is* one, and the Lean development shares `Fsm.Reachable` /
`Fsm.invariant_of_preserved` **verbatim** across both (`EXPLAINER_PETRI.md` §5).

```
                       step : State → Action → Option State          (the core)
  FSM      State = control state          Action = event            (LTS, finite)
  PT-net   State = marking (ℕ-vector)     Action = transition id    (interleaving)
  CPN      State = multiset of typed tok. Action = (transition, binding)
  BT       compiles to an LTS over (node-status × blackboard)
  SPN/GSPN PT-net/CPN + a per-transition LABEL: rate λ (timed) | weight w (immediate)
```

Layered IR (each level is the one below + a structure):

- **L0 LTS/FSM** — finite `State`, `step`, `initial`. The reachability graph of
  *everything* is an L0 object.
- **L1 PT-net** — `Marking : Place → ℕ`, transition `⟨pre, post⟩`, guarded firing
  `m ↦ m − pre + post`; **loss** = a transition with `post = ∅`.
- **L2 CPN** — places typed by **colour sets** (finite); tokens carry values
  (multisets); **arc expressions** (total functions of bound variables) + boolean
  **guards** + variable **bindings** (Jensen §1, §3). Unfolds to L1 when colour
  sets are finite (Jensen p.9: every CP-net ↔ a PT-net).
- **Stochastic overlay** — attach `rate`/`weight`; the reachability graph carries
  the labels → a **CTMC** (timed) / **DTMC** (discrete) / **MDP** (with choice).
  Immediate transitions make markings **vanishing**; eliminate them → the tangible
  CTMC (`gspn.py reach_tangible`, day49 §2).
- **BT** — a control structure (tick → `Success | Failure | Running`, a
  blackboard); **executes** natively as code, and **compiles to an L0 LTS** over
  (active-node, status, blackboard-abstraction) for analysis.

## 5. Properties — one property IR, two epistemic weight classes

Properties normalise to a **Model Contract IR** (the dual of SPEC §7's code
Contract IR). The division of labour is the whole point (`formal-day49 §1, §6`):

| property | logic | backend | method | ladder |
|---|---|---|---|---|
| **safety / invariant** `□φ` | — | **Lean** | invariant + induction (`invariant_of_preserved`); `omega` for Petri | **M3** |
| **bounded liveness** | — | **Lean** | a **variant** (measure strictly decreases) | **M3** |
| **reachable / inevitable** | CTL `AF` | **Lean** | `Inev` inductive (day49 `Ctmc.lean`) | **M3** |
| **probability / time** | **CSL/PCTL** `P=?[F φ]`, `P=?[F≤T φ]`, `R=?[…]` | **PRISM/Storm** | linear solve / **uniformization** | **M2** |

The correspondence is exact and load-bearing: **CSL `P=?[F φ]` is the
quantitative refinement of CTL `AF φ`** (day49 §6). Lean proves the event is
*well-posed and inevitable*; PRISM returns *the number*. Neither subsumes the
other — the certificate carries **both**.

The **safety-vs-liveness-under-loss split** is a first-class modelling lesson the
tool must surface (`EXPLAINER_PETRI.md` §3): an **upper-bound** invariant
(`csA+csB ≤ 1`, mutex) is *monotone under loss* and survives a lossy channel; a
**conservation equality** (`free+cs+msg = 1`, availability) is *broken by loss*
→ deadlock. The tool reports: state your property as an inequality if you can;
treat every conservation equality as a liveness obligation needing a delivery
guarantee (retransmit/timeout).

## 6. The model-certification ladder (parallel to SPEC §10's L0–L3)

| level | meaning | produced by |
|---|---|---|
| **M0 modeled** | the text model parses; the generated Lean **L0-typechecks** / the PRISM model builds | exporters |
| **M1 checked** | the native BFS confirms the invariant on the (bounded) reachable set; deadlocks classified; coverage/uncovered reported | in-tool checker |
| **M2 model-checked** | PRISM/Storm confirms a CSL/PCTL property (cross-checked vs the native CTMC solver) | PRISM export |
| **M3 proved** | a Lean theorem (safety / variant / inevitability) closed, **sorry-free**, kernel-checked (`#print axioms`) | Lean export |
| **+ conformance** | the *generated code*, run through `lift verify` (difftest) against the model's reference semantics → **L1**; optionally `lift prove` the Rust export → re-derives M3 on the code | the existing engine |

**Honesty rules carry over** (SPEC §13, day49 §7): M1 is *evidence* (it trusts
the checker, the bound, and that the right space was enumerated — a terminating
BFS without a counterexample is not a proof). M2 numbers are *computed, not
proven* — trust them as you trust a linear-algebra routine, validated against
analytic closed forms (day49 §5). M3 is the only kernel-checked claim. A
bounded result must never be reported as universal; a proof guarded by a
precondition must surface it.

## 7. Architecture (extends SPEC §4)

```
lift/
  models/
    ir/         → DTS-IR: Lts, PtNet, Cpn, Bt, StochasticOverlay; the TransitionSystem trait
    formats/    → native *.model.toml  ⇄  SCXML, BT-XML, PNML, PRISM   (import/export)
    color/      → Colour IR: finite colour sets, arc-expr sublanguage, guards, bindings, unfold→PT
    check/      → native model checker: BFS reachable / invariant / deadlock / variant   (port of petri.py)
    stoch/      → GSPN→CTMC: vanishing elimination + numpy-free solver (absorption / E[t] / uniformization)
    lean/       → Lean exporter (port of export_lean.py / export_petri.py) → Generated.lean → lake elaborate → certify
    prism/      → PRISM/Storm exporter (port of export_prism.py) → .prism + .props → run → parse → cross-check
    codegen/    → model → executor/simulator + runtime monitor, in C++ / Rust / Go
  lean/LeanLift/Models/   → reusable Lean theory: Fsm.lean, Petri.lean, Ctmc.lean   (ported from day48/49)
  cli/          → lift model {check|prove|export|simulate} …
```

Reused, audited Lean theory (ported into `lean/LeanLift/Models/`):
`Fsm.lean` (`Reachable`, `invariant_of_preserved`, `Inev`), `Petri.lean`
(`fire`, `Enabled`, **`fire_le`** the loss lemma, `le_preserved`), `Ctmc.lean`
(the qualitative `Inev`/`AF` skeleton). These are Mathlib-free (`omega`/`decide`/
`simp`), so they share the existing **integer-track toolchain** — no Mathlib pin.

## 8. CLI / UX (extends SPEC §9)

**Simple by default — a hard requirement.** Everything in §3–§7 is additive
machinery that must *never* leak into the basic path. The headline is always
**one verb, one file**, with the model family and the default property
**auto-detected from the file content** — no `--kind`, no mandatory config. The
verb says *what you want to know* (`check`→M1, `prove`→M3, `prism`→M2,
`export`→code), not *what kind of model it is*. Every flag has a default and only
*refines* the answer; removing all flags still gives a useful one. (Full UX bar:
`PLAN-models.md` §8.)

```bash
# parse, BFS-check the invariant, report reachable set + deadlocks  (→ M1)
lift model check dock.model.toml

# generate Generated.lean, elaborate, certify sorry-free            (→ M3)
lift model prove dock.model.toml --property mutex

# generate + run PRISM (or self-check vs the native solver)         (→ M2)
lift model prism dock.model.toml --const K=5,p=0.5,T=5

# emit a runnable executor + invariant monitor                      (further)
lift model export dock.model.toml --lang rust --out ./gen

# interop with standard formats
lift model import mission.scxml         # SCXML  → native
lift model import tree.xml --as bt      # BT-XML → native
lift model import db.pnml               # PNML   → native
lift model export net.model.toml --format pnml
```

- One `model-report.json`: the M-level, the property, reachable-set size + bound,
  the divergence/deadlock table, coverage (what was *not* explored — no silent
  truncation), the quantitative results + their analytic cross-check, and the
  content hash of the model.
- Exit code: `0` = the claimed M-level was reached, nonzero otherwise.

## 9. Text-format decision (standard **and** easy)

The user requirement is "standard and/or easy to use." We do **both**, in this
order of effort:

1. **Native `*.model.toml`** (easy; the single source of truth) — a small typed
   DSL mirroring the spike's dataclasses (`fsm.py FSM`, `petri.py Transition`):
   places/states, transitions (`pre`/`post` or `src`/`event`/`dst`), colour sets,
   arc expressions, rates/weights, initial marking, properties. Readable,
   diff-able, the thing you author and version.
2. **Standard formats** (interop; imported/exported, not authored): **SCXML** for
   FSM, **BehaviorTree.CPP / Groot XML** for BT (the de-facto robotics standard),
   **PNML** (ISO/IEC 15909-2) for PT-nets and high-level/symmetric CPNs, and the
   **PRISM language** for stochastic models. Phased *after* the native path works
   end-to-end (Plan: each family's format step comes after its check+export step).

## 10. Open questions / risks (extends SPEC §13)

- **Colour-set finiteness.** Unfolding CPN → PT-net (and thus the BFS/Lean
  backends) requires *finite* colour sets; an infinite type yields an infinite
  PT-net (Jensen p.9). v1 restricts to finite/bounded colours for analysis, and
  keeps the colored form only for compact **code/PRISM** emission.
- **State explosion.** The native BFS enforces a per-place bound and **refuses**
  (raises) rather than diverging on an unbounded net (`petri.py`, Exercise P4);
  PRISM/Storm handle larger state spaces symbolically. Always log the *uncovered*
  part (SPEC §13).
- **Toolchain pins.** The qualitative track is **Mathlib-free**, so it rides the
  existing integer-track toolchain (unlike the float track, `docs/float-formats.md`).
  Quantitative *proof* (measure-theoretic Markov chains) is deliberately **out of
  scope** — delegated to PRISM (day49 §7).
- **PRISM/Storm may be absent.** Generate the `.prism`/`.props` and **self-check
  against the native CTMC solver** (day49's pattern); the literal `prism` run is a
  documented one-liner for whoever has the tool.
- **BT semantics variants** (reactive vs non-reactive, halting/`halt()`): pin
  **BehaviorTree.CPP** semantics as canonical; document the choice.
- **Expression-language scope creep** (CPN arc expressions): keep the Colour IR a
  **small, total** sublanguage (finite enums, bounded ints, products, subset-by-
  predicate, total arc maps, boolean guards) — enough for Jensen's database
  example, no Turing-complete CPN ML.
- **Liveness needs fairness + temporal logic** (`EXPLAINER_PETRI.md` §8): v1 does
  safety + bounded liveness (variant) only; full LTL/CTL-under-fairness is a seam.
```
