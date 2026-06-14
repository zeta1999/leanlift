# Plan — behavioural **models**: FSM · BT · CPN · SPN → Lean / PRISM / code

> Status: planning doc. Companion to `SPEC-models.md` (the addendum) and the
> existing `SPEC.md` / `PLAN-proofs.md`. Written 2026-06; to be argued with.

## 0. Where we are, and what this adds

The engine today goes **code → Lean** and certifies conformance/proofs (L0–L3,
`PLAN-proofs.md`). This plan adds the **dual axis**: author one **behavioural
model** in an easy text format and generate, from that single source of truth, a
**Lean proof** (qualitative), a **PRISM model** (quantitative), and **runnable
code** (C++/Rust/Go) — productizing the day48 (FSM/Petri→Lean) and day49
(GSPN→CTMC→PRISM) spikes. The model-certification ladder is M0–M3 + conformance
(`SPEC-models.md` §6).

**Two non-negotiable invariants for every phase below:**

1. **Usage stays trivial.** The headline path is always *one command on one file*:
   `lift model check <file>` — language family auto-detected from content, the
   default property checked, a human verdict + `model-report.json` emitted. Every
   flag has a sensible default; flags only *refine*, never *enable*, the basic
   path. New families must not add new required ceremony. (UX bar: §8.)
2. **The generator is mechanical and checked, never trusted.** Exporters are dumb
   and auditable; the kernel / model-checker re-derives their output; a wrong
   model goes red in both the checker and the proof (the "teeth").

The order is **simplest-family-first**, each family taken *end to end*
(check → prove → measure → code) before the next, so there is always a working
one-command demo.

---

## Phase 0 — Foundations: the IR, the native checker, the Lean theory ✅ DONE

The shared substrate every later phase reuses. No new model family yet.

> **Status (landed):** DTS-IR `Model` trait + explicit `Lts` (`src/models/ir.rs`);
> bounded-BFS native checker that refuses to diverge silently (`src/models/check.rs`,
> **M1**); dependency-free `*.model.toml` parser + family auto-detection
> (`src/models/{toml,format}.rs`); `model-report.json` + human verdict
> (`src/models/report.rs`); `lift model check <file>` wired (`src/models/mod.rs`).
> Lean theory ported sorry-free: `lean/LeanLift/Models/{Fsm,Petri}.lean`. Exit
> criterion met — `lift model check examples/models/tiny.model.toml` prints a
> verdict; regression + teeth in `tests/run.sh`.

- **0.1 DTS-IR (`models/ir/`).** Rust types for `Lts`, `PtNet`, `Cpn`, `Bt`, and
  a `StochasticOverlay`; a unifying `TransitionSystem` trait (`initial`,
  `step(state, action) -> Option<state>`, `enabled(state)`). This is the Rust
  twin of `fsm.py`/`petri.py`'s dataclasses, and encodes the §4 insight (one
  `step`, every family).
- **0.2 Native checker (`models/check/`).** Port `petri.py`'s engine: BFS
  `reachable` (with a per-place/per-state **bound** that *raises* on an unbounded
  net — no silent divergence), `check_invariant` (return violating states),
  `deadlocks`, and a `variant`-based bounded-liveness check. Pure Rust, instant on
  1-safe nets. **→ M1.**
- **0.3 Lean theory port (`lean/LeanLift/Models/`).** Bring the reusable,
  Mathlib-free theory in-repo from day48/49: `Fsm.lean` (`Reachable`,
  `invariant_of_preserved`, `Inev`), `Petri.lean` (`fire`, `Enabled`, the loss
  lemma `fire_le`, `le_preserved`), `Ctmc.lean` (qualitative `Inev`/`AF`). Wire a
  `lake` target alongside the existing integer-track project. Confirm it
  elaborates sorry-free.
- **0.4 Native format + parser (`models/formats/`).** Define `*.model.toml` (the
  easy authoring DSL, `SPEC-models.md` §9) and a parser into the DTS-IR. **Content
  auto-detection**: infer the family from the file's shape so `lift model check`
  needs no `--kind` flag.
- **0.5 Property IR + parser.** Safety/invariant, variant (bounded liveness),
  reachability/inevitability (CTL `AF`), quantitative (CSL/PCTL) — the §5 table.
  Each property names a backend; a model with no stated property gets a sensible
  **default** (reachability + deadlock-freedom) so `check` always does something.
- **0.6 CLI skeleton + report.** `lift model {check|prove|prism|export|simulate|
  import}`; `model-report.json` carrying the M-level, reachable size + bound,
  divergence/deadlock table, coverage, content hash. `check` works end-to-end on
  a trivial 2-state model. **Exit criterion: `lift model check tiny.model.toml`
  prints a verdict.**

---

## Phase 1 — FSM, end to end (the smallest family; reuses day48 Part 1 exactly)

> **Status (landed 1.1–1.4):** FSM IR (`Lts`), native `*.model.toml` (flat +
> two-machine product), synchronous alphabetised product (`format::product`),
> Lean exporter (`src/models/lean.rs`) + `lift model prove` → **M3** sorry-free,
> and the `mcl` example (`examples/models/mcl.model.toml`, `mcl.recipe.md`).
> Teeth proven: a safety-breaking mutation fails *both* M1 (BFS) and M3 (Lean).
> Regression in `tests/run.sh`. **Deferred** (further steps): 1.5 SCXML/DOT
> interop, 1.6 code export (lands in Phase 6).

- **1.1 FSM IR + native format.** `states, alphabet, transitions:(s,e)->t,
  initial`, partial step (missing entry = BLOCKED), per `fsm.py`.
- **1.2 Native check.** Reachable set, invariant violations, and **synchronous
  (alphabetised) product** composition (`FSM.product`: shared event ⇒ both move,
  private event ⇒ owner moves / other self-loops). **→ M1.**
- **1.3 Lean export (`models/lean/`).** Port `export_lean.py`: `inductive State`,
  `inductive Event`, `step`, `Inv`, and the exhaustive proof template
  (`cases … <;> simp_all`); elaborate via `lake env lean`; certify sorry-free via
  `#print axioms`. **→ M3.**
- **1.4 Example `mcl`.** The supervisor × belief product; property **"never
  reach `Navigate|Delocalized`"** (`fsm.py safe`). Ship the worked
  `mcl.recipe.md`. **Teeth:** mutate one transition → checker reports the
  violation *and* the generated Lean proof fails to compile.
- **1.5 Standard format (interop).** SCXML import/export; DOT export for
  visualization. *After* 1.1–1.4 are green.
- **1.6 Code export (further).** FSM → C++/Rust/Go: a `step` table + a driver
  loop + a runtime monitor of the invariant. Feeds Phase 6.

---

## Phase 2 — PT-net (place/transition Petri) **with token loss** (day48 Part 2)

- **2.1 PT-net IR + native format.** `places`, `transitions:⟨pre,post⟩`, `initial`
  marking; **loss** = `post = ∅` (`petri.py`).
- **2.2 Native check.** Bounded reachability, `deadlocks`, the **mutex upper-bound**
  invariant (`csA+csB ≤ 1`) and the **conservation equality** (`sum = 1`); report
  the **safety-survives-loss / liveness-doesn't split** (`EXPLAINER_PETRI.md` §3)
  as a first-class finding. **→ M1.**
- **2.3 Lean export.** Port `export_petri.py`: `structure M` (one `Nat` field per
  place — so `omega` sees plain arithmetic), guarded `step`, the upper-bound
  `Inv`, `inv_holds` (`cases t <;> simp [step] <;> split <;> omega`), `safety`
  corollary; uses `Petri.lean`'s loss lemmas. Certify sorry-free. **→ M3.**
- **2.4 Example `dock`.** Two rovers, one dock, lossy release channel. Prove mutex
  survives loss; *detect* the loss-induced deadlock. `dock.recipe.md`. **Teeth:**
  set `free := 2` → checker finds `csA+csB = 2` reachable *and* the Lean base case
  `total init = 2 ≤ 1` fails to build.
- **2.5 Bounded liveness (the deadlock fix).** Add `timeout`/`resend` transitions
  (retry budget); prove the **variant** (a measure decreases ⇒ the dock is
  eventually reacquired) — `EXPLAINER_PETRI.md` §9 / day13 retry-budget. **→ M3.**
- **2.6 Standard format.** PNML (P/T) import/export.
- **2.7 Code export (further).** The signed, sequence-numbered, UDP **coordinator
  + rover-client lease protocol** of `EXPLAINER_PETRI.md` §7 — where the safety
  invariant *becomes* the runtime guard `verify-signature ∧ check-seq`. Feeds
  Phase 6; Go is the natural target (networked).

---

## Phase 3 — Behaviour trees

- **3.1 BT IR + standard format.** Sequence / Fallback(Selector) / Parallel /
  Decorator / Action / Condition, with reactive variants; **BehaviorTree.CPP /
  Groot XML** as the canonical format (it is the de-facto robotics standard, so
  here the "standard" format *is* the easy one — import it directly).
- **3.2 BT semantics + native executor.** tick → `Success | Failure | Running`;
  a blackboard. A simulator that replays a tick trace (mirrors `fsm.run`).
- **3.3 BT → LTS compilation.** Compile the tree to an L0 LTS over (active node ×
  status × abstracted blackboard) so **Phase-1 check + Lean export apply
  unchanged** — the reuse payoff. **→ M1/M3** for BT safety properties.
- **3.4 Example.** A robot-mission BT (patrol → recover → dock) whose compiled LTS
  is the Phase-1 `mcl` machine; prove a safety property ("never run two conflicting
  actions", or "a recovery is always reachable"). `bt.recipe.md`.
- **3.5 Code export.** BT → C++ (BehaviorTree.CPP nodes) / Rust / Go executor.
  BTs *exist to be executed*, so codegen is a **first-class** output here, not a
  "further step".

---

## Phase 4 — Coloured Petri nets (CPN) (Jensen, LNCS 803)

- **4.1 Colour IR (`models/color/`).** Finite colour sets (enum, bounded int,
  product, **subset-by-predicate** — Jensen's `MES = {(s,r) | s≠r}`); arc
  expressions as **total functions** of bound variables; boolean **guards**;
  variable **bindings** (Jensen §1, §3). A small, total sublanguage — *not* CPN ML.
- **4.2 Native CPN simulator.** Binding enumeration, enabling, multiset firing
  (Jensen §1 occurrence rule); the **occurrence graph** (reachability) + **place
  invariants** (Jensen §6–7). **→ M1.**
- **4.3 Unfold CPN → PT-net** (finite colours). The bridge to all Phase-2
  backends (Jensen p.9: every CP-net ↔ a PT-net). Validate `unfold ≡ coloured`
  on the occurrence graph. This is what makes M3 free for CPNs.
- **4.4 Lean export.** Path (a): export the **unfolded PT-net** → immediate reuse
  of Phase-2 proofs (place invariant → Lean theorem). Path (b, research): a
  **coloured** Lean model (typed tokens, multiset markings) for compactness.
- **4.5 Example `db`.** Jensen's distributed-database CP-net (n sites, `Mes(s)`):
  prove a place invariant (mutual exclusion via place `Passive`). Demonstrate the
  **compactness lesson** — at n=5 the PT-net has 97 places / 50 transitions, the
  CPN only 9 / 4. `db.recipe.md`.
- **4.6 Standard format.** PNML high-level / symmetric net import/export; note
  CPN-Tools interop.
- **4.7 Code export (further).** CPN → typed-token executor (colours → structs/
  enums) in C++/Rust/Go.

---

## Phase 5 — Stochastic / GSPN → CTMC → PRISM (day49)

- **5.1 Stochastic overlay IR.** Timed transitions (exponential **rate** λ),
  immediate transitions (**weight** w), budget tokens; modes (`lease`/`giveup`).
  `mu_l = mu_d·p/(1−p)` realises a target per-attempt loss `p`.
- **5.2 GSPN unfolding (`models/stoch/`).** Reachability graph carrying rates →
  CTMC over **tangible** markings; **eliminate vanishing** (immediate) markings
  (`gspn.py reach_tangible` + `ctmc`, day49 §2).
- **5.3 Native CTMC solver.** numpy-free Rust: absorption probabilities (embedded
  jump chain `(I−P_TT)x = P_TA`), expected time (fundamental matrix), transient by
  **uniformization** (`Λ = max −Qᵢᵢ`, Poisson-weighted powers). **Cross-check vs
  analytic closed forms** — `P(freed)=1−p^{K+1}`, `E[time]=1/μ_d`,
  `P(freed≤T)=1−e^{−μ_d T}` (day49 §4–5). This *is* the M2 trust anchor when no
  PRISM binary is present.
- **5.4 PRISM/Storm export (`models/prism/`).** Port `export_prism.py`: `.prism`
  (`ctmc`/`dtmc`/`mdp` module) + `.props` (CSL/PCTL: `P=?[F φ]`, `P=?[F≤T φ]`,
  `R{"time"}=?[…]`, `P≥0.99[F≤T φ]`). Run the binary if present; **parse + diff
  vs the native solver**. **→ M2.**
- **5.5 Wire the division of labour.** Lean proves the qualitative skeleton
  (`freed` reachable + absorbing + `Inev`/`AF`); PRISM returns the number. The
  certificate states **both** and the exact CSL↔CTL correspondence (day49 §6).
- **5.6 Example `dock-gspn`.** Lease vs giveup: `P(freed)=1` vs `1−p^{K+1}`;
  `E[time]=1/μ_d` (independent of K, p — the instructive surprise). **Teeth:**
  switch lease→giveup → the number drops *and* the Lean inevitability proof flips
  (`stuck` now reachable, `AF freed` false). `dock-gspn.recipe.md`.
- **5.7 Seams (further).** DTMC (Bernoulli-p + RTT, day49 §7); MDP/CTMDP for
  loss-robust **policy synthesis** (RDDL, day49 §8); bursty loss (Gilbert–Elliott);
  rewards/performability (`R=?` energy/SLA).

---

## Phase 6 — Code export (C++/Rust/Go), unified — and the loop closure

- **6.1 Common codegen backend (`models/codegen/`).** model → executor/simulator
  in each language: state/marking as a struct/enum, `step` as a `match`/`switch`,
  a driver loop. One backend, three language idioms.
- **6.2 Runtime monitors.** Compile a proved invariant into asserts/guards — the
  M3 property *becomes* a runtime check (the dock's `verify-sig ∧ check-seq`).
- **6.3 Loop closure with the existing engine.** Run the **generated code**
  through `lift verify` (differential test) against the model's native reference
  semantics → **L1 conformance**; optionally `lift prove` the Rust export
  (Aeneas) → re-derive **M3 on the code**. *The two halves of leanlift meet*
  (`SPEC-models.md` §2).
- **6.4 Per-language idioms.** C++ (BehaviorTree.CPP for BTs; enum+switch FSM),
  Rust (enums+match — Aeneas-friendly, so the prove-back path works), Go (the
  networked coordinator/UDP protocol of Phase 2.7).

---

## Phase 7 — Integration, docs, regression, and the UX bar

- **7.1 CLI wired.** All `lift model …` subcommands; `model-report.json` with the
  M-ladder; **family auto-detection** so the one-command path needs no `--kind`.
- **7.2 Recipes.** A worked `*.recipe.md` per example (mirrors `PLAN-proofs.md`
  Appendix A): model → check → export → proof/number → certificate.
- **7.3 Regression (`tests/run.sh`).** Every example green at its claimed M-level;
  **teeth tests** (mutate model → checker red + proof red) for each family.
- **7.4 Docs.** Keep `SPEC-models.md` (addendum) + this plan + a **formats
  reference** current.
- **7.5 UX audit (gate, every phase).** Re-confirm the headline command stays
  *one command, one file, auto-detected, sensible defaults* (§8). Any family that
  needs extra required ceremony fails this gate until the ceremony is defaulted
  away.

---

## 8. The UX bar (kept simple and intuitive — a standing requirement)

The richness above must never leak into the basic path. Concretely:

- **One command, one file.** `lift model check mission.scxml`,
  `lift model prove dock.model.toml`, `lift model prism dock.model.toml` — the
  family (FSM/BT/PT/CPN/SPN) and the default property are **auto-detected from the
  file**; no `--kind`, no mandatory config.
- **Verbs map to the ladder, 1:1 and memorable.** `check` → M1 (fast BFS),
  `prove` → M3 (Lean), `prism` → M2 (quantitative), `export` → code,
  `simulate` → run a trace, `import` → from a standard format. You pick the verb
  by *what you want to know*, not by *what kind of model it is*.
- **Defaults everywhere.** No stated property ⇒ check reachability +
  deadlock-freedom. No `--lang` ⇒ Rust (the prove-back-able one). No PRISM binary
  ⇒ self-check against the native solver and say so.
- **Standard formats just work as input.** `lift model check tree.xml` (a
  BehaviorTree.CPP file) or `db.pnml` is detected and handled — no conversion
  step the user must run first.
- **One report, always.** Human verdict to stdout + `model-report.json`; exit
  `0` iff the claimed M-level was reached.
- **Flags refine, never enable.** Every flag (`--property`, `--const`, `--lang`,
  `--bound`, `--harness`) has a default; removing all flags still gives a useful
  answer. This is the same bar `SPEC.md` §9 sets for the code path.

---

## 9. Cross-cutting risks (see `SPEC-models.md` §10 for the full list)

- **Finite colours only** for the analysis (unfold) path; colored form kept for
  code/PRISM. **State explosion** → bounded BFS that *refuses* unbounded nets,
  symbolic PRISM for scale, always log uncovered. **Mathlib-free** qualitative
  track shares the integer toolchain; quantitative *proof* stays out of scope
  (delegated to PRISM). **PRISM optional** → native-solver self-check. **BT
  semantics** pinned to BehaviorTree.CPP. **Liveness** = safety + bounded-variant
  only; fairness/LTL is a seam.

---

## 10. Ordered next steps

1. **Phase 0** — IR + native checker + Lean-theory port + `lift model check` on a
   trivial model. The substrate everything else stands on.
2. **Phase 1** — FSM end to end (`mcl`), the smallest family, direct port of
   day48 Part 1. First one-command `check` → `prove` → M3 + teeth.
3. **Phase 2** — PT-net + loss (`dock`), day48 Part 2; the safety-survives-loss
   lesson and the deadlock-fix variant.
4. **Phase 5** — stochastic (`dock-gspn`) brought forward *if* the quantitative
   story is wanted early (day49 is self-contained and high-impact); else continue
   3 → 4 → 5 in order.
5. **Phase 3 / Phase 4** — BT, then CPN (CPN reuses Phase-2 via unfolding).
6. **Phase 6 / 7** — code export + loop closure, integration, recipes, UX audit.
```
