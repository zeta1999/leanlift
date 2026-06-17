# PLAN — FPGA (Aria-HDL) verification support

> Make leanlift verify FPGA designs authored in **Aria-HDL** (`../fpga-meta-compiler`)
> by **projecting Aria's hardware IR onto the leanlift model families that already
> exist** — adding as little new code as possible. The capstone is a two-chip
> serial protocol proved correct end-to-end: Lean4 export, **equivalence to a
> reference Petri net**, and correctness **under given timing + channel-loss
> assumptions**.
>
> **Quality bar (unchanged): bugs are not an option.** Every implementation step
> ends with BOTH `./ci.sh` GREEN (+ `verify.sh` where a proved kernel is touched)
> AND a **brutally-honest code-review subagent** over that step's diff, triaged
> and fixed before moving on. Cross-check every number against a closed form, an
> analysis, AND a simulation (here: Aria's own cycle-accurate emulator).

## Why this is a natural fit (reuse map)

Aria-HDL is already mature: its own IR (`IrModule` — `IrNode`, `IrFormalProperty`,
`TimingInfo`, `PipelineInfo`, `SystolicInfo`), and backends for Verilog/VHDL,
**Lean4 proof obligations**, SVA/PSL+SymbiYosys, resource reports, Leiserson–Saxe
retiming, C-slowing, and a cycle-accurate emulator. What it does *not* have is what
leanlift already is:

| FPGA concern (Aria IR) | leanlift family (existing) | Reused engine |
|---|---|---|
| Control FSM (enum `Register` + `when`/`Mux` `next`) | **FSM** (`Lts`) | `check.rs` (reach/deadlock/safety), `lean.rs::emit_fsm` (sorry-free) |
| FIFO / `PipelineReg` / ready-valid flow; channel loss | **Petri** (`PtNet`) | bound invariant + loss lemma (`Petri.lean`) |
| Pipeline latency / II (hard "valid within N cycles") | **tasks** (`TaskSet`) | `rt.rs` exact RTA/EDF |
| Streaming throughput / backpressure / bottleneck stage | **qnet** (Jackson) | `qnet.rs` traffic eqns, stability, bottleneck |
| Channel error/loss → delivery probability, **phase change** | **GSPN→CTMC** | `gspn.rs` GTH + uniformization (the `link`/`dock-gspn` story) |
| Protocol ≟ reference model | **equivalence** (NEW, mechanical) | product BFS over two `Model`s + Lean bisimulation invariant |

A streaming FPGA pipeline **is the shared-workload demo in silicon**: hard latency
bound = RTA, steady throughput/backpressure = queueing — the *provably-safe ⊊
probably-safe* boundary already built, now under a clock.

## Bridge direction (decided)

The Lean-relevant content lives **in the IR** (`IrFormalProperty.expr : IrExpr` is
a full expression tree; `lean4.rs` already emits from it). So:

- **Primary — leanlift ingests Aria IR JSON.** Aria gains one small backend,
  `--emit-ir-json` (hand-written, zero-dep, matching Aria's no-deps policy and its
  existing JSON resource report). leanlift gains a `fpga` frontend that parses that
  JSON and **projects** it onto the families above. Projection (verification
  semantics) lives in the verification tool — mirrors how leanlift already ingests
  PNML→Petri and SCXML→FSM.
- **Fallback — aria-hdl emits leanlift files.** For anything the IR genuinely
  cannot carry (should be nothing, given `IrFormalProperty`), Aria writes a ready
  `*.model.toml` and leanlift verifies it unchanged.

### The No-LLM invariant (hard requirement)

**Every transform on the FPGA verification path is deterministic and mechanical**
— generator proposes, kernel/checker disposes. No LLM is in the loop for any
projection, proof emission, or analysis. The only LLM-tagged surface anywhere in
leanlift is C++/Go **codegen optimization** (Rust uses Aeneas) — that path is
**not touched** here. Every step below records its transform in the ledger (§ No-LLM
ledger) and is triple-checked: Lean kernel (sorry-free) ∧ BFS checker ∧ Aria's
cycle-accurate emulator. Any step that would need an LLM is called out and
**rejected or gated**, never silently used.

### Hardware test tags

Each test/step is tagged for where it must run. CI (`ci.sh`) runs only `[CPU]`.

- **`[CPU]`** — pure Rust / Lean-core; runs anywhere, in `ci.sh`. All projections,
  `check`/`prove`, RTA/qnet/Petri/equivalence, Aria emulator cross-checks.
- **`[M24]`** — **24 GB Apple-Silicon Mac.** Aria **Metal** backend emit+run;
  leanlift Kani harnesses (arm64); the Mathlib-cached optimization proofs.
- **`[GPU]`** — **RTX 6000 Pro box.** Aria **CUDA/OpenCL** emulation kernels
  build+run; **Verilator** co-sim (large); **PRISM/Storm** heavy CTMC cross-check
  of the loss model; `yosys` synthesis sanity. Tagged, run off-CI, results logged.

---

## Phase B — the bridge (Aria IR ⇄ leanlift)

- **B1 — bridge contract.** Specify a versioned JSON serialization of the IR subset
  leanlift needs: `ports`, `IrNode` (`Register{ty,next,reset,enable,clock_domain}`,
  `Wire`, `Mux`/`CaseMux`, `Fifo{depth,src/dst clock}`, `PipelineReg{stage,valid,ready}`,
  `Instance`, `FormalProperty`), `clock_domains`, `PipelineInfo`, `SystolicInfo`,
  `TimingInfo` (critical_path_ns, target_period_ns, II), and `@clock_freq`/`@max_*`
  annotations. Document the schema in `docs/FORMATS-fpga.md`. `[CPU]`
- **B2 — Aria emitter** `--emit-ir-json` (in `../fpga-meta-compiler`, `src/ir_json.rs`):
  hand-written JSON, deterministic, schema-versioned. Round-trips the demo modules.
  Brutal review: faithfulness to the in-memory IR (no field dropped silently). `[CPU]`
- **B3 — leanlift frontend** `src/models/fpga.rs`: a dep-free JSON reader (sibling to
  `xml.rs`) → an `AriaIr` struct; `lift fpga <design.aria.json>` dispatch entry in
  `src/models/mod.rs`. No analysis yet — just faithful ingest + `--emit-ir` echo to
  prove the round-trip. `[CPU]`

## Phase T — slice ① pipeline timing + throughput (reuse `rt.rs` + `qnet.rs`)

- **T1 — latency projection → tasks.** Project `PipelineInfo` (num_stages, latency,
  II, per-stage comb_delay) + `@clock_freq` → a `TaskSet`/latency obligation; reuse
  `rt.rs` RTA to certify **"valid output within N cycles"** (a hard bound). Mechanical.
  Cross-check N against Aria's emulator latency and Leiserson–Saxe min-period. `[CPU]`
- **T2 — throughput projection → qnet.** Project the streaming pipeline → a Jackson
  network (stage = M/M/1 station; service rate from stage delay/II; backpressure =
  routing); reuse `qnet.rs` for **throughput, the bottleneck stage, stability** (is
  II feasible at the target clock?). Cross-check bottleneck vs the critical-path stage. `[CPU]`
- **T3 — the hard-vs-soft pair.** One pipeline, both boundaries on a clock/load axis:
  RTA latency bound (hard) vs queueing delay under stalls (soft). `scripts/fpga-pipeline-sweep.sh`
  (with `--check` self-test). The phase boundary in hardware. `[CPU]`; heavy Verilator
  confirmation of II `[GPU]`.

## Phase F — slice ② control-FSM safety (reuse `check.rs` + `lean.rs`)

- **F1 — FSM extraction.** From the Aria IR: an enum-typed `Register` + its `next`
  `Mux`/`CaseMux` tree → an `Lts` (states = enum variants; events = input guard
  literals; transitions from the Mux conditions). Mechanical, total, deterministic. `[CPU]`
- **F2 — check + prove.** `lift fpga check` → reachability, **dead (unreachable)
  states**, **deadlock**, and safety from `IrFormalProperty` (`assert`/`never` →
  leanlift `forbid`). `lift fpga prove` → **sorry-free Lean** via `emit_fsm` — strictly
  stronger than Aria's emitted obligations (we *certify*, not just *state*). Cross-check
  reachable set vs the emulator; teeth (mutate a transition ⇒ checker ∧ proof both red). `[CPU]`

## Phase D — slice ③ FIFO / dataflow flow-safety (reuse `PtNet` + `Petri.lean`)

- **D1 — flow projection → Petri.** `Fifo`/`PipelineReg`/ready-valid handshake →
  `PtNet` (FIFO occupancy = place; enqueue/dequeue = transitions; `depth` = `[[bound]]`).
  Channel loss = a loss transition (empty post). CDC FIFO = dual-clock place pair.
  Mechanical. `[CPU]`
- **D2 — prove + check.** `prove` the **bound invariant** (FIFO never overflows
  `≤ depth`) via the existing upper-bound inductive strengthening — and it **survives
  loss** (reuse `Petri.lean` loss lemma). `check` surfaces handshake **deadlock**.
  Teeth: shrink `depth` ⇒ proof goes red. `[CPU]`

## Phase E — equivalence to a reference model (NEW capability, mechanical)

- **E1 — product equivalence (M1).** `lift fpga equiv <design.aria.json> <ref.petri>`:
  build the **synchronous product** of the extracted protocol `Lts` and the reference
  `PtNet`'s induced `Lts` over a shared **observable alphabet**; BFS the product
  (reuse `check.rs`) and assert **observational/trace equivalence** — every reachable
  `(s,t)` pair agrees on observable outputs and on which observable events are
  enabled/refused. Report the first disagreeing pair as a counterexample. Bounded,
  mechanical. `[CPU]`
- **E2 — bisimulation certificate (M3).** Emit a Lean **bisimulation relation** `R`
  and `theorem equiv` proved by the existing `invariant_of_preserved`-style induction
  (`R` is an invariant of the product `Reachable`), **sorry-free**. Generation is
  mechanical; the kernel checks it. `[CPU]`

## Phase S — capstone: serial protocol across two FPGA chips

The marquee demo. A basic framed serial link — **TX chip** + **RX chip** Aria
modules + a **lossy channel** — proved correct on every axis at once.

- **S1 — author the demo.** `../fpga-meta-compiler/examples/serial_link.ahdl`
  (TX FSM, RX FSM, channel with loss); the reference `examples/fpga/serial-link.petri`
  (the intended protocol as a Petri net); `examples/fpga/serial-link.recipe.md`. `[CPU]`
- **S2 — the full ladder on it:**
  1. **Export Lean4** (Aria `--emit-lean4`) **and** `lift fpga prove` the FSM safety
     (no illegal frame state) — sorry-free. `[CPU]`
  2. **Prove equivalence** of the two-chip protocol to the reference Petri net (Phase E).
     `[CPU]`
  3. **Timing assumptions** — RTA: a frame is delivered within `N` cycles at clock `f`
     (Phase T). `[CPU]`
  4. **Channel error/loss assumptions** — GSPN→CTMC: `P(frame delivered)` vs loss rate
     `p`, and the **phase transition** "works up to a loss threshold `p*`, then not"
     (reuse `gspn.rs`, the `link`/`dock-gspn` engine). `[CPU]`; PRISM/Storm cross-check
     of `p*` `[GPU]`.
  5. **The combined certificate:** equivalence ∧ (latency ≤ N at f) ∧ (loss `p < p*`)
     ⇒ the protocol is correct. One recipe, one story.
- **S3 — sweeps + tutorial.** `scripts/serial-link-sweep.sh` (loss-rate sweep → the
  delivery cliff; clock-freq sweep → the latency boundary), and a `docs/TUTORIAL.md`
  FPGA section. Verilator co-sim of the link `[GPU]`; Metal emulation path `[M24]`. `[CPU]`

## Phase X — finalize (hardening, mirrors prior plans)

- **X1 — docs.** `docs/FORMATS-fpga.md` (the bridge schema + `lift fpga` verbs),
  README + `docs/FORMATS-models.md` pointers, `SPEC` note. `[CPU]`
- **X2 — manual-test subagent.** Append an FPGA section to `docs/TESTING.md` (every
  `lift fpga` verb on the demo, expected verdicts/exit codes, with `[CPU]`/`[M24]`/`[GPU]`
  tags); run the `[CPU]` subset end-to-end in a subagent; capture transcript; fix
  deviations. List the `[M24]`/`[GPU]` steps for those machines. `[CPU]` (+ tagged)
- **X3 — final brutal-review subagent** over the whole FPGA diff: IR-projection
  faithfulness, equivalence soundness (no false ACCEPT), overflow/off-by-one in the
  latency/throughput math, JSON-parser robustness. Triage + fix. `[CPU]`
- **X4 — mini tutorial** entry tying the capstone together. `[CPU]`

---

## No-LLM ledger (every FPGA-path transform is mechanical)

| Step | Transform | Deterministic? | Checked by |
|---|---|---|---|
| B2 | IrModule → IR-JSON | yes (hand-written serializer) | round-trip echo |
| B3 | IR-JSON → AriaIr | yes (parser) | round-trip echo |
| T1 | PipelineInfo → latency/closure + C-slow fold→TaskSet | yes | dual-source cross-check (stage-delay↔critical-path, freq↔period) + RTA over-fold |
| T2 | pipeline → Jackson net (qnet) | yes | bottleneck value-cross-check vs critical-path stage; saturation teeth |
| F1 | Register+priority-Mux → Lts (width-aware interp) | yes | exhaustive 2^k valuation; uint-wrap teeth; reach set |
| F2 | Lts → Lean | yes (`emit_fsm`) | Lean kernel (sorry-free) |
| D1 | Fifo → PtNet (occ/free + pure-loss leak) | yes | over-approx (sound for overflow); BFS vs closed-form markings |
| D2 | PtNet → Lean `occ ≤ depth` | yes (`emit_petri`) | Lean kernel (omega); tight-bound teeth |
| E1 | (Lts × PtNet) product | yes (BFS) | counterexample search |
| E2 | bisim relation → Lean | yes | Lean kernel (sorry-free) |
| S2.4 | channel → GSPN→CTMC | yes (`gspn.rs`) | closed form + PRISM `[GPU]` |

**Zero LLM-tagged steps on the verification path.** Aria's `--emit-lean4` and
leanlift's `emit_fsm`/`emit_petri` are all syntax-directed. (LLM codegen for C++/Go
in leanlift is unrelated and untouched.)

## Ordered execution (CI + brutal review at each ★)

`B1 → B2★ → B3★ → T1★ → T2★ → T3 → F1★ → F2★ → D1★ → D2★ → E1★ → E2★ → S1 → S2★ → S3 → X1 → X2 → X3★ → X4`

Each ★ ends CI-green and brutal-reviewed; `verify.sh` (Kani + Aeneas) green where a
proved kernel is touched.

---

## Tasks / TODO (tracked)

### Bridge
- [x] B1 — `docs/FORMATS-fpga.md` bridge schema (versioned, `aria-ir-json/v1`). `[CPU]`
- [x] B2 — `../fpga-meta-compiler` `--emit-ir-json` (`src/ir_json.rs`); 118 tests, all
      12 examples round-trip to valid JSON; annotations + formal props exported. `[CPU]` ★
- [x] B3 — leanlift `src/models/fpga.rs` JSON reader + `lift fpga info` + echo;
      ci.sh FPGA section GREEN; fixture `examples/fpga/tcp_ip.aria.json`. `[CPU]` ★

### Slice ① timing + throughput
- [x] T1 — `lift fpga timing`: hard latency (`latency × clk_period`) + timing
      closure (critical-path ≤ clock period), each cross-checked against an
      INDEPENDENT source (max stage-delay vs Aria critical-path; @clock_freq vs
      target_period_ns), fail-closed on disagreement; C-slow fold feasibility via
      `rt.rs` RTA (`c_slow_factor` streams ≤ II slots — over-fold caught). 16 unit
      tests; ci.sh GREEN with closure + over-fold teeth; brutal-reviewed
      (tautological-fold/false-accept findings fixed). `[CPU]` ★
- [x] T2 — `lift fpga throughput`: project the pipeline → an open tandem Jackson
      network (one M/M/1 station per stage, μ = 1/comb_delay, λ⁰ = clock/II),
      REUSE `qnet.rs` for max sustainable rate, bottleneck stage, stability
      (ρ<1 = per-stage closure), per-stage occupancy (soft companion). Bottleneck
      value-cross-checked vs the critical-path stage; balanced fallback when Aria
      gives no per-stage delays. 21 fpga unit tests; ci.sh GREEN with bottleneck +
      saturation teeth; brutal-reviewed (tie-break false-reject + tautology fixed). `[CPU]` ★
- [x] T3 — `scripts/fpga-pipeline-sweep.sh`: sweep clock frequency, tabulate
      timing closure (hard, `lift fpga timing`) vs queue stability (soft, `lift fpga
      throughput`); both knees land on f* = 1/critical-path, the ≤-vs-< gap at f*
      being the hard/soft boundary. `--check` self-test wired into ci.sh GREEN.
      `[CPU]`; heavy Verilator II confirmation `[GPU]` (off-CI).

### Slice ② control-FSM safety
- [x] F1 — `src/models/fpga_fsm.rs`: extract a control FSM (single state Register +
      priority-Mux `next`) → an `Lts` via a width-aware IR interpreter + reachability
      fixpoint + behavioural event-dedup (2^k valuations → distinct successor
      vectors); safety forbid from the IR's own `assert always P` state-only formal
      properties. `lift fpga check` reuses `check.rs` (M1, pure Rust). 29 fpga unit
      tests; ci.sh GREEN with SAFE + illegal-state teeth; brutal-reviewed (CRITICAL
      uint-wrap false-SAFE + exit-code + property-abort fixed). `[CPU]` ★
- [x] F2 — `lift fpga prove`: emit a sorry-free Lean safety proof per FSM via the
      existing `lean::emit_fsm` and elaborate it (shared `elaborate_lean` helper);
      the kernel re-derives what M1 checked. tcp_fsm proved sorry-free (axioms:
      propext only). Vacuous proofs (no usable property) disclosed honestly, not
      passed off as certificates. ci.sh (lean-gated) GREEN with sorry-free + unsafe
      red teeth; brutal-reviewed (vacuous-disclosure gap fixed). `[CPU]` ★

### Slice ③ FIFO flow-safety
- [x] D1 — `src/models/fpga_fifo.rs`: each Aria `Fifo` node → a bounded `PtNet`
      (places occ/free, occ+free=depth; enqueue/dequeue + a pure-loss `leak`),
      over-approximating (enables unconstrained ⇒ sound for the overflow bound).
      `lift fpga check` runs M1, sizing the BFS bound per FIFO (deep FIFOs deferred
      to symbolic prove); reports the leaked-jam deadlock honestly. `[CPU]` ★
- [x] D2 — `lift fpga prove` proves `occ ≤ depth` via the existing `emit_petri`
      (conserved-mass upper bound, monotone under the pure-loss leak) — sorry-free
      (axioms propext, Quot.sound). Teeth: a too-tight bound is caught (check
      violation). 8 fifo unit tests; ci.sh GREEN (check SAFE + lean-gated prove);
      brutal-reviewed (no false SAFE; bound/BFS-size + underflow-scope fixed). `[CPU]` ★

### Equivalence
- [ ] E1 — `lift fpga equiv` product trace-equivalence (M1) + counterexample. `[CPU]` ★
- [ ] E2 — Lean bisimulation certificate (M3), sorry-free. `[CPU]` ★

### Capstone
- [ ] S1 — author `serial_link.ahdl` (TX/RX/lossy channel) + `serial-link.petri` + recipe. `[CPU]`
- [ ] S2 — full ladder: Lean4+prove safety, equiv, RTA timing, GSPN loss phase-change, combined cert. `[CPU]`(+`[GPU]` PRISM) ★
- [ ] S3 — `scripts/serial-link-sweep.sh` + TUTORIAL section. `[CPU]`(+`[M24]`/`[GPU]`)

### Finalize
- [ ] X1 — docs (FORMATS-fpga, README, FORMATS-models, SPEC). `[CPU]`
- [ ] X2 — manual-test subagent over the `[CPU]` FPGA section; list `[M24]`/`[GPU]` steps. `[CPU]`
- [ ] X3 — final brutal-review subagent over the FPGA diff. `[CPU]` ★
- [ ] X4 — mini tutorial entry. `[CPU]`

### Cross-machine validation runs (tagged, off-CI)
- [ ] `[M24]` 24 GB Mac: Aria Metal emit+run; leanlift Kani (arm64); cached opt proofs.
- [ ] `[GPU]` RTX 6000 Pro: Aria CUDA/OpenCL emulation; Verilator co-sim of the link;
      PRISM/Storm cross-check of `p*`; `yosys` synthesis sanity.

> Reuse first: B/T/F/D/E add a thin `fpga.rs` projection layer; **all backends
> (`check`/`prove`/`prism`/`simulate`, the RTA/qnet/Petri/CTMC engines, the Lean
> theory) are reused unchanged.** The only genuinely new logic is the equivalence
> product (Phase E) and the IR-JSON bridge (Phase B).
