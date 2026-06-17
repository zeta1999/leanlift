# Tutorial — modeling performance- and correctness-critical systems with `lift model`

A 10-minute, hands-on walkthrough. You author **one model** in an easy text
format and get back proofs (does it *ever* go wrong?), performance (how *fast* /
how *likely*?), and an empirical cross-check — and you see the **safe operating
region** with its sharp boundary.

```sh
cargo build --release
LIFT=./target/release/lift          # or add target/release to PATH
```

Every command: `lift model <verb> <file.model.toml>`. The family is auto-detected;
exit code is `0` iff the claimed property holds. No flags needed to start.

---

## 1. Correctness — prove a safety property (qualitative)

A model is just a text file. Check reachability + safety, then *prove* it in Lean:

```sh
$LIFT model check examples/models/dock.model.toml    # M1: BFS, "csA+csB ≤ 1" holds, even under loss
$LIFT model prove examples/models/dock.model.toml    # M3: the same, as a sorry-free Lean theorem
```

A *wrong* model goes red in **both** the checker and the proof — that's the trust
model. Try it: change `free:1` to `free:2` in a copy and re-`check` — it reports
`csA+csB = 2 > 1`.

## 2. Performance — how fast, how likely (quantitative)

`examples/models/link.model.toml` is a 1→1 network link with arrivals, a buffer,
and lossy retransmission. Solve its CTMC, then dial the loss rate `p`:

```sh
$LIFT model prism examples/models/link.model.toml             # throughput X, queue L, P(block)
$LIFT model prism examples/models/link.model.toml --set p=0.9 # crank loss → X collapses, L climbs
$LIFT model simulate examples/models/link.model.toml          # SSA simulation ≈ the analytic CTMC
```

**See the phase transition** — where it works until a threshold, then falls off a
cliff:

```sh
./scripts/link-sweep.sh
#  p rises → throughput holds at λ, then collapses near the closed-form p* = 0.882
```

## 3. Bottlenecks — a queueing network

`examples/models/qnet.model.toml` is a 3-station open network with a feedback
loop. One command finds the **bottleneck** and the **load margin**:

```sh
$LIFT model check examples/models/qnet.model.toml   # per-station ρ/L/W; "worker ◀ bottleneck"; STABLE
./scripts/qnet-sweep.sh                             # the bottleneck's queue diverges at scale* = 1/maxρ
```

## 4. Real-time — does it *ever* miss a deadline (worst case)

`examples/models/tasks.model.toml` is a periodic task set. `check` gives the exact
**response-time analysis** (RM/DM) or **demand-bound test** (EDF):

```sh
$LIFT model check examples/models/tasks.model.toml      # RTA: SCHEDULABLE (exact, tighter than the U-bound)
$LIFT model check examples/models/tasks-edf.model.toml  # EDF: U≤1 passes, but demand test catches dbf(1)>1
```

## 5. The whole point — provably safe vs probably safe

The same workload, both ways, on one load axis:

```sh
./scripts/shared-workload-sweep.sh
#  HARD (RT/RTA): certifiably meets deadlines up to ℓ ≈ 1.4
#  SOFT (queue):  still stable on average up to ℓ ≈ 2.0
#  ⇒ provably-safe ⊊ probably-safe; the gap [1.4,1.9] is your margin
```

Certify to the hard line for hard-real-time guarantees; ride into the soft region
(with a known, growing delay) where best-effort is acceptable.

## 6. Authoring your own

Copy an example and edit it — the format is small (see
[`docs/FORMATS-models.md`](FORMATS-models.md)). Minimal templates:

```toml
# a task set
kind = "tasks"
policy = "RM"          # RM | DM | EDF
[[task]]
name = "ctrl"
c = "10"               # worst-case execution
t = "40"               # period
d = "20"               # deadline (≤ period; defaults to period)
```

```toml
# a queueing network
kind = "qnet"
[[station]]
name = "server"
mu = "1.0"             # service rate
lambda = "0.5"         # external arrivals
```

Refining flags: `--set name=value` (override a GSPN param), `--scale S` (load
knob), `--time T --seed S` (simulation). Exit code `0` = safe/schedulable/stable.

## 7. Trust it

The analysis isn't hand-waved. Each performance number is cross-checked against a
closed form, a sweep, **and** a simulation; the analysis *kernels themselves* are
proved — the Petri firing rule and the RTA recurrence are certified sorry-free by
Aeneas (`$LIFT prove rta-kernel`) and bounded-model-checked by Kani
(`./verify-kani.sh`). Run the full battery any time:

```sh
./ci.sh        # fast: build, tests, every family, the sweeps, the teeth
./verify.sh    # deep: + Kani bounded proofs + the Aeneas dogfood (when installed)
```

The complete, copy-pasteable check list with expected outputs is
[`docs/TESTING.md`](TESTING.md).

## 8. Verify an FPGA design (Aria-HDL)

leanlift also verifies FPGA designs authored in **Aria-HDL** by ingesting its
hardware IR (`aria-hdl --emit-ir-json`) and projecting it onto the same families —
no new proof machinery. The whole ladder on the two-chip serial link:

```sh
./scripts/serial-link-certify.sh        # one combined certificate
```

```
① FSM safety   — TX,RX frame state ≤ 3, sorry-free Lean
② Equivalence  — TX ≡ golden (bisimulation) + a buggy TX correctly rejected
③ Hard timing  — frame latency read from the verified FSM
④ Channel loss — delivery X(p), asymptotic stability threshold p* ≈ 0.882
⇒ safe ∧ equivalent ∧ (latency ≤ 40 ns) ∧ (loss p < p*) ⇒ CORRECT.
```

Each axis reuses an existing engine: control FSMs ride `check`/`emit_fsm`, FIFOs
ride `PtNet`/`emit_petri`, pipeline timing rides `rt.rs`, throughput rides
`qnet.rs`, and protocol equivalence is a synchronous product checked by the same
BFS and proved by the same `emit_fsm`. The story and schema are in
[`docs/FORMATS-fpga.md`](FORMATS-fpga.md) and
[`examples/fpga/serial-link.recipe.md`](../examples/fpga/serial-link.recipe.md).
