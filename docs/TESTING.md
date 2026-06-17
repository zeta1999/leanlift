# Manual testing manual — `lift model` (+ verification tiers)

A copy-pasteable, unambiguous checklist. Run each command from the repo root;
the **Expect** line says exactly what a pass looks like (exit code and/or a key
output line). Executable by a person or an agent. `$?` is the shell exit code.

> Setup: `cargo build --release` then `LIFT=./target/release/lift`.

## 0. Automated suites (run these first)

| Step | Command | Expect |
|---|---|---|
| 0.1 fast CI | `./ci.sh; echo $?` | ends `CI GREEN — model axis verified end to end`, exit `0` |
| 0.2 deep tier | `./verify.sh; echo $?` | `VERIFY GREEN`, exit `0` (Kani/Aeneas run if installed, else SKIP) |
| 0.3 unit tests | `cargo test --release 2>&1 | tail -1` | `test result: ok. … 0 failed` |

## 1. M1 — `lift model check` (each family, auto-detected)

| Step | Command | Expect |
|---|---|---|
| 1.1 FSM | `$LIFT model check examples/models/tiny.model.toml; echo $?` | `M1`/`reachable : 2 state`, exit `0` |
| 1.2 Petri (loss) | `$LIFT model check examples/models/dock.model.toml; echo $?` | safe, exit `0` |
| 1.3 BT | `$LIFT model check examples/models/mission.model.toml; echo $?` | exit `0` |
| 1.4 CPN | `$LIFT model check examples/models/resource.model.toml; echo $?` | exit `0` |
| 1.5 tasks (RT) | `$LIFT model check examples/models/tasks.model.toml; echo $?` | `FAIL — sufficient` then `SCHEDULABLE`, exit `0` |
| 1.6 tasks EDF | `$LIFT model check examples/models/tasks-edf.model.toml; echo $?` | `dbf(1) = 2 > 1`, `NOT SCHEDULABLE`, exit `1` |
| 1.7 qnet | `$LIFT model check examples/models/qnet.model.toml; echo $?` | `worker … ◀ bottleneck`, `STABLE`, exit `0` |

## 2. M3 — `lift model prove` (Lean, sorry-free)

| Step | Command | Expect |
|---|---|---|
| 2.1 FSM product | `$LIFT model prove examples/models/mcl.model.toml` | `M3 proved`, sorry-free |
| 2.2 Petri | `$LIFT model prove examples/models/dock.model.toml` | `M3 proved` |
| 2.3 GSPN safety | `$LIFT model prove examples/models/link.model.toml` | `M3 proved` (buf ≤ 8) |

## 3. M2 + empirical — `lift model prism` / `simulate`

| Step | Command | Expect |
|---|---|---|
| 3.1 GSPN CTMC | `$LIFT model prism examples/models/link.model.toml` | `X ≈ 0.40`, `Pblock` tiny, stable |
| 3.2 param sweep | `$LIFT model prism examples/models/link.model.toml --set p=0.9` | `X` drops to ≈0.335, `L`≈4.4 |
| 3.3 GSPN sim | `$LIFT model simulate examples/models/link.model.toml --time 200000` | empirical ≈ analytic, `|Δ|` small |
| 3.4 qnet sim | `$LIFT model simulate examples/models/qnet.model.toml --time 200000` | per-station empirical ≈ analytic |

## 4. Phase-transition sweeps

| Step | Command | Expect |
|---|---|---|
| 4.1 link cliff | `./scripts/link-sweep.sh --check` | knee p≈0.88 ≈ p*=0.882, `PASS` |
| 4.2 qnet bottleneck | `./scripts/qnet-sweep.sh --check` | instability ≈ 1.4 = closed form, `PASS` |
| 4.3 RT hard/soft | `./scripts/tasks-sweep.sh --check` | hard boundary conservative, `PASS` |
| 4.4 shared workload | `./scripts/shared-workload-sweep.sh --check` | provably ⊊ probably (1.4 < 2.0), `PASS` |

## 5. L3 — Aeneas code→Lean proofs (need Aeneas built; else these are skipped)

| Step | Command | Expect |
|---|---|---|
| 5.1 Petri kernel | `$LIFT prove models-fire` | `L3 proved`, sorry-free |
| 5.2 buffer kernel | `$LIFT prove link-buffer` | `L3 proved`, sorry-free |
| 5.3 RTA kernel | `$LIFT prove rta-kernel` | `L3 proved`, `rta_term_spec` + `rta_term_mono_nat` |

## 6. Kani bounded proofs (deep tier; need `cargo-kani`)

| Step | Command | Expect |
|---|---|---|
| 6.1 | `./verify-kani.sh` | `KANI GREEN` — `fire_no_underflow`, `div_ceil_safe`, `term_monotone` |

## 7. Teeth — wrong models must go RED (the safety-critical direction)

| Step | Command | Expect |
|---|---|---|
| 7.1 overloaded RT | `printf 'kind="tasks"\npolicy="RM"\n[[task]]\nname="a"\nc="3"\nt="4"\n[[task]]\nname="b"\nc="3"\nt="5"\n' | $LIFT model check /dev/stdin; echo $?` | `NOT SCHEDULABLE`, exit `1` |
| 7.2 saturated qnet | `printf 'kind="qnet"\n[[station]]\nname="x"\nmu="3"\nlambda="5"\n' | $LIFT model check /dev/stdin; echo $?` | `UNSTABLE`, exit `1` |
| 7.3 trapped qnet | `printf 'kind="qnet"\n[[station]]\nname="a"\nmu="9"\nlambda="2"\n[[station]]\nname="b"\nmu="9"\n[[route]]\nfrom="a"\nto="b"\nprob="1.0"\n[[route]]\nfrom="b"\nto="a"\nprob="1.0"\n' | $LIFT model check /dev/stdin; echo $?` | errors "not open", exit ≠ `0` |
| 7.4 D > T refused | `printf 'kind="tasks"\npolicy="EDF"\n[[task]]\nname="x"\nc="1"\nt="3"\nd="5"\n' | $LIFT model check /dev/stdin; echo $?` | errors "D ≤ T", exit ≠ `0` |

## Pass criterion

All of §0–§4 and §7 must pass on any machine. §5–§6 pass where Aeneas / Kani are
installed and SKIP cleanly otherwise — they must never produce a *wrong* result,
only run-or-skip.

## 8. FPGA (Aria-HDL bridge) — `[CPU]` unless tagged

`$F = examples/fpga`. All `[CPU]`; `prove`/`equiv --prove` need `lean` on PATH
(skip cleanly otherwise). Heavier cross-machine runs are tagged.

| Step | Command | Expect |
|---|---|---|
| 8.1 ingest | `$LIFT fpga info $F/tcp_ip.aria.json` | `4 module(s)`, annotations + `assert always` echoed |
| 8.2 timing | `$LIFT fpga timing $F/pipeline_demo.aria.json` | `mac`: 16 ns latency @125 MHz, closes 0.8 ≤ 8 ns |
| 8.3 throughput | `$LIFT fpga throughput $F/pipeline_demo.aria.json` | `125 Mitems/s`, balanced (no per-stage delays) |
| 8.4 FSM check | `$LIFT fpga check $F/tcp_ip.aria.json` | `tcp_fsm` 7 states, `state ≤ 10` **SAFE** |
| 8.5 FSM prove | `$LIFT fpga prove $F/tcp_ip.aria.json` | `tcp_fsm` **M3 PROVED sorry-free** |
| 8.6 FIFO check | `$LIFT fpga check $F/fifo_link.aria.json` | CDC FIFO depth 4, `occ ≤ depth` **SAFE** |
| 8.7 FIFO prove | `$LIFT fpga prove $F/fifo_link.aria.json` | `occ ≤ depth 4` **sorry-free** (survives loss) |
| 8.8 equiv | `$LIFT fpga equiv $F/protocol_impl.aria.json $F/protocol_golden.aria.json` | **EQUIVALENT ✓** |
| 8.9 capstone | `./scripts/serial-link-certify.sh --check; echo $?` | `the serial protocol is CORRECT`, exit `0` |
| 8.10 sweep | `./scripts/serial-link-sweep.sh --check; echo $?` | delivery roll-off, knee ≈ `p* 0.882`, exit `0` |

### FPGA teeth — must go RED

| Step | Command | Expect |
|---|---|---|
| 8.T1 timing | a stage slower than the clock (3 ns path, 2 ns clock) | `VIOLATED`, exit `1` |
| 8.T2 throughput | offered rate > a stage rate | `SATURATED`, exit `1` |
| 8.T3 FSM | an FSM that reaches an illegal state | `VIOLATION` (check) / proof red (prove), exit `1` |
| 8.T4 FIFO | `occ ≤ depth-1` (too tight) | overflow violation (unit test `tight_bound_is_violated`) |
| 8.T5 equiv | `$LIFT fpga equiv $F/protocol_impl.aria.json $F/protocol_bug.aria.json` | **NOT EQUIVALENT** + counterexample, exit `1` |

All of §8 (and §8.T) runs in `ci.sh`.

### Cross-machine (tagged, off-CI)

- `[M24]` 24 GB Mac: Aria **Metal** emit+run of TX/RX; the Mathlib-cached proofs.
- `[GPU]` RTX 6000 Pro: Aria **CUDA/OpenCL** kernels; **Verilator** co-sim of the
  serial link; **PRISM/Storm** cross-check of the delivery `p*`; `yosys` sanity.
