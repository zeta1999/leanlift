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
