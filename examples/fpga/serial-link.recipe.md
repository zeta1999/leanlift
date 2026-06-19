# Serial-link capstone — recipe

The marquee FPGA demo: a UART-like **serial protocol across two FPGA chips**,
proved correct on **every axis at once**, entirely mechanically (no LLM anywhere
on the path). One story, one combined certificate.

## The design (Aria-HDL)

`../fpga-meta-compiler-public/examples/serial_link.ahdl` — two control FSMs at 100 MHz:

- **`serial_tx`** — frames a byte: `idle → start → data → stop → idle` (`state : uint<2>`).
- **`serial_rx`** — mirrors the frame on the receive side.

Both carry the formal property `assert always state <= 3` (no illegal frame
state). The lossy channel between the chips is modelled separately as a GSPN,
`serial-channel.model.toml` (stop-and-wait with per-attempt frame loss `p`).

## The ladder (run by `scripts/serial-link-certify.sh`)

| # | Axis | Command | Engine | Result |
|---|------|---------|--------|--------|
| ① | **FSM safety** | `lift fpga prove serial_link.aria.json` | `check` + `emit_fsm` | TX, RX `state ≤ 3` — **sorry-free Lean** |
| ② | **Equivalence** | `lift fpga equiv serial_tx serial_tx_golden --prove` | product + `emit_fsm` | TX ≡ golden — **bisimulation, sorry-free** |
| ③ | **Hard timing** | (frame-state count × clock) | reads axis ① | frame in **4 cycles = 40 ns** *(tick every cycle)* |
| ④ | **Channel loss** | `lift model prism serial-channel.model.toml` | `gspn` → CTMC | delivery `X(p)`, roll-off toward `p*` |
| + | **Buffer bound** | `lift model prove serial-channel.model.toml` | `emit_petri` | frames ≤ K — **sorry-free, survives loss** |

**On axis ②:** `serial_tx_golden` is a *distinct source file* (the frame guards are
reordered — mutually exclusive on state, so behaviour is unchanged), so EQUIVALENT
is a non-trivial result, not a file compared to a copy of itself. The certify
script also checks **discrimination**: a buggy TX (`serial_tx_bug`, stop→data) is
correctly rejected as NOT EQUIVALENT with a counterexample.

**On axis ③:** the latency is `frame-states × clock-period`; "40 ns" assumes `tick`
asserted every cycle. With a baud strobe, a frame takes `1 + (states-1)/tick-rate`
cycles — larger but still a hard bound. The frame-state count is *read from the
verified FSM* (axis ①), not hard-coded.

The **channel story**: each delivery needs `Geometric(1-p)` attempts, so the mean
service time is `S(p) = 1/μd + p/((1-p)·μr)` and an *unbounded* buffer would be
stable iff `λ·S(p) < 1`, i.e. up to

```
p* = R/(1+R),   R = (1 - λ/μd)·μr/λ        (≈ 0.882 for λ=0.4, μd=1, μr=5)
```

`p*` is the **asymptotic (K→∞) stability threshold**. The model's buffer is finite
(K=4), so its CTMC is always ergodic and the delivered throughput `X(p)` *rolls off
smoothly* as `p → p*` — there is no literal cliff in the finite model; `p*` marks
where an unbounded buffer would saturate. `scripts/serial-link-sweep.sh` draws that
roll-off and checks the empirical knee sits near the closed-form `p*`.

## The combined certificate

```
(FSM safe) ∧ (impl ≡ golden) ∧ (frame latency ≤ 40 ns) ∧ (loss p < p*)
    ⇒ the serial protocol is CORRECT.
```

`scripts/serial-link-certify.sh --check` runs all of it and self-tests (exit 1 on
any failure); `ci.sh` runs both `--check`s. The Lean-kernel axes degrade to the
sound M1 checker when no `lean` toolchain is on `PATH`.

## Cross-machine (tagged, off-CI)

- `[M24]` 24 GB Mac: the Aria **Metal** emulation of TX/RX; the cached Lean proofs.
- `[GPU]` RTX 6000 Pro: **Verilator** co-sim of the two-chip link; **PRISM/Storm**
  cross-check of the delivery `p*`; `yosys` synthesis sanity.
