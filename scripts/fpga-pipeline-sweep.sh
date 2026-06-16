#!/usr/bin/env bash
# fpga-pipeline-sweep.sh — T3 (PLAN-fpga slice ①): the hard-vs-soft boundary of
# one streaming pipeline, swept on a CLOCK-FREQUENCY axis. For a pipeline whose
# slowest stage has combinational delay `crit` ns, the sustainable clock is
# f* = 1/crit. This sweep drives `lift fpga timing` (HARD: does the critical path
# fit one clock period?) and `lift fpga throughput` (queue stability: does the
# offered rate stay below the bottleneck stage's rate?) across f and marks where
# each verdict flips — the silicon image of the provably-safe boundary.
#
# Closed form: stages = [2,4,1] ns ⇒ crit = 4 ns ⇒ f* = 1/4ns = 250 MHz.
#   * timing closure uses `crit ≤ period`  ⇒ CLOSES through f = f* (period = crit).
#   * queue stability uses `ρ < 1` (strict) ⇒ STABLE only below f* (ρ=1 saturates).
# That ≤-vs-< gap at the exact knee IS the hard/soft distinction.
#
# `--check` makes it self-test (exit 1 if the empirical knees disagree with f*),
# so ci.sh can run it as a regression.
set -uo pipefail
cd "$(dirname "$0")/.."

LIFT="target/release/lift"
CHECK="${1:-}"
[ -x "$LIFT" ] || { cargo build --release --quiet || exit 1; }

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
STAGES='[2,4,1]'   # ns; slowest = 4 ns
CRIT_NS=4
FSTAR_MHZ=250      # 1/4ns

# Emit a faithful aria-ir-json/v1 pipeline at clock frequency $1 (Hz). The
# target_period_ns is kept consistent with @clock_freq (else the certificate's
# period cross-check would fail-closed — see T1).
emit() {
  local hz="$1"
  local period; period=$(awk -v h="$hz" 'BEGIN{printf "%.6f", 1e9/h}')
  cat <<JSON
{"schema":"aria-ir-json/v1","id":0,"name":"sweep","ports":[],"clock_domains":[],
 "annotations":[{"kind":"clock_freq","value":"$hz"}],"nodes":[],
 "pipeline":{"id":0,"num_stages":3,"latency":3,"initiation_interval":1,"flow_control":{"fc":"ready_valid"},
  "stages":[{"index":0,"name":null,"comb_delay_ns":2.0,"lut_count":null,"reg_count":0,"forwarded_values":[]},
            {"index":1,"name":null,"comb_delay_ns":4.0,"lut_count":null,"reg_count":0,"forwarded_values":[]},
            {"index":2,"name":null,"comb_delay_ns":1.0,"lut_count":null,"reg_count":0,"forwarded_values":[]}]},
 "systolic":null,
 "timing":{"c_slow_factor":1,"target_period_ns":$period,"critical_path_ns":4.0,"retiming_weights":[],"buffers":[]}}
JSON
}

echo "fpga pipeline sweep — stages=$STAGES ns  crit=$CRIT_NS ns   closed-form f* = $FSTAR_MHZ MHz"
printf "%-8s %9s   %-9s  %-10s\n" "f(MHz)" "period(ns)" "closure" "stability"
last_closes=""; first_saturates=""
for fmhz in 100 150 200 225 240 250 260 275 300 400; do
  hz=$((fmhz * 1000000))
  emit "$hz" >"$TMP/p.json"
  period=$(awk -v h="$hz" 'BEGIN{printf "%.3f", 1e9/h}')

  if "$LIFT" fpga timing "$TMP/p.json" >"$TMP/t.out" 2>&1; then tc="CLOSES"; else tc="VIOLATED"; fi
  # throughput exits 1 on saturation; read the verdict text too.
  "$LIFT" fpga throughput "$TMP/p.json" >"$TMP/q.out" 2>&1
  if grep -q "STABLE" "$TMP/q.out"; then st="STABLE"; else st="SATURATED"; fi

  printf "%-8s %9s   %-9s  %-10s\n" "$fmhz" "$period" "$tc" "$st"
  [ "$tc" = "CLOSES" ] && last_closes=$fmhz
  [ "$st" = "SATURATED" ] && [ -z "$first_saturates" ] && first_saturates=$fmhz
done
echo
echo "hard knee  (last freq that CLOSES timing)   : ${last_closes:-none} MHz   (f* = $FSTAR_MHZ)"
echo "soft knee  (first freq that SATURATES queue): ${first_saturates:-none} MHz   (f* = $FSTAR_MHZ)"
echo "the ≤-vs-< gap at f* IS the hard/soft boundary."

if [ "$CHECK" = "--check" ]; then
  ok=1
  # timing closes through f* (period == crit closes), so last CLOSES == 250.
  [ "$last_closes" = "$FSTAR_MHZ" ] || { echo "FAIL: hard knee $last_closes ≠ f* $FSTAR_MHZ"; ok=0; }
  # queue saturates AT f* (ρ=1), so first SATURATES == 250.
  [ "$first_saturates" = "$FSTAR_MHZ" ] || { echo "FAIL: soft knee $first_saturates ≠ f* $FSTAR_MHZ"; ok=0; }
  [ "$ok" = 1 ] && echo "PASS: both knees sit at the closed-form f* = $FSTAR_MHZ MHz" || exit 1
fi
