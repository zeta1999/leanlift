#!/usr/bin/env bash
# shared-workload-sweep.sh — Phase C (PLAN-qnet-rta): ONE workload, TWO safe-region
# boundaries. The same shared server is analyzed both ways as the load `ℓ` rises:
#   HARD — deterministic real-time schedulability (shared-tasks, RTA worst-case)
#   SOFT — stochastic queueing stability/delay (shared-queue, M/M/1 average-case)
# The two models share a base utilization (0.5 at ℓ=1). The point: the
# PROVABLY-safe region (hard, RTA, critical-instant worst case) is a SUBSET of the
# PROBABLY-safe region (soft, the queue is still stable on average) — the gap is
# the margin between "certifiably meets every deadline" and "usually fine".
#
# `--check` asserts the hard boundary precedes the soft one (provably ⊆ probably).
set -uo pipefail
cd "$(dirname "$0")/.."
LIFT="target/release/lift"
TASKS="examples/models/shared-tasks.model.toml"
QUEUE="examples/models/shared-queue.model.toml"
CHECK="${1:-}"
[ -x "$LIFT" ] || { cargo build --release --quiet || exit 1; }

echo "shared workload — one server, two safe-region boundaries (base utilization 0.5)"
printf "%-6s  %-16s  %-14s  %s\n" "load ℓ" "HARD (RT/RTA)" "SOFT (queue)" "queue mean delay W"
hard_b=""; soft_b=""
for l in 1.0 1.2 1.3 1.4 1.6 1.8 1.9 2.0; do
  h=$("$LIFT" model check "$TASKS" --scale "$l" >/dev/null 2>&1 && echo SCHEDULABLE || echo UNSCHEDULABLE)
  qout=$("$LIFT" model check "$QUEUE" --scale "$l" 2>/dev/null || true)
  s=$(echo "$qout" | awk '/level :/{print $3}')
  w=$(echo "$qout" | awk '/^  server/{print $5}')
  printf "%-6s  %-16s  %-14s  %s\n" "$l" "$h" "$s" "${w:-—}"
  [ -z "$hard_b" ] && [ "$h" = UNSCHEDULABLE ] && hard_b=$l
  [ -z "$soft_b" ] && [ "$s" = UNSTABLE ] && soft_b=$l
done
echo
echo "provably-safe boundary (HARD, first UNSCHEDULABLE): ℓ ≈ ${hard_b:-none}"
echo "probably-safe boundary (SOFT, first UNSTABLE):      ℓ ≈ ${soft_b:-none}"

if [ "$CHECK" = "--check" ]; then
  { [ -n "$hard_b" ] && [ -n "$soft_b" ]; } || { echo "FAIL: a boundary was not reached"; exit 1; }
  if awk -v h="$hard_b" -v s="$soft_b" 'BEGIN{exit !(h < s)}'; then
    echo "PASS: provably-safe ⊊ probably-safe (hard boundary $hard_b < soft boundary $soft_b)"
  else
    echo "FAIL: hard boundary $hard_b not before soft $soft_b"; exit 1
  fi
fi
