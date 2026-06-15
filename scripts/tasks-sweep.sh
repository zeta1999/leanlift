#!/usr/bin/env bash
# tasks-sweep.sh — R4 (PLAN-perf-demo §8): the HARD/SOFT intersection on one task
# model. Sweeps the load scale (multiplies every worst-case C) and shows, side by
# side, the DETERMINISTIC schedulability verdict (RTA on worst-case C — a hard
# step) and the STOCHASTIC deadline-miss probability (Monte-Carlo with typical
# execution ∈ [0.5C, C] — a soft sigmoid). The designer takeaway: the hard
# boundary is CONSERVATIVE — it declares "unschedulable" well before things
# actually start missing, so you get a provably-safe region and a margin.
#
# `--check` self-tests the conservatism (at the hard boundary, soft miss is still
# low), so ci.sh can run it as a regression.
set -uo pipefail
cd "$(dirname "$0")/.."
LIFT="target/release/lift"
MODEL="examples/models/tasks.model.toml"
CHECK="${1:-}"
[ -x "$LIFT" ] || { cargo build --release --quiet || exit 1; }

echo "task-set hard/soft sweep — RTA (worst-case C) vs Monte-Carlo miss (exec ∈ [0.5C,C])"
printf "%-7s  %-16s  %-9s  %s\n" "scale" "hard (RTA)" "soft miss" "P(miss) bar"
hard_boundary=""
soft_at_boundary=""
for s in 1.0 1.3 1.6 1.9 2.2 2.5 3.0 3.5 4.0; do
  h=$("$LIFT" model check "$MODEL" --scale "$s" >/dev/null 2>&1 && echo SCHED || echo UNSCHED)
  m=$("$LIFT" model simulate "$MODEL" --scale "$s" --seed 9 2>/dev/null | awk '/soft/{print $NF}')
  bar=$(awk -v x="$m" 'BEGIN{n=int(40*x+0.5); for(i=0;i<n;i++)printf "█"}')
  printf "%-7s  %-16s  %-9s  %s\n" "$s" "$h" "$m" "$bar"
  if [ -z "$hard_boundary" ] && [ "$h" = UNSCHED ]; then hard_boundary=$s; soft_at_boundary=$m; fi
done
echo
echo "hard boundary (first UNSCHED): scale ≈ ${hard_boundary:-none}   soft miss there: ${soft_at_boundary:-n/a}"

if [ "$CHECK" = "--check" ]; then
  [ -n "$hard_boundary" ] || { echo "FAIL: hard boundary never reached in sweep"; exit 1; }
  # conservatism: at the hard boundary the soft miss prob is still modest (<0.3).
  if awk -v m="$soft_at_boundary" 'BEGIN{exit !(m < 0.3)}'; then
    echo "PASS: hard boundary is conservative (soft miss ${soft_at_boundary} < 0.3 there)"
  else
    echo "FAIL: soft miss ${soft_at_boundary} ≥ 0.3 at the hard boundary"; exit 1
  fi
fi
