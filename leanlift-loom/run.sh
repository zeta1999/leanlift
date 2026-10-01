#!/usr/bin/env bash
# [LOOM] bounded weak-memory model checking — off-CI (ci.sh does not run this).
#
# For each core: the clean model must pass, and the same model with that core's
# single ordering mutation enabled must FAIL. A mutant that passes means the
# check has no teeth for that core, and this script exits non-zero.
#
# Usage:  ./run.sh            # preemption bound 3 (LOOM_MAX_PREEMPTIONS)
#         BOUND=4 ./run.sh    # a different bound
#         BOUND= ./run.sh     # no bound (exhaustive within loom's model; slow for spmc)
set -uo pipefail
cd "$(dirname "$0")"

BOUND="${BOUND-3}"
if [[ -n "$BOUND" ]]; then export LOOM_MAX_PREEMPTIONS="$BOUND"; else unset LOOM_MAX_PREEMPTIONS; fi

cores=(spsc:spsc seqlock:seqlock mpsc:mpsc spmc:spmc treiber:treiber chaselev:chase_lev)
fail=0
log="$(mktemp)"
trap 'rm -f "$log"' EXIT

cargo test --release --quiet --no-run >"$log" 2>&1 || { cat "$log"; exit 1; }

for pair in "${cores[@]}"; do
  feat="${pair%%:*}"; test="${pair##*:}"

  cargo test --release --quiet --test loom "$test" -- --exact --test-threads=1 --nocapture >"$log" 2>&1
  rc=$?
  if [[ $rc -eq 0 ]]; then
    grep -o '\[LOOM\].*' "$log"
  else
    echo "[LOOM] $test: CLEAN MODEL FAILED (rc=$rc)"; tail -20 "$log"; fail=1
  fi

  cargo test --release --quiet --features "mutant-$feat" --test loom "$test" -- --exact --test-threads=1 --nocapture >"$log" 2>&1
  rc=$?
  if [[ $rc -ne 0 ]]; then
    why=$(grep -m1 -E 'Causality violation|assertion .* failed' "$log" || echo "failed (rc=$rc)")
    echo "[LOOM] $test: mutant-$feat caught — $why"
  else
    echo "[LOOM] $test: mutant-$feat NOT caught — the check has no teeth for this core"; fail=1
  fi
done

echo "[LOOM] bound: ${BOUND:-none}; result: $([[ $fail -eq 0 ]] && echo 'all clean, all mutants caught' || echo FAIL)"
exit $fail
