#!/usr/bin/env bash
# qnet-sweep.sh — Q5 (PLAN-qnet-rta): the bottleneck PHASE TRANSITION of an open
# queueing network. Scales the external load and shows the bottleneck station's
# utilization ρ and queue L climbing until the network goes UNSTABLE — the
# multi-station analogue of the link's single-server cliff. Since ρ is linear in
# the external rate, the closed-form boundary is scale* = 1 / max ρ(1).
#
# `--check` self-tests that the empirical instability scale ≈ the closed form.
set -uo pipefail
cd "$(dirname "$0")/.."
LIFT="target/release/lift"
MODEL="examples/models/qnet.model.toml"
CHECK="${1:-}"
[ -x "$LIFT" ] || { cargo build --release --quiet || exit 1; }

# closed-form boundary: scale* = 1 / (max ρ at scale 1).
rho1=$("$LIFT" model check "$MODEL" 2>/dev/null | awk '/◀ bottleneck/{print $3}')
sstar=$(awk -v r="$rho1" 'BEGIN{printf "%.3f", 1.0/r}')
echo "qnet bottleneck sweep — bottleneck ρ(1)=$rho1   closed-form instability scale* = $sstar"
printf "%-7s  %-10s  %-10s  %s\n" "scale" "verdict" "bottleneck" "L(bottleneck)"
knee=""
for s in 0.5 0.8 1.0 1.2 1.3 1.4 1.5 1.8; do
  out=$("$LIFT" model check "$MODEL" --scale "$s" 2>/dev/null || true)
  verdict=$(echo "$out" | awk '/level :/{print $3}')
  lb=$(echo "$out" | awk '/◀ bottleneck/{print $4}')
  printf "%-7s  %-10s  %-10s  %s\n" "$s" "$verdict" "$(echo "$out" | awk '/◀ bottleneck/{print $1}')" "${lb:-—}"
  if [ -z "$knee" ] && [ "$verdict" = "UNSTABLE" ]; then knee=$s; fi
done
echo
echo "empirical instability (first UNSTABLE): scale ≈ ${knee:-none}   closed-form scale* = $sstar"

if [ "$CHECK" = "--check" ]; then
  [ -n "$knee" ] || { echo "FAIL: never went unstable"; exit 1; }
  # the swept grid steps by ~0.1 near the boundary; accept |knee - s*| ≤ 0.15.
  if awk -v k="$knee" -v s="$sstar" 'BEGIN{d=k-s; if(d<0)d=-d; exit !(d<=0.15)}'; then
    echo "PASS: empirical instability ≈ closed-form scale* (within 0.15)"
  else
    echo "FAIL: knee $knee vs scale* $sstar differ by > 0.15"; exit 1
  fi
fi
