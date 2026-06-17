#!/usr/bin/env bash
# serial-link-sweep.sh — S3 (PLAN-fpga Phase S): draw the DELIVERY ROLL-OFF of the
# two-chip serial link. Sweeps the per-attempt frame-loss probability `p`,
# tabulating the delivered throughput X (and P(buffer full)) of
# examples/fpga/serial-channel.model.toml, renders X as an ASCII bar, and marks
# the closed-form ASYMPTOTIC (K→∞) stability threshold p*. NB: the model's buffer
# is finite (K=4), so the CTMC is always ergodic and X(p) rolls off SMOOTHLY as p
# approaches p* — p* locates where an unbounded buffer would saturate, not a sharp
# cliff in this finite model.
#
# Stop-and-wait: each delivery needs Geometric(1-p) attempts, so the mean service
# time is S(p) = 1/μd + p/((1-p)·μr) and the link is stable iff λ·S(p) < 1 ⇒
#   p* = R/(1+R),  R = (1 - λ/μd)·μr/λ
#
# `--check` makes it self-test (exit 1 if the empirical knee and p* disagree), so
# ci.sh can run it as a regression. Params below must match the model file.
set -uo pipefail
cd "$(dirname "$0")/.."

LIFT="target/release/lift"
MODEL="examples/fpga/serial-channel.model.toml"
CHECK="${1:-}"
[ -x "$LIFT" ] || { cargo build --release --quiet || exit 1; }

LAM=0.4; MUD=1.0; MUR=5.0
PSTAR=$(awk -v lam=$LAM -v mud=$MUD -v mur=$MUR \
  'BEGIN{a=lam/mud; R=(1-a)*mur/lam; printf "%.3f", R/(1+R)}')

echo "serial-link delivery sweep — λ=$LAM μd=$MUD μr=$MUR     closed-form p* = $PSTAR"
printf "%-6s %9s %9s   %s\n" "p" "X" "Pblock" "delivered throughput X (full bar = λ)"
knee=""
for p in 0.05 0.15 0.25 0.35 0.45 0.50 0.52 0.55 0.60 0.70 0.85; do
  o=$("$LIFT" model prism "$MODEL" --set p=$p --emit /tmp/sl --out /tmp/sl.json 2>/dev/null \
        | grep -E '^[[:space:]]+(X|Pblock)')
  X=$(echo "$o"  | awk '$1=="X"{print $3}')
  PB=$(echo "$o" | awk '$1=="Pblock"{print $3}')
  bar=$(awk -v x="${X:-0}" -v lam=$LAM 'BEGIN{n=int(40*x/lam+0.5); for(i=0;i<n;i++)printf "█"}')
  printf "%-6s %9.4f %9.4f   %s\n" "$p" "${X:-0}" "${PB:-0}" "$bar"
  if [ -z "$knee" ] && awk -v x="${X:-0}" -v lam=$LAM 'BEGIN{exit !(x < 0.9*lam)}'; then knee=$p; fi
done
echo
echo "empirical knee (first p with X < 0.9·λ): p ≈ ${knee:-none}     closed-form p* = $PSTAR"

if [ "$CHECK" = "--check" ]; then
  [ -n "$knee" ] || { echo "FAIL: no delivery knee found in sweep"; exit 1; }
  # the 0.9λ knee trips near p*; accept |knee - p*| ≤ 0.12.
  if awk -v k=$knee -v ps=$PSTAR 'BEGIN{d=k-ps; if(d<0)d=-d; exit !(d<=0.12)}'; then
    echo "PASS: empirical delivery cliff ≈ closed-form p* (within 0.12)"
  else
    echo "FAIL: knee $knee vs p* $PSTAR differ by > 0.12"; exit 1
  fi
fi
