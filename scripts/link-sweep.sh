#!/usr/bin/env bash
# link-sweep.sh — D3 (PLAN-perf-demo): draw the PHASE TRANSITION of
# examples/models/link.model.toml. Sweeps the per-attempt loss `p`, tabulates the
# steady-state queue length L, throughput X and blocking P(buf=K), renders X as
# an ASCII bar, marks the CLOSED-FORM stability threshold p*, and finds the
# EMPIRICAL knee — the triangulation the demo is about (closed form ↔ exact CTMC).
#
# Closed form: each delivery needs Geometric(1-p) attempts; mean service
#   S(p) = 1/μd + p/((1-p)·μr),  ρ = λ·S(p),  stable iff ρ < 1
#   ⇒  p* = R/(1+R),  R = (1 - λ/μd)·μr/λ.
#
# `--check` makes it self-test (exit 1 if the empirical knee and p* disagree),
# so ci.sh can run it as a regression. Params below must match the model file.
set -uo pipefail
cd "$(dirname "$0")/.."
LIFT="target/release/lift"
MODEL="examples/models/link.model.toml"
CHECK="${1:-}"
[ -x "$LIFT" ] || { cargo build --release --quiet || exit 1; }

LAM=0.4; MUD=1.0; MUR=5.0
PSTAR=$(awk -v lam=$LAM -v mud=$MUD -v mur=$MUR \
  'BEGIN{a=lam/mud; R=(1-a)*mur/lam; printf "%.3f", R/(1+R)}')

echo "link phase sweep — λ=$LAM  μd=$MUD  μr=$MUR     closed-form p* = $PSTAR"
printf "%-6s %9s %9s %9s   %s\n" "p" "L" "X" "Pblock" "throughput X (full bar = λ)"
knee=""
for p in 0.10 0.30 0.50 0.70 0.80 0.85 0.88 0.90 0.92 0.95 0.98; do
  o=$("$LIFT" model prism "$MODEL" --set p=$p --emit /tmp/lk --out /tmp/lk.json 2>/dev/null \
        | grep -E '^[[:space:]]+(L|X|Pblock)')
  L=$(echo "$o"  | awk '$1=="L"{print $3}')
  X=$(echo "$o"  | awk '$1=="X"{print $3}')
  PB=$(echo "$o" | awk '$1=="Pblock"{print $3}')
  bar=$(awk -v x=$X -v lam=$LAM 'BEGIN{n=int(40*x/lam+0.5); for(i=0;i<n;i++)printf "█"}')
  printf "%-6s %9.4f %9.4f %9.4f   %s\n" "$p" "$L" "$X" "$PB" "$bar"
  if [ -z "$knee" ] && awk -v x=$X -v lam=$LAM 'BEGIN{exit !(x < 0.95*lam)}'; then knee=$p; fi
done
echo
echo "empirical knee (first p with X < 0.95·λ): p ≈ ${knee:-none}     closed-form p* = $PSTAR"

if [ "$CHECK" = "--check" ]; then
  [ -n "$knee" ] || { echo "FAIL: no knee found in sweep"; exit 1; }
  # the 0.95λ knee trips just below p*; accept |knee - p*| ≤ 0.06.
  if awk -v k=$knee -v ps=$PSTAR 'BEGIN{d=k-ps; if(d<0)d=-d; exit !(d<=0.06)}'; then
    echo "PASS: empirical knee ≈ closed-form p* (within 0.06)"
  else
    echo "FAIL: knee $knee vs p* $PSTAR differ by > 0.06"; exit 1
  fi
fi
