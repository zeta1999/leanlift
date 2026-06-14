#!/usr/bin/env bash
# verify-m1m3.sh — Phase V0.5 of PLAN-verification: M1 ↔ M3 agreement over
# RANDOM FSMs. Systematizes the hand-written "teeth": for every random model the
# native checker (M1, `lift model check`) and the Lean proof (M3, `lift model
# prove`) must reach the SAME verdict, and that verdict must match the model's
# construction-guaranteed ground truth.
#
#   safe class   — no edge into the forbidden `bad` state ⇒ unreachable ⇒ M1 safe
#                  ⇒ the Lean safety theorem is true ⇒ M3 elaborates sorry-free.
#   unsafe class — an edge `s0 → bad` from the initial state ⇒ `bad` reachable
#                  ⇒ M1 violated ⇒ the safety theorem is false ⇒ M3 fails to
#                  elaborate.
#
# Ground truth is by CONSTRUCTION (no reachability computed in the harness).
# Transitions use a unique event per edge, so the FSM is deterministic by
# construction (no `(from,on)` collisions). Needs `lake`/`lean` (M3); SKIPs if
# absent. Bounded N (Lean elaboration is seconds per model). Exit = #failures.

set -uo pipefail
cd "$(dirname "$0")"
ROOT="$(pwd)"
LIFT="$ROOT/target/release/lift"
N="${1:-5}"              # models per class
fails=0

pass(){ printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad(){  printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fails=$((fails+1)); }
skip(){ printf '  \033[33mSKIP\033[0m  %s\n' "$1"; }

printf '\033[1m== M1 ↔ M3 agreement over random FSMs (V0.5) ==\033[0m\n'

if ! command -v lake >/dev/null 2>&1; then
  skip "lake/lean not on PATH — M3 unavailable, V0.5 skipped"
  exit 0
fi
if [ ! -x "$LIFT" ]; then
  RUSTFLAGS="-D warnings" cargo build --release --quiet || { bad "cargo build"; exit 1; }
fi

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

# Emit a random FSM .model.toml. $1=file $2=class(safe|unsafe) $3=nstates
gen_fsm() {
  local f=$1 class=$2 n=$3 i t from to
  {
    echo 'initial = "s0"'
    printf 'states = ['
    for ((i=0;i<n;i++)); do printf '"s%d", ' "$i"; done
    echo '"bad"]'
    local nt=$((n + RANDOM % (n + 1)))
    for ((t=0;t<nt;t++)); do
      from=$((RANDOM % n)); to=$((RANDOM % n))   # never targets `bad`
      printf '[[transition]]\nfrom = "s%d"\non   = "e%d"\nto   = "s%d"\n' "$from" "$t" "$to"
    done
    if [ "$class" = unsafe ]; then               # reachable violation: s0 → bad
      printf '[[transition]]\nfrom = "s0"\non   = "boom"\nto   = "bad"\n'
    fi
    printf '[[forbid]]\nstate = "bad"\n'
  } > "$f"
}

# Check that M1 and M3 both agree with the expected verdict.
# $1=file $2=label $3=expect(safe|unsafe)
agree() {
  local f=$1 label=$2 expect=$3
  "$LIFT" model check "$f" --out "$TMP/c.json" >"$TMP/c.out" 2>&1; local mc=$?
  "$LIFT" model prove "$f" --out "$TMP/p.json" >"$TMP/p.out" 2>&1; local mp=$?
  # expected exit codes: safe ⇒ 0/0 ; unsafe ⇒ 1/1
  local want=0; [ "$expect" = unsafe ] && want=1
  if [ "$mc" -eq "$want" ] && [ "$mp" -eq "$want" ]; then
    pass "$label ($expect): M1=$mc M3=$mp agree"
  else
    bad "$label ($expect): M1=$mc M3=$mp (want $want/$want) — M1↔M3 disagree or wrong verdict"
    echo "      --- model ---"; sed 's/^/      /' "$f"
    echo "      --- prove ---"; tail -8 "$TMP/p.out" | sed 's/^/      /'
  fi
}

RANDOM="${SEED:-2026}"   # reproducible
for ((k=0;k<N;k++)); do
  ns=$((2 + RANDOM % 4))
  gen_fsm "$TMP/safe_$k.toml"   safe   "$ns"; agree "$TMP/safe_$k.toml"   "safe#$k"   safe
  gen_fsm "$TMP/unsafe_$k.toml" unsafe "$ns"; agree "$TMP/unsafe_$k.toml" "unsafe#$k" unsafe
done

if [ "$fails" -eq 0 ]; then
  printf '\033[32mM1↔M3 GREEN\033[0m — %d random FSMs, checker and proof agree\n' "$((2 * N))"
else
  printf '\033[31m%d M1↔M3 disagreement(s)\033[0m\n' "$fails"
fi
exit "$fails"
