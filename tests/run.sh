#!/usr/bin/env bash
# Regression check for the M0 slice: every built-in example must verify (L1,
# exit 0), and a deliberately-broken candidate must be caught (L0, exit nonzero).
# No tracked files are mutated — broken candidates are written to a temp dir and
# fed via `--lean`.
set -uo pipefail
cd "$(dirname "$0")/.."

cargo build --release --quiet || { echo "build failed"; exit 1; }
LIFT=./target/release/lift
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
fail=0

pass()  { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad()   { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fail=1; }

echo "== positive: each example verifies (L1, exit 0) =="
for ex in streamed avg; do
  if "$LIFT" verify "$ex" --out "$TMP/$ex.json" >"$TMP/$ex.out" 2>&1; then
    pass "$ex  ($(grep -o 'L1 conformant/[0-9]*' "$TMP/$ex.out"))"
  else
    bad "$ex did not verify"; cat "$TMP/$ex.out"
  fi
done
# quant: one parametric quantizer across fp8 → f64; rounding-error bound at L1
if "$LIFT" verify quant --out "$TMP/quant.json" >"$TMP/quant.out" 2>&1; then
  pass "quant (fp8→f64)  ($(grep -o 'L1 conformant/[0-9]*' "$TMP/quant.out"); $(grep -o 'postcond: [0-9]*/[0-9]* hold' "$TMP/quant.out"))"
else
  bad "quant did not verify"; cat "$TMP/quant.out"
fi

echo "== sound path: Rust → Aeneas extraction (if built) =="
AENEAS="${LEANLIFT_AENEAS:-$HOME/work/_verif-tools/aeneas}"
if [ -x "$AENEAS/bin/aeneas" ]; then
  if "$LIFT" verify rust-streamed --out "$TMP/rust.json" >"$TMP/rust.out" 2>&1; then
    pass "rust-streamed  ($(grep -o 'L1 conformant/[0-9]*' "$TMP/rust.out"))"
  else
    bad "rust-streamed did not verify"; tail -20 "$TMP/rust.out"
  fi
  for le in rust-isqrt rust-bisect; do
    if "$LIFT" verify "$le" --out "$TMP/$le.json" >"$TMP/$le.out" 2>&1; then
      pass "$le (loop)  ($(grep -o 'L1 conformant/[0-9]*' "$TMP/$le.out"); $(grep -o 'postcond: [0-9]*/[0-9]* hold' "$TMP/$le.out"))"
    else
      bad "$le did not verify"; tail -20 "$TMP/$le.out"
    fi
  done
  echo "== L3 proofs =="
  for pe in rust-streamed rust-isqrt rust-bisect; do
    if "$LIFT" prove "$pe" --out "$TMP/proof_$pe.json" >"$TMP/prove_$pe.out" 2>&1; then
      n=$(grep -c '✓' "$TMP/prove_$pe.out")
      pass "prove $pe  ($(grep -o 'L3 proved' "$TMP/prove_$pe.out"), $n obligations, sorry-free)"
    else
      bad "prove $pe did not certify L3"; tail -15 "$TMP/prove_$pe.out"
    fi
  done
else
  printf '  \033[33mSKIP\033[0m  rust-streamed + prove (aeneas not built — scripts/build_aeneas.sh)\n'
fi

echo "== LLM path: claude -p translates C++ (cached → free + deterministic) =="
SOL=""
command -v forge >/dev/null 2>&1 && SOL="sol-dot2"
if command -v claude >/dev/null 2>&1; then
  for ex in cpp-streamed cpp-dot2 go-avg cpp-isqrt cpp-bisect cpp-quant $SOL; do
    if "$LIFT" verify "$ex" --out "$TMP/$ex.json" >"$TMP/$ex.out" 2>&1; then
      pass "$ex  ($(grep -o 'L1 conformant/[0-9]*' "$TMP/$ex.out"); $(grep -o 'settled after [0-9]* iter' "$TMP/$ex.out"))"
    else
      bad "$ex did not verify"; tail -20 "$TMP/$ex.out"
    fi
  done
else
  printf '  \033[33mSKIP\033[0m  cpp-* (claude not on PATH)\n'
fi

echo "== negative: broken candidates are caught (L0, exit nonzero) =="
# streamed: multiply span by itself instead of deposit
sed 's/UInt.mul deposit span/UInt.mul span span/' examples/streamed/Streamed.lean > "$TMP/BadStreamed.lean"
# avg: add -> multiply
sed 's/UInt.add a b/UInt.mul a b/' examples/avg/Avg.lean > "$TMP/BadAvg.lean"
for pair in "streamed:$TMP/BadStreamed.lean" "avg:$TMP/BadAvg.lean"; do
  ex="${pair%%:*}"; cand="${pair#*:}"
  if "$LIFT" verify "$ex" --lean "$cand" --out "$TMP/bad_$ex.json" >"$TMP/bad_$ex.out" 2>&1; then
    bad "broken $ex candidate was NOT caught (exit 0)"
  else
    pass "broken $ex caught ($(grep -o 'mismatch: [0-9]*' "$TMP/bad_$ex.out" | head -1))"
  fi
done

echo
[ "$fail" -eq 0 ] && echo "all green" || echo "REGRESSIONS"
exit "$fail"
