#!/usr/bin/env bash
# verify.sh — the DEEP verification tier (PLAN-verification §V5.2).
#
# Two tiers:
#   ci.sh      FAST, every commit — build, unit/property/differential/exhaustive
#              tests, Lean theory, M1/M2/M3/L1 sweep, teeth, exhaustive loop
#              closure.
#   verify.sh  DEEP, nightly/manual — everything that is too slow or needs an
#              external tool to run per-commit:
#                * property/differential/exhaustive tests   (always; fast)
#                * Kani bounded model checking               (verify-kani.sh)
#                * the Aeneas dogfood L3 proof               (lift prove models-fire)
#                * parser fuzzing                            (cargo-fuzz — V2, TODO)
#
# Tools run ONE AT A TIME (sequential), so peak memory is the single heaviest
# checker (CBMC / charon / lean), never a pile of parallel builds. External tools
# never FAIL when missing — they SKIP. Exit code = number of failures (0 = green).

set -uo pipefail
cd "$(dirname "$0")"
ROOT="$(pwd)"
fails=0
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

pass(){ printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad(){  printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fails=$((fails+1)); }
skip(){ printf '  \033[33mSKIP\033[0m  %s\n' "$1"; }
sect(){ printf '\n\033[1m== %s ==\033[0m\n' "$1"; }
have(){ command -v "$1" >/dev/null 2>&1; }

# ---------------------------------------------------------------------------- #
sect "build (release, warnings = errors)"
if RUSTFLAGS="-D warnings" cargo build --release --quiet 2>"$TMP/build.err"; then
  pass "cargo build --release"
else
  bad "cargo build"; cat "$TMP/build.err"; echo; echo "build failed — aborting"; exit 1
fi
LIFT="$ROOT/target/release/lift"

# ---------------------------------------------------------------------------- #
sect "property / differential / exhaustive tests"
if cargo test --release --quiet >"$TMP/test.out" 2>&1; then
  pass "cargo test  ($(grep -oE '[0-9]+ passed' "$TMP/test.out" | head -1))"
else
  bad "cargo test"; tail -30 "$TMP/test.out"
fi

# ---------------------------------------------------------------------------- #
sect "Kani — bounded model checking (V1)"
if have cargo-kani; then
  if ./verify-kani.sh >"$TMP/kani.out" 2>&1; then
    pass "verify-kani.sh  ($(grep -c 'PASS' "$TMP/kani.out") harness(es))"
  else
    bad "verify-kani.sh"; sed 's/^/      /' "$TMP/kani.out" | tail -25
  fi
else
  skip "kani not installed (cargo install --locked kani-verifier) — V1 skipped"
fi

# ---------------------------------------------------------------------------- #
sect "Aeneas — dogfood L3 proof (V3)"
AEN="${LEANLIFT_AENEAS:-$HOME/work/_verif-tools/aeneas}"
if [ -x "$AEN/bin/aeneas" ]; then
  if "$LIFT" prove models-fire --out "$TMP/fire.json" >"$TMP/fire.out" 2>&1; then
    if grep -q '"sorry_free": true' "$TMP/fire.json"; then
      pass "lift prove models-fire  (L3, sorry-free, $(grep -c '✓' "$TMP/fire.out") obligations)"
    else
      bad "lift prove models-fire  (proof present but NOT sorry-free)"; tail -20 "$TMP/fire.out"
    fi
  else
    bad "lift prove models-fire  (did not certify L3)"; tail -25 "$TMP/fire.out"
  fi
else
  skip "aeneas not built at $AEN (scripts/build_aeneas.sh) — V3 dogfood skipped"
fi

# ---------------------------------------------------------------------------- #
sect "M1 ↔ M3 agreement over random FSMs (V0.5)"
if command -v lake >/dev/null 2>&1; then
  if ./verify-m1m3.sh 5 >"$TMP/m1m3.out" 2>&1; then
    pass "verify-m1m3.sh  ($(grep -oE '[0-9]+ random FSMs' "$TMP/m1m3.out" | head -1), M1↔M3 agree)"
  else
    bad "verify-m1m3.sh"; sed 's/^/      /' "$TMP/m1m3.out" | tail -30
  fi
else
  skip "lake/lean not on PATH — M3 unavailable, V0.5 skipped"
fi

# ---------------------------------------------------------------------------- #
sect "native CTMC vs PRISM cross-check (V0.6)"
if command -v prism >/dev/null 2>&1; then
  if "$LIFT" model prism examples/models/dock-gspn.model.toml --emit "$TMP/dg" \
       --out "$TMP/prism.json" >"$TMP/prism.out" 2>&1; then
    if grep -qi 'mismatch' "$TMP/prism.out"; then
      bad "model prism dock-gspn — native CTMC disagrees with PRISM"
      grep -i 'mismatch' "$TMP/prism.out" | sed 's/^/      /'
    else
      pass "model prism dock-gspn — native CTMC agrees with PRISM (≤1e-4)"
    fi
  else
    bad "model prism dock-gspn failed"; tail -15 "$TMP/prism.out"
  fi
else
  skip "prism not installed — V0.6 native-CTMC-vs-PRISM cross-check skipped"
fi

# ---------------------------------------------------------------------------- #
sect "parser fuzzing (V2)"
if have cargo-fuzz && [ -d fuzz ]; then
  # V2 not yet implemented; when it is, run a short time-budget here.
  skip "fuzz targets present but the V2 runner is not wired yet"
else
  skip "cargo-fuzz / fuzz/ targets not present — V2 not implemented yet"
fi

# ---------------------------------------------------------------------------- #
echo
if [ "$fails" -eq 0 ]; then
  printf '\033[32mVERIFY GREEN\033[0m — deep tier passed (SKIPs are not failures)\n'
else
  printf '\033[31m%d deep check(s) failed\033[0m\n' "$fails"
fi
exit "$fails"
