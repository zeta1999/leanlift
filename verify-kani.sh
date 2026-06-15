#!/usr/bin/env bash
# verify-kani.sh — Phase V1 of PLAN-verification: bounded model checking with
# Kani (CBMC under the hood). Proves panic-freedom + bounded invariants for the
# integer/identifier kernels that the rest of the tool trusts implicitly.
#
# Kani is an EXTERNAL tool (like lean / aeneas), not a shipped dependency. If it
# is not on PATH this script SKIPs (exit 0) so it can sit in CI unconditionally.
# Harnesses live behind `#[cfg(kani)]` and are inert for normal cargo builds.
#
# Harnesses run ONE AT A TIME (`--harness`) to keep CBMC's memory bounded.

set -uo pipefail
cd "$(dirname "$0")"

pass(){ printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad(){  printf '  \033[31mFAIL\033[0m  %s\n' "$1"; }
skip(){ printf '  \033[33mSKIP\033[0m  %s\n' "$1"; }

printf '\033[1m== Kani — bounded model checking (V1) ==\033[0m\n'

if ! command -v cargo-kani >/dev/null 2>&1; then
  skip "kani not installed (cargo install --locked kani-verifier && cargo kani setup) — V1 skipped"
  exit 0
fi

# Each harness, verified in isolation so CBMC peaks low.
# NOTE: V1.3 (vid/ctor identifier validity) is NOT here — CBMC chokes on the
# symbolic UTF-8 decode of `&str::chars()` (intractable, minutes-to-never). That
# property is instead discharged by EXHAUSTIVE enumeration over all ASCII inputs
# of length ≤ 2 in the `cargo test` unit tests (codegen.rs / lean.rs) — complete
# for the bound and sub-millisecond. Kani is reserved for the integer kernel,
# where bounded model checking is genuinely unbounded-over-the-domain and fast.
HARNESSES=(
  "fire_no_underflow"             # V1.2 — PtNet fire kernel never u32-underflows
  "div_ceil_safe"                 # R2  — RTA ⌈a/b⌉ overflow-free, ⌈a/b⌉ ≤ a
  "term_monotone"                 # R2  — RTA interference term monotone in r (LFP soundness)
)

fails=0
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
for h in "${HARNESSES[@]}"; do
  if cargo kani --harness "$h" >"$TMP/$h.log" 2>&1; then
    pass "$h"
  else
    bad "$h"; fails=$((fails+1))
    sed 's/^/      /' "$TMP/$h.log" | tail -25
  fi
done

if [ "$fails" -eq 0 ]; then
  printf '\033[32mKANI GREEN\033[0m — %d bounded proof(s)\n' "${#HARNESSES[@]}"
else
  printf '\033[31m%d Kani harness(es) failed\033[0m\n' "$fails"
fi
exit "$fails"
