#!/usr/bin/env bash
# ci.sh — CI for the behavioural-models axis (`lift model`).
#
# Self-contained: needs rustc/cargo (always); lean, c++, and go are used if on
# PATH and otherwise SKIPped (never fail). It builds warnings-as-errors, runs the
# Rust unit tests, elaborates the Lean theory, exercises every verb/family/format
# end to end (M1 check, M2 prism, M3 prove, L1 export+loop-closure), and runs the
# negative "teeth" tests (a wrong model must go red in BOTH the checker and the
# proof). Exit code = number of failures (0 = green).
#
# This covers the model axis only; the broader engine suite (LLM/Aeneas/forge
# paths) is `tests/run.sh`. This is the FAST tier (every commit); the DEEP tier
# (Kani bounded proofs, the Aeneas dogfood, fuzzing) is `verify.sh` — run it
# nightly/manually (PLAN-verification §V5.2).

set -uo pipefail
cd "$(dirname "$0")"
ROOT="$(pwd)"
LIFT="$ROOT/target/release/lift"
M="$ROOT/examples/models"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
fails=0

pass(){ printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad(){  printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fails=$((fails+1)); }
skip(){ printf '  \033[33mSKIP\033[0m  %s\n' "$1"; }
sect(){ printf '\n\033[1m== %s ==\033[0m\n' "$1"; }

have(){ command -v "$1" >/dev/null 2>&1; }

# ---------------------------------------------------------------------------- #
sect "build (warnings = errors)"
if RUSTFLAGS="-D warnings" cargo build --release --quiet 2>"$TMP/build.err"; then
  pass "cargo build --release  (RUSTFLAGS=-D warnings)"
else
  bad "cargo build"; cat "$TMP/build.err"
  echo; echo "build failed — aborting CI"; exit 1
fi

# ---------------------------------------------------------------------------- #
sect "unit tests"
if cargo test --release --quiet >"$TMP/test.out" 2>&1; then
  pass "cargo test  ($(grep -oE '[0-9]+ passed' "$TMP/test.out" | head -1))"
else
  bad "cargo test"; cat "$TMP/test.out"
fi

# Optional, non-fatal: clippy as a lint signal if installed.
if cargo clippy --version >/dev/null 2>&1; then
  if RUSTFLAGS="" cargo clippy --release --quiet -- -W clippy::all >"$TMP/clippy.out" 2>&1; then
    pass "cargo clippy (clean)"
  else
    skip "cargo clippy reported lints (non-fatal) — see $TMP/clippy.out"
  fi
else
  skip "cargo clippy (not installed)"
fi

# ---------------------------------------------------------------------------- #
sect "Lean theory — LeanLift/Models/*.lean elaborates sorry-free"
if have lean; then
  for f in Fsm Petri Ctmc; do
    if (cd lean && lean "LeanLift/Models/$f.lean") >"$TMP/$f.out" 2>&1; then
      pass "LeanLift/Models/$f.lean"
    else
      bad "LeanLift/Models/$f.lean"; cat "$TMP/$f.out"
    fi
  done
else
  skip "Lean theory (lean not on PATH)"
fi

# ---------------------------------------------------------------------------- #
sect "M1 — check (native models + standard formats, auto-detected)"
for f in tiny mcl dock mission resource; do
  if "$LIFT" model check "$M/$f.model.toml" --out "$TMP/r.json" >"$TMP/o" 2>&1; then
    pass "check $f  ($(grep -o 'reachable : [0-9]* state' "$TMP/o"))"
  else
    bad "check $f"; cat "$TMP/o"
  fi
done
for f in turnstile.scxml dock.pnml; do
  if "$LIFT" model check "$M/$f" --out "$TMP/r.json" >"$TMP/o" 2>&1; then
    pass "check $f  (standard format)"
  else
    bad "check $f"; cat "$TMP/o"
  fi
done

# ---------------------------------------------------------------------------- #
sect "M2 — prism (GSPN → tangible CTMC; vs day49 closed forms)"
if "$LIFT" model prism "$M/dock-gspn.model.toml" --emit "$TMP/dg" --out "$TMP/r.json" >"$TMP/o" 2>&1; then
  pf=$(grep 'P(freed)' "$TMP/o" | grep -o '[0-9]\.[0-9]*')
  et=$(grep 'E\[time\]' "$TMP/o" | grep -o '[0-9]\.[0-9]*')
  if [ "$pf" = "1.000000" ] && [ "$et" = "1.000000" ]; then
    pass "prism dock-gspn lease  (P(freed)=$pf, E[time]=$et)"
  else
    bad "prism dock-gspn: P(freed)=$pf E[time]=$et (expected 1.0, 1.0)"
  fi
else
  bad "prism dock-gspn"; cat "$TMP/o"
fi

# ---------------------------------------------------------------------------- #
sect "M3 — prove (Lean, sorry-free)"
if have lean; then
  for f in mcl dock mission resource; do
    if "$LIFT" model prove "$M/$f.model.toml" --emit "$TMP/$f.gen.lean" --out "$TMP/r.json" >"$TMP/o" 2>&1; then
      pass "prove $f  ($(grep -o 'M3 proved' "$TMP/o"))"
    else
      bad "prove $f"; tail -12 "$TMP/o"
    fi
  done
  if "$LIFT" model prove "$M/turnstile.scxml" --emit "$TMP/ts.gen.lean" --out "$TMP/r.json" >"$TMP/o" 2>&1; then
    pass "prove turnstile.scxml  (SCXML → M3)"
  else
    bad "prove turnstile.scxml"; tail -12 "$TMP/o"
  fi
else
  skip "prove (lean not on PATH)"
fi

# ---------------------------------------------------------------------------- #
sect "L1 — export + loop closure (generated code ≡ model)"
LANGS="rust"; have c++ && LANGS="$LANGS c++"; have go && LANGS="$LANGS go"
for f in mcl mission dock resource; do
  for lg in $LANGS; do
    ext=rs; [ "$lg" = c++ ] && ext=cpp; [ "$lg" = go ] && ext=go
    if "$LIFT" model export "$M/$f.model.toml" --lang "$lg" --emit "$TMP/e.$ext" --verify >"$TMP/o" 2>&1; then
      pass "export $f/$lg  ($(grep -o 'L1 conformant — [0-9]*/[0-9]*' "$TMP/o"))"
    else
      bad "export $f/$lg"; tail -6 "$TMP/o"
    fi
  done
done
"$LIFT" model export "$M/mcl.model.toml" --lang dot --emit "$TMP/mcl.dot" >/dev/null 2>&1 \
  && grep -q "digraph" "$TMP/mcl.dot" && pass "export dot (graphviz)" || bad "export dot"

# ---------------------------------------------------------------------------- #
sect "teeth — a wrong model goes RED in checker AND proof"
# mcl: belief never relocalizes ⇒ the robot navigates while delocalized.
if have python3; then
  python3 - "$M/mcl.model.toml" "$TMP/mcl-bad.model.toml" <<'PY'
import sys
s = open(sys.argv[1]).read()
s = s.replace('machine = "belief"\nfrom = "Delocalized"\non   = "converged"\nto   = "Localized"',
              'machine = "belief"\nfrom = "Delocalized"\non   = "converged"\nto   = "Delocalized"')
open(sys.argv[2], 'w').write(s)
PY
  if "$LIFT" model check "$TMP/mcl-bad.model.toml" --out "$TMP/r.json" >"$TMP/o" 2>&1; then
    bad "broken mcl was NOT caught at M1"
  else
    pass "broken mcl caught at M1  ($(grep -o 'Navigate|Delocalized' "$TMP/o" | head -1))"
  fi
  if have lean; then
    if "$LIFT" model prove "$TMP/mcl-bad.model.toml" --emit "$TMP/b.gen.lean" --out "$TMP/r.json" >"$TMP/o" 2>&1; then
      bad "broken mcl proof did NOT fail"
    else
      pass "broken mcl proof fails to elaborate (M3 red)"
    fi
  fi
else
  skip "mcl teeth (python3 not on PATH)"
fi

# dock: two dock tokens break mutual exclusion.
sed 's/initial = "free:1"/initial = "free:2"/' "$M/dock.model.toml" > "$TMP/dock-bad.model.toml"
if "$LIFT" model check "$TMP/dock-bad.model.toml" --out "$TMP/r.json" >"$TMP/o" 2>&1; then
  bad "broken dock (free:2) was NOT caught at M1"
else
  pass "broken dock caught at M1  ($(grep -o 'csA+csB = 2 > 1' "$TMP/o" | head -1))"
fi

# dock-gspn: lease→giveup drops P(freed) to 1−p^(K+1)=0.9375.
GIVEUP="$TMP/dock-giveup.model.toml"
{
  sed -e 's/mode    = "lease"/mode    = "giveup"/' \
      -e 's/places  = \["holding", "inflight", "freed", "budget"\]/places  = ["holding", "inflight", "freed", "budget", "stuck"]/' \
      "$M/dock-gspn.model.toml"
  printf '\n[[transition]]\nname="abort"\nkind="timed"\nrate="mu_l"\npre="inflight:1"\ninhibit="budget"\npost="stuck:1"\n'
} > "$GIVEUP"
gp=$("$LIFT" model prism "$GIVEUP" --emit "$TMP/gg" --out "$TMP/r.json" 2>/dev/null | grep 'P(freed)' | grep -o '[0-9]\.[0-9]*')
[ "$gp" = "0.937500" ] && pass "giveup teeth  (P(freed)=$gp = 1−p^(K+1))" || bad "giveup teeth: P(freed)=$gp (expected 0.937500)"

# ---------------------------------------------------------------------------- #
echo
if [ "$fails" -eq 0 ]; then
  printf '\033[32mCI GREEN\033[0m — model axis verified end to end\n'
else
  printf '\033[31mCI RED\033[0m — %d failure(s)\n' "$fails"
fi
exit "$fails"
