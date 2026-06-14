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

echo "== models (M1 native checker — docs/PLAN-models.md Phase 0) =="
# positive: the tiny FSM checks clean (exit 0), family auto-detected.
if "$LIFT" model check examples/models/tiny.model.toml --out "$TMP/tiny.json" >"$TMP/tiny.out" 2>&1; then
  pass "tiny.model.toml  ($(grep -o 'M1 checked' "$TMP/tiny.out"); $(grep -o 'reachable : [0-9]* state' "$TMP/tiny.out"))"
else
  bad "tiny.model.toml did not check"; cat "$TMP/tiny.out"
fi
# teeth: a model that can reach a forbidden state must go red (exit nonzero).
cat > "$TMP/bad.model.toml" <<'EOF'
initial = "off"
states  = ["off", "error"]
[[transition]]
from = "off"
on   = "break"
to   = "error"
[[forbid]]
state = "error"
EOF
if "$LIFT" model check "$TMP/bad.model.toml" --out "$TMP/badm.json" >"$TMP/badm.out" 2>&1; then
  bad "reachable forbidden state was NOT caught (exit 0)"
else
  pass "forbidden-state model caught ($(grep -o 'safety VIOLATED' "$TMP/badm.out" | head -1 || echo 'safety VIOLATED'))"
fi

# mcl: the supervisor × belief product (Phase 1). M1 check, then teeth.
if "$LIFT" model check examples/models/mcl.model.toml --out "$TMP/mcl.json" >"$TMP/mcl.out" 2>&1; then
  pass "mcl product check  ($(grep -o 'reachable : [0-9]* state' "$TMP/mcl.out"))"
else
  bad "mcl did not check"; cat "$TMP/mcl.out"
fi
python3 - <<'PY'
src = open("examples/models/mcl.model.toml").read()
old = 'machine = "belief"\nfrom = "Delocalized"\non   = "converged"\nto   = "Localized"'
new = 'machine = "belief"\nfrom = "Delocalized"\non   = "converged"\nto   = "Delocalized"'
open("/tmp/mcl-broken-test.model.toml","w").write(src.replace(old,new,1))
PY
if "$LIFT" model check /tmp/mcl-broken-test.model.toml --out "$TMP/mclb.json" >"$TMP/mclb.out" 2>&1; then
  bad "broken mcl was NOT caught at M1 (exit 0)"
else
  pass "broken mcl caught at M1 ($(grep -o 'Navigate|Delocalized' "$TMP/mclb.out" | head -1))"
fi

# dock: PT-net with token loss (Phase 2). M1 check + the safety-survives-loss
# note, then teeth (free:2 breaks mutual exclusion).
if "$LIFT" model check examples/models/dock.model.toml --out "$TMP/dock.json" >"$TMP/dock.out" 2>&1; then
  pass "dock PT-net check  ($(grep -o 'reachable : [0-9]* state' "$TMP/dock.out"); lossy, mutex safe)"
else
  bad "dock did not check"; cat "$TMP/dock.out"
fi
sed 's/initial = "free:1"/initial = "free:2"/' examples/models/dock.model.toml > /tmp/dock-broken-test.model.toml
if "$LIFT" model check /tmp/dock-broken-test.model.toml --out "$TMP/dockb.json" >"$TMP/dockb.out" 2>&1; then
  bad "broken dock (free:2) was NOT caught at M1 (exit 0)"
else
  pass "broken dock caught at M1 ($(grep -o 'csA+csB = 2 > 1' "$TMP/dockb.out" | head -1))"
fi

# mission: a behaviour tree compiled to an LTS (Phase 3). M1 check + teeth.
if "$LIFT" model check examples/models/mission.model.toml --out "$TMP/mis.json" >"$TMP/mis.out" 2>&1; then
  pass "mission BT check  ($(grep -o 'reachable : [0-9]* state' "$TMP/mis.out"); compiled to LTS)"
else
  bad "mission did not check"; cat "$TMP/mis.out"
fi
cat > /tmp/mission-broken-test.model.toml <<'EOF'
kind = "bt"
vars = ["lost", "atGoal", "moving"]
initial = ["lost"]
tree = "fallback( act:navigate, sequence(cond:lost, act:recover) )"
[[action]]
name = "navigate"
effect = "moving=true, atGoal=true"
[[action]]
name = "recover"
guard = "lost=true"
effect = "lost=false"
[[forbid]]
true = ["lost", "moving"]
EOF
if "$LIFT" model check /tmp/mission-broken-test.model.toml --out "$TMP/misb.json" >"$TMP/misb.out" 2>&1; then
  bad "broken mission (unguarded navigate) NOT caught at M1 (exit 0)"
else
  pass "broken mission caught at M1 ($(grep -o 'lost_atGoal_moving' "$TMP/misb.out" | head -1))"
fi

# resource: a coloured Petri net unfolded to a PT-net (Phase 4). M1 + teeth.
if "$LIFT" model check examples/models/resource.model.toml --out "$TMP/res.json" >"$TMP/res.out" 2>&1; then
  pass "resource CPN check  ($(grep -o 'reachable : [0-9]* state' "$TMP/res.out"); $(grep -o 'unfolded [0-9]* PT place' "$TMP/res.out"))"
else
  bad "resource did not check"; cat "$TMP/res.out"
fi
sed 's/init   = "lk"/init   = "lk, lk"/' examples/models/resource.model.toml > /tmp/res-broken-test.model.toml
if "$LIFT" model check /tmp/res-broken-test.model.toml --out "$TMP/resb.json" >"$TMP/resb.out" 2>&1; then
  bad "broken resource (two locks) NOT caught at M1 (exit 0)"
else
  pass "broken resource caught at M1 ($(grep -o 'crit_p1+crit_p2+crit_p3 = 2 > 1' "$TMP/resb.out" | head -1))"
fi

# dock-gspn: a GSPN → tangible CTMC, quantitative M2 (Phase 5). Native solver
# results cross-checked against the day49 closed forms; giveup teeth.
if "$LIFT" model prism examples/models/dock-gspn.model.toml --emit "$TMP/dg" --out "$TMP/dg.json" >"$TMP/dg.out" 2>&1; then
  pf=$(grep 'P(freed)' "$TMP/dg.out" | grep -o '[0-9]\.[0-9]*')
  et=$(grep 'E\[time\]' "$TMP/dg.out" | grep -o '[0-9]\.[0-9]*')
  if [ "$pf" = "1.000000" ] && [ "$et" = "1.000000" ]; then
    pass "dock-gspn lease M2  (P(freed)=$pf=1, E[time]=$et=1/μd; $(grep -o 'tangible states : [0-9]*' "$TMP/dg.out"))"
  else
    bad "dock-gspn lease wrong: P(freed)=$pf E[time]=$et (expected 1.0, 1.0)"; cat "$TMP/dg.out"
  fi
else
  bad "dock-gspn did not measure"; cat "$TMP/dg.out"
fi
# giveup teeth: P(freed) drops to 1 - p^(K+1) = 1 - 0.5^4 = 0.9375.
python3 - <<'PY'
src=open("examples/models/dock-gspn.model.toml").read()
src=src.replace('mode    = "lease"','mode    = "giveup"')
src=src.replace('places  = ["holding", "inflight", "freed", "budget"]',
                'places  = ["holding", "inflight", "freed", "budget", "stuck"]')
src+='\n[[transition]]\nname="abort"\nkind="timed"\nrate="mu_l"\npre="inflight:1"\ninhibit="budget"\npost="stuck:1"\n'
open("/tmp/dock-giveup-test.model.toml","w").write(src)
PY
gp=$("$LIFT" model prism /tmp/dock-giveup-test.model.toml --emit "$TMP/dgg" --out "$TMP/dgg.json" 2>/dev/null | grep 'P(freed)' | grep -o '[0-9]\.[0-9]*')
if [ "$gp" = "0.937500" ]; then
  pass "dock-gspn giveup M2  (P(freed)=$gp = 1-p^(K+1), lease→giveup teeth)"
else
  bad "dock-gspn giveup wrong: P(freed)=$gp (expected 0.937500)"
fi
rm -f /tmp/dock-giveup-test.model.toml

echo "== models (code export + loop closure — Phase 6) =="
# Rust is always available (this is a cargo project). C++/Go best-effort.
# LTS families (mcl/mission) and Petri families (dock/resource) all export.
for me in mcl mission dock resource; do
  if "$LIFT" model export "examples/models/$me.model.toml" --lang rust --emit "$TMP/$me.rs" --verify >"$TMP/$me.cg.out" 2>&1; then
    pass "$me → rust + loop closure ($(grep -o 'L1 conformant — [0-9]*/[0-9]* traces' "$TMP/$me.cg.out"))"
  else
    bad "$me rust export did not conform"; tail -8 "$TMP/$me.cg.out"
  fi
done
if command -v c++ >/dev/null 2>&1; then
  if "$LIFT" model export examples/models/mcl.model.toml --lang c++ --emit "$TMP/mcl.cpp" --verify >"$TMP/mcl.cpp.out" 2>&1; then
    pass "mcl → c++ + loop closure ($(grep -o 'L1 conformant — [0-9]*/[0-9]* traces' "$TMP/mcl.cpp.out"))"
  else
    bad "mcl c++ export did not conform"; tail -8 "$TMP/mcl.cpp.out"
  fi
else
  printf '  \033[33mSKIP\033[0m  mcl c++ export (c++ not on PATH)\n'
fi
if command -v go >/dev/null 2>&1; then
  if "$LIFT" model export examples/models/mcl.model.toml --lang go --emit "$TMP/mcl.go" --verify >"$TMP/mcl.go.out" 2>&1; then
    pass "mcl → go + loop closure ($(grep -o 'L1 conformant — [0-9]*/[0-9]* traces' "$TMP/mcl.go.out"))"
  else
    bad "mcl go export did not conform"; tail -8 "$TMP/mcl.go.out"
  fi
else
  printf '  \033[33mSKIP\033[0m  mcl go export (go not on PATH)\n'
fi

# turnstile.scxml: standard SCXML import, auto-detected (Phase 1.5 interop).
if "$LIFT" model check examples/models/turnstile.scxml --out "$TMP/ts.json" >"$TMP/ts.out" 2>&1; then
  pass "turnstile.scxml import (FSM auto-detected, $(grep -o 'reachable : [0-9]* state' "$TMP/ts.out"))"
else
  bad "turnstile.scxml did not check"; cat "$TMP/ts.out"
fi
if "$LIFT" model export examples/models/turnstile.scxml --lang rust --emit "$TMP/ts.rs" --verify >"$TMP/ts.cg.out" 2>&1; then
  pass "turnstile.scxml → rust loop closure ($(grep -o 'L1 conformant — [0-9]*/[0-9]* traces' "$TMP/ts.cg.out"))"
else
  bad "turnstile.scxml rust export did not conform"; tail -6 "$TMP/ts.cg.out"
fi
"$LIFT" model export examples/models/mcl.model.toml --lang dot --emit "$TMP/mcl.dot" >/dev/null 2>&1 \
  && grep -q "digraph" "$TMP/mcl.dot" && pass "dot export (graphviz)" || bad "dot export failed"
# dock.pnml: standard PNML import → the Petri checker (same 6 reachable + sink).
if "$LIFT" model check examples/models/dock.pnml --out "$TMP/pn.json" >"$TMP/pn.out" 2>&1; then
  pass "dock.pnml import (PT-net auto-detected, $(grep -o 'reachable : [0-9]* state' "$TMP/pn.out"); lossy)"
else
  bad "dock.pnml did not check"; cat "$TMP/pn.out"
fi

echo "== models (M3 Lean proof — Phases 1–4, needs lean on PATH) =="
if command -v lean >/dev/null 2>&1; then
  if "$LIFT" model prove examples/models/turnstile.scxml --emit "$TMP/Turnstile.gen.lean" --out "$TMP/tsp.json" >"$TMP/tsp.out" 2>&1; then
    pass "turnstile.scxml prove ($(grep -o 'M3 proved' "$TMP/tsp.out"))"
  else
    bad "turnstile.scxml did not certify M3"; tail -10 "$TMP/tsp.out"
  fi
  for me in mcl dock mission resource; do
    if "$LIFT" model prove "examples/models/$me.model.toml" --emit "$TMP/$me.gen.lean" --out "$TMP/${me}p.json" >"$TMP/${me}p.out" 2>&1; then
      pass "$me prove  ($(grep -o 'M3 proved' "$TMP/${me}p.out"), sorry-free)"
    else
      bad "$me did not certify M3"; tail -15 "$TMP/${me}p.out"
    fi
  done
  # teeth: the broken product / broken net must FAIL to elaborate (M3 red).
  if "$LIFT" model prove /tmp/mcl-broken-test.model.toml --emit "$TMP/Broken.gen.lean" --out "$TMP/mclbp.json" >"$TMP/mclbp.out" 2>&1; then
    bad "broken mcl proof did NOT fail (exit 0)"
  else
    pass "broken mcl proof fails to elaborate ($(grep -o 'did NOT elaborate' "$TMP/mclbp.out" | head -1))"
  fi
  if "$LIFT" model prove /tmp/dock-broken-test.model.toml --emit "$TMP/DockBad.gen.lean" --out "$TMP/dockbp.json" >"$TMP/dockbp.out" 2>&1; then
    bad "broken dock proof did NOT fail (exit 0)"
  else
    pass "broken dock proof fails to elaborate ($(grep -o 'did NOT elaborate' "$TMP/dockbp.out" | head -1))"
  fi
  if "$LIFT" model prove /tmp/mission-broken-test.model.toml --emit "$TMP/MisBad.gen.lean" --out "$TMP/misbp.json" >"$TMP/misbp.out" 2>&1; then
    bad "broken mission proof did NOT fail (exit 0)"
  else
    pass "broken mission proof fails to elaborate ($(grep -o 'did NOT elaborate' "$TMP/misbp.out" | head -1))"
  fi
  if "$LIFT" model prove /tmp/res-broken-test.model.toml --emit "$TMP/ResBad.gen.lean" --out "$TMP/resbp.json" >"$TMP/resbp.out" 2>&1; then
    bad "broken resource proof did NOT fail (exit 0)"
  else
    pass "broken resource proof fails to elaborate ($(grep -o 'did NOT elaborate' "$TMP/resbp.out" | head -1))"
  fi
  rm -f /tmp/mcl-broken-test.model.toml /tmp/dock-broken-test.model.toml /tmp/mission-broken-test.model.toml /tmp/res-broken-test.model.toml
else
  printf '  \033[33mSKIP\033[0m  mcl/dock/mission/resource prove (lean not on PATH)\n'
fi

echo
[ "$fail" -eq 0 ] && echo "all green" || echo "REGRESSIONS"
exit "$fail"
