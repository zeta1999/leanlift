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

# Queued stop-and-wait link (steady-state metrics: mean / throughput / full).
if "$LIFT" model prism "$M/link.model.toml" --emit "$TMP/lk" --out "$TMP/lk.json" >"$TMP/lko" 2>&1; then
  xx=$(grep -E '^\s+X ' "$TMP/lko" | grep -o '[0-9]\.[0-9]*' | head -1)
  # stable regime (p=0.3, λ=0.4): throughput ≈ λ ⇒ X in (0.39, 0.41).
  if awk "BEGIN{exit !($xx > 0.39 && $xx < 0.41)}"; then
    pass "prism link  (steady-state X=$xx ≈ λ=0.4, stable)"
  else
    bad "prism link: throughput X=$xx out of stable-regime band (0.39,0.41)"
  fi
else
  bad "prism link"; cat "$TMP/lko"
fi

# Phase-transition sweep: the empirical knee must match the closed-form p*.
if ./scripts/link-sweep.sh --check >"$TMP/sweep" 2>&1; then
  k=$(grep -oE 'knee.*p ≈ [0-9.]+' "$TMP/sweep" | grep -oE '[0-9.]+$')
  pass "link phase sweep  (empirical knee p≈$k ≈ closed-form p*)"
else
  bad "link phase sweep — knee vs p* mismatch"; tail -6 "$TMP/sweep"
fi

# LE3 cross-check: the depolarizing-noise GSPN steady-state fidelity must equal the
# Lean/Kraus closed form F = 1 - p/2 across a p-sweep (LEAN_ERROR_PLAN.md LE3 stochastic
# axis ↔ Leanproofs/Quantum/Depolarizing.lean depolarizing_fidelity). Tolerance ≤1e-3.
le3_ok=1
for p in 0.05 0.1 0.2 0.3 0.5 0.8; do
  mu=$(awk "BEGIN{print 2 - $p}")
  exp=$(awk "BEGIN{print 1 - $p/2}")
  F=$("$LIFT" model prism "$M/depolarizing.model.toml" --set p=$p --set mu_restore=$mu \
        --out "$TMP/dp.json" 2>/dev/null | grep -E '^\s+F ' | grep -oE '[0-9]+\.[0-9]+' | head -1)
  if ! awk "BEGIN{d=$F-$exp; if(d<0)d=-d; exit !(d<=1e-3)}"; then
    le3_ok=0; echo "    p=$p: F_native=$F vs 1-p/2=$exp (Δ>1e-3)"
  fi
done
if [ "$le3_ok" = 1 ]; then
  pass "LE3 depolarizing fidelity  (PRISM steady-state F = 1-p/2 = Lean/Kraus law, Δ≤1e-3 over p∈[.05,.8])"
else
  bad "LE3 depolarizing fidelity — PRISM steady-state disagrees with the Lean F=1-p/2 bound"
fi

# LE3 cross-check (amplitude + phase damping): the GSPN steady-states must equal the Lean/Kraus
# laws — amplitude survival π(excited)=1−γ (amplitudeDamping_relax) and phase coherence
# π(coherent)=1−λ (phaseDamping_coherence) — across a rate sweep. Tolerance ≤1e-3.
le3d_ok=1
for r in 0.05 0.1 0.2 0.3 0.5; do
  mu=$(awk "BEGIN{printf \"%.4f\", 1 - $r}")
  exp=$(awk "BEGIN{print 1 - $r}")
  Fa=$("$LIFT" model prism "$M/amplitude_damping.model.toml" --set gamma=$r --set pump=$mu \
        2>/dev/null | awk '$1=="Fsurv"{print $3}')
  Fc=$("$LIFT" model prism "$M/phase_damping.model.toml" --set lam=$r --set rephase=$mu \
        2>/dev/null | awk '$1=="Coh"{print $3}')
  awk "BEGIN{d=$Fa-$exp; if(d<0)d=-d; exit !(d<=1e-3)}" || { le3d_ok=0; echo "    amp γ=$r: Fsurv=$Fa vs 1−γ=$exp"; }
  awk "BEGIN{d=$Fc-$exp; if(d<0)d=-d; exit !(d<=1e-3)}" || { le3d_ok=0; echo "    phase λ=$r: Coh=$Fc vs 1−λ=$exp"; }
done
if [ "$le3d_ok" = 1 ]; then
  pass "LE3 amplitude/phase damping  (PRISM steady-states 1−γ / 1−λ = Lean/Kraus laws, Δ≤1e-3 over r∈[.05,.5])"
else
  bad "LE3 amplitude/phase damping — PRISM steady-states disagree with the Lean damping laws"
fi

# ---------------------------------------------------------------------------- #
sect "RT — schedulability (utilization bound + exact RTA)"
if "$LIFT" model check "$M/tasks.model.toml" >"$TMP/rt" 2>&1; then
  # the teaching case: util test FAILs but RTA proves SCHEDULABLE.
  if grep -q "FAIL — sufficient" "$TMP/rt" && grep -q "level : SCHEDULABLE" "$TMP/rt"; then
    pass "schedulability tasks  (RTA exact beats the bound: U>bound yet schedulable)"
  else
    bad "schedulability tasks: unexpected verdict"; cat "$TMP/rt"
  fi
else
  bad "schedulability tasks did not return schedulable (exit $?)"; cat "$TMP/rt"
fi
# teeth: an overloaded set (U>1) must be reported NOT schedulable (exit 1).
printf 'kind="tasks"\npolicy="RM"\n[[task]]\nname="a"\nc="3"\nt="4"\n[[task]]\nname="b"\nc="3"\nt="5"\n' >"$TMP/over.toml"
if "$LIFT" model check "$TMP/over.toml" >"$TMP/rto" 2>&1; then
  bad "overloaded task set wrongly reported schedulable"; cat "$TMP/rto"
else
  pass "schedulability teeth  (U>1 overload caught as NOT schedulable)"
fi
# EDF demand-bound: U≤1 passes but constrained deadlines make it infeasible.
if "$LIFT" model check "$M/tasks-edf.model.toml" >"$TMP/edf" 2>&1; then
  bad "tasks-edf wrongly reported schedulable"; cat "$TMP/edf"
else
  if grep -q "PASS — sufficient" "$TMP/edf" && grep -q "dbf(1) = 2 > 1" "$TMP/edf"; then
    pass "EDF demand-bound  (U≤1 passes, but demand test catches dbf(1)>1)"
  else
    bad "EDF demand-bound: unexpected output"; cat "$TMP/edf"
  fi
fi

# R4 intersection: hard boundary is conservative (soft miss still low there).
if ./scripts/tasks-sweep.sh --check >"$TMP/tsweep" 2>&1; then
  hb=$(grep -oE 'hard boundary.*scale ≈ [0-9.]+' "$TMP/tsweep" | grep -oE '[0-9.]+$')
  pass "hard/soft intersection  (hard boundary scale≈$hb conservative vs soft miss)"
else
  bad "hard/soft intersection sweep"; tail -6 "$TMP/tsweep"
fi

# ---------------------------------------------------------------------------- #
sect "QNET — open queueing network (traffic equations + bottleneck)"
if "$LIFT" model check "$M/qnet.model.toml" >"$TMP/qn" 2>&1; then
  if grep -q "worker" "$TMP/qn" && grep -q "◀ bottleneck" "$TMP/qn" && grep -q "level : STABLE" "$TMP/qn"; then
    pass "qnet check  (feedback network STABLE, worker is the bottleneck)"
  else
    bad "qnet check: unexpected verdict"; cat "$TMP/qn"
  fi
else
  bad "qnet check did not return stable (exit $?)"; cat "$TMP/qn"
fi
# teeth: an over-driven station (λ>μ) must be reported UNSTABLE (exit 1).
printf 'kind="qnet"\n[[station]]\nname="x"\nmu="3.0"\nlambda="5.0"\n' >"$TMP/qover.toml"
if "$LIFT" model check "$TMP/qover.toml" >"$TMP/qno" 2>&1; then
  bad "over-driven station wrongly reported stable"; cat "$TMP/qno"
else
  pass "qnet teeth  (λ>μ saturation caught as UNSTABLE)"
fi
# bottleneck phase transition: empirical instability scale ≈ closed-form 1/maxρ.
if ./scripts/qnet-sweep.sh --check >"$TMP/qsweep" 2>&1; then
  ks=$(grep -oE 'instability.*scale ≈ [0-9.]+' "$TMP/qsweep" | grep -oE '[0-9.]+$')
  pass "qnet bottleneck sweep  (instability scale≈$ks ≈ closed-form 1/maxρ)"
else
  bad "qnet bottleneck sweep"; tail -6 "$TMP/qsweep"
fi

# shared workload: provably-safe (RT/RTA) ⊊ probably-safe (queue stability).
if ./scripts/shared-workload-sweep.sh --check >"$TMP/shared" 2>&1; then
  hb=$(grep -oE 'provably-safe boundary.*ℓ ≈ [0-9.]+' "$TMP/shared" | grep -oE '[0-9.]+$')
  sb=$(grep -oE 'probably-safe boundary.*ℓ ≈ [0-9.]+' "$TMP/shared" | grep -oE '[0-9.]+$')
  pass "shared workload  (provably-safe ℓ≈$hb ⊊ probably-safe ℓ≈$sb)"
else
  bad "shared workload sweep"; tail -6 "$TMP/shared"
fi
# teeth: a trapped/closed cycle must ERROR, not report a bogus verdict.
printf 'kind="qnet"\n[[station]]\nname="a"\nmu="9"\nlambda="2"\n[[station]]\nname="b"\nmu="9"\n[[route]]\nfrom="a"\nto="b"\nprob="1.0"\n[[route]]\nfrom="b"\nto="a"\nprob="1.0"\n' >"$TMP/qtrap.toml"
if "$LIFT" model check "$TMP/qtrap.toml" >"$TMP/qtr" 2>&1; then
  bad "trapped network wrongly accepted"; cat "$TMP/qtr"
else
  pass "qnet teeth  (trapped/closed cycle rejected, not falsely stable)"
fi

# ---------------------------------------------------------------------------- #
sect "FPGA — Aria-HDL IR-JSON bridge (Phase B round-trip)"
if "$LIFT" fpga info "$M/../fpga/tcp_ip.aria.json" >"$TMP/fp" 2>&1; then
  if grep -q "4 module(s)" "$TMP/fp" \
     && grep -q "annotations: clock_freq=125000000" "$TMP/fp" \
     && grep -q "assert always" "$TMP/fp"; then
    pass "fpga ingest  (4 modules; annotations + formal properties carried)"
  else
    bad "fpga ingest: missing annotations/formals"; cat "$TMP/fp"
  fi
else
  bad "fpga ingest failed (exit $?)"; cat "$TMP/fp"
fi
# teeth: a wrong-schema document must be rejected (exit 1), not silently accepted.
printf '{"schema":"nope","id":0,"name":"x","ports":[],"clock_domains":[],"annotations":[],"nodes":[],"timing":{}}\n' >"$TMP/badschema.json"
if "$LIFT" fpga info "$TMP/badschema.json" >"$TMP/fpb" 2>&1; then
  bad "fpga accepted an unsupported schema"; cat "$TMP/fpb"
else
  pass "fpga teeth  (unsupported schema rejected)"
fi

# T1 — pipeline timing certificate: hard latency + timing closure (cross-checked).
if "$LIFT" fpga timing "$M/../fpga/pipeline_demo.aria.json" >"$TMP/ft" 2>&1; then
  if grep -q "16.000 ns" "$TMP/ft" \
     && grep -q "0.800 ns ≤ clock 8.000 ns → CLOSES" "$TMP/ft" \
     && grep -q "2/2 pipeline(s) certified" "$TMP/ft"; then
    pass "fpga timing  (mac: 2-cyc 16ns latency @125MHz, closes 0.8≤8ns)"
  else
    bad "fpga timing: wrong certificate"; cat "$TMP/ft"
  fi
else
  bad "fpga timing failed (exit $?)"; cat "$TMP/ft"
fi
# teeth: a stage slower than the clock must FAIL closure (exit 1).
printf '{"schema":"aria-ir-json/v1","id":0,"name":"slow","ports":[],"clock_domains":[],"annotations":[{"kind":"clock_freq","value":"500000000"}],"nodes":[],"pipeline":{"id":0,"num_stages":2,"latency":2,"initiation_interval":1,"flow_control":{"fc":"none"},"stages":[{"index":0,"name":null,"comb_delay_ns":3.0,"lut_count":null,"reg_count":0,"forwarded_values":[]},{"index":1,"name":null,"comb_delay_ns":1.0,"lut_count":null,"reg_count":0,"forwarded_values":[]}]},"systolic":null,"timing":{"c_slow_factor":1,"target_period_ns":2.0,"critical_path_ns":3.0,"retiming_weights":[],"buffers":[]}}\n' >"$TMP/slow.json"
if "$LIFT" fpga timing "$TMP/slow.json" >"$TMP/fts" 2>&1; then
  bad "fpga timing accepted a path slower than the clock"; cat "$TMP/fts"
else
  grep -q "VIOLATED" "$TMP/fts" && pass "fpga timing teeth  (3ns path > 2ns clock → VIOLATED, exit 1)" \
    || { bad "fpga timing teeth: wrong failure"; cat "$TMP/fts"; }
fi
# teeth: over-folding (more C-slow streams than II slots) must be caught by the RTA
# fold check — proves it is a real schedulability test, not a tautology.
printf '{"schema":"aria-ir-json/v1","id":0,"name":"overfold","ports":[],"clock_domains":[],"annotations":[{"kind":"clock_freq","value":"125000000"}],"nodes":[],"pipeline":{"id":0,"num_stages":2,"latency":2,"initiation_interval":2,"flow_control":{"fc":"none"},"stages":[]},"systolic":null,"timing":{"c_slow_factor":4,"target_period_ns":8.0,"critical_path_ns":1.0,"retiming_weights":[],"buffers":[]}}\n' >"$TMP/overfold.json"
if "$LIFT" fpga timing "$TMP/overfold.json" >"$TMP/fto" 2>&1; then
  bad "fpga timing accepted 4 streams over 2 slots (over-fold)"; cat "$TMP/fto"
else
  grep -q "OVER-FOLDED" "$TMP/fto" && pass "fpga timing teeth  (4 streams > 2 slots → OVER-FOLDED, exit 1)" \
    || { bad "fpga timing teeth: over-fold not caught"; cat "$TMP/fto"; }
fi

# T2 — throughput: balanced fallback on the real fixture (no per-stage delays).
if "$LIFT" fpga throughput "$M/../fpga/pipeline_demo.aria.json" >"$TMP/fq" 2>&1; then
  grep -q "125.000 Mitems/s" "$TMP/fq" && grep -q "2/2 pipeline(s) certified" "$TMP/fq" \
    && pass "fpga throughput  (mac: 125 Mitems/s @125MHz, II 1)" \
    || { bad "fpga throughput: wrong report"; cat "$TMP/fq"; }
else
  bad "fpga throughput failed (exit $?)"; cat "$TMP/fq"
fi
# qnet bottleneck must coincide with the critical-path (slowest) stage.
printf '{"schema":"aria-ir-json/v1","id":0,"name":"unbal","ports":[],"clock_domains":[],"annotations":[{"kind":"clock_freq","value":"125000000"}],"nodes":[],"pipeline":{"id":0,"num_stages":3,"latency":3,"initiation_interval":1,"flow_control":{"fc":"ready_valid"},"stages":[{"index":0,"name":null,"comb_delay_ns":2.0,"lut_count":null,"reg_count":0,"forwarded_values":[]},{"index":1,"name":null,"comb_delay_ns":4.0,"lut_count":null,"reg_count":0,"forwarded_values":[]},{"index":2,"name":null,"comb_delay_ns":1.0,"lut_count":null,"reg_count":0,"forwarded_values":[]}]},"systolic":null,"timing":{"c_slow_factor":1,"target_period_ns":8.0,"critical_path_ns":4.0,"retiming_weights":[],"buffers":[]}}\n' >"$TMP/unbal.json"
if "$LIFT" fpga throughput "$TMP/unbal.json" >"$TMP/fqu" 2>&1; then
  grep -q "qnet bottleneck stage1 is a slowest stage (critical-path stage1) ✓" "$TMP/fqu" \
    && pass "fpga throughput  (qnet bottleneck == critical-path stage)" \
    || { bad "fpga throughput: bottleneck cross-check wrong"; cat "$TMP/fqu"; }
else
  bad "fpga throughput on unbal failed"; cat "$TMP/fqu"
fi
# teeth: a stage slower than the offered rate must SATURATE (exit 1).
printf '{"schema":"aria-ir-json/v1","id":0,"name":"sat","ports":[],"clock_domains":[],"annotations":[{"kind":"clock_freq","value":"1000000000"}],"nodes":[],"pipeline":{"id":0,"num_stages":2,"latency":2,"initiation_interval":1,"flow_control":{"fc":"ready_valid"},"stages":[{"index":0,"name":null,"comb_delay_ns":2.0,"lut_count":null,"reg_count":0,"forwarded_values":[]},{"index":1,"name":null,"comb_delay_ns":0.5,"lut_count":null,"reg_count":0,"forwarded_values":[]}]},"systolic":null,"timing":{"c_slow_factor":1,"target_period_ns":1.0,"critical_path_ns":2.0,"retiming_weights":[],"buffers":[]}}\n' >"$TMP/sat.json"
if "$LIFT" fpga throughput "$TMP/sat.json" >"$TMP/fqs" 2>&1; then
  bad "fpga throughput accepted a saturated pipeline"; cat "$TMP/fqs"
else
  grep -q "SATURATED" "$TMP/fqs" && pass "fpga throughput teeth  (offered > stage rate → SATURATED, exit 1)" \
    || { bad "fpga throughput teeth: saturation not caught"; cat "$TMP/fqs"; }
fi

# T3 — the hard-vs-soft sweep self-test: both knees must land on the closed-form f*.
if bash "$ROOT/scripts/fpga-pipeline-sweep.sh" --check >"$TMP/fsw" 2>&1; then
  grep -q "both knees sit at the closed-form f\* = 250 MHz" "$TMP/fsw" \
    && pass "fpga sweep  (hard/soft knees both at f*=250MHz)" \
    || { bad "fpga sweep: knees off"; cat "$TMP/fsw"; }
else
  bad "fpga pipeline sweep --check failed"; cat "$TMP/fsw"
fi

# F1 — control-FSM extraction + M1 safety from the IR's own formal properties.
if "$LIFT" fpga check "$M/../fpga/tcp_ip.aria.json" >"$TMP/fc" 2>&1; then
  grep -q "FSM on register \`state\`" "$TMP/fc" \
    && grep -q "7 reachable" "$TMP/fc" \
    && grep -q "SAFE ✓" "$TMP/fc" \
    && pass "fpga check  (tcp_fsm: 7 states, state<=10 SAFE)" \
    || { bad "fpga check: wrong verdict"; cat "$TMP/fc"; }
else
  bad "fpga check failed (exit $?)"; cat "$TMP/fc"
fi
# teeth: an FSM that reaches an illegal state must be caught (VIOLATION, exit 1).
printf '{"schema":"aria-ir-json/v1","id":0,"name":"toggle","ports":[{"id":0,"value":10,"name":"go","ty":{"t":"bit"},"dir":"input","clock_domain":0}],"clock_domains":[],"annotations":[],"nodes":[{"id":1,"name":"state","kind":{"k":"register","ty":{"t":"uint","n":2},"clock_domain":0,"reset_value":{"e":"lit","lit":{"l":"uint","value":"0","width":2}},"enable":null,"next":{"e":"mux","cond":{"e":"ref","value":10},"true":{"e":"lit","lit":{"l":"uint","value":"3","width":2}},"false":{"e":"lit","lit":{"l":"uint","value":"0","width":2}}}}},{"id":2,"name":"p","kind":{"k":"formal_property","property":{"kind":"assert","temporal":{"tt":"always"},"expr":{"e":"binop","op":"le","lhs":{"e":"ref","value":1},"rhs":{"e":"lit","lit":{"l":"uint","value":"1","width":32}},"ty":{"t":"bit"}},"name":"safe"}}}],"timing":{}}\n' >"$TMP/badfsm.json"
if "$LIFT" fpga check "$TMP/badfsm.json" >"$TMP/fcb" 2>&1; then
  bad "fpga check accepted an FSM that reaches an illegal state"; cat "$TMP/fcb"
else
  grep -q "VIOLATION" "$TMP/fcb" && pass "fpga check teeth  (illegal state reached → VIOLATION, exit 1)" \
    || { bad "fpga check teeth: violation not caught"; cat "$TMP/fcb"; }
fi

# F3 — multi-register (product) FSM: a two-flag mutex arbiter whose mutual-exclusion
# safety is a CROSS-register property (`!(ns & ew)`). Exercises the bit-packed
# composite state, joint transition, and cross-register property eval.
if "$LIFT" fpga check "$M/../fpga/mutex_arbiter.aria.json" >"$TMP/f3" 2>&1; then
  grep -q "product of 2 registers" "$TMP/f3" \
    && grep -q "3 reachable" "$TMP/f3" \
    && grep -q "SAFE ✓" "$TMP/f3" \
    && pass "fpga check  (product FSM: ns/ew mutex, 3 states, never-both SAFE)" \
    || { bad "fpga check: product FSM wrong verdict"; cat "$TMP/f3"; }
else
  bad "fpga check product FSM failed (exit $?)"; cat "$TMP/f3"
fi
# teeth: arp_cache (81-bit composite datapath) must be SKIPPED, never refused/errored.
if grep -q "FSM refused" "$TMP/fc"; then
  bad "tcp_ip check refused a module (wide datapath should skip silently)"; cat "$TMP/fc"
else
  pass "fpga check  (wide datapath arp_cache skipped, 0 refused)"
fi

# F2 — sorry-free Lean proof of FSM safety (needs the Lean toolchain).
if have lean; then
  if "$LIFT" fpga prove "$M/../fpga/tcp_ip.aria.json" --emit "$TMP/tcp.gen.lean" >"$TMP/fp2" 2>&1; then
    grep -q "M3 PROVED sorry-free" "$TMP/fp2" && grep -q "1/1 obligation(s) proved sorry-free" "$TMP/fp2" \
      && pass "fpga prove  (tcp_fsm safety, sorry-free M3)" \
      || { bad "fpga prove: not sorry-free"; cat "$TMP/fp2"; }
  else
    bad "fpga prove failed (exit $?)"; cat "$TMP/fp2"
  fi
  # F3 — the product (multi-register) FSM's cross-register safety proven sorry-free.
  if "$LIFT" fpga prove "$M/../fpga/mutex_arbiter.aria.json" --emit "$TMP/mutex.gen.lean" >"$TMP/fp3f" 2>&1; then
    grep -q "M3 PROVED sorry-free" "$TMP/fp3f" && grep -q "1/1 obligation(s) proved sorry-free" "$TMP/fp3f" \
      && pass "fpga prove  (product FSM mutex, cross-register safety, sorry-free M3)" \
      || { bad "fpga prove: product FSM not sorry-free"; cat "$TMP/fp3f"; }
  else
    bad "fpga prove product FSM failed (exit $?)"; cat "$TMP/fp3f"
  fi
  # teeth: the unsafe FSM's safety theorem must NOT elaborate (M1, exit 1).
  if "$LIFT" fpga prove "$TMP/badfsm.json" --emit "$TMP/bad.gen.lean" >"$TMP/fp2b" 2>&1; then
    bad "fpga prove certified an unsafe FSM"; cat "$TMP/fp2b"
  else
    grep -q "did NOT elaborate" "$TMP/fp2b" && pass "fpga prove teeth  (unsafe FSM → proof red, exit 1)" \
      || { bad "fpga prove teeth: wrong failure"; cat "$TMP/fp2b"; }
  fi
  # D2 — FIFO occ ≤ depth proven sorry-free via emit_petri (survives pure loss).
  if "$LIFT" fpga prove "$M/../fpga/fifo_link.aria.json" --emit "$TMP/fifo.gen.lean" >"$TMP/fp3" 2>&1; then
    grep -q "occ ≤ depth 4 (survives the pure-loss leak)" "$TMP/fp3" \
      && grep -q "1/1 obligation(s) proved sorry-free" "$TMP/fp3" \
      && pass "fpga prove  (FIFO occ≤depth 4, sorry-free M3, survives loss)" \
      || { bad "fpga prove: FIFO bound not proved"; cat "$TMP/fp3"; }
  else
    bad "fpga prove (fifo) failed (exit $?)"; cat "$TMP/fp3"
  fi
else
  skip "fpga prove  (no lean toolchain)"
fi

# D1 — FIFO flow-safety: occ ≤ depth holds in every reachable marking (M1).
if "$LIFT" fpga check "$M/../fpga/fifo_link.aria.json" >"$TMP/fcf" 2>&1; then
  grep -q "FIFO \`q\` (depth 4 CDC 0→1)" "$TMP/fcf" \
    && grep -q "occ never exceeds 4" "$TMP/fcf" \
    && pass "fpga check  (CDC FIFO depth 4, occ≤depth SAFE)" \
    || { bad "fpga check: FIFO bound wrong"; cat "$TMP/fcf"; }
else
  bad "fpga check (fifo) failed (exit $?)"; cat "$TMP/fcf"
fi

# E1 — protocol equivalence: impl ≟ golden → EQUIVALENT (M1 product).
if "$LIFT" fpga equiv "$M/../fpga/protocol_impl.aria.json" "$M/../fpga/protocol_golden.aria.json" >"$TMP/fe" 2>&1; then
  grep -q "EQUIVALENT ✓" "$TMP/fe" && pass "fpga equiv  (impl ≟ golden → EQUIVALENT)" \
    || { bad "fpga equiv: wrong verdict"; cat "$TMP/fe"; }
else
  bad "fpga equiv (equivalent) failed (exit $?)"; cat "$TMP/fe"
fi
# teeth: a buggy reference (done→busy) must be caught as NOT EQUIVALENT (exit 1).
if "$LIFT" fpga equiv "$M/../fpga/protocol_impl.aria.json" "$M/../fpga/protocol_bug.aria.json" >"$TMP/feb" 2>&1; then
  bad "fpga equiv accepted a behaviourally-different design"; cat "$TMP/feb"
else
  grep -q "NOT EQUIVALENT" "$TMP/feb" && pass "fpga equiv teeth  (buggy ref → NOT EQUIVALENT + counterexample, exit 1)" \
    || { bad "fpga equiv teeth: divergence not caught"; cat "$TMP/feb"; }
fi
# E2 — the bisimulation certificate is sorry-free (needs the Lean toolchain).
if have lean; then
  if "$LIFT" fpga equiv "$M/../fpga/protocol_impl.aria.json" "$M/../fpga/protocol_golden.aria.json" --prove --emit "$TMP/eq.gen.lean" >"$TMP/fep" 2>&1; then
    grep -q "bisimulation: M3 PROVED sorry-free" "$TMP/fep" \
      && pass "fpga equiv --prove  (bisimulation certificate, sorry-free M3)" \
      || { bad "fpga equiv --prove: not sorry-free"; cat "$TMP/fep"; }
  else
    bad "fpga equiv --prove failed (exit $?)"; cat "$TMP/fep"
  fi
else
  skip "fpga equiv --prove  (no lean toolchain)"
fi

# S — the capstone: the WHOLE ladder on the two-chip serial link, one certificate.
if bash "$ROOT/scripts/serial-link-certify.sh" --check >"$TMP/scap" 2>&1; then
  grep -q "the serial protocol is CORRECT" "$TMP/scap" \
    && grep -q "PASS: all capstone axes certified" "$TMP/scap" \
    && pass "serial-link capstone  (safety ∧ equivalence ∧ timing ∧ loss → CORRECT)" \
    || { bad "serial-link capstone: incomplete"; cat "$TMP/scap"; }
else
  bad "serial-link capstone --check failed"; cat "$TMP/scap"
fi
# S2 — the QUANTUM capstone (LE4): Kraus CPTP proof ∧ Lean fidelity law ∧ PRISM knee
# ∧ SSA sim all agree on F=1−p/2 for the depolarizing error model. One certificate.
if bash "$ROOT/scripts/depolarizing-certify.sh" --check >"$TMP/qcap" 2>&1; then
  grep -q "depolarized fidelity ≥ τ" "$TMP/qcap" \
    && grep -q "PASS: LE4 depolarizing capstone certified" "$TMP/qcap" \
    && pass "depolarizing capstone (LE4)  (Kraus-CPTP ∧ Lean F=1−p/2 ∧ PRISM ∧ SSA → CERTIFIED)" \
    || { bad "depolarizing capstone: incomplete"; cat "$TMP/qcap"; }
else
  bad "depolarizing capstone --check failed"; cat "$TMP/qcap"
fi
# S2b — the QUANTUM capstone (LE4) for the other two standard channels: amplitude damping
# (T₁, survival 1−γ) and phase damping (T₂, coherence 1−λ), each Kraus CPTP proof ∧ Lean law
# ∧ PRISM steady-state ∧ SSA sim. With S2 this closes all 3 standard single-qubit error models.
if bash "$ROOT/scripts/damping-certify.sh" --check >"$TMP/dcap" 2>&1; then
  grep -q "both error models CERTIFIED" "$TMP/dcap" \
    && grep -q "PASS: LE4 amplitude/phase-damping capstone certified" "$TMP/dcap" \
    && pass "amplitude/phase-damping capstone (LE4)  (Kraus-CPTP ∧ Lean 1−γ/1−λ ∧ PRISM ∧ SSA → CERTIFIED)" \
    || { bad "damping capstone: incomplete"; cat "$TMP/dcap"; }
else
  bad "damping capstone --check failed"; cat "$TMP/dcap"
fi
# S2c — the per-ALGORITHM depth fidelity floor (LE4): the single-gate depolarizing law lifted
# to a depth-G circuit, F_G(p)=(1+(1−p)^G)/2, instantiated at G=3 for the circulant CyclicShift
# solver. Lean depth theorem ∧ single-gate consistency ∧ threshold knee ∧ independent Monte-Carlo.
if bash "$ROOT/scripts/depth-certify.sh" --check >"$TMP/depthcap" 2>&1; then
  grep -q "fidelity floor F_3(p)=(1+(1−p)^3)/2 is CERTIFIED" "$TMP/depthcap" \
    && grep -q "PASS: LE4 depth fidelity floor certified" "$TMP/depthcap" \
    && pass "depth fidelity floor (LE4)  (circulant G=3: Lean F_G=(1+(1−p)^G)/2 ∧ consistency ∧ MC → CERTIFIED)" \
    || { bad "depth capstone: incomplete"; cat "$TMP/depthcap"; }
else
  bad "depth capstone --check failed"; cat "$TMP/depthcap"
fi
# S2d — the multi-qubit WIDTH fidelity floor (LE4): single-qubit channels on each factor of an
# n-qubit register are CPTP and the fidelity factorizes across qubits, F=(1−p/2)^n, instantiated
# n=3 for the circulant register. Lean tensor CPTP+factorization ∧ consistency ∧ threshold ∧ MC.
if bash "$ROOT/scripts/tensor-certify.sh" --check >"$TMP/tencap" 2>&1; then
  grep -q "width fidelity floor (1−p/2)^3 is CERTIFIED" "$TMP/tencap" \
    && grep -q "PASS: LE4 tensor width fidelity floor certified" "$TMP/tencap" \
    && pass "tensor width fidelity floor (LE4)  (circulant n=3: Lean tensor-CPTP ∧ (1−p/2)^n ∧ MC → CERTIFIED)" \
    || { bad "tensor capstone: incomplete"; cat "$TMP/tencap"; }
else
  bad "tensor capstone --check failed"; cat "$TMP/tencap"
fi
# S3 — the delivery-cliff sweep: empirical knee must match the closed-form p*.
if bash "$ROOT/scripts/serial-link-sweep.sh" --check >"$TMP/ssw" 2>&1; then
  grep -q "empirical delivery cliff ≈ closed-form p\*" "$TMP/ssw" \
    && pass "serial-link sweep  (delivery roll-off toward p* ≈ 0.882)" \
    || { bad "serial-link sweep: knee off"; cat "$TMP/ssw"; }
else
  bad "serial-link sweep --check failed"; cat "$TMP/ssw"
fi

# ---------------------------------------------------------------------------- #
sect "M3 — prove (Lean, sorry-free)"
if have lean; then
  for f in mcl dock mission resource link; do
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
