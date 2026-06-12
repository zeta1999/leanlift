# leanlift

Lift a function into a **Lean 4** model and **prove it's the same function** by
**bit-exact differential execution**. See [`SPEC.md`](./SPEC.md) for the full
design. The trust model: *LLM proposes, algorithm disposes* — a candidate Lean
translation is never trusted; the differential oracle and the Lean kernel
discharge or refute it.

## Status — spine + sound Rust path + LLM C++ front-end

The validation spine is complete end to end, the engine is generic over the
signature (any arity / integer width), and **all three front-ends are wired**:

```
lift verify streamed       # C++    hand-written candidate, vs C++ oracle
lift verify avg            # C++    (a+b)/2, the midpoint-overflow bug
lift verify rust-streamed  # Rust   SOUND: Charon+Aeneas extract Lean from Rust
lift verify cpp-streamed   # C++    LLM: claude -p translates streamed.cpp → Lean
lift verify cpp-dot2       # C++    LLM: a fresh kernel (a*b + c*d), no reference
lift verify go-avg         # Go     LLM: Go oracle (go build), Go also wraps
lift verify sol-dot2       # Solidity LLM: EVM oracle (forge), unchecked overflow
```

Oracle per language (SPEC §6): **C++** `clang++` + typed runner; **Go**
`go build` + typed runner; **Solidity** a `forge` script that replays vectors
through forge's in-process EVM (calldata in, return data out; a revert becomes the
`OVERFLOW` token). Go (installed) and Foundry (`forge`, installed) are needed for
those two.

- **Sound Rust path** (`rust-streamed`): candidate Lean is extracted *from Rust*
  by Charon+Aeneas (no hand-writing). Needs them built — run
  `scripts/build_aeneas.sh` (~20–40 min, into `~/work/_verif-tools`; override
  with `LEANLIFT_AENEAS`).
- **LLM C++ path** (`cpp-*`): `claude -p` translates the C++ against the audited
  `LeanLift.Checked` library; the engine runs the candidate, and on a typecheck
  error or difftest mismatch feeds a *structured* failure (Lean error, or the
  minimal counterexample) back for repair — bounded by `max_iters`. Responses are
  content-addressed under `.leanlift-cache/`, so reproduced runs don't re-bill.
  *LLM proposes, algorithm disposes.*

```
  level: L1 conformant/450  (bit-exact on the safe domain)
  conform : 410   declared: 40   mismatch: 0
  coverage: clamp-low=150 clamp-high=138 ramp=162
  divergence (declared, overflow class):
    lean: …561633 => OVERFLOW
    cpp : …561633 => 30861823284991  (silently wrapped)
```

For `streamed` the 40/450 divergences are the **declared** `deposit*(t-start) ≥
2^64` overflow class — C++ wraps, the checked Lean model fails — the same
boundary the original spike found four independent ways. A wrong candidate is
caught: it produces *unexplained* mismatches, drops to L0, and exits nonzero.
`--lean <candidate.lean>` overrides an example's built-in candidate (the hook the
LLM front-end writes to). Run `tests/run.sh` for the positive + negative suite.

## The pieces (mapped to SPEC §4)

| path | role |
|---|---|
| `examples/{streamed,avg}/*.cpp` | source kernels; `extern "C"` ABI for the oracle |
| `examples/{streamed,avg}/*.lean` | the **candidate** models + vector runners (untrusted) |
| `lean/LeanLift/Checked.lean` | audited support library: checked-`UInt` `Res` monad (the `wrap`-vs-`fail` semantics) |
| `src/sig.rs` | machine-integer types + function signatures |
| `src/lang.rs` | source languages (C++, Go, Solidity) |
| `src/frontend.rs` | how a candidate is obtained: prewritten, Charon+Aeneas, or LLM |
| `src/harness.rs` | LLM front-end: `claude -p` translate + propose→difftest→repair loop |
| `src/vectors.rs` | deterministic vector generation (edge / safe / overflow) |
| `src/oracle.rs` | C++/Go oracle: compile source + a generated typed runner |
| `src/oracle_sol.rs` | Solidity oracle: a `forge` script over forge's in-process EVM |
| `src/leanrt.rs` | run the candidate (support-lib `lean --run`, or Aeneas `lake env lean`) |
| `src/compare.rs` | bit-exact comparator + profile-driven divergence classifier |
| `src/report.rs` | L0/L1 verdict, human report, `report.json` |
| `src/prove.rs` | L3 path: assemble model + theorems, certify sorry-free, recipe |
| `src/examples.rs` | built-in example registry |
| `src/main.rs` | the `lift` CLI |
| `scripts/build_aeneas.sh` | build Charon+Aeneas from source (the sound Rust path) |

## Build & run

```bash
cargo build --release
./target/release/lift verify streamed --out report.json
./target/release/lift verify rust-streamed   # sound path (needs Aeneas built)
./tests/run.sh                               # positive + negative + sound suite
```

The engine compiles the Lean support library to `.olean` on first run.

## Proof: L3 (`lift prove`)

Beyond L1 conformance, `lift prove` discharges a theorem on the extracted model:

```
lift prove rust-streamed   # streamed_low/high/bounded/mono
lift prove rust-isqrt       # isqrt_correct: r·r ≤ n < (r+1)² over the extracted LOOP
  → level: L3 proved  (Lean theorems closed, sorry-free)
    axioms: propext, Classical.choice, Quot.sound   # no sorryAx → kernel-checked
```

The Rust sources live in-repo at `examples/rust-kernels/src/lib.rs`; the proof
obligations are hand-written fragments wired per example via `proof_frag` in
`src/examples.rs` (`examples/*/​*Proofs.lean`). `isqrt_correct` is proved over the
Aeneas-extracted binary-search loop with `loop.spec_decr_nat` (measure `hi-lo`,
invariant `lo²≤n ∧ n<(hi+1)² ∧ lo≤hi ∧ hi≤65535`).

It runs Charon+Aeneas to extract the `Result Std.U64` model, prepends it to a
proven theorem fragment (`examples/streamed/StreamedProofs.lean`), elaborates via
`lake env lean`, and certifies the result is **sorry-free** (`#print axioms`
shows no `sorryAx`). It emits a worked `*.recipe.md` (source → model → obligations
→ certificate) and a `proof.json`. A false theorem fails to elaborate and exits
nonzero — the Lean kernel is the gate (the agent-assisted *closing* of harder
goals is the generalization).

`streamed_bounded` is proved **under** the no-overflow hypothesis
`deposit*(t-start) ≤ U64.max` — the exact side-condition the differential test
discovered empirically. Same boundary, now a proof premise.

## Next

The proof procedure and the path toward a numerical algorithm (isqrt → bisection
→ float error-bounds) are planned in
[`docs/PLAN-proofs.md`](docs/PLAN-proofs.md). Also pending: a proof kernel for the
support library (so LLM/hand candidates carry proofs too), signed/float types,
structs/arrays, annotation ingestion → Contract IR (SPEC §7).
