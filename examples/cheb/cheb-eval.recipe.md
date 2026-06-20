# Proof recipe — `cheb-eval` (L1)

The QLSS/QSVT inversion-polynomial kernel, lifted and differentially validated.
`eval_chebyshev` (Clenshaw) is the float path, so the honest ceiling is **L1**
(bit-exact differential conformance) — native `Float` is opaque to Aeneas, so
there is no L3 here. This is `LEAN_ERROR_PLAN.md` step **LE1-a**.

## 1. Source (Rust — `quantum-core/src/linalg/chebyshev.rs`, fixed to 4 coeffs)

```rust
pub fn eval_chebyshev(coeffs: &[f64], x: f64) -> f64 {
    // ... specialized to coeffs = [c0, c1, c2, c3]:
    let mut b1 = 0.0; let mut b2 = 0.0;
    for &c in [c3, c2, c1] {           // coeffs.iter().skip(1).rev()
        let b0 = 2.0 * x * b1 - b2 + c;
        b2 = b1; b1 = b0;
    }
    c0 + x * b1 - b2                   // = Σ_{k=0}^3 c_k T_k(x)
}
```

The oracle is the op-for-op C++ `double` mirror `examples/cheb/cheb_eval.cpp`
(`-ffp-contract=off`, so no FMA collapses `2*x*b1`). Only `+ - *`, so the two
agree bit-for-bit with the Lean model.

## 2. Model (Lean candidate, `examples/cheb/ChebEval.lean`, verbatim)

```lean
def cheb_eval4 (c0 c1 c2 c3 x : Float) : Float :=
  let b1₀ : Float := 0.0
  let b2₀ : Float := 0.0
  let b0a := 2.0 * x * b1₀ - b2₀ + c3
  let b2a := b1₀
  let b1a := b0a
  let b0b := 2.0 * x * b1a - b2a + c2
  let b2b := b1a
  let b1b := b0b
  let b0c := 2.0 * x * b1b - b2b + c1
  let b2c := b1b
  let b1c := b0c
  c0 + x * b1c - b2c
```

(Native binary64; the Clenshaw fold unrolled three steps.)

## 3. Differential result (L1)

- `lift verify cheb-eval` → **236/236 vectors conform, bit-exact** (Lean ==
  C++), 0 mismatch, seed `0x1ea511f720260612`.
- **Postcondition (L1 analysis):** Clenshaw cross-checked against the direct
  Chebyshev sum `Σ c_k T_k(x)` (`T_k` by the recurrence), holds on **236/236**:
  `|Clenshaw − Σ c_k T_k(x)| ≤ 16u·Σ|c_k T_k|`, `u = 2⁻⁵³`.

## 4. Certificate

- level: **L1 conformant** (bit-exact on the safe domain)
- report: `cheb-report.json` (`"level": "L1_conformant"`, `"conformant": true`)
- ceiling: **L1** — `Float` is opaque (no Aeneas L3); the differential oracle is
  the trust anchor. The *classical* correctness of the recurrence (Clenshaw ≡
  direct sum) is what the postcondition certifies empirically.

Run: `lift verify cheb-eval` (bit-exact) — part of `tests/run.sh`.
