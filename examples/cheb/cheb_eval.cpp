// cheb_eval4 — Clenshaw evaluation of a degree-3 Chebyshev series, the ORACLE.
//
//   cheb_eval4(c0,c1,c2,c3, x) = Σ_{k=0}^{3} c_k · T_k(x)
//
// computed by the Clenshaw recurrence (no explicit T_k), the exact arithmetic of
// `quantum-core/src/linalg/chebyshev.rs::eval_chebyshev` specialized to a
// fixed 4-coefficient series. The Rust loop iterates the tail coefficients
// [c3, c2, c1] in reverse:
//
//   b1 = 0; b2 = 0;
//   for c in [c3, c2, c1]:  b0 = 2*x*b1 - b2 + c;  b2 = b1;  b1 = b0;
//   result = c0 + x*b1 - b2;
//
// Unrolled below op-for-op. Only `+ - *` over IEEE-754 binary64, so Lean's
// native `Float` matches this bit-for-bit (compiled -ffp-contract=off, no FMA
// collapses 2*x*b1). Mirrors examples/cheb/ChebEval.lean.

extern "C" double cheb_eval4(double c0, double c1, double c2, double c3,
                             double x) noexcept {
    double b1 = 0.0, b2 = 0.0, b0;
    // c = c3
    b0 = 2.0 * x * b1 - b2 + c3;
    b2 = b1;
    b1 = b0;
    // c = c2
    b0 = 2.0 * x * b1 - b2 + c2;
    b2 = b1;
    b1 = b0;
    // c = c1
    b0 = 2.0 * x * b1 - b2 + c1;
    b2 = b1;
    b1 = b0;
    return c0 + x * b1 - b2;
}
