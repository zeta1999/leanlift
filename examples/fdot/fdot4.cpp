// fdot4 — a 4-term f32 dot product, the ORACLE summing left-to-right.
//
//   fdot4(a0..a3, b0..b3) = ((a0*b0 + a1*b1) + a2*b2) + a3*b3   over f32
//
// The Lean model (examples/fdot/Fdot4.lean) sums the SAME four rounded products
// in PAIRWISE/tree order  (a0*b0 + a1*b1) + (a2*b2 + a3*b3).  Reassociating a
// floating-point reduction changes the rounding, so the two are NOT bit-identical
// in general — but for the well-scaled, all-positive vectors they agree to within
// a few ULPs. This is the canonical "validate a reordered / vectorized reduction
// against a serial oracle" case: it FAILS under `--float-tol exact` and PASSES
// under `--float-tol rel:1e-6`, with the differences reported as tolerance
// divergences. Compiled -ffp-contract=off so no FMA collapses a*b+c.

extern "C" float fdot4(float a0, float a1, float a2, float a3,
                       float b0, float b1, float b2, float b3) noexcept {
    float r = a0 * b0;
    r += a1 * b1;
    r += a2 * b2;
    r += a3 * b3;
    return r;
}
