// Phase-1 float smoke for leanlift's IEEE-754 differential path.
//
//   fadd(a, b) = a + b   over f64
//
// The whole point is bit-exactness: C++ `double` (compiled `-ffp-contract=off`)
// and Lean's native binary64 `Float` agree bit-for-bit on `+`. The oracle and
// the Lean runner exchange IEEE bit patterns; NaN and -0.0 are canonicalized.
//
// Mirrors examples/fadd/Fadd.lean.

extern "C" double fadd(double a, double b) noexcept {
    return a + b;
}
