// Example source (C++): 1D optimization — GOLDEN-SECTION SEARCH.
//
//   gss(a, b, tol): minimize the unimodal objective  f(x) = (x-3)^2 + 1
//     on the bracket [a, b] by golden-section search. Each step shrinks the
//     bracket by the golden ratio, keeping the minimizer enclosed, until the
//     width  b - a <= tol;  return the bracket midpoint (a + b)/2.
//
// Embedded/numerical style: a BOUNDED loop (≤100 steps — 0.618^100 ≈ 1e-21 of
// the initial width, so tol is always reached first), only `+ - * /` and
// `sqrt`, no transcendentals. The irrational golden constants are *computed*
// from sqrt(5) so C++ `double` and the Lean `Float` model share the exact bits
// (a truncated decimal literal would not). Compiled `-ffp-contract=off`.
//
// Mirrors examples/opt/Gss.lean op-for-op.

#include <cmath>

extern "C" double gss(double a, double b, double tol) noexcept {
    const double s5 = std::sqrt(5.0);
    const double invphi = (s5 - 1.0) / 2.0;   // 1/φ  ≈ 0.6180339887
    const double invphi2 = (3.0 - s5) / 2.0;  // 1/φ² ≈ 0.3819660113
    for (int i = 0; i < 100; ++i) {
        double h = b - a;
        if (h <= tol) break;                  // bracket narrow enough
        double c = a + invphi2 * h;
        double d = a + invphi * h;
        double fc = (c - 3.0) * (c - 3.0) + 1.0;
        double fd = (d - 3.0) * (d - 3.0) + 1.0;
        if (fc < fd) {
            b = d;                            // minimum in [a, d]
        } else {
            a = c;                            // minimum in [c, b]
        }
    }
    return (a + b) / 2.0;
}
