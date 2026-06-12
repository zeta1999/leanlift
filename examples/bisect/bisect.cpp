// Example source (C++): the bisection METHOD — bracket sqrt(n) to within eps.
//
//   bisect_sqrt(n, eps): halve [lo, hi] (from [0, 65535]) keeping
//     lo*lo <= n < (hi+1)^2, until hi - lo <= eps; return lo, which then
//     satisfies  lo*lo <= n < (lo + eps + 1)^2.  (eps = 0  ⇒  exact isqrt.)
//
// The new ingredient over isqrt is ε-termination: the loop stops on bracket
// width, not exactness. No overflow: mid <= hi <= 65535 so mid*mid < 2^32.
//
// Mirrors examples/rust-kernels/src/lib.rs::bisect_sqrt byte-for-byte.

#include <cstdint>

extern "C" std::uint32_t bisect_sqrt(std::uint32_t n, std::uint32_t eps) noexcept {
    std::uint32_t lo = 0, hi = 65535;
    while (hi - lo > eps) {
        std::uint32_t mid = (lo + hi + 1) / 2;
        if (mid * mid <= n) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    return lo;
}
