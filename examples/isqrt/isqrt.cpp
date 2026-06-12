// Example source (C++): integer square root over u32 — the first kernel with a
// LOOP and a real numerical postcondition.
//
//   isqrt(n) = the largest r with r*r <= n     (equivalently r*r <= n < (r+1)^2)
//
// Binary search bounded by sqrt(u32::MAX) = 65535, so `mid*mid <= 65535^2 < 2^32`
// never overflows u32. There is no overflow-divergence class here; the point is
// the postcondition, which the engine checks empirically per vector (L1) and which
// the Rust path proves as a theorem (L3, see docs/PLAN-proofs.md).
//
// Mirrors examples/rust-kernels/src/lib.rs::isqrt byte-for-byte.

#include <cstdint>

extern "C" std::uint32_t isqrt(std::uint32_t n) noexcept {
    std::uint32_t lo = 0, hi = 65535;
    while (lo < hi) {
        std::uint32_t mid = (lo + hi + 1) / 2;
        if (mid * mid <= n) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    return lo;
}
