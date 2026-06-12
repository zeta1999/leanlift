// Example source (C++): the rounding core of float casts, parametric over the
// mantissa width — covering fp8 through f64 with ONE function.
//
//   quantize_rne(prec, n) = round the integer n to the nearest value with `prec`
//   mantissa bits below the leading bit, round-to-nearest-ties-to-even (RNE).
//
// The format IS the `prec` parameter:
//     prec = 2  fp8 E5M2     prec = 10  fp16
//     prec = 3  fp8 E4M3     prec = 23  f32
//     prec = 7  bf16         prec = 52  f64
//
// This is exactly what casting to that float does to the significand. Integer
// inputs stay in the normal range (exponent/subnormal/NaN encoding is the next
// step — see docs/float-formats.md). n is u64 so f32/f64 rounding is genuinely
// exercised (small n is exact at high prec, large n rounds).
//
// Quantization error is bounded: |q - n| <= ulp/2 = 2^(e-prec)/2 with
// e = floor(log2 n) — checked empirically per vector (L1).
//
// Mirrors examples/quant/Quant.lean::qrne byte-for-byte.

#include <cstdint>

extern "C" std::uint64_t quantize_rne(std::uint8_t prec_, std::uint64_t n) noexcept {
    std::uint64_t prec = prec_;
    if (n == 0) return 0;
    std::uint64_t e = 0;
    while (((std::uint64_t)1 << (e + 1)) <= n) e++;   // e = floor(log2 n)
    if (e <= prec) return n;                          // already representable
    std::uint64_t shift = e - prec;
    std::uint64_t step = (std::uint64_t)1 << shift;   // ulp in this binade
    std::uint64_t low = (n >> shift) << shift;        // round toward zero
    std::uint64_t rem = n - low;
    std::uint64_t half = step >> 1;
    if (rem > half) return low + step;
    if (rem < half) return low;
    // tie: round to even mantissa
    return (((low >> shift) & 1ull) == 0) ? low : low + step;
}
