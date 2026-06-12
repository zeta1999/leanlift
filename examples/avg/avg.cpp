// Example source: the integer average — the classic midpoint-overflow bug.
//
//   avg(a, b) = (a + b) / 2
//
// In u32, `a + b` wraps mod 2^32 (uint32_t is unsigned int; the sum stays
// 32-bit, no promotion to a wider type). So for large a, b the C++ result is a
// wrapped (wrong) value — the same bug that lurked in binary-search midpoints
// for years. The checked Lean model reports OVERFLOW where a + b >= 2^32; the
// differential test surfaces exactly that boundary.
//
// Different shape from `streamed`: 2 args, u32 — exercises the engine's
// signature generalization (any arity / integer width).

#include <cstdint>

extern "C" std::uint32_t avg(std::uint32_t a, std::uint32_t b) noexcept {
    return (a + b) / 2;  // a + b WRAPS mod 2^32 on overflow
}
