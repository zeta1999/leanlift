// Fresh example source (no hand-written or extracted Lean reference): a 2-term
// dot product.
//
//   dot2(a, b, c, d) = a*b + c*d
//
// In u32 every step wraps mod 2^32 — the two products and the sum are all
// overflow points. The checked Lean model the LLM must produce fails at the
// first step that leaves range; C++ wraps. Since a*b + c*d >= a*b and >= c*d,
// the model fails exactly when the true (wide) value `a*b + c*d` reaches 2^32 —
// which is the declared-overflow predicate the comparator checks.
//
// This exercises the LLM front-end on a function the engine has never seen:
// nested checked binds (two muls feeding an add), 4 args, u32.

#include <cstdint>

extern "C" std::uint32_t dot2(std::uint32_t a, std::uint32_t b,
                              std::uint32_t c, std::uint32_t d) noexcept {
    return a * b + c * d;  // u32: each * and the + WRAP on overflow
}
