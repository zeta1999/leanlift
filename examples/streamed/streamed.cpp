// Example source for `lift verify`: the clamped floor-division vesting ramp,
// shared across the streaming-vesting thread (Day 36–44 of the spike).
//
//   streamed(deposit, start, stop, t) =
//       0                                        if t <= start
//       deposit                                  if t >= stop
//       deposit * (t - start) / (stop - start)   otherwise
//
// The middle case computes `deposit * (t - start)` in u64, which WRAPS silently
// on overflow — C/C++ unsigned arithmetic is modular. The engine's differential
// test against the checked Lean model exposes exactly that: on the safe domain
// the two agree bit-for-bit; where the product reaches 2^64 the C++ result is a
// wrapped (wrong) number while Lean reports OVERFLOW.
//
// The leanlift oracle (SPEC §6) compiles this to a shared library and calls
// `streamed` through its `extern "C"` ABI via dlopen — so the function carries
// C linkage and a fixed, unmangled signature.

#include <cstdint>

extern "C" std::uint64_t streamed(std::uint64_t deposit,
                                  std::uint64_t start,
                                  std::uint64_t stop,
                                  std::uint64_t t) noexcept {
    if (t <= start) return 0;
    if (stop <= t)  return deposit;
    return deposit * (t - start) / (stop - start);  // u64 multiply WRAPS on overflow
}
