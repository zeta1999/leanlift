// The float32 twin of fadd.cpp: leanlift's IEEE-754 binary32 differential path.
//
//   fadd32(a, b) = a + b   over f32
//
// Lean's native `Float32` (binary32) agrees bit-for-bit with C++ `float`
// (compiled -ffp-contract=off). Same code as fadd.cpp but at single precision —
// running both on the same logical inputs exposes the real f32-vs-f64 rounding
// difference. Mirrors examples/fadd/Fadd32.lean.

extern "C" float fadd32(float a, float b) noexcept {
    return a + b;
}
