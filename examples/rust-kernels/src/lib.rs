//! Numerical kernels for leanlift proof examples.

/// Integer square root over u32: the largest `r` with `r*r <= n`.
///
/// Binary search bounded by `sqrt(u32::MAX) = 65535`, so `mid*mid` is always
/// `<= 65535^2 < 2^32` and never overflows u32. Postcondition:
/// `r*r <= n  &&  n < (r+1)*(r+1)`  (the latter checked in wider arithmetic).
pub fn isqrt(n: u32) -> u32 {
    let mut lo: u32 = 0;
    let mut hi: u32 = 65535;
    while lo < hi {
        let mid = (lo + hi + 1) / 2;
        if mid * mid <= n {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}
