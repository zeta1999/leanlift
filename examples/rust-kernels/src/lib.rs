//! Numerical kernels for leanlift proof examples.

/// Clamped floor-division vesting ramp (the streaming-vesting kernel).
///
///   streamed(deposit, start, stop, t) =
///       0                                        if t <= start
///       deposit                                  if t >= stop
///       deposit * (t - start) / (stop - start)   otherwise
///
/// `deposit * (t - start)` can overflow u64; the no-overflow side-condition
/// `deposit*(t-start) < 2^64` is what `streamed_bounded` carries as a premise.
pub fn streamed(deposit: u64, start: u64, stop: u64, t: u64) -> u64 {
    if t <= start {
        return 0;
    }
    if t >= stop {
        return deposit;
    }
    deposit * (t - start) / (stop - start)
}

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

/// Bisection method: bracket `sqrt(n)` to within `eps`. Halves the interval
/// `[lo, hi]` (initially `[0, 65535]`), preserving `lo*lo <= n < (hi+1)^2`, until
/// the bracket width `hi - lo <= eps`. Returns `lo`, which then satisfies the
/// ε-guarantee `lo*lo <= n < (lo + eps + 1)^2` (with `eps = 0` this is `isqrt`).
///
/// This is the first numerical *method* (vs. the `isqrt` kernel): the new
/// ingredient is ε-termination — the loop stops on bracket width, not exactness.
pub fn bisect_sqrt(n: u32, eps: u32) -> u32 {
    let mut lo: u32 = 0;
    let mut hi: u32 = 65535;
    while hi - lo > eps {
        let mid = (lo + hi + 1) / 2;
        if mid * mid <= n {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}
