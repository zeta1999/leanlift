//! Numerical kernels for leanlift proof examples.

/// Per-place Petri firing: the successor token count `m - pre + post` at one
/// place. This is leanlift's OWN substrate — a verbatim mirror of
/// `src/models/ir.rs::fire_place`, the scalar body every marking update reduces
/// to. The dogfood (PLAN-verification §V3): Charon+Aeneas extracts THIS to Lean
/// and `examples/models/FireProofs.lean` proves it sorry-free against the
/// abstract theory in `lean/LeanLift/Models/Petri.lean` (`fire_le`,
/// `le_preserved`) — leanlift certifying its own kernel with its own pipeline.
///
/// PRECONDITION (enabled): `pre <= m`, so the `u32` subtraction never underflows;
/// with `post <= pre` the `+ post` never overflows (result <= m).
pub fn fire_place(m: u32, pre: u32, post: u32) -> u32 {
    m - pre + post
}

/// Admit a message into a K-bounded buffer (the link protocol's arrival
/// arithmetic, `examples/models/link.model.toml`): occupancy rises by one unless
/// the buffer is full. The CODE mirror of the model's `buf ≤ K` safety invariant
/// — Charon+Aeneas extracts it and `examples/models/BufferProofs.lean` proves
/// (L3, PLAN-perf-demo): admit never exceeds K (so the `u32` add never overflows).
pub fn admit(buf: u32, k: u32) -> u32 {
    if buf < k {
        buf + 1
    } else {
        buf
    }
}

/// Release a message from the buffer on delivery: occupancy falls by one unless
/// already empty. Proved (L3): never underflows, never increases.
pub fn release(buf: u32) -> u32 {
    if buf > 0 {
        buf - 1
    } else {
        buf
    }
}

/// One RTA interference term — `⌈r/tj⌉·cj` — the body of the response-time
/// recurrence (a verbatim mirror of `src/models/rt.rs::term`). Charon+Aeneas
/// extracts it and `examples/models/RtaProofs.lean` proves it equals the spec
/// `((r+tj−1)/tj)·cj` (the DEDUCTIVE, unbounded companion to the R2 Kani proof);
/// monotonicity in `r` — what makes the RTA fixed point the true WCRT — follows
/// from the spec as a Nat lemma. PRECONDITION: tj ≥ 1, no u32 overflow.
pub fn rta_term(r: u32, cj: u32, tj: u32) -> u32 {
    ((r + tj - 1) / tj) * cj
}

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
