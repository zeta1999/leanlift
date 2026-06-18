//! Deterministic differential-test vector generation (SPEC §6 `vectors/`).
//!
//! A "vector" is one input tuple for the kernel under test, held as `u64`s (each
//! within its argument's width). Generation is per-example for now — the input
//! domain and the "deliberate overflow" class depend on the function's
//! semantics; SPEC §7's Contract IR is what eventually drives this generically.
//! All generators are deterministic (fixed seed, no wall clock), so a passing
//! run is reproducible.

/// One generated input tuple (arguments in declaration order, each `< 2^width`).
#[derive(Clone, Debug)]
pub struct Vector {
    pub args: Vec<u64>,
}

impl Vector {
    pub fn new(args: Vec<u64>) -> Vector {
        Vector { args }
    }
    /// Normalized join key: the arguments, space-separated decimals — identical
    /// to what both the oracle runner and the Lean runner echo back.
    pub fn key(&self) -> String {
        self.args
            .iter()
            .map(u64::to_string)
            .collect::<Vec<_>>()
            .join(" ")
    }
}

/// A tiny deterministic PRNG (SplitMix64) — no crates, no wall-clock seeding.
pub struct SplitMix64(pub u64);
impl SplitMix64 {
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// Uniform in `[lo, hi]` inclusive.
    pub fn range(&mut self, lo: u64, hi: u64) -> u64 {
        debug_assert!(lo <= hi);
        lo + self.next() % (hi - lo + 1)
    }
}

/// The shared seed (the analogue of the spike generator's fixed Python seed).
pub const SEED: u64 = 0x1EA5_11F7_2026_0612;

/// Encode an `f64` as the `u64` IEEE-754 bit pattern a float Vector arg carries.
/// (The whole float path moves bit patterns so the integer join-key/compare
/// machinery is reused unchanged.)
pub fn f64_bits(x: f64) -> u64 {
    x.to_bits()
}

/// A finite `f64` drawn from `rng`, uniform in `[lo, hi]` (full mantissa
/// randomness via the 53-bit quotient).
fn rand_f64(rng: &mut SplitMix64, lo: f64, hi: f64) -> f64 {
    let u = (rng.next() >> 11) as f64 / (1u64 << 53) as f64; // [0,1)
    lo + u * (hi - lo)
}

/// Encode an `f32` as its 32-bit IEEE pattern, carried in the `u64` Vector arg.
pub fn f32_bits(x: f32) -> u64 {
    x.to_bits() as u64
}

/// `fadd32(a, b) = a + b` over **f32** — the float32 twin of `fadd`, proving the
/// `Float32` path (Lean binary32 ≡ C++ `float`, bit-exact). Same logical inputs
/// as `fadd` so a side-by-side run shows the real f32-vs-f64 divergence.
pub fn fadd32_vectors() -> Vec<Vector> {
    let mut v = Vec::new();
    let mut push = |a: f32, b: f32| v.push(Vector::new(vec![f32_bits(a), f32_bits(b)]));
    for (a, b) in [
        (0.0f32, 0.0),
        (1.0, 2.0),
        (-1.0, 1.0),
        (0.1, 0.2),       // f32 rounding differs from f64
        (1e7, 1.0),       // 1.0 lost below the f32 ulp at 1e7
        (3.1415927, 2.7182817),
        (-0.0, 0.0),
    ] {
        push(a, b);
    }
    let mut rng = SplitMix64(SEED);
    for _ in 0..200 {
        let a = (rand_f64(&mut rng, -1e6, 1e6)) as f32;
        let b = (rand_f64(&mut rng, -1e6, 1e6)) as f32;
        push(a, b);
    }
    v
}

/// `fdot4(a0..a3, b0..b3)` — a 4-term f32 dot product. Args travel as the eight
/// f32 bit patterns a0 a1 a2 a3 b0 b1 b2 b3. The vectors are **all-positive and
/// well-scaled** (factors in [0.1, 10]), so the products are positive and the
/// reassociation error between the oracle's left-to-right sum and the model's
/// pairwise sum is bounded by a few ULPs — bit-exact on many inputs, a small
/// `--float-tol` divergence on the rest, never catastrophic cancellation.
pub fn fdot4_vectors() -> Vec<Vector> {
    let mut v = Vec::new();
    let mut push = |a: [f32; 4], b: [f32; 4]| {
        let mut bits = Vec::with_capacity(8);
        bits.extend(a.iter().map(|&x| f32_bits(x)));
        bits.extend(b.iter().map(|&x| f32_bits(x)));
        v.push(Vector::new(bits));
    };
    // Hand vectors: small integers are exact (bit-exact, Conform); fractional and
    // wide-magnitude (still positive) exercise the reassociation rounding.
    push([1.0, 2.0, 3.0, 4.0], [1.0, 1.0, 1.0, 1.0]); // = 10, exact both orders
    push([0.1, 0.2, 0.3, 0.4], [0.5, 0.5, 0.5, 0.5]);
    push([1.5, 2.5, 3.5, 4.5], [2.5, 1.5, 0.5, 3.5]);
    push([100.0, 0.001, 100.0, 0.001], [1.0, 1.0, 1.0, 1.0]); // wide, all positive
    push([9.9, 9.9, 9.9, 9.9], [9.9, 9.9, 9.9, 9.9]);
    let mut rng = SplitMix64(SEED);
    for _ in 0..240 {
        let mut a = [0f32; 4];
        let mut b = [0f32; 4];
        for i in 0..4 {
            a[i] = rand_f64(&mut rng, 0.1, 10.0) as f32;
            b[i] = rand_f64(&mut rng, 0.1, 10.0) as f32;
        }
        push(a, b);
    }
    v
}

/// `fadd(a, b) = a + b` over f64 — the Phase-1 smoke test for the float path.
/// Edge doubles (zeros, ±1, fractions, large/small) plus random finite pairs;
/// the only point is that C++ `double` and Lean `Float` agree bit-for-bit.
pub fn fadd_vectors() -> Vec<Vector> {
    let mut v = Vec::new();
    let mut push = |a: f64, b: f64| v.push(Vector::new(vec![f64_bits(a), f64_bits(b)]));
    for (a, b) in [
        (0.0, 0.0),
        (1.0, 2.0),
        (-1.0, 1.0),
        (0.1, 0.2),       // the classic non-representable sum
        (0.5, 0.25),
        (1e16, 1.0),      // 1.0 lost below the ulp
        (1e-300, 1e-300), // tiny
        (3.141592653589793, 2.718281828459045),
        (-0.0, 0.0),      // signed-zero canonicalization check
    ] {
        push(a, b);
    }
    let mut rng = SplitMix64(SEED);
    for _ in 0..200 {
        push(rand_f64(&mut rng, -1e6, 1e6), rand_f64(&mut rng, -1e6, 1e6));
    }
    v
}

/// `gss(a, b, tol)` over f64 — golden-section search for the min of
/// f(x)=(x-3)²+1. Brackets that enclose the minimizer x*=3, across a spread of
/// tolerances (tight → exact, loose → early exit) plus random enclosing
/// brackets. Encoded as IEEE bit patterns.
pub fn gss_vectors() -> Vec<Vector> {
    let mut v = Vec::new();
    let tols = [1.0_f64, 1e-1, 1e-3, 1e-6, 1e-9, 1e-12];
    let mut push = |a: f64, b: f64, t: f64| {
        v.push(Vector::new(vec![f64_bits(a), f64_bits(b), f64_bits(t)]))
    };
    // edges: brackets straddling x*=3, including asymmetric and wide ones
    for (a, b) in [(0.0, 10.0), (2.5, 3.5), (-10.0, 20.0), (2.9, 3.1), (0.0, 3.0), (3.0, 6.0)] {
        for &t in &tols {
            push(a, b, t);
        }
    }
    let mut rng = SplitMix64(SEED);
    // random enclosing brackets: a ∈ [-20,2.9], b ∈ [3.1,20]
    for _ in 0..150 {
        let a = rand_f64(&mut rng, -20.0, 2.9);
        let b = rand_f64(&mut rng, 3.1, 20.0);
        let t = tols[(rng.range(0, tols.len() as u64 - 1)) as usize];
        push(a, b, t);
    }
    v
}

/// `gd(x0, y0, eta)` over f64 — fixed-step gradient descent on
/// f(x,y)=(x-1)²+(y-2)². A spread of starting points × step sizes: mostly
/// stable η ∈ (0,1) (converging), plus η = 1 (oscillating, objective preserved)
/// and a couple of large η (diverging — still bit-exact; the postcondition skips
/// non-finite results). Encoded as IEEE bit patterns.
pub fn gd_vectors() -> Vec<Vector> {
    let mut v = Vec::new();
    let etas = [0.01_f64, 0.05, 0.1, 0.25, 0.5, 0.9, 1.0, 1.5];
    let mut push = |x: f64, y: f64, e: f64| {
        v.push(Vector::new(vec![f64_bits(x), f64_bits(y), f64_bits(e)]))
    };
    for (x, y) in [(0.0, 0.0), (1.0, 2.0), (-5.0, 5.0), (10.0, -10.0), (3.0, 3.0)] {
        for &e in &etas {
            push(x, y, e);
        }
    }
    let mut rng = SplitMix64(SEED);
    for _ in 0..150 {
        let x = rand_f64(&mut rng, -50.0, 50.0);
        let y = rand_f64(&mut rng, -50.0, 50.0);
        // bias toward stable steps so the descent postcondition is meaningful
        let e = etas[(rng.range(0, 5)) as usize];
        push(x, y, e);
    }
    v
}

/// `hooke_jeeves(x0, y0, step)` over f64 — derivative-free pattern search on
/// f(x,y)=(x-1)²+(y-2)². Starting points × initial step sizes; the method never
/// diverges (it only descends or shrinks the step), so every result is finite.
/// Encoded as IEEE bit patterns.
pub fn hj_vectors() -> Vec<Vector> {
    let mut v = Vec::new();
    let steps = [0.05_f64, 0.1, 0.25, 0.5, 1.0, 2.0];
    let mut push = |x: f64, y: f64, s: f64| {
        v.push(Vector::new(vec![f64_bits(x), f64_bits(y), f64_bits(s)]))
    };
    for (x, y) in [(0.0, 0.0), (1.0, 2.0), (-5.0, 5.0), (10.0, -10.0), (3.0, 3.0)] {
        for &s in &steps {
            push(x, y, s);
        }
    }
    let mut rng = SplitMix64(SEED);
    for _ in 0..150 {
        let x = rand_f64(&mut rng, -50.0, 50.0);
        let y = rand_f64(&mut rng, -50.0, 50.0);
        let s = steps[(rng.range(0, steps.len() as u64 - 1)) as usize];
        push(x, y, s);
    }
    v
}

/// `streamed(deposit, start, stop, t)` — edge + safe + deliberate-overflow.
pub fn streamed_vectors() -> Vec<Vector> {
    let mut v = Vec::new();
    let mut push = |a: [u64; 4]| v.push(Vector::new(a.to_vec()));

    // 1. edge cases
    for e in [
        [1000, 10, 110, 5],   // t < start  -> 0
        [1000, 10, 110, 10],  // t == start -> 0
        [1000, 10, 110, 11],  // just inside ramp
        [1000, 10, 110, 60],  // mid ramp   -> 500
        [1000, 10, 110, 109], // near stop
        [1000, 10, 110, 110], // t == stop  -> deposit
        [1000, 10, 110, 200], // t > stop   -> deposit
        [0, 10, 110, 60],     // zero deposit
        [7, 0, 3, 1],         // 7*1/3 = 2
        [7, 0, 3, 2],         // 7*2/3 = 4
    ] {
        push(e);
    }

    let mut rng = SplitMix64(SEED);
    // 2. safe random (product bounded < 2^64)
    for _ in 0..400 {
        let deposit = rng.range(0, 1_000_000_000);
        let start = rng.range(0, 1_000_000);
        let span = rng.range(1, 1_000_000); // product <= 1e15 < 2^64
        let stop = start + span;
        let t = rng.range(0, stop + span);
        push([deposit, start, stop, t]);
    }
    // 3. deliberate overflow (deposit*(t-start) >= 2^64)
    for _ in 0..40 {
        let deposit = rng.range(1u64 << 60, u64::MAX);
        let start = rng.range(0, 1_000_000);
        let span = rng.range(2, 1_000_000);
        let stop = start + span;
        let need = ((1u128 << 64) + deposit as u128 - 1) / deposit as u128;
        let t = start + (need as u64).max(1) + rng.range(0, 1000);
        push([deposit, start, stop, t]);
    }
    v
}

/// `avg(a, b)` over u32 — edge + safe + deliberate-overflow (`a+b >= 2^32`).
pub fn avg_vectors() -> Vec<Vector> {
    const U32MAX: u64 = u32::MAX as u64;
    let mut v = Vec::new();
    let mut push = |a: u64, b: u64| v.push(Vector::new(vec![a, b]));

    // 1. edge cases
    for (a, b) in [
        (0, 0),
        (1, 1),
        (10, 20),               // (10+20)/2 = 15
        (3, 4),                 // floor: 7/2 = 3
        (U32MAX, 0),            // (2^32-1)/2
        (U32MAX, 1),            // a+b == 2^32 -> OVERFLOW
        (U32MAX, U32MAX),       // sum ~2^33    -> OVERFLOW
        (2_000_000_000, 2_000_000_000), // 4e9 > 2^32 -> OVERFLOW
    ] {
        push(a, b);
    }

    let mut rng = SplitMix64(SEED);
    // 2. safe random (a, b < 2^31 so a+b < 2^32)
    for _ in 0..200 {
        let a = rng.range(0, 1u64 << 31);
        let b = rng.range(0, (1u64 << 31) - 1); // a+b <= 2^32-1, no overflow
        push(a, b);
    }
    // 3. deliberate overflow (a + b >= 2^32)
    for _ in 0..40 {
        let a = rng.range(1u64 << 31, U32MAX);
        // pick b so a+b >= 2^32, but keep b <= U32MAX
        let lo = ((1u64 << 32) - a).min(U32MAX);
        let b = rng.range(lo, U32MAX);
        push(a, b);
    }
    v
}

/// `dot2(a, b, c, d) = a*b + c*d` over u32 — edge + safe + overflow
/// (`a*b + c*d >= 2^32`, wide).
pub fn dot2_vectors() -> Vec<Vector> {
    const U32MAX: u64 = u32::MAX as u64;
    let mut v = Vec::new();
    let mut push = |a: u64, b: u64, c: u64, d: u64| v.push(Vector::new(vec![a, b, c, d]));

    // 1. edge cases
    for q in [
        [0, 0, 0, 0],
        [2, 3, 4, 5],                       // 6 + 20 = 26
        [1, 1, 1, 1],                       // 2
        [65535, 65535, 0, 0],               // 4294836225 < 2^32 (safe, near edge)
        [65536, 65536, 0, 0],               // == 2^32 -> OVERFLOW
        [0, 0, 65536, 65536],               // == 2^32 -> OVERFLOW
        [50000, 50000, 50000, 50000],       // 5e9 > 2^32 -> OVERFLOW
    ] {
        push(q[0], q[1], q[2], q[3]);
    }

    let mut rng = SplitMix64(SEED);
    // 2. safe random (each operand <= 30000 so a*b + c*d <= 1.8e9 < 2^32)
    for _ in 0..200 {
        push(rng.range(0, 30_000), rng.range(0, 30_000), rng.range(0, 30_000), rng.range(0, 30_000));
    }
    // 3. deliberate overflow (large operands -> products dwarf 2^32)
    for _ in 0..40 {
        push(
            rng.range(50_000, U32MAX),
            rng.range(50_000, U32MAX),
            rng.range(0, U32MAX),
            rng.range(0, U32MAX),
        );
    }
    v
}

/// `isqrt(n)` over u32 — edges around perfect squares + random. No overflow
/// class; the interesting property is the postcondition r*r ≤ n < (r+1)².
pub fn isqrt_vectors() -> Vec<Vector> {
    const U32MAX: u64 = u32::MAX as u64;
    let mut v = Vec::new();
    // 1. edges: small ints, perfect squares and their neighbours, the max
    for n in [
        0, 1, 2, 3, 4, 5, 8, 9, 10, 15, 16, 17, 24, 25, 26, 35, 36, 99, 100, 101,
        65535, 65536, 1_000_000, 4_294_836_224, 4_294_836_225, // 65535^2
        4_294_967_295, // u32::MAX
    ] {
        v.push(Vector::new(vec![n]));
    }
    let mut rng = SplitMix64(SEED);
    // 2. random across the whole u32 range
    for _ in 0..200 {
        v.push(Vector::new(vec![rng.range(0, U32MAX)]));
    }
    v
}

/// `bisect_sqrt(n, eps)` over u32 — n across the range × a spread of tolerances
/// (eps=0 is exact isqrt; large eps exits the loop early).
pub fn bisect_vectors() -> Vec<Vector> {
    const U32MAX: u64 = u32::MAX as u64;
    let mut v = Vec::new();
    let epss = [0u64, 1, 2, 3, 5, 10, 100, 1000, 65535, 100_000];
    // edges: perfect squares and neighbours, paired with each eps
    for n in [0u64, 1, 3, 4, 24, 25, 100, 65535, 4_294_836_225, U32MAX] {
        for &e in &epss {
            v.push(Vector::new(vec![n, e]));
        }
    }
    let mut rng = SplitMix64(SEED);
    for _ in 0..200 {
        let n = rng.range(0, U32MAX);
        let e = epss[(rng.range(0, epss.len() as u64 - 1)) as usize];
        v.push(Vector::new(vec![n, e]));
    }
    v
}

/// `quantize_rne(prec, n)` — one quantizer across the float formats. `prec`
/// selects fp8-E5M2 (2), fp8-E4M3 (3), bf16 (7), fp16 (10), f32 (23), f64 (52).
/// Inputs span small ints (exact at high prec) and large ints `≥ 2^prec` (so each
/// format's rounding actually fires — incl. f32/f64 on wide values).
pub fn quant_vectors() -> Vec<Vector> {
    let mut v = Vec::new();
    let mut rng = SplitMix64(SEED);
    for &prec in &[2u64, 3, 7, 10, 23, 52] {
        for n in 0u64..=48 {
            v.push(Vector::new(vec![prec, n]));
        }
        // n in [2^prec, 2^62): more than `prec` significant bits ⇒ rounding fires
        let lo = 1u64 << prec;
        for _ in 0..100 {
            v.push(Vector::new(vec![prec, rng.range(lo, (1u64 << 62) - 1)]));
        }
    }
    v
}
