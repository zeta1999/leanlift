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
