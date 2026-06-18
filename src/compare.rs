//! The deterministic comparator + divergence classifier (SPEC §6, §10, §12).
//!
//! Joins the oracle's result and the Lean candidate's result for every vector
//! and classifies each line. A divergence is NOT a flat pass/fail: where the
//! checked Lean model reports OVERFLOW and C++ silently wraps, that is a
//! *declared* semantic-divergence class (SPEC §11: C/C++ unsigned overflow =
//! `wrap`) — confirmed independently here by recomputing the overflow predicate
//! in wide arithmetic. A divergence the profile does NOT explain is a real bug.

use crate::vectors::Vector;
use std::collections::HashMap;

/// The per-example semantic profile: branch labels (coverage) and the declared
/// overflow predicate. This is the hand-pinned stand-in for the SPEC §11
/// fidelity profile / §7 Contract IR until those are generated.
#[derive(Clone, Copy)]
pub enum Profile {
    Streamed,
    Avg,
    Dot2,
    Isqrt,
    Bisect,
    Quant,
    // Float optimizers (bit-pattern args/result; postconditions decode via
    // `f64::from_bits`). No declared-overflow class — floats produce NaN/Inf,
    // canonicalized by the runner, not a `wrap` divergence.
    OptGss,
    OptGd,
    OptHj,
    /// Phase-1 float smoke (`a + b`): no postcondition, no divergence class.
    Fadd,
    /// 4-term f32 dot product (oracle sums left-to-right, model pairwise). The
    /// postcondition is the standard dot-product rounding-error bound; the two
    /// summation orders agree only within a `--float-tol` tolerance.
    Fdot4,
}

impl Profile {
    /// All branch labels, in display order (for coverage).
    pub fn branch_labels(self) -> &'static [&'static str] {
        match self {
            Profile::Streamed => &["clamp-low (t<=start)", "clamp-high (t>=stop)", "ramp"],
            Profile::Avg => &["avg"],
            Profile::Dot2 => &["dot2"],
            Profile::Isqrt => &["isqrt"],
            Profile::Bisect => &["bisect"],
            Profile::Quant => &["quant"],
            Profile::OptGss => &["gss"],
            Profile::OptGd => &["gd"],
            Profile::OptHj => &["hj"],
            Profile::Fadd => &["fadd"],
            Profile::Fdot4 => &["fdot4"],
        }
    }

    /// A per-result postcondition to check empirically (L1 "analysis"): given
    /// the inputs and the (agreed) result, does the spec hold? `None` = no
    /// postcondition declared for this profile.
    pub fn postcondition(self, args: &[u64], result: u64) -> Option<bool> {
        match self {
            // r*r ≤ n < (r+1)*(r+1), in wide arithmetic.
            Profile::Isqrt => {
                let (n, r) = (args[0] as u128, result as u128);
                Some(r * r <= n && n < (r + 1) * (r + 1))
            }
            // lo*lo ≤ n < (lo + eps + 1)²  (the ε-bracket guarantee)
            Profile::Bisect => {
                let (n, eps, lo) = (args[0] as u128, args[1] as u128, result as u128);
                Some(lo * lo <= n && n < (lo + eps + 1) * (lo + eps + 1))
            }
            // q is representable at `prec` bits and within ulp/2 of n (the RNE
            // rounding-error bound — a real error estimate, checked empirically).
            Profile::Quant => {
                let (prec, n, q) = (args[0], args[1], result);
                if n == 0 {
                    return Some(q == 0);
                }
                let e = n.ilog2() as u64;
                if e <= prec {
                    return Some(q == n); // exact
                }
                let step = 1u128 << (e - prec);
                let repr = (q as u128) % step == 0;
                let err = (q as i128 - n as i128).unsigned_abs() <= step / 2;
                Some(repr && err)
            }
            // Float optimizers — args/result are IEEE bit patterns. The objective
            // is fixed per kernel; we check the optimizer's own guarantee.
            // gss: minimize f(x)=(x-3)²+1 on [a,b] → a ≤ x ≤ b and no worse than
            // either endpoint (robust to the tolerance).
            Profile::OptGss => {
                let (a, b, tol) =
                    (f64::from_bits(args[0]), f64::from_bits(args[1]), f64::from_bits(args[2]));
                let x = f64::from_bits(result);
                if !x.is_finite() {
                    return None;
                }
                // The GSS accuracy guarantee, with the finite-precision floor:
                // a derivative-free search on a quadratic locates the minimizer
                // to ≈√ε ≈ 1e-8 (the objective goes flat and `fc<fd` drowns in
                // rounding below that), so the bound is max(½·tol, √ε·scale).
                Some(a <= x && x <= b && (x - 3.0).abs() <= 0.5 * tol + 1e-7)
            }
            // gd: returns the final objective f(x_K); in the STABLE regime
            // (η ≤ 1) it must not exceed f(x_0). η > 1 diverges by design — its
            // bit-exactness is still checked by conformance, but the descent
            // claim does not apply, so it is out of scope here (None).
            Profile::OptGd => {
                let (x0, y0, eta) =
                    (f64::from_bits(args[0]), f64::from_bits(args[1]), f64::from_bits(args[2]));
                let fr = f64::from_bits(result);
                if !fr.is_finite() || eta > 1.0 {
                    return None;
                }
                let f0 = (x0 - 1.0) * (x0 - 1.0) + (y0 - 2.0) * (y0 - 2.0);
                let eps = 1e-9 * (1.0 + f0.abs());
                Some(fr >= 0.0 && fr <= f0 + eps)
            }
            // nm: returns the best objective; it is no worse than the start.
            Profile::OptHj => {
                let (x0, y0) = (f64::from_bits(args[0]), f64::from_bits(args[1]));
                let fr = f64::from_bits(result);
                if !fr.is_finite() {
                    return None;
                }
                let f0 = (x0 - 1.0) * (x0 - 1.0) + (y0 - 2.0) * (y0 - 2.0);
                let eps = 1e-9 * (1.0 + f0.abs());
                Some(fr >= 0.0 && fr <= f0 + eps)
            }
            // The standard dot-product rounding-error bound: a real per-result error
            // estimate (L1 "analysis"). |fl(Σaᵢbᵢ) − Σaᵢbᵢ| ≤ γ·Σ|aᵢbᵢ| with the
            // f32 unit roundoff u = 2⁻²⁴; γ = 8u is a comfortable bound on the
            // 4-product, 3-addition reduction (and on either summation order).
            Profile::Fdot4 => {
                let f = |i: usize| f32::from_bits(args[i] as u32) as f64;
                let (mut dot, mut mag) = (0.0f64, 0.0f64);
                for i in 0..4 {
                    let t = f(i) * f(i + 4);
                    dot += t;
                    mag += t.abs();
                }
                let r = f32::from_bits(result as u32) as f64;
                let u = 2f64.powi(-24);
                Some((r - dot).abs() <= 8.0 * u * mag + 1e-7)
            }
            _ => None,
        }
    }

    /// Human description of the postcondition (for the report).
    pub fn postcondition_desc(self) -> Option<&'static str> {
        match self {
            Profile::Isqrt => Some("r·r ≤ n < (r+1)²"),
            Profile::Bisect => Some("lo·lo ≤ n < (lo+eps+1)²"),
            Profile::Quant => Some("q representable, |q−n| ≤ ulp/2"),
            Profile::OptGss => Some("a ≤ x ≤ b ∧ |x − 3| ≤ ½·tol + √ε"),
            Profile::OptGd => Some("0 ≤ f(x_K) ≤ f(x_0)  (descent)"),
            Profile::OptHj => Some("0 ≤ f(best) ≤ f(start)  (no worse than start)"),
            Profile::Fdot4 => Some("|fl·dot − Σaᵢbᵢ| ≤ 8u·Σ|aᵢbᵢ|  (u = 2⁻²⁴)"),
            _ => None,
        }
    }

    /// Which branch a vector exercises.
    pub fn branch(self, a: &[u64]) -> &'static str {
        match self {
            Profile::Streamed => {
                let (start, stop, t) = (a[1], a[2], a[3]);
                if t <= start {
                    "clamp-low (t<=start)"
                } else if t >= stop {
                    "clamp-high (t>=stop)"
                } else {
                    "ramp"
                }
            }
            Profile::Avg => "avg",
            Profile::Dot2 => "dot2",
            Profile::Isqrt => "isqrt",
            Profile::Bisect => "bisect",
            Profile::Quant => "quant",
            Profile::OptGss => "gss",
            Profile::OptGd => "gd",
            Profile::OptHj => "hj",
            Profile::Fadd => "fadd",
            Profile::Fdot4 => "fdot4",
        }
    }

    /// Does the source semantically diverge here in a *declared* class — i.e.
    /// the unsigned-overflow `wrap` boundary? Recomputed in u128 so the
    /// classifier confirms it independently of the candidate's OVERFLOW label.
    pub fn declared_divergence(self, a: &[u64]) -> bool {
        match self {
            Profile::Streamed => {
                let (deposit, start, t) = (a[0], a[1], a[3]);
                t > start && deposit as u128 * (t - start) as u128 >= (1u128 << 64)
            }
            Profile::Avg => a[0] as u128 + a[1] as u128 >= (1u128 << 32),
            // a*b + c*d (wide) >= 2^32 covers all three overflow points, since
            // the sum dominates either product.
            Profile::Dot2 => {
                a[0] as u128 * a[1] as u128 + a[2] as u128 * a[3] as u128 >= (1u128 << 32)
            }
            // bounded / deterministic, or float (NaN/Inf canonicalized, not a
            // declared `wrap` class): no overflow-divergence.
            Profile::Isqrt | Profile::Bisect | Profile::Quant => false,
            Profile::OptGss | Profile::OptGd | Profile::OptHj | Profile::Fadd | Profile::Fdot4 => false,
        }
    }
}

/// Float comparison tolerance for the difftest (SPEC §6). `Exact` is bit-identical
/// agreement — the default, and what native f64/f32 use (Lean's binary64/binary32
/// ≡ C++ `double`/`float` bit-for-bit). The tolerance modes are for low-precision /
/// vendor-oracle paths where bit-exactness is not achievable but a *bounded*
/// rounding divergence is acceptable and must be REPORTED, not silently passed.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum FloatTol {
    /// Bit-identical (after NaN / signed-zero canonicalization).
    Exact,
    /// Within `n` ULPs (units in the last place) at the compared width.
    Ulp(u32),
    /// Relative: `|a−b| ≤ rel · max(|a|,|b|)`.
    Rel(f64),
    /// Absolute: `|a−b| ≤ abs`.
    Abs(f64),
}

impl FloatTol {
    /// Parse a CLI spec: `exact`, `ulp:2`, `rel:1e-6`, `abs:1e-9`.
    pub fn parse(s: &str) -> Result<FloatTol, String> {
        let s = s.trim();
        if s.eq_ignore_ascii_case("exact") {
            return Ok(FloatTol::Exact);
        }
        let (kind, val) = s
            .split_once(':')
            .ok_or_else(|| format!("bad --float-tol `{s}` (want exact | ulp:N | rel:E | abs:E)"))?;
        match kind {
            "ulp" => val.parse::<u32>().map(FloatTol::Ulp).map_err(|_| format!("ulp needs an integer, got `{val}`")),
            "rel" => parse_pos_f64(val).map(FloatTol::Rel),
            "abs" => parse_pos_f64(val).map(FloatTol::Abs),
            other => Err(format!("unknown --float-tol kind `{other}` (want ulp | rel | abs | exact)")),
        }
    }
}

fn parse_pos_f64(v: &str) -> Result<f64, String> {
    match v.parse::<f64>() {
        Ok(x) if x.is_finite() && x >= 0.0 => Ok(x),
        _ => Err(format!("tolerance must be a finite non-negative number, got `{v}`")),
    }
}

/// A float difftest configuration: the tolerance and the bit width (32 or 64) the
/// result patterns are decoded at.
#[derive(Clone, Copy, Debug)]
pub struct FloatCompare {
    pub tol: FloatTol,
    pub width: u32,
}

/// The bit-level outcome of comparing two float results.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FloatCmp {
    /// Identical (or canonical-equal: same NaN-ness, ±0, same-sign Inf).
    BitExact,
    /// Differ in bits but within the declared tolerance — a benign rounding
    /// divergence (reported, not a bug).
    WithinTolerance,
    /// Outside tolerance, or a structural mismatch (NaN vs finite, ±Inf, etc.).
    Diverge,
}

/// Compare two IEEE results given as raw bit patterns, with NaN canonicalization
/// (any NaN == any NaN), signed-zero canonicalization (−0 == +0), and Inf handled
/// by sign. Finite values that are not bit-identical are accepted only within the
/// declared tolerance. `width` selects f32 (low 32 bits) vs f64.
///
/// Soundness: the default `Exact` accepts ONLY bit-identical-or-canonical pairs, so
/// it can never mask a real divergence; the tolerance modes accept a strictly wider
/// (and explicitly reported) set, never narrower.
pub fn float_match(a_bits: u64, b_bits: u64, fc: FloatCompare) -> FloatCmp {
    if fc.width == 32 {
        float_match_generic(a_bits as u32 as u64, b_bits as u32 as u64, fc.tol, 32)
    } else {
        float_match_generic(a_bits, b_bits, fc.tol, 64)
    }
}

fn decode(bits: u64, width: u32) -> f64 {
    if width == 32 { f32::from_bits(bits as u32) as f64 } else { f64::from_bits(bits) }
}

/// Map an IEEE bit pattern to a monotone signed integer so that ULP distance is
/// `|order(a) − order(b)|` (the standard total-ordering transform).
fn monotone_order(bits: u64, width: u32) -> i128 {
    let sign_bit: u64 = 1u64 << (width - 1);
    if bits & sign_bit != 0 {
        // negative: flip to a descending-from-zero order.
        -((bits & !sign_bit) as i128)
    } else {
        bits as i128
    }
}

fn float_match_generic(a_bits: u64, b_bits: u64, tol: FloatTol, width: u32) -> FloatCmp {
    let (a, b) = (decode(a_bits, width), decode(b_bits, width));

    // NaN canonicalization: any NaN equals any NaN; NaN vs non-NaN diverges.
    if a.is_nan() || b.is_nan() {
        return if a.is_nan() && b.is_nan() {
            if a_bits == b_bits { FloatCmp::BitExact } else { FloatCmp::WithinTolerance }
        } else {
            FloatCmp::Diverge
        };
    }
    // Exactly equal bits (covers identical zeros, identical Inf, identical finite).
    if a_bits == b_bits {
        return FloatCmp::BitExact;
    }
    // Signed zero: −0.0 and +0.0 are canonical-equal (bits differ ⇒ WithinTolerance).
    if a == 0.0 && b == 0.0 {
        return FloatCmp::WithinTolerance;
    }
    // Infinities (non-equal bits ⇒ opposite signs, or Inf vs finite): a divergence.
    if a.is_infinite() || b.is_infinite() {
        return FloatCmp::Diverge;
    }
    // Finite, not bit-identical: accept only within the declared tolerance.
    let within = match tol {
        FloatTol::Exact => false,
        FloatTol::Ulp(n) => {
            // Integer monotone-order distance — no float arithmetic, cannot overflow.
            let d = (monotone_order(a_bits, width) - monotone_order(b_bits, width)).abs();
            d <= n as i128
        }
        // Rel/Abs: the difference of two far-apart finite values can OVERFLOW to
        // ±Inf (e.g. MAX − (−MAX) = +Inf). `Inf <= Inf` would be `true` and mask the
        // *maximal* divergence as within-tolerance, so require a FINITE difference
        // first (fail-closed). With a finite difference the comparison is sound even
        // when `eps·scale` is itself Inf (a genuine ≥100% relative tolerance).
        FloatTol::Rel(eps) => {
            let d = (a - b).abs();
            d.is_finite() && d <= eps * a.abs().max(b.abs())
        }
        FloatTol::Abs(eps) => {
            let d = (a - b).abs();
            d.is_finite() && d <= eps
        }
    };
    if within { FloatCmp::WithinTolerance } else { FloatCmp::Diverge }
}

/// The classification of a single joined line.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Class {
    /// Both sides produced the same value. Full agreement.
    Conform,
    /// Lean reported OVERFLOW, C++ wrapped, and the profile confirms a genuine
    /// overflow — the declared `wrap` divergence class. Expected, not a bug.
    DeclaredOverflow,
    /// Float results differ in bits but agree within the declared `--float-tol`
    /// tolerance — a benign rounding divergence. Reported, counts as conformant.
    ToleranceDivergence,
    /// A divergence the profile does NOT explain — a real conformance bug.
    Mismatch,
}

/// One fully classified line, retained for the divergence table / report.
pub struct Line {
    pub vector: Vector,
    pub branch: &'static str,
    pub cpp: String,
    pub lean: String,
    pub class: Class,
}

pub struct Comparison {
    pub lines: Vec<Line>,
    pub profile: Profile,
}

impl Comparison {
    /// Conformant iff no line is an unexplained `Mismatch`. `DeclaredOverflow` and
    /// `ToleranceDivergence` are explained (declared) divergences, not bugs.
    pub fn conformant(&self) -> bool {
        self.lines.iter().all(|l| l.class != Class::Mismatch)
    }
    pub fn count(&self, c: Class) -> usize {
        self.lines.iter().filter(|l| l.class == c).count()
    }
    pub fn mismatches(&self) -> impl Iterator<Item = &Line> {
        self.lines.iter().filter(|l| l.class == Class::Mismatch)
    }
    pub fn branch_coverage(&self) -> HashMap<&'static str, usize> {
        let mut m = HashMap::new();
        for l in &self.lines {
            *m.entry(l.branch).or_insert(0) += 1;
        }
        m
    }

    /// Empirically check the profile's postcondition on every result. Returns
    /// `(held, total)`, or `None` if the profile declares no postcondition.
    pub fn postcondition(&self) -> Option<(usize, usize)> {
        self.profile.postcondition_desc()?;
        let mut held = 0;
        let mut total = 0;
        for l in &self.lines {
            if let Ok(r) = l.cpp.parse::<u64>() {
                if let Some(ok) = self.profile.postcondition(&l.vector.args, r) {
                    total += 1;
                    if ok {
                        held += 1;
                    }
                }
            }
        }
        Some((held, total))
    }
}

/// Join oracle results and the Lean result map (both keyed by `"a b c …"`) and
/// classify each line against the profile.
pub fn compare(
    vectors: &[Vector],
    cpp: &HashMap<String, String>,
    lean: &HashMap<String, String>,
    profile: Profile,
    float: Option<FloatCompare>,
) -> Comparison {
    let mut lines = Vec::with_capacity(vectors.len());
    for v in vectors {
        let key = v.key();
        let cpp_val = cpp.get(&key).cloned().unwrap_or_else(|| "<missing>".into());
        let lean_val = lean.get(&key).cloned().unwrap_or_else(|| "<missing>".into());

        // Float-tolerance path (SPEC §6): when a `--float-tol` is in effect, decode
        // both results as bit patterns and classify by `float_match`. A bit-exact
        // pair is Conform; within-tolerance is the reported ToleranceDivergence;
        // anything else (or an unparseable / missing side) is a Mismatch. Floats
        // never carry the OVERFLOW token (NaN/Inf are canonicalized), so this path
        // is independent of the integer wrap-divergence logic below.
        if let Some(fc) = float {
            let class = match (cpp_val.parse::<u64>(), lean_val.parse::<u64>()) {
                (Ok(cb), Ok(lb)) => match float_match(cb, lb, fc) {
                    FloatCmp::BitExact => Class::Conform,
                    FloatCmp::WithinTolerance => Class::ToleranceDivergence,
                    FloatCmp::Diverge => Class::Mismatch,
                },
                _ => Class::Mismatch, // a missing or non-bit-pattern side
            };
            lines.push(Line {
                vector: v.clone(),
                branch: profile.branch(&v.args),
                cpp: cpp_val,
                lean: lean_val,
                class,
            });
            continue;
        }

        let lean_fail = lean_val == "OVERFLOW";
        let oracle_fail = cpp_val == "OVERFLOW"; // e.g. a Solidity revert
        let class = if lean_fail && oracle_fail {
            // Both report the error token → agreement (e.g. Solidity checked
            // arithmetic reverts exactly where the checked model fails).
            Class::Conform
        } else if lean_fail {
            // Lean failed, the source produced a value → the declared `wrap`
            // divergence (C/C++/Go/unchecked-Solidity), if the profile confirms.
            if profile.declared_divergence(&v.args) {
                Class::DeclaredOverflow
            } else {
                Class::Mismatch // Lean failed inside the safe domain → model bug
            }
        } else if oracle_fail {
            Class::Mismatch // source failed but the model didn't → real divergence
        } else if lean_val == cpp_val && lean_val != "<missing>" {
            Class::Conform
        } else {
            Class::Mismatch // values differ, or a side is missing
        };

        lines.push(Line {
            vector: v.clone(),
            branch: profile.branch(&v.args),
            cpp: cpp_val,
            lean: lean_val,
            class,
        });
    }
    Comparison { lines, profile }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f64c(tol: FloatTol) -> FloatCompare {
        FloatCompare { tol, width: 64 }
    }
    fn f32c(tol: FloatTol) -> FloatCompare {
        FloatCompare { tol, width: 32 }
    }

    #[test]
    fn parse_specs() {
        assert_eq!(FloatTol::parse("exact").unwrap(), FloatTol::Exact);
        assert_eq!(FloatTol::parse("ulp:2").unwrap(), FloatTol::Ulp(2));
        assert_eq!(FloatTol::parse("rel:1e-6").unwrap(), FloatTol::Rel(1e-6));
        assert_eq!(FloatTol::parse("abs:0.5").unwrap(), FloatTol::Abs(0.5));
        assert!(FloatTol::parse("ulp:-1").is_err());
        assert!(FloatTol::parse("rel:-0.1").is_err()); // negative tolerance refused
        assert!(FloatTol::parse("rel:nan").is_err());
        assert!(FloatTol::parse("bogus").is_err());
        assert!(FloatTol::parse("wat:1").is_err());
    }

    #[test]
    fn identical_bits_are_bit_exact() {
        let x = 2.5f64.to_bits();
        assert_eq!(float_match(x, x, f64c(FloatTol::Exact)), FloatCmp::BitExact);
    }

    #[test]
    fn exact_mode_rejects_any_bit_difference() {
        // The default must never accept a non-identical finite pair — it can only
        // ever shrink, never widen, the conformance set. This is the soundness core.
        let a = 1.0f64.to_bits();
        let b = (1.0f64 + f64::EPSILON).to_bits(); // 1 ULP away
        assert_eq!(float_match(a, b, f64c(FloatTol::Exact)), FloatCmp::Diverge);
    }

    #[test]
    fn nan_canonicalization() {
        let qnan = f64::NAN.to_bits();
        let snan = qnan ^ 0x000_8000_0000_0000; // a different NaN payload
        assert!(f64::from_bits(snan).is_nan());
        // Any NaN equals any NaN, even under Exact (canonical), different payloads
        // ⇒ WithinTolerance (not bit-identical) but never a Mismatch.
        assert_eq!(float_match(qnan, snan, f64c(FloatTol::Exact)), FloatCmp::WithinTolerance);
        assert_eq!(float_match(qnan, qnan, f64c(FloatTol::Exact)), FloatCmp::BitExact);
        // NaN vs a finite number is a hard divergence at ANY tolerance.
        let big = f64c(FloatTol::Abs(1e300));
        assert_eq!(float_match(qnan, 0.0f64.to_bits(), big), FloatCmp::Diverge);
    }

    #[test]
    fn signed_zero_is_canonical_equal() {
        let pz = 0.0f64.to_bits();
        let nz = (-0.0f64).to_bits();
        assert_ne!(pz, nz, "the bit patterns really do differ");
        assert_eq!(float_match(pz, nz, f64c(FloatTol::Exact)), FloatCmp::WithinTolerance);
    }

    #[test]
    fn infinities_by_sign() {
        let pinf = f64::INFINITY.to_bits();
        let ninf = f64::NEG_INFINITY.to_bits();
        let huge = f64c(FloatTol::Abs(f64::MAX));
        assert_eq!(float_match(pinf, pinf, huge), FloatCmp::BitExact);
        // +Inf vs −Inf and Inf vs finite never agree, regardless of tolerance.
        assert_eq!(float_match(pinf, ninf, huge), FloatCmp::Diverge);
        assert_eq!(float_match(pinf, 1.0f64.to_bits(), huge), FloatCmp::Diverge);
    }

    #[test]
    fn ulp_distance_is_exact() {
        let a = 1.0f64.to_bits();
        let b1 = a + 1; // adjacent representable above 1.0
        let b3 = a + 3;
        assert_eq!(float_match(a, b1, f64c(FloatTol::Ulp(1))), FloatCmp::WithinTolerance);
        assert_eq!(float_match(a, b3, f64c(FloatTol::Ulp(2))), FloatCmp::Diverge); // 3 > 2
        assert_eq!(float_match(a, b3, f64c(FloatTol::Ulp(3))), FloatCmp::WithinTolerance);
    }

    #[test]
    fn ulp_distance_crosses_sign_and_zero_monotonically() {
        // The smallest subnormal either side of zero must be 2 ULPs apart (through
        // +0/−0), exercising the sign-magnitude → monotone-order transform.
        let pos = 1u64; // +smallest subnormal (f64)
        let neg = 1u64 | (1u64 << 63); // −smallest subnormal
        assert_eq!(float_match(pos, neg, f64c(FloatTol::Ulp(2))), FloatCmp::WithinTolerance);
        assert_eq!(float_match(pos, neg, f64c(FloatTol::Ulp(1))), FloatCmp::Diverge);
    }

    #[test]
    fn rel_and_abs_modes() {
        let a = 1000.0f64.to_bits();
        let b = 1000.1f64.to_bits();
        // |Δ| = 0.1, rel = 0.1/1000.1 ≈ 1e-4.
        assert_eq!(float_match(a, b, f64c(FloatTol::Rel(2e-4))), FloatCmp::WithinTolerance);
        assert_eq!(float_match(a, b, f64c(FloatTol::Rel(1e-5))), FloatCmp::Diverge);
        assert_eq!(float_match(a, b, f64c(FloatTol::Abs(0.2))), FloatCmp::WithinTolerance);
        assert_eq!(float_match(a, b, f64c(FloatTol::Abs(0.05))), FloatCmp::Diverge);
    }

    #[test]
    fn rel_abs_overflow_does_not_mask_maximal_divergence() {
        // teeth (brutal-review FINDING 1): +MAX vs −MAX is the most-different finite
        // pair. Their difference overflows to +Inf; without the finite-difference
        // guard, `Inf <= eps·MAX(=Inf)` would be true and CONFORM the worst possible
        // divergence. It must be a Diverge at ANY tolerance.
        let pmax = f64::MAX.to_bits();
        let nmax = (-f64::MAX).to_bits();
        for tol in [FloatTol::Rel(1.5), FloatTol::Rel(1e9), FloatTol::Abs(f64::MAX)] {
            assert_eq!(float_match(pmax, nmax, f64c(tol)), FloatCmp::Diverge, "{tol:?} masked +MAX vs −MAX");
        }
        // Sanity: a genuine ≥100% relative tolerance still accepts a finite ratio
        // (MAX vs MAX/2 is a 50% relative error, within Rel(1.0)).
        let half = (f64::MAX / 2.0).to_bits();
        assert_eq!(float_match(pmax, half, f64c(FloatTol::Rel(1.0))), FloatCmp::WithinTolerance);
    }

    #[test]
    fn f32_width_decodes_low_32_bits() {
        // A garbage high half must not affect a 32-bit comparison.
        let a = 1.5f32.to_bits() as u64 | 0xDEAD_0000_0000_0000;
        let b = 1.5f32.to_bits() as u64;
        assert_eq!(float_match(a, b, f32c(FloatTol::Exact)), FloatCmp::BitExact);
        let c = (1.5f32 + 4.0 * f32::EPSILON).to_bits() as u64;
        assert_eq!(float_match(a, c, f32c(FloatTol::Ulp(8))), FloatCmp::WithinTolerance);
        assert_eq!(float_match(a, c, f32c(FloatTol::Ulp(1))), FloatCmp::Diverge);
    }

    // ── compare() integration: the new float path classifies correctly ──────────
    use crate::vectors::Vector;

    fn one_vec_maps(arg: u64, cpp: &str, lean: &str) -> (Vec<Vector>, HashMap<String, String>, HashMap<String, String>) {
        let v = Vector::new(vec![arg]);
        let key = v.key();
        let c = HashMap::from([(key.clone(), cpp.to_string())]);
        let l = HashMap::from([(key, lean.to_string())]);
        (vec![v], c, l)
    }

    #[test]
    fn compare_float_path_classes() {
        let a = 1.0f64.to_bits();
        let near = (a + 1).to_string(); // 1 ULP
        let far = (a + 50).to_string();
        let exact = a.to_string();

        // bit-exact ⇒ Conform
        let (v, c, l) = one_vec_maps(0, &exact, &exact);
        let cmp = compare(&v, &c, &l, Profile::Fadd, Some(f64c(FloatTol::Ulp(2))));
        assert_eq!(cmp.count(Class::Conform), 1);
        assert!(cmp.conformant());

        // within tolerance ⇒ ToleranceDivergence, still conformant
        let (v, c, l) = one_vec_maps(0, &exact, &near);
        let cmp = compare(&v, &c, &l, Profile::Fadd, Some(f64c(FloatTol::Ulp(2))));
        assert_eq!(cmp.count(Class::ToleranceDivergence), 1);
        assert_eq!(cmp.count(Class::Conform), 0);
        assert!(cmp.conformant(), "within-tolerance is a benign, conformant divergence");

        // outside tolerance ⇒ Mismatch, NOT conformant (teeth: no masking real bugs)
        let (v, c, l) = one_vec_maps(0, &exact, &far);
        let cmp = compare(&v, &c, &l, Profile::Fadd, Some(f64c(FloatTol::Ulp(2))));
        assert_eq!(cmp.count(Class::Mismatch), 1);
        assert!(!cmp.conformant());
    }

    #[test]
    fn compare_exact_default_is_unchanged_string_equality() {
        // With `float = None`, the integer/bit-exact string path is used verbatim —
        // identical strings Conform, differing strings Mismatch.
        let (v, c, l) = one_vec_maps(5, "42", "42");
        let cmp = compare(&v, &c, &l, Profile::Avg, None);
        assert_eq!(cmp.count(Class::Conform), 1);
        let (v, c, l) = one_vec_maps(5, "42", "43");
        let cmp = compare(&v, &c, &l, Profile::Avg, None);
        assert_eq!(cmp.count(Class::Mismatch), 1);
    }

    #[test]
    fn compare_float_missing_or_unparseable_side_is_mismatch() {
        let exact = 1.0f64.to_bits().to_string();
        let (v, c, l) = one_vec_maps(0, &exact, "<missing>");
        let cmp = compare(&v, &c, &l, Profile::Fadd, Some(f64c(FloatTol::Ulp(4))));
        assert_eq!(cmp.count(Class::Mismatch), 1, "a missing side is never within tolerance");
    }
}
