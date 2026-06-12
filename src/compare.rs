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
}

impl Profile {
    /// All branch labels, in display order (for coverage).
    pub fn branch_labels(self) -> &'static [&'static str] {
        match self {
            Profile::Streamed => &["clamp-low (t<=start)", "clamp-high (t>=stop)", "ramp"],
            Profile::Avg => &["avg"],
            Profile::Dot2 => &["dot2"],
            Profile::Isqrt => &["isqrt"],
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
            _ => None,
        }
    }

    /// Human description of the postcondition (for the report).
    pub fn postcondition_desc(self) -> Option<&'static str> {
        match self {
            Profile::Isqrt => Some("r·r ≤ n < (r+1)²"),
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
            Profile::Isqrt => false, // bounded algorithm: no overflow class
        }
    }
}

/// The classification of a single joined line.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Class {
    /// Both sides produced the same value. Full agreement.
    Conform,
    /// Lean reported OVERFLOW, C++ wrapped, and the profile confirms a genuine
    /// overflow — the declared `wrap` divergence class. Expected, not a bug.
    DeclaredOverflow,
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
) -> Comparison {
    let mut lines = Vec::with_capacity(vectors.len());
    for v in vectors {
        let key = v.key();
        let cpp_val = cpp.get(&key).cloned().unwrap_or_else(|| "<missing>".into());
        let lean_val = lean.get(&key).cloned().unwrap_or_else(|| "<missing>".into());

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
