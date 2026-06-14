//! `model-report.json` + the human verdict (PLAN-models §0.6, §8: "one report,
//! always"). Hand-serialized JSON, no serde — matching the existing `report.rs`
//! and SPEC §13's offline-safe, dependency-free stance.
//!
//! The report carries the M-level reached, the reachable-set size and the bound
//! it was checked against, the safety verdict, and the deadlock/violation
//! tables. A content hash of the source ties a verdict to the exact model text.

use super::check::CheckResult;
use std::path::Path;

/// FNV-1a — a tiny, dependency-free content hash so a verdict names the exact
/// model text it certified (same role as the cache keys under `.leanlift-cache`).
pub fn content_hash(src: &str) -> String {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in src.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    format!("{h:016x}")
}

pub fn print_human(r: &CheckResult, file: &str, hash: &str) {
    println!();
    println!("  leanlift model certificate — {} `{}`", r.family, file);
    println!("  ────────────────────────────────────────────────");
    if r.safe() {
        println!("  level : M1 checked  (reachable set explored, safety holds)");
    } else if r.truncated {
        println!("  level : M0 modelled  (UNBOUNDED — bound {} hit, coverage partial)", r.bound);
    } else {
        println!("  level : M0 modelled  (safety VIOLATED — see below)");
    }
    println!();
    println!("  reachable : {} state(s){}", r.reachable, if r.truncated { " (truncated!)" } else { "" });
    println!("  deadlocks : {}", if r.deadlocks.is_empty() { "none".into() } else { r.deadlocks.join(", ") });
    if r.violations.is_empty() {
        println!("  safety    : ok (no forbidden state reachable)");
    } else {
        println!("  safety    : VIOLATED");
        for (s, why) in &r.violations {
            println!("    ✗ {s} — {why}");
        }
    }
    for note in &r.notes {
        println!("  note      : {note}");
    }
    println!("  hash      : {hash}");
    println!();
}

pub fn write_json(r: &CheckResult, file: &str, hash: &str, out: &Path) -> std::io::Result<()> {
    let level = if r.safe() {
        "M1_checked"
    } else {
        "M0_modelled"
    };
    let viols = r
        .violations
        .iter()
        .map(|(s, why)| format!("    {{ \"state\": {}, \"reason\": {} }}", json_str(s), json_str(why)))
        .collect::<Vec<_>>()
        .join(",\n");
    let deads = r
        .deadlocks
        .iter()
        .map(|s| json_str(s))
        .collect::<Vec<_>>()
        .join(", ");
    let body = format!(
        "{{\n  \"family\": {},\n  \"file\": {},\n  \"level\": \"{}\",\n  \"safe\": {},\n  \"reachable\": {},\n  \"bound\": {},\n  \"truncated\": {},\n  \"deadlocks\": [{}],\n  \"violations\": [\n{}\n  ],\n  \"hash\": \"{}\"\n}}\n",
        json_str(&r.family),
        json_str(file),
        level,
        r.safe(),
        r.reachable,
        r.bound,
        r.truncated,
        deads,
        viols,
        hash,
    );
    std::fs::write(out, body)
}

/// Report for `lift model prove`: the M1 facts plus the M3 verdict.
pub fn write_prove_json(
    m1: &CheckResult,
    file: &str,
    hash: &str,
    sorry_free: bool,
    out: &Path,
) -> std::io::Result<()> {
    let level = if sorry_free { "M3_proved" } else { "M2_unverified" };
    let body = format!(
        "{{\n  \"family\": {},\n  \"file\": {},\n  \"level\": \"{}\",\n  \"sorry_free\": {},\n  \"reachable\": {},\n  \"deadlocks\": [{}],\n  \"hash\": \"{}\"\n}}\n",
        json_str(&m1.family),
        json_str(file),
        level,
        sorry_free,
        m1.reachable,
        m1.deadlocks.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(", "),
        hash,
    );
    std::fs::write(out, body)
}

/// Minimal JSON string escaping (quotes + backslashes + control chars).
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
