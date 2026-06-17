//! Verdict, certification ladder, and report emission (SPEC §10).
//!
//!   L0 typechecks    — candidate Lean compiled/ran against the support lib
//!   L1 conformant/N  — bit-exact vs source on N vectors, divergences only in
//!                      declared semantic classes
//!   (L2 bounded-proved / L3 proved are later milestones.)

use crate::compare::{Class, Comparison};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Level {
    L0Typechecks,
    L1Conformant,
}

impl Level {
    pub fn tag(self) -> &'static str {
        match self {
            Level::L0Typechecks => "L0_typechecks",
            Level::L1Conformant => "L1_conformant",
        }
    }
}

pub struct Verdict {
    pub level: Level,
    pub conformant: bool,
    pub vectors: usize,
    pub seed: u64,
}

impl Verdict {
    pub fn assess(cmp: &Comparison, seed: u64) -> Verdict {
        let conformant = cmp.conformant();
        Verdict {
            level: if conformant { Level::L1Conformant } else { Level::L0Typechecks },
            conformant,
            vectors: cmp.lines.len(),
            seed,
        }
    }
}

/// Render the human-facing report to stdout.
pub fn print_human(cmp: &Comparison, v: &Verdict, fn_name: &str) {
    let conform = cmp.count(Class::Conform);
    let declared = cmp.count(Class::DeclaredOverflow);
    let tolerance = cmp.count(Class::ToleranceDivergence);
    let mismatch = cmp.count(Class::Mismatch);

    println!();
    println!("  leanlift verdict — fn `{fn_name}`");
    println!("  ────────────────────────────────────────────────");
    if v.conformant {
        println!("  level: L1 conformant/{}  (bit-exact on the safe domain)", v.vectors);
    } else {
        println!("  level: L0 typechecks  —  NOT conformant ({mismatch} unexplained divergence(s))");
    }
    println!();
    println!("  vectors : {}  (seed {:#018x})", v.vectors, v.seed);
    println!("  conform : {conform}  (Lean == C++, bit-exact)");
    println!("  declared: {declared}  (Lean OVERFLOW, C++ wraps — declared overflow class)");
    if tolerance > 0 {
        println!("  tol-div : {tolerance}  (float results differ but within --float-tol — benign rounding)");
    }
    println!("  mismatch: {mismatch}  (unexplained — would be a real bug)");

    let cov = cmp.branch_coverage();
    print!("  coverage:");
    for b in cmp.profile.branch_labels() {
        print!(" {}={}", b, cov.get(b).copied().unwrap_or(0));
    }
    println!();

    // Empirical postcondition ("analysis") if the profile declares one.
    if let (Some((held, total)), Some(desc)) =
        (cmp.postcondition(), cmp.profile.postcondition_desc())
    {
        let mark = if held == total { "✔" } else { "✘" };
        println!("  postcond: {held}/{total} hold  ({desc})  {mark}");
    }

    if let Some(l) = cmp.lines.iter().find(|l| l.class == Class::DeclaredOverflow) {
        println!();
        println!("  divergence (declared, overflow class):");
        println!("    lean: {} => OVERFLOW", l.vector.key());
        println!("    cpp : {} => {}  (silently wrapped)", l.vector.key(), l.cpp);
    }

    if mismatch > 0 {
        println!();
        println!("  UNEXPLAINED MISMATCHES (conformance failures):");
        for l in cmp.mismatches().take(20) {
            println!("    {}  cpp={}  lean={}", l.vector.key(), l.cpp, l.lean);
        }
    }
    println!();
}

/// JSON string escaping (values are numbers/ASCII tokens).
fn jstr(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Emit a decimal token as a bare JSON number, else as a quoted string.
fn jval(s: &str) -> String {
    if s.parse::<u64>().is_ok() {
        s.to_string()
    } else {
        jstr(s)
    }
}

/// Write `report.json` (SPEC §10).
pub fn write_json(
    cmp: &Comparison,
    v: &Verdict,
    fn_name: &str,
    path: &std::path::Path,
) -> std::io::Result<()> {
    use std::fmt::Write as _;
    let cov = cmp.branch_coverage();

    let mut s = String::new();
    writeln!(s, "{{").unwrap();
    writeln!(s, "  \"fn\": {},", jstr(fn_name)).unwrap();
    writeln!(s, "  \"level\": {},", jstr(v.level.tag())).unwrap();
    writeln!(s, "  \"conformant\": {},", v.conformant).unwrap();
    writeln!(s, "  \"vectors\": {},", v.vectors).unwrap();
    writeln!(s, "  \"seed\": {},", jstr(&format!("{:#018x}", v.seed))).unwrap();
    writeln!(s, "  \"counts\": {{").unwrap();
    writeln!(s, "    \"conform\": {},", cmp.count(Class::Conform)).unwrap();
    writeln!(s, "    \"declared_overflow\": {},", cmp.count(Class::DeclaredOverflow)).unwrap();
    writeln!(s, "    \"tolerance_divergence\": {},", cmp.count(Class::ToleranceDivergence)).unwrap();
    writeln!(s, "    \"mismatch\": {}", cmp.count(Class::Mismatch)).unwrap();
    writeln!(s, "  }},").unwrap();

    writeln!(s, "  \"coverage\": {{").unwrap();
    let labels = cmp.profile.branch_labels();
    for (i, b) in labels.iter().enumerate() {
        let comma = if i + 1 < labels.len() { "," } else { "" };
        writeln!(s, "    {}: {}{}", jstr(b), cov.get(b).copied().unwrap_or(0), comma).unwrap();
    }
    writeln!(s, "  }},").unwrap();

    writeln!(s, "  \"divergences\": [").unwrap();
    let div: Vec<_> = cmp.lines.iter().filter(|l| l.class != Class::Conform).collect();
    for (i, l) in div.iter().enumerate() {
        let cls = match l.class {
            Class::DeclaredOverflow => "declared_overflow",
            Class::ToleranceDivergence => "tolerance_divergence",
            Class::Mismatch => "mismatch",
            Class::Conform => unreachable!(),
        };
        let comma = if i + 1 < div.len() { "," } else { "" };
        writeln!(
            s,
            "    {{ \"input\": {}, \"cpp\": {}, \"lean\": {}, \"class\": {} }}{}",
            jstr(&l.vector.key()),
            jval(&l.cpp),
            jval(&l.lean),
            jstr(cls),
            comma
        )
        .unwrap();
    }
    writeln!(s, "  ]").unwrap();
    writeln!(s, "}}").unwrap();

    std::fs::write(path, s)
}
