//! `lift` — leanlift CLI (SPEC §9).
//!
//! M0 slice: `lift verify <example> [--out report.json]`
//!   1. ensure the audited Lean support library is compiled
//!   2. generate deterministic vectors for the example
//!   3. compile source + a typed runner → run it (the native oracle)
//!   4. run the Lean candidate over the same vectors (the L0 gate)
//!   5. bit-exact compare + classify divergences against the profile
//!   6. emit a human report + report.json, and a 0/nonzero exit code
//!
//! "LLM proposes, algorithm disposes" — the candidate here is hand-written, but
//! the validation path is the real one the LLM/Aeneas front-ends plug into.

mod compare;
mod examples;
mod frontend;
mod harness;
mod lang;
mod leanrt;
mod oracle;
mod oracle_sol;
mod report;
mod sig;
mod vectors;

use std::path::{Path, PathBuf};
use std::process::{exit, Command};

struct Args {
    example: String,
    lean_path: PathBuf,
    out: PathBuf,
    candidate: Option<PathBuf>,
}

fn usage() -> ! {
    eprintln!(
        "usage: lift verify <example> [--lean <candidate.lean>] \\\n\
        \x20            [--lean-path <dir>] [--out <report.json>]\n\n\
        \x20 verify a source function against a Lean candidate by bit-exact\n\
        \x20 differential execution (M0 slice). --lean overrides the example's\n\
        \x20 built-in candidate (the hook the LLM front-end writes to).\n\n\
        \x20 examples: {}\n",
        examples::NAMES.join(", ")
    );
    exit(2);
}

fn parse_args() -> Args {
    let mut a: Vec<String> = std::env::args().skip(1).collect();
    if a.first().map(String::as_str) != Some("verify") {
        usage();
    }
    a.remove(0);

    let mut example: Option<String> = None;
    let mut lean_path = PathBuf::from("lean");
    let mut out = PathBuf::from("report.json");
    let mut candidate: Option<PathBuf> = None;

    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
            "--example" => example = Some(take(&a, &mut i)),
            "--lean" => candidate = Some(PathBuf::from(take(&a, &mut i))),
            "--lean-path" => lean_path = PathBuf::from(take(&a, &mut i)),
            "--out" => out = PathBuf::from(take(&a, &mut i)),
            s if s.starts_with("--") => {
                eprintln!("unknown flag: {s}");
                usage();
            }
            _ => {
                if example.is_some() {
                    usage();
                }
                example = Some(a[i].clone());
            }
        }
        i += 1;
    }

    Args { example: example.unwrap_or_else(|| usage()), lean_path, out, candidate }
}

fn take(a: &[String], i: &mut usize) -> String {
    *i += 1;
    a.get(*i).cloned().unwrap_or_else(|| usage())
}

/// Compile every `LeanLift/*.lean` support module to `.olean` if stale/missing.
fn ensure_support_lib(lean_path: &Path) -> Result<(), String> {
    let dir = lean_path.join("LeanLift");
    let entries = std::fs::read_dir(&dir)
        .map_err(|e| format!("cannot read support lib dir {}: {e}", dir.display()))?;
    for entry in entries.flatten() {
        let src = entry.path();
        if src.extension().and_then(|s| s.to_str()) != Some("lean") {
            continue;
        }
        let olean = src.with_extension("olean");
        let stale = match (std::fs::metadata(&olean), std::fs::metadata(&src)) {
            (Ok(o), Ok(s)) => match (o.modified(), s.modified()) {
                (Ok(om), Ok(sm)) => om < sm,
                _ => true,
            },
            _ => true,
        };
        if !stale {
            continue;
        }
        eprintln!("  building support lib: {}", src.display());
        let rel = src.strip_prefix(lean_path).unwrap();
        let status = Command::new("lean")
            .arg("-o")
            .arg(olean.strip_prefix(lean_path).unwrap())
            .arg(rel)
            .current_dir(lean_path)
            .status()
            .map_err(|e| format!("failed to invoke lean: {e}"))?;
        if !status.success() {
            return Err(format!("support lib failed to compile: {}", src.display()));
        }
    }
    Ok(())
}

fn main() {
    let args = parse_args();
    let ex = examples::lookup(&args.example).unwrap_or_else(|| {
        eprintln!("unknown example `{}` (have: {})", args.example, examples::NAMES.join(", "));
        exit(2);
    });

    let work = std::env::temp_dir().join("leanlift-work");
    let _ = std::fs::create_dir_all(&work);

    // 1. audited Lean support library.
    if let Err(e) = ensure_support_lib(&args.lean_path) {
        eprintln!("error: {e}");
        exit(1);
    }

    // 2. deterministic vectors.
    let vecs = (ex.gen)();
    eprintln!("  example `{}`: {} vectors (seed {:#018x})", ex.name, vecs.len(), vectors::SEED);

    // 3. source oracle (native for C++/Go, EVM for Solidity).
    let cpp = match oracle::run(ex.lang, &ex.source, ex.fn_name, &ex.signature, &vecs, &work) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error building/running oracle: {e}");
            exit(1);
        }
    };

    // 4. Obtain the candidate via the front-end (the sound Rust path runs
    //    Charon+Aeneas here), then run it over the same vectors — the L0 gate.
    //    A --lean override swaps in an external candidate (e.g. LLM-generated).
    let frontend = match &args.candidate {
        Some(p) => frontend::Frontend::Prewritten {
            runner: p.clone(),
            lean_path: args.lean_path.clone(),
        },
        None => ex.frontend,
    };
    let candidate = match &frontend {
        // The LLM path runs its own propose→difftest→repair loop (it needs the
        // oracle results), and returns the final candidate.
        frontend::Frontend::Llm { max_iters } => {
            match harness::run_llm(
                ex.lang, &ex.source, ex.fn_name, &ex.signature, &vecs, &cpp, ex.profile,
                &args.lean_path, &work, *max_iters,
            ) {
                Ok(o) => {
                    eprintln!("  harness: settled after {} iter(s), conformant={}", o.iters, o.conformant);
                    o.candidate
                }
                Err(e) => {
                    eprintln!("error in LLM front-end: {e}");
                    exit(1);
                }
            }
        }
        other => match other.produce(&ex.signature, &work) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("error in front-end: {e}");
                exit(1);
            }
        },
    };
    let lean = match leanrt::run(&candidate, &vecs, &work) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("\n  level: L0 FAILED — candidate did not typecheck/run:\n");
            eprintln!("{}", e.0);
            exit(1);
        }
    };

    // 5. compare + classify.
    let cmp = compare::compare(&vecs, &cpp, &lean, ex.profile);
    let verdict = report::Verdict::assess(&cmp, vectors::SEED);

    // 6. report.
    report::print_human(&cmp, &verdict, ex.fn_name);
    if let Err(e) = report::write_json(&cmp, &verdict, ex.fn_name, &args.out) {
        eprintln!("warning: could not write {}: {e}", args.out.display());
    } else {
        eprintln!("  report.json -> {}", args.out.display());
    }

    exit(if verdict.conformant { 0 } else { 1 });
}
