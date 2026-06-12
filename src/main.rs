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
mod prove;
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
        "usage:\n\
        \x20 lift verify <example> [--lean <candidate.lean>] [--lean-path <dir>] [--out <report.json>]\n\
        \x20     bit-exact differential validation (L1). --lean overrides the example's candidate.\n\
        \x20 lift prove  <example> [--out <proof.json>]\n\
        \x20     discharge the example's proof obligation on the extracted model (L3, Aeneas only).\n\n\
        \x20 examples: {}\n",
        examples::NAMES.join(", ")
    );
    exit(2);
}

fn parse_verify_args(a: Vec<String>) -> Args {

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
    let mut argv: Vec<String> = std::env::args().skip(1).collect();
    match argv.first().map(String::as_str) {
        Some("verify") => {
            argv.remove(0);
            verify_cmd(parse_verify_args(argv));
        }
        Some("prove") => {
            argv.remove(0);
            prove_cmd(argv);
        }
        _ => usage(),
    }
}

/// `lift prove <example>` — extract the model and discharge its proof obligation.
fn prove_cmd(a: Vec<String>) {
    let mut example: Option<String> = None;
    let mut out = PathBuf::from("proof.json");
    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
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
    let name = example.unwrap_or_else(|| usage());
    let ex = examples::lookup(&name).unwrap_or_else(|| {
        eprintln!("unknown example `{name}` (have: {})", examples::NAMES.join(", "));
        exit(2);
    });
    let frag = ex.proof_frag.clone().unwrap_or_else(|| {
        eprintln!("no proof obligation defined for `{}`", ex.name);
        exit(2);
    });
    let (crate_dir, entrypoint) = match &ex.frontend {
        frontend::Frontend::RustAeneas { crate_dir, entrypoint } => {
            (crate_dir.clone(), entrypoint.clone())
        }
        _ => {
            eprintln!("`lift prove` currently supports Aeneas-extracted (Rust) examples only");
            exit(2);
        }
    };

    let work = std::env::temp_dir().join("leanlift-work");
    let _ = std::fs::create_dir_all(&work);
    eprintln!("  proving `{}` (L3) — extract model, discharge obligations", ex.name);

    let def = match frontend::extract_rust_def(&crate_dir, &entrypoint, &work) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error extracting model: {e}");
            exit(1);
        }
    };
    let rep = match prove::prove_aeneas(&def, &frag, &frontend::aeneas_install(), &work) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("\n  level: L1 (proof did NOT close):\n{e}");
            exit(1);
        }
    };

    println!();
    println!("  leanlift certificate — fn `{}`", ex.fn_name);
    println!("  ────────────────────────────────────────────────");
    if rep.sorry_free {
        println!("  level: L3 proved  (Lean theorems closed, sorry-free)");
    } else {
        println!("  level: L2  —  proof present but NOT sorry-free");
    }
    println!();
    println!("  obligations ({}):", rep.theorems.len());
    for t in &rep.theorems {
        println!("    ✓ {t}");
    }
    println!("  axioms  : {}", rep.axioms.join(", "));
    println!("  sorry-free: {}", rep.sorry_free);

    let lib = std::fs::read_to_string(crate_dir.join("src/lib.rs")).unwrap_or_default();
    let crate_src = slice_rust_fn(&lib, &entrypoint).unwrap_or(lib);
    let recipe = PathBuf::from(format!("{}.recipe.md", ex.name));
    if prove::write_recipe(&recipe, ex.name, &crate_src, &def, &rep).is_ok() {
        eprintln!("  recipe  -> {}", recipe.display());
    }
    let _ = std::fs::write(
        &out,
        format!(
            "{{\n  \"fn\": \"{}\",\n  \"level\": \"{}\",\n  \"sorry_free\": {},\n  \"theorems\": [{}],\n  \"axioms\": [{}]\n}}\n",
            ex.fn_name,
            if rep.sorry_free { "L3_proved" } else { "L2_unverified" },
            rep.sorry_free,
            rep.theorems.iter().map(|t| format!("\"{t}\"")).collect::<Vec<_>>().join(", "),
            rep.axioms.iter().map(|x| format!("\"{x}\"")).collect::<Vec<_>>().join(", "),
        ),
    );
    eprintln!("  proof.json -> {}", out.display());
    exit(if rep.sorry_free { 0 } else { 1 });
}

/// Slice `fn <name>( … )` from Rust source: from the signature line down to the
/// first column-0 `}` (for the recipe — avoids dumping the whole file).
fn slice_rust_fn(src: &str, name: &str) -> Option<String> {
    let lines: Vec<&str> = src.lines().collect();
    let start = lines.iter().position(|l| l.contains(&format!("fn {name}(")))?;
    let mut end = lines.len();
    for (i, l) in lines.iter().enumerate().skip(start) {
        if i > start && l.starts_with('}') {
            end = i + 1;
            break;
        }
    }
    Some(lines[start..end].join("\n"))
}

fn verify_cmd(args: Args) {
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
