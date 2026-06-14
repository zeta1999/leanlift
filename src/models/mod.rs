//! The behavioural-models axis (docs/SPEC-models.md, docs/PLAN-models.md): the
//! *dual* to leanlift's code→Lean engine. Author one behavioural model in an
//! easy text format and generate a Lean proof (qualitative), a PRISM model
//! (quantitative), and runnable code from one source of truth.
//!
//! Phase 0 (this slice): the shared substrate — the DTS-IR (`ir`), the native
//! M1 checker (`check`), the native format + auto-detection (`format`, `toml`),
//! and the `lift model check` CLI (`report` + `run`). FSM/PT-net/CPN/SPN
//! builders and the Lean/PRISM/code exporters land in later phases behind this
//! same one-command path.

mod check;
mod format;
mod ir;
mod lean;
mod report;
mod toml;

use format::Family;
use std::path::{Path, PathBuf};
use std::process::{exit, Command};

fn usage() -> ! {
    eprintln!(
        "usage:\n\
        \x20 lift model check <file> [--bound <N>] [--out <model-report.json>]\n\
        \x20     bounded reachability + safety (M1). Family auto-detected from <file>.\n\
        \x20 lift model prove <file> [--emit <Model.lean>] [--lean-path <dir>] [--out ...]\n\
        \x20     export a Lean model + safety proof and certify it sorry-free (M3, FSM).\n\n\
        \x20 (further phases: prism → M2 quantitative, export → code)\n"
    );
    exit(2);
}

/// Dispatch `lift model …`. Phases 0–1 implement `check` and `prove`; the other
/// verbs are recognised and report their phase so the CLI surface is stable.
pub fn main(mut argv: Vec<String>) {
    match argv.first().map(String::as_str) {
        Some("check") => {
            argv.remove(0);
            check_cmd(argv);
        }
        Some("prove") => {
            argv.remove(0);
            prove_cmd(argv);
        }
        Some(verb @ ("prism" | "export" | "simulate" | "import")) => {
            eprintln!("`lift model {verb}` is planned (see docs/PLAN-models.md) — not in this build");
            exit(2);
        }
        _ => usage(),
    }
}

fn check_cmd(a: Vec<String>) {
    let mut file: Option<String> = None;
    let mut out = PathBuf::from("model-report.json");
    let mut bound = check::DEFAULT_BOUND;

    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
            "--out" => out = PathBuf::from(take(&a, &mut i)),
            "--bound" => {
                bound = take(&a, &mut i)
                    .parse()
                    .unwrap_or_else(|_| fail("--bound expects a positive integer"))
            }
            s if s.starts_with("--") => fail(&format!("unknown flag: {s}")),
            _ => {
                if file.is_some() {
                    usage();
                }
                file = Some(a[i].clone());
            }
        }
        i += 1;
    }
    let file = file.unwrap_or_else(|| usage());

    let src = std::fs::read_to_string(&file)
        .unwrap_or_else(|e| fail(&format!("cannot read {file}: {e}")));
    let hash = report::content_hash(&src);

    let doc = toml::parse(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
    let family = format::detect(&doc).unwrap_or_else(|e| fail(&format!("{file}: {e}")));

    let model = match family {
        Family::Fsm => format::parse_fsm(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}"))),
        other => {
            eprintln!(
                "detected `{}` model — only `fsm` is wired in this build (see docs/PLAN-models.md)",
                other.tag()
            );
            exit(2);
        }
    };

    let result = check::check(&model, bound);
    report::print_human(&result, &file, &hash);
    if let Err(e) = report::write_json(&result, &file, &hash, &out) {
        eprintln!("warning: could not write {}: {e}", out.display());
    } else {
        eprintln!("  model-report.json -> {}", out.display());
    }
    exit(if result.safe() { 0 } else { 1 });
}

fn prove_cmd(a: Vec<String>) {
    let mut file: Option<String> = None;
    let mut out = PathBuf::from("model-report.json");
    let mut lean_path = PathBuf::from("lean");
    let mut emit: Option<PathBuf> = None;

    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
            "--out" => out = PathBuf::from(take(&a, &mut i)),
            "--lean-path" => lean_path = PathBuf::from(take(&a, &mut i)),
            "--emit" => emit = Some(PathBuf::from(take(&a, &mut i))),
            s if s.starts_with("--") => fail(&format!("unknown flag: {s}")),
            _ => {
                if file.is_some() {
                    usage();
                }
                file = Some(a[i].clone());
            }
        }
        i += 1;
    }
    let file = file.unwrap_or_else(|| usage());

    let src = std::fs::read_to_string(&file)
        .unwrap_or_else(|e| fail(&format!("cannot read {file}: {e}")));
    let hash = report::content_hash(&src);

    let doc = toml::parse(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
    match format::detect(&doc).unwrap_or_else(|e| fail(&format!("{file}: {e}"))) {
        Family::Fsm => {}
        other => {
            eprintln!(
                "`lift model prove` supports `fsm` in this build; detected `{}` (see docs/PLAN-models.md)",
                other.tag()
            );
            exit(2);
        }
    }
    let model = format::parse_fsm(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));

    // M1 first (so the certificate reports reachable size and any deadlock).
    let m1 = check::check(&model, check::DEFAULT_BOUND);

    // Compile the Models support theory, then emit + elaborate the proof.
    if let Err(e) = ensure_models_lib(&lean_path) {
        fail(&format!("{e}"));
    }
    let ns = lean_namespace(&file);
    let generated = lean::emit_fsm(&model, &ns);
    let emit_path = emit.unwrap_or_else(|| PathBuf::from(format!("{}.gen.lean", file_stem(&file))));
    if let Err(e) = std::fs::write(&emit_path, &generated) {
        fail(&format!("cannot write {}: {e}", emit_path.display()));
    }

    let abs_lean = std::fs::canonicalize(&lean_path)
        .unwrap_or_else(|e| fail(&format!("cannot resolve --lean-path {}: {e}", lean_path.display())));
    eprintln!("  proving `{file}` (M3) — emit Lean, elaborate, certify sorry-free");
    let output = Command::new("lean")
        .arg(&emit_path)
        .env("LEAN_PATH", &abs_lean)
        .output()
        .unwrap_or_else(|e| fail(&format!("failed to invoke lean: {e}")));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        eprintln!("\n  level: M1 (Lean proof did NOT elaborate):\n");
        eprintln!("{}", stderr.trim());
        let _ = report::write_prove_json(&m1, &file, &hash, false, &out);
        exit(1);
    }
    // Elaborated. Sorry-free iff `#print axioms` reports no `sorryAx`.
    let sorry_free = !stdout.contains("sorryAx");
    let axioms = stdout.lines().find(|l| l.contains("axioms")).unwrap_or("").trim();

    println!();
    println!("  leanlift model certificate — fsm `{file}`");
    println!("  ────────────────────────────────────────────────");
    if sorry_free {
        println!("  level : M3 proved  (Lean safety theorem closed, sorry-free)");
    } else {
        println!("  level : M2  —  proof present but NOT sorry-free");
    }
    println!();
    println!("  reachable : {} state(s)", m1.reachable);
    println!("  theorem   : {ns}.safety  (every reachable state satisfies safeB)");
    println!("  axioms    : {}", if axioms.is_empty() { "(none)" } else { axioms });
    println!("  Lean      : {}", emit_path.display());
    println!("  hash      : {hash}");
    println!();

    if let Err(e) = report::write_prove_json(&m1, &file, &hash, sorry_free, &out) {
        eprintln!("warning: could not write {}: {e}", out.display());
    } else {
        eprintln!("  model-report.json -> {}", out.display());
    }
    exit(if sorry_free { 0 } else { 1 });
}

/// Compile `lean/LeanLift/Models/*.lean` → `.olean` if stale, so generated
/// proofs can `import LeanLift.Models.Fsm`. Mirrors `main.rs::ensure_support_lib`
/// for the Models subdirectory.
fn ensure_models_lib(lean_path: &Path) -> Result<(), String> {
    let dir = lean_path.join("LeanLift/Models");
    let entries = std::fs::read_dir(&dir)
        .map_err(|e| format!("cannot read Models theory dir {}: {e}", dir.display()))?;
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
        eprintln!("  building Models theory: {}", src.display());
        let rel = src.strip_prefix(lean_path).unwrap();
        let status = Command::new("lean")
            .arg("-o")
            .arg(olean.strip_prefix(lean_path).unwrap())
            .arg(rel)
            .current_dir(lean_path)
            .status()
            .map_err(|e| format!("failed to invoke lean: {e}"))?;
        if !status.success() {
            return Err(format!("Models theory failed to compile: {}", src.display()));
        }
    }
    Ok(())
}

fn file_stem(file: &str) -> String {
    let stem = Path::new(file)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("model");
    // `mcl.model.toml` → file_stem `mcl.model` → drop the `.model` tag → `mcl`.
    stem.strip_suffix(".model").unwrap_or(stem).to_string()
}

/// A Lean-safe namespace from the file stem: `mcl.model` → `Mcl`, `dock-net` → `Docknet`.
fn lean_namespace(file: &str) -> String {
    let stem = file_stem(file);
    let cleaned: String = stem.chars().filter(|c| c.is_ascii_alphanumeric()).collect();
    if cleaned.is_empty() {
        return "Model".into();
    }
    let mut cs = cleaned.chars();
    let head = cs.next().unwrap().to_ascii_uppercase();
    format!("{head}{}", cs.as_str())
}

fn take(a: &[String], i: &mut usize) -> String {
    *i += 1;
    a.get(*i).cloned().unwrap_or_else(|| usage())
}

fn fail(msg: &str) -> ! {
    eprintln!("error: {msg}");
    exit(2);
}
