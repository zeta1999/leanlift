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
mod report;
mod toml;

use format::Family;
use std::path::PathBuf;
use std::process::exit;

fn usage() -> ! {
    eprintln!(
        "usage:\n\
        \x20 lift model check <file> [--bound <N>] [--out <model-report.json>]\n\
        \x20     bounded reachability + safety (M1). Family auto-detected from <file>.\n\n\
        \x20 (further phases: prove → M3 Lean, prism → M2 quantitative, export → code)\n"
    );
    exit(2);
}

/// Dispatch `lift model …`. Phase 0 implements `check`; the other verbs are
/// recognised and report their phase so the CLI surface is stable from day one.
pub fn main(mut argv: Vec<String>) {
    match argv.first().map(String::as_str) {
        Some("check") => {
            argv.remove(0);
            check_cmd(argv);
        }
        Some(verb @ ("prove" | "prism" | "export" | "simulate" | "import")) => {
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

fn take(a: &[String], i: &mut usize) -> String {
    *i += 1;
    a.get(*i).cloned().unwrap_or_else(|| usage())
}

fn fail(msg: &str) -> ! {
    eprintln!("error: {msg}");
    exit(2);
}
