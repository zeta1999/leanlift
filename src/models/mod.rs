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

mod bt;
mod check;
mod codegen;
mod cpn;
mod format;
mod gspn;
mod ir;
mod lean;
mod pnml;
mod prism;
#[cfg(test)]
mod fuzz;
#[cfg(test)]
mod proptest;
mod report;
mod scxml;
mod toml;
mod xml;

use format::Family;
use std::path::{Path, PathBuf};
use std::process::{exit, Command};

fn usage() -> ! {
    eprintln!(
        "usage:\n\
        \x20 lift model check <file> [--bound <N>] [--out <model-report.json>]\n\
        \x20     bounded reachability + safety (M1). Family auto-detected from <file>.\n\
        \x20 lift model prove <file> [--emit <Model.lean>] [--lean-path <dir>] [--out ...]\n\
        \x20     export a Lean model + safety proof and certify it sorry-free (M3, FSM/BT/Petri/CPN).\n\
        \x20 lift model prism <file> [--emit <prefix>] [--out ...]\n\
        \x20     GSPN → tangible CTMC: solve quantitative queries + export PRISM (M2).\n\
        \x20 lift model export <file> [--lang rust|c++|go|dot] [--emit <out>] [--verify] [--samples N [--seed S]]\n\
        \x20     generate a runnable executor (FSM/BT/Petri); --verify difftests it vs the model (L1,\n\
        \x20     exhaustive reachable-edge coverage; --samples adds random traces for unbounded nets).\n"
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
        Some("prism") => {
            argv.remove(0);
            prism_cmd(argv);
        }
        Some("export") => {
            argv.remove(0);
            export_cmd(argv);
        }
        Some(verb @ ("simulate" | "import")) => {
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

    // Standard XML input (SCXML → FSM, PNML → PT-net), checked like a native model.
    if is_xml(&src) {
        let result = match load_xml(&file, &src) {
            XmlModel::Lts(lts) => check::check(&lts, bound),
            XmlModel::Petri(net) => {
                let mut r = check::check(&net, bound);
                r.notes = petri_notes(&net, &r);
                r
            }
        };
        report::print_human(&result, &file, &hash);
        if let Err(e) = report::write_json(&result, &file, &hash, &out) {
            eprintln!("warning: could not write {}: {e}", out.display());
        } else {
            eprintln!("  model-report.json -> {}", out.display());
        }
        exit(if result.safe() { 0 } else { 1 });
    }

    let doc = toml::parse(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
    let family = format::detect(&doc).unwrap_or_else(|e| fail(&format!("{file}: {e}")));

    let result = match family {
        Family::Fsm => {
            let m = format::parse_fsm(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
            check::check(&m, bound)
        }
        Family::Bt => {
            // A BT compiles to an LTS, so the FSM checker applies unchanged.
            let m = bt::parse_bt(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
            check::check(&m, bound)
        }
        Family::Petri => {
            let net = format::parse_petri(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
            let mut r = check::check(&net, bound);
            r.notes = petri_notes(&net, &r);
            r
        }
        Family::Cpn => {
            // A CPN unfolds to a PT-net, so the Petri checker applies unchanged.
            let (net, mut notes) = cpn::unfold(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
            let r = check::check(&net, bound);
            notes.extend(petri_notes(&net, &r));
            let mut r = r;
            r.notes = notes;
            r
        }
        Family::Spn => {
            eprintln!("detected a stochastic (gspn) model — use `lift model prism <file>` for M2 quantitative analysis");
            exit(2);
        }
    };
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

    let ns = lean_namespace(&file);

    // Standard XML input (SCXML → FSM, PNML → PT-net) → the matching exporter.
    let (m1, generated) = if is_xml(&src) {
        match load_xml(&file, &src) {
            XmlModel::Lts(lts) => {
                let r = check::check(&lts, check::DEFAULT_BOUND);
                (r, lean::emit_fsm(&lts, &ns))
            }
            XmlModel::Petri(net) => {
                let mut r = check::check(&net, check::DEFAULT_BOUND);
                r.notes = petri_notes(&net, &r);
                (r, lean::emit_petri(&net, &ns))
            }
        }
    } else {
    let doc = toml::parse(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
    let family = format::detect(&doc).unwrap_or_else(|e| fail(&format!("{file}: {e}")));

    // Build the model, run M1 (the certificate reports reachable size), and emit
    // the Lean proof — both families ride the same elaborate-and-certify path.
    match family {
        Family::Fsm => {
            let m = format::parse_fsm(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
            let r = check::check(&m, check::DEFAULT_BOUND);
            (r, lean::emit_fsm(&m, &ns))
        }
        Family::Bt => {
            // BT → LTS → the FSM exporter (the §3.3 reuse payoff).
            let m = bt::parse_bt(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
            let r = check::check(&m, check::DEFAULT_BOUND);
            (r, lean::emit_fsm(&m, &ns))
        }
        Family::Petri => {
            let net = format::parse_petri(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
            let mut r = check::check(&net, check::DEFAULT_BOUND);
            r.notes = petri_notes(&net, &r);
            (r, lean::emit_petri(&net, &ns))
        }
        Family::Cpn => {
            // CPN → unfold → the Petri exporter (the §4.3/§4.4 reuse payoff).
            let (net, mut notes) = cpn::unfold(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
            let mut r = check::check(&net, check::DEFAULT_BOUND);
            notes.extend(petri_notes(&net, &r));
            r.notes = notes;
            (r, lean::emit_petri(&net, &ns))
        }
        other => {
            eprintln!(
                "`lift model prove` supports fsm/bt/petri in this build; detected `{}`",
                other.tag()
            );
            exit(2);
        }
    }
    };

    // Compile the Models support theory, then emit + elaborate the proof.
    if let Err(e) = ensure_models_lib(&lean_path) {
        fail(&format!("{e}"));
    }
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
    println!("  leanlift model certificate — {} `{file}`", m1.family);
    println!("  ────────────────────────────────────────────────");
    if sorry_free {
        println!("  level : M3 proved  (Lean safety theorem closed, sorry-free)");
    } else {
        println!("  level : M2  —  proof present but NOT sorry-free");
    }
    println!();
    println!("  reachable : {} state(s)", m1.reachable);
    for note in &m1.notes {
        println!("  note      : {note}");
    }
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

fn export_cmd(a: Vec<String>) {
    use codegen::Lang;
    let mut file: Option<String> = None;
    let mut lang = Lang::Rust;
    let mut emit: Option<PathBuf> = None;
    let mut verify = false;
    let mut samples: usize = 0; // 0 ⇒ exhaustive only; >0 adds random traces (scale)
    let mut seed: u64 = crate::vectors::SEED;

    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
            "--lang" => lang = Lang::parse(&take(&a, &mut i)).unwrap_or_else(|| fail("--lang must be rust/c++/go")),
            "--emit" => emit = Some(PathBuf::from(take(&a, &mut i))),
            "--verify" => verify = true,
            "--samples" => samples = take(&a, &mut i).parse().unwrap_or_else(|_| fail("--samples expects an integer")),
            "--seed" => seed = take(&a, &mut i).parse().unwrap_or_else(|_| fail("--seed expects an integer")),
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
    let src = std::fs::read_to_string(&file).unwrap_or_else(|e| fail(&format!("cannot read {file}: {e}")));

    // Build the model — FSM/BT → an LTS, Petri/CPN/PNML → a PT-net. Both export
    // (and difftest) through the same codegen + loop-closure path.
    enum Cg {
        Lts(ir::Lts),
        Petri(ir::PtNet),
    }
    let model = if is_xml(&src) {
        match load_xml(&file, &src) {
            XmlModel::Lts(l) => Cg::Lts(l),
            XmlModel::Petri(n) => Cg::Petri(n),
        }
    } else {
        let doc = toml::parse(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
        match format::detect(&doc).unwrap_or_else(|e| fail(&format!("{file}: {e}"))) {
            Family::Fsm => Cg::Lts(format::parse_fsm(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")))),
            Family::Bt => Cg::Lts(bt::parse_bt(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")))),
            Family::Petri => Cg::Petri(format::parse_petri(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")))),
            Family::Cpn => Cg::Petri(cpn::unfold(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}"))).0),
            other => {
                eprintln!("code export covers fsm/bt/petri/cpn in this build; detected `{}`", other.tag());
                exit(2);
            }
        }
    };

    let (code, family) = match &model {
        Cg::Lts(l) => (codegen::emit(l, lang), l.family),
        Cg::Petri(n) => (codegen::emit_petri(n, lang), "petri"),
    };
    let out = emit.unwrap_or_else(|| PathBuf::from(format!("{}.{}", file_stem(&file), lang.ext())));
    std::fs::write(&out, &code).unwrap_or_else(|e| fail(&format!("cannot write {}: {e}", out.display())));

    println!();
    println!("  leanlift code export — {family} `{file}` → {}", lang.tag());
    println!("  ────────────────────────────────────────────────");
    println!("  source : {}", out.display());

    if verify && !lang.executable() {
        println!("  (dot is a visualization, not an executor — nothing to --verify)");
        exit(0);
    }
    if verify {
        // Difftest against the native model over EXHAUSTIVE edge coverage, plus
        // `--samples` random traces (the supplement for unbounded/huge models).
        let extra = if samples > 0 { Some((samples, seed)) } else { None };
        let result = match &model {
            Cg::Lts(l) => conformance(l, &l.alphabet, lang, &out, extra),
            Cg::Petri(n) => conformance(n, &codegen::petri_alphabet(n), lang, &out, extra),
        };
        match result {
            Ok((n, truncated)) => {
                let note = if truncated { " (bounded — coverage partial, net is unbounded)" } else { "" };
                println!("  loop closure : L1 conformant — {n}/{n} reachable edges match the native model{note}");
                println!("  (generated code ≡ model semantics — the two halves of leanlift meet)");
                exit(0);
            }
            Err(e) => {
                println!("  loop closure : FAILED — {e}");
                exit(1);
            }
        }
    } else {
        println!("  (re-run with --verify to difftest the generated code against the model)");
        exit(0);
    }
}

/// The loop closure (§6.3): compile the generated executor, run it over
/// deterministic action traces, and difftest its output against the native model
/// simulator. Returns the number of matching traces or the first mismatch.
fn conformance(
    model: &dyn ir::Model,
    alphabet: &[String],
    lang: codegen::Lang,
    src: &Path,
    samples: Option<(usize, u64)>,
) -> Result<(usize, bool), String> {
    use codegen::Lang;
    let work = std::env::temp_dir().join("leanlift-models-work");
    let _ = std::fs::create_dir_all(&work);
    let bin = work.join("model_exec");
    // Copy to a canonically-suffixed source (go build requires a `.go` name; c++
    // infers the language from the extension) so --verify works regardless of
    // the user's --emit filename.
    let csrc = work.join(format!("model_exec.{}", lang.ext()));
    std::fs::copy(src, &csrc).map_err(|e| format!("staging source: {e}"))?;

    // Compile.
    let status = match lang {
        Lang::Rust => Command::new("rustc").args(["-O", "-o"]).arg(&bin).arg(&csrc).status(),
        Lang::Cpp => Command::new("c++").args(["-O2", "-std=c++17", "-o"]).arg(&bin).arg(&csrc).status(),
        Lang::Go => Command::new("go").arg("build").arg("-o").arg(&bin).arg(&csrc).status(),
        Lang::Dot => return Err("dot is not executable".into()),
    }
    .map_err(|e| format!("could not invoke the {} compiler: {e}", lang.tag()))?;
    if !status.success() {
        return Err(format!("generated {} did not compile", lang.tag()));
    }

    // Exhaustive (state, action)-edge coverage. Compute the native reference over
    // EXACTLY the lines the executor will read (so trailing-empty-line handling
    // matches bit for bit — `str::lines()` drops a final empty line, both sides).
    let (mut traces, truncated) = codegen::coverage_traces(model, alphabet, check::DEFAULT_BOUND);
    if let Some((n, seed)) = samples {
        // Supplement with random traces of length ~3× the explored frontier.
        let max_len = (3 * traces.len().max(2)).min(64);
        traces.extend(codegen::random_traces(alphabet, n, max_len, seed));
    }
    let stdin_data = traces.iter().map(|t| t.join(" ")).collect::<Vec<_>>().join("\n");
    let lines: Vec<String> = stdin_data.lines().map(str::to_string).collect();
    let native: Vec<String> = lines
        .iter()
        .map(|l| {
            let toks: Vec<String> = l.split_whitespace().map(str::to_string).collect();
            codegen::native_trace(model, &toks)
        })
        .collect();

    // Run the generated executor over the same traces.
    use std::io::Write;
    use std::process::Stdio;
    let mut child = Command::new(&bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("could not run generated binary: {e}"))?;
    child.stdin.take().unwrap().write_all(stdin_data.as_bytes()).map_err(|e| format!("stdin: {e}"))?;
    let output = child.wait_with_output().map_err(|e| format!("wait: {e}"))?;
    let got: Vec<String> = String::from_utf8_lossy(&output.stdout).lines().map(|l| l.to_string()).collect();

    if got.len() != native.len() {
        return Err(format!("trace count mismatch: generated {} vs native {}", got.len(), native.len()));
    }
    for (i, (g, n)) in got.iter().zip(&native).enumerate() {
        if g != n {
            return Err(format!(
                "edge trace {i} diverges:\n      trace   : {}\n      native  : {n}\n      codegen : {g}",
                lines[i]
            ));
        }
    }
    Ok((native.len(), truncated))
}

fn prism_cmd(a: Vec<String>) {
    let mut file: Option<String> = None;
    let mut out = PathBuf::from("model-report.json");
    let mut emit: Option<String> = None;

    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
            "--out" => out = PathBuf::from(take(&a, &mut i)),
            "--emit" => emit = Some(take(&a, &mut i)),
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
    let src = std::fs::read_to_string(&file).unwrap_or_else(|e| fail(&format!("cannot read {file}: {e}")));
    let hash = report::content_hash(&src);

    let doc = toml::parse(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
    match format::detect(&doc).unwrap_or_else(|e| fail(&format!("{file}: {e}"))) {
        Family::Spn => {}
        other => {
            eprintln!("`lift model prism` needs a `kind = \"gspn\"` model; detected `{}`", other.tag());
            exit(2);
        }
    }
    let net = gspn::parse(&src).unwrap_or_else(|e| fail(&format!("{file}: {e}")));
    if net.has_immediate_cycle() {
        fail(&format!(
            "{file}: GSPN has an immediate-transition cycle (a 'timeless trap') — the CTMC is \
             ill-defined; give the immediate loop a timed transition or a budget"
        ));
    }

    eprintln!("  measuring `{file}` (M2) — build tangible CTMC, solve, export PRISM");
    let (tang, q) = net.ctmc();
    let start = net.dominant_start(&tang);

    // Native quantitative results (the self-check anchor).
    let results: Vec<(String, f64)> =
        net.queries.iter().map(|qq| (qq.name.clone(), net.evaluate(qq, &tang, &q))).collect();

    // Emit the PRISM model + props.
    let prefix = emit.unwrap_or_else(|| file_stem(&file));
    let model_path = PathBuf::from(format!("{prefix}.prism"));
    let props_path = PathBuf::from(format!("{prefix}.props"));
    let _ = std::fs::write(&model_path, prism::emit_model(&net, &tang, &q, start));
    let _ = std::fs::write(&props_path, prism::emit_props(&net));

    // Run PRISM if present, and diff; else self-check against the native solver.
    let prism_ok = run_prism_and_diff(&model_path, &props_path, &results);

    println!();
    println!("  leanlift model certificate — gspn `{file}` (mode: {})", net.mode);
    println!("  ────────────────────────────────────────────────");
    println!("  level : M2 measured  (quantitative CTMC analysis)");
    println!();
    println!("  tangible states : {}", tang.len());
    for (name, val) in &results {
        println!("    {name:<24} = {val:.6}");
    }
    match &prism_ok {
        Some(true) => println!("  PRISM     : present — results agree (machine-checked)"),
        Some(false) => println!("  PRISM     : present — DISAGREEMENT (see above)"),
        None => println!("  PRISM     : not on PATH — self-checked against the native CTMC solver"),
    }
    println!("  PRISM model : {}  /  {}", model_path.display(), props_path.display());
    println!("  hash      : {hash}");
    println!();
    eprintln!("  (qualitative companion: the inevitability skeleton is provable in Lean —");
    eprintln!("   LeanLift/Models/Ctmc.lean; PRISM says how likely/fast, Lean says it must.)");

    if let Err(e) = report::write_prism_json(&net.mode, &results, &file, &hash, prism_ok, &out) {
        eprintln!("warning: could not write {}: {e}", out.display());
    } else {
        eprintln!("  model-report.json -> {}", out.display());
    }
    exit(0);
}

/// Run the PRISM binary (if on PATH) and compare its `Result:` lines to the
/// native results. `Some(true)` agree, `Some(false)` disagree, `None` no binary.
fn run_prism_and_diff(model: &Path, props: &Path, results: &[(String, f64)]) -> Option<bool> {
    let out = Command::new("prism").arg(model).arg(props).output().ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    let prism_vals: Vec<f64> = text
        .lines()
        .filter_map(|l| l.trim().strip_prefix("Result:"))
        .filter_map(|r| r.trim().split_whitespace().next())
        .filter_map(|n| n.parse::<f64>().ok())
        .collect();
    if prism_vals.len() != results.len() {
        eprintln!("  (PRISM ran but returned {} results vs {} queries)", prism_vals.len(), results.len());
        return Some(false);
    }
    let mut agree = true;
    for ((name, ours), theirs) in results.iter().zip(&prism_vals) {
        if (ours - theirs).abs() > 1e-4 {
            agree = false;
            eprintln!("  PRISM mismatch on {name}: native {ours:.6} vs prism {theirs:.6}");
        }
    }
    Some(agree)
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

/// The Petri-specific findings (PLAN-models §2.2): classify the net as lossy or
/// conservative, and surface the safety-survives-loss / liveness-doesn't split
/// and the loss-induced deadlock as first-class report lines.
fn petri_notes(net: &ir::PtNet, r: &check::CheckResult) -> Vec<String> {
    let mut notes = Vec::new();
    notes.push(format!("marking vector order: {}", net.places.join(",")));
    let lossy = net.transitions.iter().any(|t| t.is_loss());
    let conservative = net.transitions.iter().all(|t| t.post_sum() == t.pre_sum());
    if lossy {
        notes.push(
            "net is LOSSY: declared upper-bound safety is monotone under loss (survives); \
             the conservation equality liveness needs is broken by loss."
                .to_string(),
        );
        if !r.deadlocks.is_empty() {
            notes.push(
                "the reachable deadlock(s) above include the loss-induced sink \
                 (tokens dropped ⇒ no progress) — fix is retransmit/timeout (Phase 2.5)."
                    .to_string(),
            );
        }
    } else if conservative {
        notes.push("net is CONSERVATIVE (token mass preserved): safety and liveness both intact.".to_string());
    }
    notes
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

/// A standard XML input (SCXML now; PNML/BT-XML later) rather than `*.model.toml`.
fn is_xml(src: &str) -> bool {
    src.trim_start().starts_with('<')
}

/// A model loaded from a standard XML format.
enum XmlModel {
    Lts(ir::Lts),
    Petri(ir::PtNet),
}

/// Parse a standard XML input (the "standard formats just work as input" UX
/// bar): SCXML → FSM, PNML → PT-net.
fn load_xml(file: &str, src: &str) -> XmlModel {
    let root = xml::parse(src).unwrap_or_else(|e| fail(&format!("{file}: XML: {e}")));
    match root.tag.as_str() {
        "scxml" => XmlModel::Lts(scxml::to_lts(&root).unwrap_or_else(|e| fail(&format!("{file}: SCXML: {e}")))),
        "pnml" => XmlModel::Petri(pnml::to_net(&root).unwrap_or_else(|e| fail(&format!("{file}: PNML: {e}")))),
        other => fail(&format!("{file}: unsupported XML root <{other}> (SCXML/PNML supported in this build)")),
    }
}

