//! Front-ends (SPEC §5): how a candidate Lean model is *obtained* for a source.
//!
//!   - `Prewritten`: a hand-written (or, later, LLM-written) candidate file run
//!     against our audited support library. Used by the C++/Go LLM path and the
//!     hand-built examples.
//!   - `RustAeneas`: the **sound** path — run Charon then Aeneas to extract Lean
//!     from the real Rust, slice out the entrypoint, and wrap it in a runner.
//!     This is the one front-end that is trusted by construction; the others
//!     still go through the differential oracle.

use crate::leanrt::{Candidate, LeanEnv};
use crate::sig::Signature;
use std::path::{Path, PathBuf};
use std::process::Command;

pub enum Frontend {
    /// A candidate Lean runner already on disk, run with the support library.
    Prewritten { runner: PathBuf, lean_path: PathBuf },
    /// Extract the candidate from Rust via Charon + Aeneas (the sound path).
    RustAeneas { crate_dir: PathBuf, entrypoint: String },
    /// Translate the source via an LLM (`claude -p`) with a repair loop. This
    /// one is driven from the verify loop (it needs the oracle for difftest), so
    /// `produce` is not used for it.
    Llm { max_iters: usize },
    /// Translate C++ → Rust with the external `cpp2rust` tool, then reuse the
    /// sound Rust path (Charon+Aeneas) on the generated crate. The translation
    /// itself is untrusted — the differential oracle still disposes — but the
    /// whole chain is deterministic (no LLM). Optional: self-skips when the
    /// tool is not built (see `cpp2rust_available`).
    Cpp2Rust { source: PathBuf, entrypoint: String },
}

impl Frontend {
    /// Produce a runnable candidate (this is where the sound path does its work).
    pub fn produce(&self, sig: &Signature, work_dir: &Path) -> Result<Candidate, String> {
        match self {
            Frontend::Prewritten { runner, lean_path } => Ok(Candidate {
                runner: runner.clone(),
                env: LeanEnv::Support(lean_path.clone()),
            }),
            Frontend::RustAeneas { crate_dir, entrypoint } => {
                extract_rust(crate_dir, entrypoint, sig, work_dir)
            }
            Frontend::Llm { .. } => {
                Err("LLM front-end is driven from the verify loop, not produce()".into())
            }
            Frontend::Cpp2Rust { source, entrypoint } => {
                let crate_dir = cpp2rust_translate(source, entrypoint, work_dir)?;
                extract_rust(&crate_dir, entrypoint, sig, work_dir)
            }
        }
    }
}

/// The built cpp2rust checkout (`<dir>/build/cpp2rust/cpp2rust`).
/// Override with `LEANLIFT_CPP2RUST`; defaults next to the Aeneas install.
fn cpp2rust_dir() -> PathBuf {
    if let Ok(d) = std::env::var("LEANLIFT_CPP2RUST") {
        return PathBuf::from(d);
    }
    let home = std::env::var("HOME").unwrap_or_default();
    PathBuf::from(home).join("work/_verif-tools/cpp2rust")
}

fn cpp2rust_bin() -> PathBuf {
    cpp2rust_dir().join("build/cpp2rust/cpp2rust")
}

/// Whether the optional cpp2rust translator is built. Absence is a SKIP, not a
/// failure (same contract as the `lh` lane): the verify loop reports SKIPPED
/// and exits 0 so CI records the lane as unavailable rather than broken.
pub fn cpp2rust_available() -> bool {
    cpp2rust_bin().exists()
}

/// Run cpp2rust on `source` and wrap its output in a generated lib crate that
/// Charon can consume. Returns the crate dir. The translation is untrusted —
/// the differential oracle downstream is what disposes.
fn cpp2rust_translate(
    source: &Path,
    entrypoint: &str,
    work_dir: &Path,
) -> Result<PathBuf, String> {
    let bin = cpp2rust_bin();
    if !bin.exists() {
        return Err(format!(
            "cpp2rust not built at {} — run scripts/build_cpp2rust.sh (or set LEANLIFT_CPP2RUST)",
            bin.display()
        ));
    }
    let crate_dir = work_dir.join("c2r-crate");
    let src_dir = crate_dir.join("src");
    let _ = std::fs::create_dir_all(&src_dir);
    let out_rs = work_dir.join("c2r-translated.rs");

    eprintln!("  front-end: cpp2rust  (C++ → Rust)…");
    // `--model=unsafe` emits scalar Rust (plain locals, `wrapping_*` ops — the
    // faithful C++ unsigned semantics). The default safe model wraps every
    // local in `Rc<RefCell<_>>` via the libcc2rs runtime, which Aeneas cannot
    // extract; for the pointer-free kernels leanlift lifts, the two models
    // compute identically and the `unsafe` qualifier is vacuous (stripped
    // below — cargo re-checks the result, so a body that truly needed unsafe
    // fails loudly in charon.log, not silently).
    let out = Command::new(&bin)
        .arg(format!("--rules={}", cpp2rust_dir().join("build/rules").display()))
        .arg("--model=unsafe")
        .arg(format!("--file={}", source.display()))
        .arg(format!("-o={}", out_rs.display()))
        .output()
        .map_err(|e| format!("failed to run cpp2rust: {e}"))?;
    log_output(work_dir, "cpp2rust", &out);
    if !out.status.success() {
        return Err(format!("cpp2rust failed (see {}/cpp2rust.log)", work_dir.display()));
    }
    let translated = std::fs::read_to_string(&out_rs)
        .map_err(|e| format!("cpp2rust produced no output: {e}"))?;
    let lib_rs = sanitize_cpp2rust_output(&translated, entrypoint)?;
    eprintln!("  front-end: cpp2rust emitted {} lines of Rust", lib_rs.lines().count());

    std::fs::write(src_dir.join("lib.rs"), lib_rs)
        .map_err(|e| format!("cannot write generated lib.rs: {e}"))?;
    std::fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"leanlift-c2r-kernel\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n\
         [lib]\nname = \"c2r_kernel\"\npath = \"src/lib.rs\"\n",
    )
    .map_err(|e| format!("cannot write generated Cargo.toml: {e}"))?;
    // Stale LLBC from a previous run would mask a failed re-translation
    // (extract_rust picks the newest .llbc in the crate dir).
    for e in std::fs::read_dir(&crate_dir).into_iter().flatten().flatten() {
        if e.path().extension().and_then(|s| s.to_str()) == Some("llbc") {
            let _ = std::fs::remove_file(e.path());
        }
    }
    Ok(crate_dir)
}

/// Adapt raw cpp2rust `--model=unsafe` output to a dependency-free lib crate
/// Charon+Aeneas can extract from:
///   - drop the import preamble (`extern crate libc/libcc2rs`, `use …` — the
///     generated crate has no deps; a body that really needed one fails in
///     cargo/charon, loudly),
///   - drop any generated `fn main`,
///   - strip the blanket `unsafe` fn qualifier (cargo re-checks the body),
///   - undo cpp2rust's `_0` overload suffix on the entrypoint,
///   - ensure the entrypoint is `pub`,
/// and reject output that still needs the libcc2rs pointer runtime (Aeneas
/// cannot model `Rc<RefCell<_>>` cells — the kernel must be pointer-free).
fn sanitize_cpp2rust_output(translated: &str, entrypoint: &str) -> Result<String, String> {
    let mut out: Vec<String> = Vec::new();
    let mut skip_depth: i32 = -1; // >=0 while inside a skipped `fn main` block
    for line in translated.lines() {
        let t = line.trim_start();
        if skip_depth >= 0 {
            skip_depth += line.matches('{').count() as i32;
            skip_depth -= line.matches('}').count() as i32;
            if skip_depth <= 0 {
                skip_depth = -1;
            }
            continue;
        }
        if t.starts_with("extern crate ") || (t.starts_with("use ") && t.ends_with(';')) {
            continue;
        }
        if t.starts_with("fn main(") || t.starts_with("pub fn main(") {
            let opens = line.matches('{').count() as i32 - line.matches('}').count() as i32;
            if opens > 0 {
                skip_depth = opens;
            }
            continue;
        }
        out.push(line.replace("pub unsafe fn ", "pub fn ").replace("unsafe fn ", "fn "));
    }
    let mut text = out.join("\n");
    // Aeneas's Lean Std models wrapping add/sub/mul/shl/shr but has no
    // `wrapping_div`/`wrapping_rem` — they'd extract as opaque axioms the
    // runner cannot evaluate. On unsigned types they coincide exactly with
    // `/` and `%` (truncating, fail on zero), which Aeneas does model. If a
    // signed kernel ever hits the one divergent case (INT_MIN / -1), the
    // differential oracle catches it at L1 — the rewrite cannot silently lie.
    text = text.replace(".wrapping_div(", " / (").replace(".wrapping_rem(", " % (");
    // cpp2rust disambiguates overloads as `<name>_0`; our kernels have one
    // definition, so fold the suffix back onto the true entrypoint name.
    let suffixed = format!("{entrypoint}_0");
    if !text.contains(&format!("fn {entrypoint}(")) && text.contains(&format!("fn {suffixed}(")) {
        text = text.replace(&suffixed, entrypoint);
    }
    if text.contains("libcc2rs") || text.contains("Value<") || text.contains("Ptr<") {
        return Err(
            "cpp2rust output uses the libcc2rs pointer runtime — not extractable by \
             Aeneas (kernel must be pointer-free)"
                .into(),
        );
    }
    // Make the entrypoint pub so the lib crate exports it for Charon.
    let def = format!("fn {entrypoint}(");
    if let Some(pos) = text.find(&def) {
        let line_start = text[..pos].rfind('\n').map_or(0, |i| i + 1);
        if !text[line_start..pos].contains("pub ") {
            text.insert_str(pos, "pub ");
        }
    } else {
        return Err(format!("cpp2rust output has no fn `{entrypoint}`"));
    }
    Ok(text.trim_start().to_string() + "\n")
}

/// The built Aeneas install (`<dir>/bin/aeneas`, `<dir>/charon/bin/charon`).
/// Override with `LEANLIFT_AENEAS`; defaults to the spike's location.
fn aeneas_dir() -> PathBuf {
    if let Ok(d) = std::env::var("LEANLIFT_AENEAS") {
        return PathBuf::from(d);
    }
    let home = std::env::var("HOME").unwrap_or_default();
    PathBuf::from(home).join("work/_verif-tools/aeneas")
}

fn extract_rust(
    crate_dir: &Path,
    entrypoint: &str,
    sig: &Signature,
    work_dir: &Path,
) -> Result<Candidate, String> {
    let def = extract_rust_def(crate_dir, entrypoint, work_dir)?;
    let runner = work_dir.join("RustRunner.lean");
    std::fs::write(&runner, rust_runner(&def, entrypoint, sig))
        .map_err(|e| format!("cannot write runner: {e}"))?;
    Ok(Candidate { runner, env: LeanEnv::Aeneas { aeneas_dir: aeneas_dir() } })
}

/// The Aeneas install dir (exposed so the prove path can run `lake env lean`).
pub fn aeneas_install() -> PathBuf {
    aeneas_dir()
}

/// Run Charon+Aeneas and return the extracted entrypoint `def` as Lean text.
/// Shared by the candidate runner (L1) and the proof assembler (L3).
pub fn extract_rust_def(
    crate_dir: &Path,
    entrypoint: &str,
    work_dir: &Path,
) -> Result<String, String> {
    let aeneas = aeneas_dir();
    let charon = aeneas.join("charon/bin/charon");
    let aeneas_bin = aeneas.join("bin/aeneas");
    if !aeneas_bin.exists() {
        return Err(format!(
            "aeneas not built at {} — run scripts/build_aeneas.sh (or set LEANLIFT_AENEAS)",
            aeneas_bin.display()
        ));
    }

    // 1. Charon: Rust crate -> LLBC. (Output captured to a log; the tools are
    //    very chatty and only matter when something fails.)
    eprintln!("  front-end: Charon  (Rust → LLBC)…");
    let st = Command::new(&charon)
        .args(["cargo", "--preset", "aeneas", "--", "--lib"])
        .current_dir(crate_dir)
        .output()
        .map_err(|e| format!("failed to run charon: {e}"))?;
    log_output(work_dir, "charon", &st);
    if !st.status.success() {
        return Err(format!("charon failed (see {}/charon.log)", work_dir.display()));
    }
    let llbc = newest_with_ext(crate_dir, "llbc")
        .ok_or_else(|| format!("no .llbc produced in {}", crate_dir.display()))?;

    // 2. Aeneas: LLBC -> Lean. Partial extraction (unknown stdlib -> axiom) is
    //    expected (§13); we don't fail on a nonzero exit, we check the output.
    eprintln!("  front-end: Aeneas  (LLBC → Lean)…");
    let extract_dir = work_dir.join("rust-extract");
    let _ = std::fs::create_dir_all(&extract_dir);
    let out = Command::new(&aeneas_bin)
        .args(["-backend", "lean"])
        .arg(&llbc)
        .arg("-dest")
        .arg(&extract_dir)
        .arg("-lean-default-lakefile")
        .output()
        .map_err(|e| format!("failed to run aeneas: {e}"))?;
    log_output(work_dir, "aeneas", &out);

    // 3. Slice the entrypoint def out of the extracted module.
    let module = newest_with_ext(&extract_dir, "lean")
        .ok_or_else(|| format!("aeneas produced no .lean in {}", extract_dir.display()))?;
    let text = std::fs::read_to_string(&module)
        .map_err(|e| format!("cannot read extracted module: {e}"))?;
    let def = slice_def(&text, entrypoint).ok_or_else(|| {
        format!("entrypoint `{entrypoint}` not found in extracted {}", module.display())
    })?;
    eprintln!("  front-end: extracted `{entrypoint}` ({} lines)", def.lines().count());
    let _ = aeneas_bin; // (kept above only to validate the install exists)
    Ok(def)
}

/// Write a tool's captured stdout+stderr to `<work>/<name>.log`.
fn log_output(work_dir: &Path, name: &str, out: &std::process::Output) {
    let mut buf = out.stdout.clone();
    buf.extend_from_slice(&out.stderr);
    let _ = std::fs::write(work_dir.join(format!("{name}.log")), buf);
}

/// Newest file with the given extension directly in `dir`.
fn newest_with_ext(dir: &Path, ext: &str) -> Option<PathBuf> {
    let mut best: Option<(std::time::SystemTime, PathBuf)> = None;
    for e in std::fs::read_dir(dir).ok()?.flatten() {
        let p = e.path();
        if p.extension().and_then(|s| s.to_str()) == Some(ext) {
            let t = e.metadata().and_then(|m| m.modified()).ok()?;
            if best.as_ref().map_or(true, |(bt, _)| t >= *bt) {
                best = Some((t, p));
            }
        }
    }
    best.map(|(_, p)| p)
}

/// Slice the extracted defs for `name`: the entrypoint plus any Aeneas-generated
/// loop helpers (which it names `<name>_loop`, `<name>_loop.body`). Consumes from
/// the first `def <name>…` up to the next unrelated `def` or `end <ns>`/EOF,
/// keeping the attribute/doc lines between them.
fn slice_def(text: &str, name: &str) -> Option<String> {
    let lines: Vec<&str> = text.lines().collect();
    let is_def_for = |l: &str| {
        l.trim_start().strip_prefix("def ").is_some_and(|r| r.starts_with(name))
    };
    let start = lines.iter().position(|l| is_def_for(l))?;
    let mut end = lines.len();
    let mut i = start + 1;
    while i < lines.len() {
        let t = lines[i].trim_start();
        if t.starts_with("end ") || (t.starts_with("def ") && !is_def_for(lines[i])) {
            end = i;
            break;
        }
        // A `/-- … -/` doc belongs to the def that follows it. If that def isn't
        // ours, stop here — a dangling doc with no following decl is a syntax
        // error. (Docs between our own helper defs are kept.)
        if t.starts_with("/--") {
            let next_def = lines[i..].iter().find(|l| l.trim_start().starts_with("def "));
            if next_def.map_or(true, |l| !is_def_for(l)) {
                end = i;
                break;
            }
        }
        i += 1;
    }
    Some(lines[start..end].join("\n").trim_end().to_string())
}

#[cfg(test)]
mod tests {
    use super::sanitize_cpp2rust_output;

    /// The real shape of `cpp2rust --model=unsafe` output for examples/avg/avg.cpp.
    const AVG_UNSAFE: &str = "extern crate libc;\nuse libc::*;\nextern crate libcc2rs;\nuse libcc2rs::*;\nuse std::rc::Rc;\npub unsafe fn avg_0(mut a: u32, mut b: u32) -> u32 {\n    return ((a).wrapping_add(b)).wrapping_div(2_u32);\n}\n";

    #[test]
    fn adapts_real_unsafe_model_output() {
        let out = sanitize_cpp2rust_output(AVG_UNSAFE, "avg").unwrap();
        assert!(out.starts_with("pub fn avg("), "got: {out}");
        assert!(!out.contains("unsafe"));
        assert!(!out.contains("use "));
        assert!(!out.contains("extern crate"));
        assert!(!out.contains("avg_0"));
        assert!(out.contains("wrapping_add"));
        // wrapping_div has no Aeneas model — must be rewritten to plain `/`.
        assert!(!out.contains("wrapping_div"));
        assert!(out.contains(" / (2_u32)"));
    }

    #[test]
    fn strips_main_and_makes_entrypoint_pub() {
        let raw = "fn avg(a: u32, b: u32) -> u32 {\n    (a + b) / 2\n}\n\nfn main() {\n    let _ = avg(1, 2);\n}\n";
        let out = sanitize_cpp2rust_output(raw, "avg").unwrap();
        assert!(out.contains("pub fn avg("));
        assert!(!out.contains("fn main("));
    }

    #[test]
    fn keeps_already_pub_entrypoint_and_helpers() {
        let raw = "pub fn isqrt(n: u32) -> u32 { n }\nfn helper(x: u32) -> u32 { x }\n";
        let out = sanitize_cpp2rust_output(raw, "isqrt").unwrap();
        assert!(out.contains("pub fn isqrt("));
        assert!(!out.contains("pub pub"));
        assert!(out.contains("fn helper("));
    }

    #[test]
    fn rejects_pointer_runtime_output() {
        let raw = "fn f(p: Value<u32>) -> u32 { *p.borrow() }\n";
        assert!(sanitize_cpp2rust_output(raw, "f").unwrap_err().contains("libcc2rs"));
    }

    #[test]
    fn rejects_missing_entrypoint() {
        assert!(sanitize_cpp2rust_output("fn other() {}\n", "avg").is_err());
    }
}

/// Generate a Lean runner around an extracted entrypoint (any arity/width).
/// Mirrors the spike's `run_lean.lean`: build each `Std.U*` from a runtime `Nat`,
/// print `args => value` or `OVERFLOW` on a `Result.fail`. Opens `ControlFlow`
/// so extracted loops (`loop`/`cont`/`done`) resolve.
fn rust_runner(def: &str, name: &str, sig: &Signature) -> String {
    let n = sig.arity();
    let pat = (0..n).map(|i| format!("a{i}")).collect::<Vec<_>>().join(", ");
    let echo = (0..n).map(|i| format!("{{a{i}}}")).collect::<Vec<_>>().join(" ");
    let call = (0..n)
        .map(|i| {
            let t = sig.args[i];
            format!("(⟨BitVec.ofNat {} a{i}⟩ : {})", t.bits(), t.aeneas_name())
        })
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        "-- generated by leanlift: runner around the Aeneas-extracted `{name}`\n\
         import Aeneas\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\n\
         namespace kernel\n{def}\nend kernel\n\n\
         def fmt : Result {ret} → String | .ok v => toString v.val | _ => \"OVERFLOW\"\n\n\
         def main : IO Unit := do\n\
         \x20 let path := (← IO.getEnv \"LEANLIFT_VECTORS\").getD \"vectors.txt\"\n\
         \x20 for line in (← IO.FS.lines path) do\n\
         \x20   let nums := (line.splitOn \" \").filterMap (·.toNat?)\n\
         \x20   match nums with\n\
         \x20   | [{pat}] => IO.println s!\"{echo} => {{fmt (kernel.{name} {call})}}\"\n\
         \x20   | _ => pure ()\n",
        ret = sig.ret.aeneas_name(),
    )
}
