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
        }
    }
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
