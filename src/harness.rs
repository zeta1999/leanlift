//! LLM harness (SPEC §8): the untrusted C++/Go/… front-end.
//!
//! `claude -p` is asked to translate a C++ function into a Lean model that uses
//! ONLY the audited `LeanLift.Checked` library. The translation is a hypothesis:
//! the engine wraps it in a runner, runs it, and the differential oracle either
//! confirms it (L1) or hands back a *structured* failure — a Lean elaboration
//! error or the minimal counterexample — which is fed back for repair. Bounded
//! by `max_iters`. "LLM proposes, algorithm disposes."
//!
//! Every prompt is content-addressed and cached under `.leanlift-cache/`, so a
//! reproduced run does not re-query (and does not re-bill) the model.

use crate::compare::{self, Class, Profile};
use crate::lang::Lang;
use crate::leanrt::{self, Candidate, LeanEnv};
use crate::sig::Signature;
use crate::vectors::Vector;
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Outcome of the propose→repair loop.
pub struct LlmOutcome {
    pub candidate: Candidate,
    pub iters: usize,
    pub conformant: bool,
}

/// The API surface the model is allowed to target (kept in sync with
/// `lean/LeanLift/Checked.lean`). Pinning this in the prompt is what makes the
/// candidate target a *fixed, audited* library (SPEC §13).
const SUPPORT_API: &str = "\
The library `LeanLift.Checked` (already imported; `open LeanLift` is in scope):
  inductive Res (α) | ok (v : α) | fail        -- a Monad: `pure`/`do`/`←` work
  structure UInt (width : Nat) where val : Nat -- abbrevs: U8 U16 U32 U64
  UInt.ofNat (width n : Nat) : Res (UInt width)  -- range-checked injection
  UInt.lit  (n : Nat) : UInt width               -- literal (width inferred)
  UInt.le / UInt.ge (a b : UInt w) : Bool        -- comparisons
  UInt.add / UInt.sub / UInt.mul (a b : UInt w) : Res (UInt w)  -- CHECKED: fail on over/underflow
  UInt.div (a b : UInt w) : Res (UInt w)         -- CHECKED: fail on div-by-zero
Checked ops FAIL where C/C++ would wrap — that is intended and is what the tool
tests for; translate the arithmetic faithfully, do not add saturation.";

/// Run the bounded propose→typecheck→difftest→repair loop for an LLM-translated
/// source in `lang` (C++/Go/Solidity).
pub fn run_llm(
    lang: Lang,
    source: &Path,
    fn_name: &str,
    sig: &Signature,
    vectors: &[Vector],
    cpp: &HashMap<String, String>,
    profile: Profile,
    lean_lib: &Path,
    work_dir: &Path,
    max_iters: usize,
) -> Result<LlmOutcome, String> {
    let src =
        std::fs::read_to_string(source).map_err(|e| format!("cannot read {}: {e}", source.display()))?;

    let prompt = translate_prompt(lang, &src, fn_name, sig);
    let mut def = extract_def(&claude(&prompt, work_dir)?);

    let mut last_candidate = None;
    for iter in 1..=max_iters {
        let runner = work_dir.join("LlmCandidate.lean");
        std::fs::write(&runner, support_runner(&def, fn_name, sig))
            .map_err(|e| format!("cannot write candidate: {e}"))?;
        let candidate = Candidate { runner, env: LeanEnv::Support(lean_lib.to_path_buf()) };

        match leanrt::run(&candidate, vectors, work_dir) {
            // Typecheck/run failure → L0; repair with the elaboration error.
            Err(e) => {
                eprintln!("  harness: iter {iter} — candidate did not typecheck; repairing");
                if iter == max_iters {
                    return Ok(LlmOutcome { candidate, iters: iter, conformant: false });
                }
                let p = repair_prompt(lang, &src, fn_name, sig, &def, &lean_error_excerpt(&e.0));
                def = extract_def(&claude(&p, work_dir)?);
                last_candidate = None;
            }
            Ok(lean_map) => {
                let cmp = compare::compare(vectors, cpp, &lean_map, profile);
                if cmp.conformant() {
                    eprintln!("  harness: iter {iter} — conformant ✔");
                    return Ok(LlmOutcome { candidate, iters: iter, conformant: true });
                }
                // Difftest failure → repair with the minimal counterexample.
                let ce = minimal_counterexample(&cmp);
                eprintln!("  harness: iter {iter} — {} mismatch(es); repairing with counterexample",
                    cmp.count(Class::Mismatch));
                if iter == max_iters {
                    return Ok(LlmOutcome { candidate, iters: iter, conformant: false });
                }
                let p = repair_prompt(lang, &src, fn_name, sig, &def, &ce);
                def = extract_def(&claude(&p, work_dir)?);
                last_candidate = Some(candidate);
            }
        }
    }
    // Unreachable for max_iters >= 1, but keep the type total.
    last_candidate
        .map(|candidate| LlmOutcome { candidate, iters: max_iters, conformant: false })
        .ok_or_else(|| "harness produced no candidate".into())
}

/// Lean type signature fragment, e.g. `(a b : U32) : Res U32`.
fn lean_sig(sig: &Signature) -> String {
    let names: Vec<String> = (0..sig.arity()).map(|i| format!("x{i}")).collect();
    let ty = uint_alias(sig.args.first().copied());
    // All args share a width in our examples; name them and annotate the type.
    format!("({} : {}) : Res {}", names.join(" "), ty, uint_alias(Some(sig.ret)))
}

fn uint_alias(t: Option<crate::sig::IntType>) -> String {
    use crate::sig::IntType::*;
    match t {
        Some(U8) => "U8".into(),
        Some(U16) => "U16".into(),
        Some(U32) => "U32".into(),
        Some(U64) | None => "U64".into(),
    }
}

fn translate_prompt(lang: Lang, src: &str, fn_name: &str, sig: &Signature) -> String {
    let l = lang.fence();
    format!(
        "Translate the {l} function `{fn_name}` into a Lean 4 model.\n\n\
        {SUPPORT_API}\n\n\
        Output ONLY a single Lean definition, no prose, no imports, no namespace, \
        no code fences. It must be named exactly `{fn_name}` with this shape:\n\
        \x20 def {fn_name} {sig}\n\
        Use `do`/`←` for the checked operations. Preserve the source control flow and \
        arithmetic exactly (the checked ops will fail where the source overflows — leave it).\n\n\
        {l} source:\n```{l}\n{src}\n```",
        sig = lean_sig(sig),
    )
}

fn repair_prompt(
    lang: Lang,
    src: &str,
    fn_name: &str,
    sig: &Signature,
    prev: &str,
    failure: &str,
) -> String {
    let l = lang.fence();
    format!(
        "Your Lean translation of `{fn_name}` is wrong. Fix it.\n\n\
        FAILURE:\n{failure}\n\n\
        YOUR PREVIOUS DEFINITION:\n{prev}\n\n\
        {SUPPORT_API}\n\n\
        Output ONLY the corrected single Lean definition named `{fn_name}` with shape \
        `def {fn_name} {sig}` — no prose, no imports, no namespace, no code fences.\n\n\
        {l} source:\n```{l}\n{src}\n```",
        sig = lean_sig(sig),
    )
}

/// The shrunk minimal counterexample fed back to the model (SPEC §8).
fn minimal_counterexample(cmp: &compare::Comparison) -> String {
    // "Minimal" here = the mismatch with the smallest argument magnitudes, so the
    // model sees the simplest failing case rather than a giant random one.
    let worst = cmp
        .lines
        .iter()
        .filter(|l| l.class == Class::Mismatch)
        .min_by_key(|l| l.vector.args.iter().sum::<u64>());
    match worst {
        Some(l) => format!(
            "On input ({}), the C++ reference returns {} but your model returns {}. \
            They must agree (your model may only report OVERFLOW where the C++ arithmetic \
            genuinely exceeds the integer range).",
            l.vector.args.iter().map(u64::to_string).collect::<Vec<_>>().join(", "),
            l.cpp,
            l.lean
        ),
        None => "A divergence was detected but could not be isolated.".into(),
    }
}

fn lean_error_excerpt(err: &str) -> String {
    let body: String = err.lines().take(12).collect::<Vec<_>>().join("\n");
    format!("Lean rejected your definition:\n{body}")
}

/// Strip prose/fences/imports from the model output, leaving the `def` body.
fn extract_def(raw: &str) -> String {
    // Prefer the first fenced code block if present.
    let body = if let Some(start) = raw.find("```") {
        let after = &raw[start + 3..];
        // drop an optional language tag on the fence line
        let after = after.splitn(2, '\n').nth(1).unwrap_or(after);
        after.split("```").next().unwrap_or(after)
    } else {
        raw
    };
    body.lines()
        .filter(|l| {
            let t = l.trim_start();
            !(t.starts_with("import ")
                || t.starts_with("open ")
                || t.starts_with("namespace ")
                || t.starts_with("end "))
        })
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

/// A support-library runner around an LLM-produced `def` (width-generic).
fn support_runner(def: &str, name: &str, sig: &Signature) -> String {
    let n = sig.arity();
    let pat = (0..n).map(|i| format!("a{i}")).collect::<Vec<_>>().join(", ");
    let echo = (0..n).map(|i| format!("{{a{i}}}")).collect::<Vec<_>>().join(" ");
    let call = (0..n).map(|i| format!("(UInt.lit a{i})")).collect::<Vec<_>>().join(" ");
    format!(
        "import LeanLift.Checked\nopen LeanLift\n\n\
         namespace Candidate\n{def}\nend Candidate\n\n\
         def fmt {{w : Nat}} : Res (UInt w) → String\n\
         \x20 | .ok v => toString v.val\n  | .fail => \"OVERFLOW\"\n\n\
         def main : IO Unit := do\n\
         \x20 let path := (← IO.getEnv \"LEANLIFT_VECTORS\").getD \"vectors.txt\"\n\
         \x20 for line in (← IO.FS.lines path) do\n\
         \x20   let nums := (line.splitOn \" \").filterMap (·.toNat?)\n\
         \x20   match nums with\n\
         \x20   | [{pat}] => IO.println s!\"{echo} => {{fmt (Candidate.{name} {call})}}\"\n\
         \x20   | _ => pure ()\n",
    )
}

/// Call `claude -p`, with a content-addressed cache to avoid re-querying.
fn claude(prompt: &str, work_dir: &Path) -> Result<String, String> {
    let cache = cache_dir();
    let _ = std::fs::create_dir_all(&cache);
    let key = {
        let mut h = DefaultHasher::new();
        prompt.hash(&mut h);
        format!("{:016x}", h.finish())
    };
    let hit = cache.join(format!("{key}.txt"));
    if let Ok(s) = std::fs::read_to_string(&hit) {
        eprintln!("  harness: claude -p (cache hit {key})");
        return Ok(s);
    }

    eprintln!("  harness: claude -p (querying, key {key})");
    // Pass the prompt on stdin to avoid arg-length limits.
    let mut child = Command::new("claude")
        .arg("-p")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn claude: {e}"))?;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(prompt.as_bytes())
        .map_err(|e| format!("failed to write prompt: {e}"))?;
    let out = child.wait_with_output().map_err(|e| format!("claude failed: {e}"))?;
    if !out.status.success() {
        let _ = std::fs::write(work_dir.join("claude.err"), &out.stderr);
        return Err(format!("claude -p exited with {}", out.status));
    }
    let resp = String::from_utf8_lossy(&out.stdout).to_string();
    let _ = std::fs::write(&hit, &resp);
    Ok(resp)
}

fn cache_dir() -> PathBuf {
    PathBuf::from(".leanlift-cache")
}
