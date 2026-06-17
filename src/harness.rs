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

/// The float API surface (kept in sync with `lean/LeanLift/Float.lean` and
/// `SKILL.md`). Native IEEE-754 binary64 — bit-exact vs C++ `double`.
const FLOAT_API: &str = "\
The library `LeanLift.Float` (already imported; `open LeanLift` is in scope) gives
Lean's native IEEE-754 binary64 `Float`:
  + - * /            -- the basic ops (Float.add/sub/mul/div), correctly rounded
  Float.sqrt a       -- correctly-rounded square root
  a < b   a <= b   a == b      -- comparisons, returning Bool
  Float literals: 0.5, 2.0, 3.0, …   (decimal; no integer/Float coercions needed)
  Float.iterate (n : Nat) (f : σ → σ) (s : σ) : σ   -- a BOUNDED loop (n steps)
Use ONLY `+ - * /`, `Float.sqrt`, and comparisons — NO transcendentals (exp/log/sin),
they are not bit-reproducible. Express any loop with `Float.iterate` (a fixed iteration
count) or structural recursion. The result is a plain `Float` (there is no `Res` monad —
floats never `fail`). Reproduce irrational constants by arithmetic on `Float.sqrt`, never
as a truncated decimal literal (e.g. invphi = (Float.sqrt 5.0 - 1.0) / 2.0).";

/// The API blurb for a signature's path (checked-int vs float).
fn api_for(sig: &Signature) -> &'static str {
    if sig.is_float() { FLOAT_API } else { SUPPORT_API }
}

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
    float: Option<compare::FloatCompare>,
    lean_lib: &Path,
    work_dir: &Path,
    max_iters: usize,
    lane: &Lane,
) -> Result<LlmOutcome, String> {
    let src =
        std::fs::read_to_string(source).map_err(|e| format!("cannot read {}: {e}", source.display()))?;
    eprintln!("  harness: lane = {}", lane.id());

    let prompt = translate_prompt(lang, &src, fn_name, sig);
    let mut def = extract_def(&query(lane, &prompt, work_dir)?);

    let mut last_candidate = None;
    for iter in 1..=max_iters {
        let runner = work_dir.join("LlmCandidate.lean");
        let runner_src = if sig.is_float() {
            float_support_runner(&def, fn_name, sig)
        } else {
            support_runner(&def, fn_name, sig)
        };
        std::fs::write(&runner, runner_src).map_err(|e| format!("cannot write candidate: {e}"))?;
        let candidate = Candidate { runner, env: LeanEnv::Support(lean_lib.to_path_buf()) };

        match leanrt::run(&candidate, vectors, work_dir) {
            // Typecheck/run failure → L0; repair with the elaboration error.
            Err(e) => {
                eprintln!("  harness: iter {iter} — candidate did not typecheck; repairing");
                if iter == max_iters {
                    return Ok(LlmOutcome { candidate, iters: iter, conformant: false });
                }
                let p = repair_prompt(lang, &src, fn_name, sig, &def, &lean_error_excerpt(&e.0));
                def = extract_def(&query(lane, &p, work_dir)?);
                last_candidate = None;
            }
            Ok(lean_map) => {
                let cmp = compare::compare(vectors, cpp, &lean_map, profile, float);
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
                def = extract_def(&query(lane, &p, work_dir)?);
                last_candidate = Some(candidate);
            }
        }
    }
    // Unreachable for max_iters >= 1, but keep the type total.
    last_candidate
        .map(|candidate| LlmOutcome { candidate, iters: max_iters, conformant: false })
        .ok_or_else(|| "harness produced no candidate".into())
}

/// Lean type signature fragment: `(a b : U32) : Res U32` for the checked-integer
/// path, or `(x y : Float) : Float` for the bit-exact float path (no `Res` —
/// floats don't fail, they produce NaN/Inf which the runner canonicalizes).
fn lean_sig(sig: &Signature) -> String {
    let names: Vec<String> = (0..sig.arity()).map(|i| format!("x{i}")).collect();
    let arg_ty = lean_ty_name(*sig.args.first().expect("nullary signature"));
    let ret = lean_ty_name(sig.ret);
    if sig.is_float() {
        format!("({} : {arg_ty}) : {ret}", names.join(" "))
    } else {
        format!("({} : {arg_ty}) : Res {ret}", names.join(" "))
    }
}

fn lean_ty_name(t: crate::sig::Ty) -> &'static str {
    use crate::sig::{FloatType, IntType::*, Ty};
    match t {
        Ty::Int(U8) => "U8",
        Ty::Int(U16) => "U16",
        Ty::Int(U32) => "U32",
        Ty::Int(U64) => "U64",
        Ty::Float(FloatType::F64) => "Float",
        Ty::Float(FloatType::F32) => "Float32",
    }
}

fn translate_prompt(lang: Lang, src: &str, fn_name: &str, sig: &Signature) -> String {
    let l = lang.fence();
    let hint = if sig.is_float() {
        "Preserve the source control flow and arithmetic exactly, op-for-op."
    } else {
        "Use `do`/`←` for the checked operations. Preserve the source control flow and \
         arithmetic exactly (the checked ops will fail where the source overflows — leave it)."
    };
    format!(
        "Translate the {l} function `{fn_name}` into a Lean 4 model.\n\n\
        {api}\n\n\
        Output ONLY a single Lean definition, no prose, no imports, no namespace, \
        no code fences. It must be named exactly `{fn_name}` with this shape:\n\
        \x20 def {fn_name} {sig}\n\
        {hint}\n\n\
        {l} source:\n```{l}\n{src}\n```",
        api = api_for(sig),
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
        {api}\n\n\
        Output ONLY the corrected single Lean definition named `{fn_name}` with shape \
        `def {fn_name} {sig}` — no prose, no imports, no namespace, no code fences.\n\n\
        {l} source:\n```{l}\n{src}\n```",
        api = api_for(sig),
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
            They must agree exactly — integer results match, and float results are compared \
            as IEEE-754 bit patterns (the token NAN is the canonical NaN; OVERFLOW the checked \
            integer failure). Re-derive the arithmetic op-for-op.",
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

/// Strip terminal escape sequences (ollama's streaming TUI leaks cursor-control
/// codes like `ESC[2D ESC[K` into stdout when not a TTY).
fn strip_ansi(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' {
            // CSI: ESC [ … <final byte 0x40..0x7e>
            if chars.peek() == Some(&'[') {
                chars.next();
                while let Some(&n) = chars.peek() {
                    chars.next();
                    if ('\u{40}'..='\u{7e}').contains(&n) {
                        break;
                    }
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// Drop a *reasoning* model's thinking preamble: text up to a `</think>` tag or
/// an ollama-style `…done thinking.` marker is not the answer.
fn strip_thinking(s: &str) -> String {
    if let Some(i) = s.rfind("</think>") {
        return s[i + "</think>".len()..].to_string();
    }
    if let Some(i) = s.rfind("done thinking.") {
        return s[i + "done thinking.".len()..].to_string();
    }
    s.to_string()
}

/// Reduce a model's reply to the bare `def` body. Robust to: terminal escape
/// codes, a leading reasoning/thinking block, prose, multiple fenced blocks (a
/// thinking model often quotes the *source* first), and stray imports. Strategy:
/// strip ANSI + thinking, then pick the fenced block (or whole text) that
/// actually contains a Lean `def`, preferring the LAST such block (the answer).
fn extract_def(raw: &str) -> String {
    let cleaned = strip_thinking(&strip_ansi(raw));

    // Collect fenced code blocks; otherwise treat the whole text as one block.
    let mut blocks: Vec<String> = Vec::new();
    let mut rest = cleaned.as_str();
    while let Some(start) = rest.find("```") {
        let after = &rest[start + 3..];
        let after = after.splitn(2, '\n').nth(1).unwrap_or(after); // drop lang tag
        if let Some(end) = after.find("```") {
            blocks.push(after[..end].to_string());
            rest = &after[end + 3..];
        } else {
            blocks.push(after.to_string());
            break;
        }
    }
    if blocks.is_empty() {
        blocks.push(cleaned.clone());
    }

    // Prefer the last block that contains a Lean `def`; else the last block.
    let body = blocks
        .iter()
        .rev()
        .find(|b| b.lines().any(|l| l.trim_start().starts_with("def ")))
        .or_else(|| blocks.last())
        .cloned()
        .unwrap_or(cleaned);

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

/// A float runner around an LLM-produced `def : (… : Float) : Float`. Inputs
/// arrive as IEEE bit patterns (decimal `Nat`s); the result is printed as its
/// bit pattern, with NaN → `NAN` and `-0.0` → `0` to mirror the C++ oracle's
/// canonicalization (so the comparison stays bit-exact and lossless).
fn float_support_runner(def: &str, name: &str, sig: &Signature) -> String {
    use crate::sig::FloatType;
    let n = sig.arity();
    // The Lean float type + bit conversions differ by precision: native `Float`
    // is binary64 (UInt64 bits), `Float32` is binary32 (UInt32 bits).
    let (fty, of_bits, to_nat, sign) = match sig.float_ty() {
        FloatType::F64 => ("Float", "Float.ofBits", "toUInt64", "0x8000000000000000 : UInt64"),
        FloatType::F32 => ("Float32", "Float32.ofBits", "toUInt32", "0x80000000 : UInt32"),
    };
    let pat = (0..n).map(|i| format!("a{i}")).collect::<Vec<_>>().join(", ");
    let echo = (0..n).map(|i| format!("{{a{i}}}")).collect::<Vec<_>>().join(" ");
    let call = (0..n)
        .map(|i| format!("({of_bits} a{i}.{to_nat})"))
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        "import LeanLift.Float\nopen LeanLift\n\n\
         namespace Candidate\n{def}\nend Candidate\n\n\
         def fmtF (x : {fty}) : String :=\n\
         \x20 if x.isNaN then \"NAN\"\n\
         \x20 else let b := x.toBits; if b == ({sign}) then \"0\" else toString b\n\n\
         def main : IO Unit := do\n\
         \x20 let path := (← IO.getEnv \"LEANLIFT_VECTORS\").getD \"vectors.txt\"\n\
         \x20 for line in (← IO.FS.lines path) do\n\
         \x20   let nums := (line.splitOn \" \").filterMap (·.toNat?)\n\
         \x20   match nums with\n\
         \x20   | [{pat}] => IO.println s!\"{echo} => {{fmtF (Candidate.{name} {call})}}\"\n\
         \x20   | _ => pure ()\n",
    )
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

// ─── Lanes: the swappable agent backends for the C++→Lean translation ───────
//
// The harness is "LLM proposes, algorithm disposes": ANY of these backends may
// propose the candidate; the differential oracle disposes identically. Four
// lanes ship, selected by `--lane` / `LEANLIFT_LANE`:
//   claude  — `claude -p` (the reference lane)
//   skill   — the same translation driven from the portable SKILL.md (proves
//             the skill doc alone reproduces the result), via a configurable
//             runner (default `claude -p`)
//   gemma   — a LOCAL model over `ollama` (default `gemma4:e4b`, the 16GB class)
//   qwen    — a REMOTE OpenAI-compatible endpoint (vLLM/ollama/TGI on the
//             RTX 6000 Pro box); env-configured, skipped until LEANLIFT_QWEN_URL
//
// Responses are content-addressed under `.leanlift-cache/`, keyed by lane id +
// prompt, so reruns don't re-query (and lanes don't collide).

/// A translation backend.
pub enum Lane {
    /// `claude -p`, prompt on stdin.
    ClaudeP,
    /// Drive the translation from `SKILL.md` via `runner` (default `claude -p`).
    Skill { runner: String, skill: PathBuf },
    /// A local model served by `ollama run <model>`.
    Ollama { model: String },
    /// A remote OpenAI-compatible chat endpoint (called via `curl`).
    OpenAiCompat { url: String, model: String, key: Option<String> },
}

impl Lane {
    /// Resolve a lane by name from flags/env. `Err(reason)` means *skip this
    /// lane* (e.g. the remote endpoint isn't configured) — not a hard failure.
    pub fn resolve(name: &str) -> Result<Lane, String> {
        let env = |k: &str| std::env::var(k).ok().filter(|s| !s.is_empty());
        match name {
            "claude" => Ok(Lane::ClaudeP),
            "skill" => Ok(Lane::Skill {
                runner: env("LEANLIFT_SKILL_RUNNER").unwrap_or_else(|| "claude -p".into()),
                skill: PathBuf::from(env("LEANLIFT_SKILL").unwrap_or_else(|| "SKILL.md".into())),
            }),
            "gemma" => Ok(Lane::Ollama {
                model: env("LEANLIFT_GEMMA_MODEL").unwrap_or_else(|| "gemma4:e4b".into()),
            }),
            "ollama" => Ok(Lane::Ollama {
                model: env("LEANLIFT_OLLAMA_MODEL")
                    .ok_or_else(|| "set LEANLIFT_OLLAMA_MODEL for the ollama lane".to_string())?,
            }),
            "qwen" => {
                let url = env("LEANLIFT_QWEN_URL").ok_or_else(|| {
                    "lane qwen not configured (set LEANLIFT_QWEN_URL to the RTX 6000 Pro endpoint)"
                        .to_string()
                })?;
                Ok(Lane::OpenAiCompat {
                    url,
                    model: env("LEANLIFT_QWEN_MODEL").unwrap_or_else(|| "qwen3".into()),
                    key: env("LEANLIFT_QWEN_KEY"),
                })
            }
            other => Err(format!("unknown lane `{other}` (have: claude, skill, gemma, qwen)")),
        }
    }

    /// A stable id used for the cache key and the run log.
    pub fn id(&self) -> String {
        match self {
            Lane::ClaudeP => "claude-p".into(),
            Lane::Skill { runner, .. } => format!("skill[{runner}]"),
            Lane::Ollama { model } => format!("ollama[{model}]"),
            Lane::OpenAiCompat { model, .. } => format!("openai[{model}]"),
        }
    }
}

/// Query the active lane for a completion, with a lane-keyed content-addressed
/// cache. This is the one seam every backend funnels through.
fn query(lane: &Lane, prompt: &str, work_dir: &Path) -> Result<String, String> {
    let cache = cache_dir();
    let _ = std::fs::create_dir_all(&cache);
    let key = {
        let mut h = DefaultHasher::new();
        lane.id().hash(&mut h);
        prompt.hash(&mut h);
        format!("{:016x}", h.finish())
    };
    let hit = cache.join(format!("{key}.txt"));
    if let Ok(s) = std::fs::read_to_string(&hit) {
        eprintln!("  harness: {} (cache hit {key})", lane.id());
        return Ok(s);
    }
    eprintln!("  harness: {} (querying, key {key})", lane.id());
    let resp = match lane {
        Lane::ClaudeP => run_stdin("claude", &["-p"], prompt, work_dir)?,
        Lane::Skill { runner, skill } => run_skill(runner, skill, prompt, work_dir)?,
        Lane::Ollama { model } => run_ollama(model, prompt)?,
        Lane::OpenAiCompat { url, model, key } => run_openai(url, model, key.as_deref(), prompt)?,
    };
    let _ = std::fs::write(&hit, &resp);
    Ok(resp)
}

/// Spawn `program args…`, write `prompt` to its stdin, return stdout.
fn run_stdin(program: &str, args: &[&str], prompt: &str, work_dir: &Path) -> Result<String, String> {
    let mut child = Command::new(program)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn {program}: {e}"))?;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(prompt.as_bytes())
        .map_err(|e| format!("failed to write prompt to {program}: {e}"))?;
    let out = child.wait_with_output().map_err(|e| format!("{program} failed: {e}"))?;
    if !out.status.success() {
        let _ = std::fs::write(work_dir.join(format!("{program}.err")), &out.stderr);
        return Err(format!("{program} exited with {}", out.status));
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

/// The `skill` lane: materialize the prompt as a reproducible artifact next to a
/// pointer to `SKILL.md`, then run the configured runner (default `claude -p`).
/// This is the executable proof that following SKILL.md alone reproduces the
/// translation — the same engine, but driven by the portable doc, not the
/// inlined prompt. (The runner is a shell word list, e.g. `claude -p`.)
fn run_skill(runner: &str, skill: &Path, prompt: &str, work_dir: &Path) -> Result<String, String> {
    let parts: Vec<&str> = runner.split_whitespace().collect();
    let (prog, args) = parts.split_first().ok_or("empty skill runner")?;
    // Prepend a one-line reference so the transcript records which skill drove it.
    let framed = format!(
        "# Following the leanlift C++→Lean translation skill ({}).\n{prompt}",
        skill.display()
    );
    let _ = std::fs::write(work_dir.join("skill-prompt.txt"), &framed);
    run_stdin(prog, args, &framed, work_dir)
}

/// The local `ollama` lane via its HTTP API (clean output — no streaming TUI
/// escape codes, and `think:false` suppresses a reasoning model's preamble).
fn run_ollama(model: &str, prompt: &str) -> Result<String, String> {
    let url = std::env::var("LEANLIFT_OLLAMA_URL")
        .ok()
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "http://localhost:11434".into());
    let body = format!(
        "{{\"model\":{},\"prompt\":{},\"stream\":false,\"think\":false}}",
        json_string(model),
        json_string(prompt)
    );
    let out = Command::new("curl")
        .args([
            "-sS", "-X", "POST", &format!("{url}/api/generate"), "-H", "Content-Type: application/json",
        ])
        .arg("--data-binary")
        .arg(&body)
        .output()
        .map_err(|e| format!("failed to run curl (is ollama serving on {url}?): {e}"))?;
    if !out.status.success() {
        return Err(format!("curl to ollama at {url} exited with {}", out.status));
    }
    let resp = String::from_utf8_lossy(&out.stdout);
    extract_json_field(&resp, "response")
        .ok_or_else(|| format!("could not parse ollama response: {resp:.400}"))
}

/// The remote OpenAI-compatible lane, via `curl` (keeps leanlift dependency-free).
/// POSTs a chat completion and extracts the assistant message content.
fn run_openai(url: &str, model: &str, key: Option<&str>, prompt: &str) -> Result<String, String> {
    let body = format!(
        "{{\"model\":{},\"temperature\":0,\"messages\":[{{\"role\":\"user\",\"content\":{}}}]}}",
        json_string(model),
        json_string(prompt)
    );
    let mut cmd = Command::new("curl");
    cmd.args(["-sS", "-X", "POST", url, "-H", "Content-Type: application/json"]);
    if let Some(k) = key {
        cmd.arg("-H").arg(format!("Authorization: Bearer {k}"));
    }
    cmd.arg("--data-binary").arg(&body);
    let out = cmd.output().map_err(|e| format!("failed to run curl: {e}"))?;
    if !out.status.success() {
        return Err(format!("curl to {url} exited with {}", out.status));
    }
    let resp = String::from_utf8_lossy(&out.stdout);
    extract_json_field(&resp, "content")
        .ok_or_else(|| format!("could not parse content from endpoint response: {resp:.400}"))
}

/// Minimal JSON string encoder (no serde): the two fields we send.
fn json_string(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

/// Pull the first `"<key>":"…"` JSON string value out of a response, decoding
/// the standard escapes. (Good enough for the OpenAI/vLLM `content` and ollama
/// `response` shapes; the qwen lane is validated against the live box.)
fn extract_json_field(resp: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\"");
    let i = resp.find(&needle)?;
    let rest = &resp[i + needle.len()..];
    let colon = rest.find(':')?;
    let after = rest[colon + 1..].trim_start();
    let mut chars = after.chars();
    if chars.next()? != '"' {
        return None;
    }
    let mut out = String::new();
    let mut esc = false;
    for c in chars {
        if esc {
            match c {
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                '/' => out.push('/'),
                other => out.push(other),
            }
            esc = false;
        } else if c == '\\' {
            esc = true;
        } else if c == '"' {
            return Some(out);
        } else {
            out.push(c);
        }
    }
    None
}

fn cache_dir() -> PathBuf {
    PathBuf::from(".leanlift-cache")
}
