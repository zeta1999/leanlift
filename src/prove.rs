//! L3 proof path (SPEC §10): assemble the Aeneas-extracted model with a proven
//! theorem fragment, elaborate it through the Aeneas Lean environment, and
//! certify it **sorry-free** (kernel-checked, no `sorryAx`). This is the rung
//! above L1 conformance: not "agrees on N vectors" but "a theorem holds ∀".

use std::path::Path;
use std::process::Command;

pub struct ProofReport {
    pub theorems: Vec<String>,
    pub axioms: Vec<String>,
    pub sorry_free: bool,
}

/// Assemble `import Aeneas … namespace kernel <def> <fragment> end kernel`, run
/// it via `lake env lean` from Aeneas's built Lean backend, and inspect the
/// `#print axioms` output for `sorryAx`.
pub fn prove_aeneas(
    def: &str,
    frag_path: &Path,
    aeneas_dir: &Path,
    work_dir: &Path,
) -> Result<ProofReport, String> {
    let frag = std::fs::read_to_string(frag_path)
        .map_err(|e| format!("cannot read proof fragment {}: {e}", frag_path.display()))?;
    let theorems: Vec<String> = frag
        .lines()
        .filter_map(|l| l.strip_prefix("theorem "))
        .map(|r| {
            r.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect::<String>()
        })
        .filter(|s| !s.is_empty())
        .collect();

    let file = work_dir.join("Proofs.lean");
    let content = format!(
        "import Aeneas\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\nnamespace kernel\n{def}\n\n{frag}\nend kernel\n"
    );
    std::fs::write(&file, content).map_err(|e| format!("cannot write proof file: {e}"))?;

    let out = Command::new("lake")
        .args(["env", "lean"])
        .arg(&file)
        .current_dir(aeneas_dir.join("backends/lean"))
        .output()
        .map_err(|e| format!("failed to run lake env lean: {e}"))?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    if !out.status.success() {
        let _ = std::fs::write(work_dir.join("proof.err"), format!("{stdout}\n{stderr}"));
        return Err(format!(
            "proof did not elaborate (see {}/proof.err):\n{}",
            work_dir.display(),
            stderr.lines().take(10).collect::<Vec<_>>().join("\n")
        ));
    }

    // Gather the union of axioms reported by `#print axioms`.
    let mut axioms: Vec<String> = Vec::new();
    for line in stdout.lines() {
        if line.contains("depends on axioms") {
            if let (Some(a), Some(b)) = (line.find('['), line.rfind(']')) {
                for ax in line[a + 1..b].split(',') {
                    let ax = ax.trim().to_string();
                    if !ax.is_empty() && !axioms.contains(&ax) {
                        axioms.push(ax);
                    }
                }
            }
        }
    }
    // The authoritative check is `#print axioms`: a `sorry` anywhere in a
    // theorem's proof surfaces as the `sorryAx` axiom. (A textual scan of the
    // fragment would false-positive on the word "sorry" in comments.)
    let sorry_free = !stdout.contains("sorryAx") && !axioms.iter().any(|a| a.contains("sorry"));

    Ok(ProofReport { theorems, axioms, sorry_free })
}

/// Optional independent re-certification of an emitted proof through the shared le-harnais Lean
/// backend: `lh --json logic lean4 <code>` with `LH_LEAN_PROJECT` pointed at `lean_project` so lh
/// elaborates in the same environment (mathlib or, here, Aeneas's `backends/lean`). Returns lh's
/// `complete` verdict (compiles ∧ no sorry ∧ no errors — the same signal our `#print axioms`
/// certification checks), or `None` when `lh` isn't installed / the call fails. le-harnais is a
/// separate, OPTIONAL, closed-source tool: absence is a clean skip, never a failure, and leanlift
/// carries no build dependency on it (this is a runtime shell-out).
pub fn lh_verify(code: &str, lean_project: &Path) -> Option<bool> {
    let out = Command::new("lh")
        .args(["--json", "logic", "lean4", code])
        .env("LH_LEAN_PROJECT", lean_project)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    // The lh-contract envelope nests the verdict; `complete` is the load-bearing boolean.
    json_bool_field(&stdout, "complete")
}

/// Read a JSON boolean field by key from `s` (naive scan — enough for lh's flat verdict envelope).
fn json_bool_field(s: &str, key: &str) -> Option<bool> {
    let needle = format!("\"{key}\"");
    let after = &s[s.find(&needle)? + needle.len()..];
    let after = after.trim_start().strip_prefix(':')?.trim_start();
    if after.starts_with("true") {
        Some(true)
    } else if after.starts_with("false") {
        Some(false)
    } else {
        None
    }
}

/// Emit a worked `*.recipe.md` documenting the procedure (the deliverable from
/// docs/PLAN-proofs.md §I.1 step 6).
pub fn write_recipe(
    path: &Path,
    example: &str,
    crate_src: &str,
    def: &str,
    rep: &ProofReport,
) -> std::io::Result<()> {
    let mut s = String::new();
    s.push_str(&format!("# Proof recipe — `{example}` (L3)\n\n"));
    s.push_str("Auto-generated by `lift prove`. The procedure, end to end:\n\n");
    s.push_str("## 1. Source (Rust)\n\n```rust\n");
    s.push_str(crate_src.trim());
    s.push_str("\n```\n\n## 2. Model (Aeneas-extracted Lean, verbatim)\n\n```lean\n");
    s.push_str(def.trim());
    s.push_str("\n```\n\n## 3. Obligations discharged (sorry-free)\n\n");
    for t in &rep.theorems {
        s.push_str(&format!("- `{t}`\n"));
    }
    s.push_str(&format!(
        "\n## 4. Certificate\n\n- level: **{}**\n- sorry-free: **{}**\n- axioms: `{}`\n",
        if rep.sorry_free { "L3 proved" } else { "L3 FAILED" },
        rep.sorry_free,
        rep.axioms.join(", ")
    ));
    s.push_str("\n`Classical.choice/propext/Quot.sound` are Lean's standard logical axioms; the absence of `sorryAx` means the kernel checked every step.\n");
    std::fs::write(path, s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_complete_from_lh_envelope() {
        let s = r#"{ "schema_version": "lh-contract/0.1", "op": "logic",
                     "backend": "lean4", "verdict": { "ok": true, "complete": true, "sorry": false } }"#;
        assert_eq!(json_bool_field(s, "complete"), Some(true));
        assert_eq!(json_bool_field(r#"{"verdict":{"complete":false}}"#, "complete"), Some(false));
        assert_eq!(json_bool_field("{}", "complete"), None);
    }
}
