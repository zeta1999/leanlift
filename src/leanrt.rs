//! The Lean candidate runtime (SPEC §6 `leanrt/`).
//!
//! Runs a candidate Lean *runner* over the vector set and collects one
//! `args => RESULT` line per vector. A candidate carries the Lean environment it
//! needs:
//!   - `Support`: our audited hand-written library — `lean --run` with
//!     `LEAN_PATH` pointing at it (the C++/Go LLM path and the hand examples).
//!   - `Aeneas`:  the Aeneas-extracted model — `lake env lean` from Aeneas's
//!     built Lean backend dir so `import Aeneas` resolves (the sound Rust path).

use crate::vectors::Vector;
use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// The Lean toolchain environment a candidate runner needs to elaborate/run.
pub enum LeanEnv {
    /// Plain `lean --run`; `LEAN_PATH` = our compiled support library dir.
    Support(PathBuf),
    /// `lake env lean` from `<aeneas>/backends/lean` (resolves `import Aeneas`).
    Aeneas { aeneas_dir: PathBuf },
}

/// A runnable candidate: a generated/written Lean runner + its environment.
pub struct Candidate {
    pub runner: PathBuf,
    pub env: LeanEnv,
}

/// A typecheck/run failure from the Lean side — this is the L0 gate.
pub struct LeanError(pub String);

/// Run the candidate over `vectors`, returning a map from input key to RESULT.
pub fn run(
    cand: &Candidate,
    vectors: &[Vector],
    work_dir: &std::path::Path,
) -> Result<HashMap<String, String>, LeanError> {
    let vec_file = work_dir.join("vectors.txt");
    {
        let mut f = std::fs::File::create(&vec_file)
            .map_err(|e| LeanError(format!("cannot write vectors: {e}")))?;
        for v in vectors {
            writeln!(f, "{}", v.key()).unwrap();
        }
    }

    // Build a fresh `Command` per attempt (`Command` is consumed by `output()`).
    let build_cmd = || {
        let mut cmd = match &cand.env {
            LeanEnv::Support(lean_path) => {
                let mut c = Command::new("lean");
                c.arg("--run").arg(&cand.runner).env("LEAN_PATH", lean_path);
                c
            }
            LeanEnv::Aeneas { aeneas_dir } => {
                let mut c = Command::new("lake");
                c.args(["env", "lean", "--run"])
                    .arg(&cand.runner)
                    .current_dir(aeneas_dir.join("backends/lean"));
                c
            }
        };
        cmd.env("LEANLIFT_VECTORS", &vec_file);
        cmd
    };

    // A successful runner over a non-empty vector set ALWAYS emits ≥1
    // `args => RESULT` line. "exit 0 but zero parsed lines" therefore means the
    // runner never actually ran (a Lean build/cache flake, or a stale `.olean`
    // mid-rebuild) — NOT that the candidate is 100% wrong. Silently returning an
    // empty map would score every vector as an unexplained mismatch ("conform
    // 0/N, lean=<missing>") — a false red. Retry once to absorb the transient,
    // then raise loudly so the real stderr surfaces instead of phantom mismatches.
    let mut last_diag = String::new();
    for _attempt in 0..2 {
        let output = build_cmd()
            .output()
            .map_err(|e| LeanError(format!("failed to invoke lean: {e}")))?;

        if !output.status.success() {
            // A genuine typecheck/run failure is deterministic — fail fast, no retry.
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LeanError(stderr.trim().to_string()));
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let map = collect_outputs(&stdout);

        if output_usable(map.len(), vectors.len()) {
            return Ok(map);
        }

        let stderr = String::from_utf8_lossy(&output.stderr);
        last_diag = format!(
            "Lean runner exited 0 but produced no `args => RESULT` lines over {} vector(s) \
             — the runner did not execute (build/cache flake or a stale .olean). This is a \
             runner failure, not a conformance result.\n  stdout: {:?}\n  stderr: {}",
            vectors.len(),
            stdout.trim().chars().take(200).collect::<String>(),
            stderr.trim(),
        );
    }
    Err(LeanError(last_diag))
}

/// Parse `args => RESULT` lines from a runner's stdout into an input→result map.
fn collect_outputs(stdout: &str) -> HashMap<String, String> {
    stdout
        .lines()
        .filter_map(|line| line.split_once("=>"))
        .map(|(lhs, rhs)| (lhs.trim().to_string(), rhs.trim().to_string()))
        .collect()
}

/// A successful runner over a non-empty vector set emits at least one output
/// line. Zero output over a non-empty set means the runner did not run — that
/// is a failure to raise, not a (silently scored) all-mismatch verdict.
fn output_usable(map_len: usize, n_vectors: usize) -> bool {
    n_vectors == 0 || map_len > 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collect_parses_arrow_lines_and_ignores_noise() {
        let out = "0 0 1 => 42\nbuilding...\n3 => NAN\n";
        let m = collect_outputs(out);
        assert_eq!(m.len(), 2);
        assert_eq!(m["0 0 1"], "42");
        assert_eq!(m["3"], "NAN");
    }

    #[test]
    fn empty_output_over_nonempty_vectors_is_a_failure() {
        // The opt-hj flake signature: exit 0, zero parsed lines, N>0 vectors.
        assert!(!output_usable(0, 180), "zero output over 180 vectors must NOT be usable");
        assert!(output_usable(180, 180), "full coverage is usable");
        assert!(output_usable(1, 180), "partial output is usable (scored normally)");
    }

    #[test]
    fn empty_output_over_empty_vectorset_is_fine() {
        // A degenerate empty vector set legitimately yields an empty map.
        assert!(output_usable(0, 0), "empty map over empty vectors is vacuously usable");
    }
}
