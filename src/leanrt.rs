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

    let output = cmd
        .env("LEANLIFT_VECTORS", &vec_file)
        .output()
        .map_err(|e| LeanError(format!("failed to invoke lean: {e}")))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(LeanError(stderr.trim().to_string()));
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut map = HashMap::new();
    for line in stdout.lines() {
        if let Some((lhs, rhs)) = line.split_once("=>") {
            map.insert(lhs.trim().to_string(), rhs.trim().to_string());
        }
    }
    Ok(map)
}
