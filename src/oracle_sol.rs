//! Solidity EVM oracle (SPEC §6): execute the function on an EVM, where the
//! "vector" is calldata and the "result" is return data — a peer of the native
//! dlopen/runner oracle, not a hack.
//!
//! Implementation: a temporary Foundry project + a generated `forge script` that
//! runs entirely in forge's in-process EVM. The script reads the vector file and
//! writes results via filesystem cheatcodes (no forge-std, no node, no network
//! once solc is cached), deploying the contract and calling the function inside a
//! `try/catch` so a revert (Solidity's checked-overflow behavior) becomes the
//! `OVERFLOW` token — exactly like the Lean side's `Result.fail`.

use crate::sig::Signature;
use crate::vectors::Vector;
use std::collections::HashMap;
use std::io::Write;
use std::path::Path;
use std::process::Command;

pub fn run(
    source: &Path,
    symbol: &str,
    sig: &Signature,
    vectors: &[Vector],
    work_dir: &Path,
) -> Result<HashMap<String, String>, String> {
    let proj = work_dir.join("sol-oracle");
    let _ = std::fs::create_dir_all(proj.join("src"));
    let _ = std::fs::create_dir_all(proj.join("script"));

    let src_text =
        std::fs::read_to_string(source).map_err(|e| format!("cannot read {}: {e}", source.display()))?;
    let contract = contract_name(&src_text)
        .ok_or_else(|| format!("no `contract X` found in {}", source.display()))?;
    let src_name = source.file_name().and_then(|s| s.to_str()).unwrap_or("Source.sol");

    std::fs::write(proj.join("src").join(src_name), &src_text)
        .map_err(|e| format!("cannot stage solidity source: {e}"))?;
    std::fs::write(
        proj.join("foundry.toml"),
        "[profile.default]\nsrc = \"src\"\nout = \"out\"\n\
         fs_permissions = [{ access = \"read-write\", path = \"./\" }]\n",
    )
    .map_err(|e| format!("cannot write foundry.toml: {e}"))?;

    // Input vectors (space-separated, one tuple per line).
    {
        let mut f = std::fs::File::create(proj.join("input.txt"))
            .map_err(|e| format!("cannot write input.txt: {e}"))?;
        for v in vectors {
            writeln!(f, "{}", v.key()).unwrap();
        }
    }

    std::fs::write(
        proj.join("script").join("Run.s.sol"),
        run_script(&contract, src_name, symbol, sig),
    )
    .map_err(|e| format!("cannot write run script: {e}"))?;

    // forge script runs run() in forge's EVM. --silent keeps stdout quiet; the
    // results land in output.txt via the writeLine cheatcode.
    let out = Command::new("forge")
        .args(["script", "script/Run.s.sol:Run", "--silent"])
        .current_dir(&proj)
        .output()
        .map_err(|e| format!("failed to invoke forge (is Foundry installed?): {e}"))?;
    if !out.status.success() {
        let mut log = out.stdout.clone();
        log.extend_from_slice(&out.stderr);
        let _ = std::fs::write(work_dir.join("forge.log"), &log);
        return Err(format!(
            "forge script failed (see {}/forge.log)",
            work_dir.display()
        ));
    }

    let results = std::fs::read_to_string(proj.join("output.txt"))
        .map_err(|e| format!("forge produced no output.txt: {e}"))?;
    let mut map = HashMap::new();
    for line in results.lines() {
        if let Some((lhs, rhs)) = line.split_once("=>") {
            map.insert(lhs.trim().to_string(), rhs.trim().to_string());
        }
    }
    Ok(map)
}

/// First `contract <Name>` in the source.
fn contract_name(src: &str) -> Option<String> {
    for line in src.lines() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("contract ") {
            let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
            if !name.is_empty() {
                return Some(name);
            }
        }
    }
    None
}

/// Generate the forge script that replays vectors through the contract.
fn run_script(contract: &str, src_name: &str, symbol: &str, sig: &Signature) -> String {
    let n = sig.arity();
    // parse parts[i] into typed locals x0..xN
    let parses = (0..n)
        .map(|i| {
            format!(
                "      {ty} x{i} = {ty}(vm.parseUint(parts[{i}]));",
                ty = sig.args[i].sol_name()
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let call_args = (0..n).map(|i| format!("x{i}")).collect::<Vec<_>>().join(", ");
    format!(
        "// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n\
         import {{{contract}}} from \"../src/{src_name}\";\n\n\
         interface Vm {{\n\
         \x20 function readLine(string calldata) external returns (string memory);\n\
         \x20 function split(string calldata, string calldata) external pure returns (string[] memory);\n\
         \x20 function parseUint(string calldata) external pure returns (uint256);\n\
         \x20 function toString(uint256) external pure returns (string memory);\n\
         \x20 function writeFile(string calldata, string calldata) external;\n\
         \x20 function writeLine(string calldata, string calldata) external;\n\
         }}\n\n\
         contract Run {{\n\
         \x20 Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);\n\
         \x20 function run() external {{\n\
         \x20   string memory inp = \"input.txt\";\n\
         \x20   string memory outp = \"output.txt\";\n\
         \x20   vm.writeFile(outp, \"\");\n\
         \x20   {contract} c = new {contract}();\n\
         \x20   while (true) {{\n\
         \x20     string memory line = vm.readLine(inp);\n\
         \x20     if (bytes(line).length == 0) break;\n\
         \x20     string[] memory parts = vm.split(line, \" \");\n\
         \x20     if (parts.length != {n}) continue;\n\
         {parses}\n\
         \x20     try c.{symbol}({call_args}) returns ({ret} r) {{\n\
         \x20       vm.writeLine(outp, string.concat(line, \" => \", vm.toString(uint256(r))));\n\
         \x20     }} catch {{\n\
         \x20       vm.writeLine(outp, string.concat(line, \" => OVERFLOW\"));\n\
         \x20     }}\n\
         \x20   }}\n\
         \x20 }}\n}}\n",
        ret = sig.ret.sol_name(),
    )
}
