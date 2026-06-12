//! Built-in example registry. Each entry wires a source kernel to a *front-end*
//! (how its candidate Lean is obtained), a source language (oracle strategy), a
//! signature, a semantic profile, and a vector generator.

use crate::compare::Profile;
use crate::frontend::Frontend;
use crate::lang::Lang;
use crate::sig::{IntType, Signature};
use crate::vectors::{self, Vector};
use std::path::PathBuf;

pub struct Example {
    pub name: &'static str,
    pub lang: Lang,
    pub source: PathBuf, // the native/EVM oracle (ground truth)
    pub fn_name: &'static str,
    pub signature: Signature,
    pub profile: Profile,
    pub gen: fn() -> Vec<Vector>,
    pub frontend: Frontend, // how the candidate Lean is produced
    pub proof_frag: Option<PathBuf>, // L3 theorem fragment (Aeneas examples)
}

pub const NAMES: &[&str] = &[
    "streamed", "avg", "rust-streamed", "cpp-streamed", "cpp-dot2", "go-avg", "sol-dot2",
    "rust-isqrt", "cpp-isqrt",
];

fn lean_lib() -> PathBuf {
    PathBuf::from("lean")
}

fn home() -> PathBuf {
    PathBuf::from(std::env::var("HOME").unwrap_or_default())
}

fn u(width: IntType, n: usize) -> Signature {
    Signature { args: vec![width; n], ret: width }
}

pub fn lookup(name: &str) -> Option<Example> {
    match name {
        "streamed" => Some(Example {
            name: "streamed",
            lang: Lang::Cpp,
            source: "examples/streamed/streamed.cpp".into(),
            fn_name: "streamed",
            signature: u(IntType::U64, 4),
            profile: Profile::Streamed,
            gen: vectors::streamed_vectors,
            frontend: Frontend::Prewritten {
                runner: "examples/streamed/Streamed.lean".into(),
                lean_path: lean_lib(),
            },
            proof_frag: None,
        }),
        "avg" => Some(Example {
            name: "avg",
            lang: Lang::Cpp,
            source: "examples/avg/avg.cpp".into(),
            fn_name: "avg",
            signature: u(IntType::U32, 2),
            profile: Profile::Avg,
            gen: vectors::avg_vectors,
            frontend: Frontend::Prewritten {
                runner: "examples/avg/Avg.lean".into(),
                lean_path: lean_lib(),
            },
            proof_frag: None,
        }),
        // Sound path: candidate Lean EXTRACTED from Rust by Charon+Aeneas,
        // validated against the C++ reference oracle.
        "rust-streamed" => Some(Example {
            name: "rust-streamed",
            lang: Lang::Cpp,
            source: "examples/streamed/streamed.cpp".into(),
            fn_name: "streamed",
            signature: u(IntType::U64, 4),
            profile: Profile::Streamed,
            gen: vectors::streamed_vectors,
            frontend: Frontend::RustAeneas {
                crate_dir: home().join("work/propaganda/tutor-tech/rust-day39-iterator-vesting"),
                entrypoint: "streamed".into(),
            },
            proof_frag: Some("examples/streamed/StreamedProofs.lean".into()),
        }),
        // LLM path, C++.
        "cpp-streamed" => Some(Example {
            name: "cpp-streamed",
            lang: Lang::Cpp,
            source: "examples/streamed/streamed.cpp".into(),
            fn_name: "streamed",
            signature: u(IntType::U64, 4),
            profile: Profile::Streamed,
            gen: vectors::streamed_vectors,
            frontend: Frontend::Llm { max_iters: 4 },
            proof_frag: None,
        }),
        "cpp-dot2" => Some(Example {
            name: "cpp-dot2",
            lang: Lang::Cpp,
            source: "examples/dot2/dot2.cpp".into(),
            fn_name: "dot2",
            signature: u(IntType::U32, 4),
            profile: Profile::Dot2,
            gen: vectors::dot2_vectors,
            frontend: Frontend::Llm { max_iters: 4 },
            proof_frag: None,
        }),
        // LLM path, Go — avg again, but Go also wraps on overflow.
        "go-avg" => Some(Example {
            name: "go-avg",
            lang: Lang::Go,
            source: "examples/go/avg.go".into(),
            fn_name: "avg",
            signature: u(IntType::U32, 2),
            profile: Profile::Avg,
            gen: vectors::avg_vectors,
            frontend: Frontend::Llm { max_iters: 4 },
            proof_frag: None,
        }),
        // LLM path, Solidity — dot2 in an `unchecked` block (so it wraps).
        "sol-dot2" => Some(Example {
            name: "sol-dot2",
            lang: Lang::Solidity,
            source: "examples/solidity/Dot2.sol".into(),
            fn_name: "dot2",
            signature: u(IntType::U32, 4),
            profile: Profile::Dot2,
            gen: vectors::dot2_vectors,
            frontend: Frontend::Llm { max_iters: 4 },
            proof_frag: None,
        }),
        // First numerical kernel (a LOOP): integer square root over u32.
        "rust-isqrt" => Some(Example {
            name: "rust-isqrt",
            lang: Lang::Cpp, // oracle = the C++ mirror
            source: "examples/isqrt/isqrt.cpp".into(),
            fn_name: "isqrt",
            signature: u(IntType::U32, 1),
            profile: Profile::Isqrt,
            gen: vectors::isqrt_vectors,
            frontend: Frontend::RustAeneas {
                crate_dir: "examples/rust-kernels".into(),
                entrypoint: "isqrt".into(),
            },
            proof_frag: None, // L3 loop proof is WIP (docs/PLAN-proofs.md)
        }),
        "cpp-isqrt" => Some(Example {
            name: "cpp-isqrt",
            lang: Lang::Cpp,
            source: "examples/isqrt/isqrt.cpp".into(),
            fn_name: "isqrt",
            signature: u(IntType::U32, 1),
            profile: Profile::Isqrt,
            gen: vectors::isqrt_vectors,
            frontend: Frontend::Llm { max_iters: 4 },
            proof_frag: None,
        }),
        _ => None,
    }
}
