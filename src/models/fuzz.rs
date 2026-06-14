//! Parser robustness fuzzing (PLAN-verification §V2, hand-rolled variant).
//!
//! The `toml`/`xml`/`scxml`/`pnml` parsers index and `unwrap`; adversarial bytes
//! are the likeliest panic (PLAN-verification §V2). cargo-fuzz/libFuzzer would be
//! the textbook tool, but it needs a *library* API to call — this crate is a
//! binary with private parser modules, and exposing a lib just to fuzz is a
//! crate-wide refactor. So, in the project's "hand-rolled, seeded, offline-safe"
//! ethos (cf. `proptest.rs`), this runs an in-crate fuzzer that has direct access
//! to the private parsers: it seeds from the example corpus, applies random
//! mutations, and asserts every parser returns Ok/Err but NEVER panics. Runs in
//! `cargo test` — no external tool, no nightly, deterministic.

#![cfg(test)]

use super::{pnml, scxml, toml, xml};
use std::panic::{self, AssertUnwindSafe};

/// A tiny seeded xorshift PRNG (test-local; mirrors proptest.rs's).
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn upto(&mut self, n: usize) -> usize {
        (self.next() as usize) % n.max(1)
    }
    fn byte(&mut self) -> u8 {
        (self.next() & 0xff) as u8
    }
}

/// The seed corpus: every parseable example (toml + the xml dialects).
fn corpus() -> Vec<Vec<u8>> {
    let files = [
        "tiny.model.toml",
        "mcl.model.toml",
        "dock.model.toml",
        "mission.model.toml",
        "resource.model.toml",
        "dock-gspn.model.toml",
        "dock.pnml",
        "turnstile.scxml",
    ];
    files
        .iter()
        .filter_map(|f| std::fs::read(format!("examples/models/{f}")).ok())
        .collect()
}

/// Apply one random mutation: bit flip / byte replace / insert / delete /
/// truncate / duplicate a run / splice in a structural metacharacter.
fn mutate(r: &mut Rng, d: &mut Vec<u8>) {
    if d.is_empty() {
        d.push(r.byte());
        return;
    }
    let meta = b"[]{}()<>=\"'/\\,.: \n\t#-";
    match r.upto(7) {
        0 => {
            let i = r.upto(d.len());
            d[i] ^= 1 << r.upto(8);
        }
        1 => {
            let i = r.upto(d.len());
            d[i] = r.byte();
        }
        2 => {
            let i = r.upto(d.len() + 1);
            d.insert(i, meta[r.upto(meta.len())]);
        }
        3 => {
            let i = r.upto(d.len());
            d.remove(i);
        }
        4 => {
            let i = r.upto(d.len());
            d.truncate(i);
        }
        5 => {
            let i = r.upto(d.len());
            let j = (i + 1 + r.upto(8)).min(d.len());
            let seg = d[i..j].to_vec();
            let at = r.upto(d.len() + 1);
            for (k, b) in seg.into_iter().enumerate() {
                d.insert(at + k, b);
            }
        }
        _ => {
            let i = r.upto(d.len());
            d[i] = meta[r.upto(meta.len())];
        }
    }
}

/// Run `f` catching panics; `Ok(v)` = no panic (with the closure's value),
/// `Err(())` = it panicked.
fn run<R, F: FnOnce() -> R>(f: F) -> Result<R, ()> {
    panic::catch_unwind(AssertUnwindSafe(f)).map_err(|_| ())
}

#[test]
fn parsers_never_panic() {
    let corpus = corpus();
    assert!(!corpus.is_empty(), "no corpus files found (run from repo root)");

    // Silence the per-catch panic noise; restore before asserting so other tests
    // keep the default hook. We re-report any real find cleanly via `failure`.
    let prev = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));

    let mut r = Rng(0x1234_5678_9abc_def1);
    let mut failure: Option<String> = None;
    // Non-vacuity: prove the fuzzer drives the parsers to BOTH accept and reject
    // (i.e. inputs reach deep into parse logic, not just bounce off byte 0).
    let (mut toml_ok, mut toml_err, mut xml_ok) = (0u32, 0u32, 0u32);
    'outer: for _ in 0..20_000 {
        // Base: a corpus entry (mutated 1–5×) or, 1/4 of the time, random bytes.
        let mut data: Vec<u8> = if r.upto(4) == 0 {
            (0..r.upto(64)).map(|_| r.byte()).collect()
        } else {
            corpus[r.upto(corpus.len())].clone()
        };
        for _ in 0..=r.upto(4) {
            mutate(&mut r, &mut data);
        }
        let s = String::from_utf8_lossy(&data).into_owned();
        let snippet = || s.chars().take(200).collect::<String>();

        match run(|| toml::parse(&s).is_ok()) {
            Ok(true) => toml_ok += 1,
            Ok(false) => toml_err += 1,
            Err(()) => {
                failure = Some(format!("toml::parse on ({} bytes): {:?}", s.len(), snippet()));
                break 'outer;
            }
        }
        match run(|| match xml::parse(&s) {
            Ok(node) => {
                let _ = scxml::to_lts(&node);
                let _ = pnml::to_net(&node);
                true
            }
            Err(_) => false,
        }) {
            Ok(true) => xml_ok += 1,
            Ok(false) => {}
            Err(()) => {
                failure = Some(format!("xml/scxml/pnml on ({} bytes): {:?}", s.len(), snippet()));
                break 'outer;
            }
        }
    }

    panic::set_hook(prev);
    assert!(failure.is_none(), "PARSER PANIC on adversarial input — {}", failure.unwrap());
    assert!(toml_ok > 0 && toml_err > 0, "fuzz near-vacuous for toml (ok={toml_ok}, err={toml_err})");
    assert!(xml_ok > 0, "fuzz never produced a valid XML parse (xml_ok={xml_ok}) — corpus/mutator too weak");
}
