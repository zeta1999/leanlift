//! FPGA protocol equivalence (PLAN-fpga Phase E, the one genuinely NEW engine).
//!
//! Given two control FSMs — an implementation and a golden reference, each
//! extracted from Aria-HDL as a Moore machine (`fpga_fsm`) — build their
//! SYNCHRONOUS PRODUCT over the shared input space and assert observational
//! equivalence: every reachable pair `(a, b)` agrees on its observable output
//! (the register value). The product is itself an `Lts` with `forbid =
//! {(a,b) : output a ≠ output b}`, so the EXISTING engines ride unchanged:
//! `check.rs` decides equivalence + yields a counterexample trace (E1, M1), and
//! `lean.rs::emit_fsm` proves the product never diverges — a sorry-free
//! bisimulation certificate (E2, M3). No new proof machinery.
//!
//! Soundness: both machines are deterministic functions of (state, input
//! valuation); driving them with the SAME input sequence and checking output
//! agreement at every reachable product state is exactly (strong) observational
//! equivalence. The check is exhaustive over the reachable product, so a PASS is
//! a real equivalence and a FAIL carries a concrete diverging input trace.

use super::fpga_fsm::FsmExtract;
use super::ir::Lts;
use std::collections::HashMap;

/// Cap on the shared input fan-out (2^k product alphabet before dedup).
const MAX_UNION_INPUTS: usize = 20;
/// Cap on the reachable product size — refuse (fail-closed) rather than build a
/// multi-million-pair table for adversarially large FSMs.
const MAX_PRODUCT_PAIRS: usize = 200_000;

pub struct Product {
    pub lts: Lts,
    /// Reachable product pairs, parallel to the `p{i}` state names.
    pub pairs: Vec<(i64, i64)>,
    /// The shared input names (union), in valuation-bit order.
    pub union_inputs: Vec<String>,
    /// Reachable pairs that DIVERGE (output a ≠ output b) — empty ⇔ equivalent.
    pub diverging: Vec<(i64, i64)>,
}

/// Build the synchronous product of two extracted Moore FSMs.
pub fn build_product(a: &FsmExtract, b: &FsmExtract) -> Result<Product, String> {
    // Shared input space = union of both machines' guard inputs (by name).
    let mut union: Vec<String> = a.moore_inputs.iter().chain(&b.moore_inputs).cloned().collect();
    union.sort();
    union.dedup();
    if union.len() > MAX_UNION_INPUTS {
        return Err(format!(
            "shared input space too large: {} bits (> {MAX_UNION_INPUTS}) — refuse exhaustive product",
            union.len()
        ));
    }
    let k = union.len();
    let combos = 1u64 << k;

    // For each machine, map its own input bit → the bit position in `union`.
    let bitmap = |inputs: &[String]| -> Vec<usize> {
        inputs
            .iter()
            .map(|n| union.iter().position(|x| x == n).expect("union superset"))
            .collect()
    };
    let a_map = bitmap(&a.moore_inputs);
    let b_map = bitmap(&b.moore_inputs);
    // Project a union valuation `u` to a machine's own valuation index.
    let project = |u: u64, map: &[usize]| -> u64 {
        let mut idx = 0u64;
        for (bit, &upos) in map.iter().enumerate() {
            idx |= ((u >> upos) & 1) << bit;
        }
        idx
    };

    let step = |m: &FsmExtract, s: i64, midx: u64| -> Result<i64, String> {
        m.moore_step
            .get(&(s, midx))
            .copied()
            .ok_or_else(|| format!("missing step for state {s} valuation {midx}"))
    };

    // BFS the reachable product from (a.reset, b.reset).
    let start = (a.reset, b.reset);
    let mut pairs: Vec<(i64, i64)> = vec![start];
    let mut idx_of: HashMap<(i64, i64), usize> = HashMap::from([(start, 0)]);
    let mut i = 0;
    while i < pairs.len() {
        let (av, bv) = pairs[i];
        i += 1;
        for u in 0..combos {
            let na = step(a, av, project(u, &a_map))?;
            let nb = step(b, bv, project(u, &b_map))?;
            let np = (na, nb);
            if !idx_of.contains_key(&np) {
                if pairs.len() >= MAX_PRODUCT_PAIRS {
                    return Err(format!("product exceeded {MAX_PRODUCT_PAIRS} pairs — FSMs too large for exhaustive equivalence"));
                }
                idx_of.insert(np, pairs.len());
                pairs.push(np);
            }
        }
    }
    let name_of = |p: (i64, i64)| format!("p{}", idx_of[&p]);

    // Behavioural dedup of union valuations over the (now fixed) pair set — keeps
    // the product alphabet (and the Lean case split) small, exactly as `fpga_fsm`.
    let mut behaviour_to_event: HashMap<Vec<(i64, i64)>, String> = HashMap::new();
    let mut events: Vec<String> = Vec::new();
    let mut transitions: HashMap<(String, String), String> = HashMap::new();
    for u in 0..combos {
        let mut behaviour = Vec::with_capacity(pairs.len());
        for &(av, bv) in &pairs {
            behaviour.push((step(a, av, project(u, &a_map))?, step(b, bv, project(u, &b_map))?));
        }
        let ev = behaviour_to_event
            .entry(behaviour.clone())
            .or_insert_with(|| {
                let e = format!("u{}", events.len());
                events.push(e.clone());
                e
            })
            .clone();
        for (pi, &p) in pairs.iter().enumerate() {
            transitions.insert((name_of(p), ev.clone()), name_of(behaviour[pi]));
        }
    }

    // Divergence: a reachable pair whose outputs (the register values) differ.
    let diverging: Vec<(i64, i64)> = pairs.iter().copied().filter(|&(av, bv)| av != bv).collect();
    let forbid: Vec<String> = diverging.iter().map(|&p| name_of(p)).collect();

    let states: Vec<String> = (0..pairs.len()).map(|i| format!("p{i}")).collect();
    let lts = Lts {
        family: "fsm",
        states,
        alphabet: events,
        initial: name_of(start),
        transitions,
        forbid,
    };
    Ok(Product { lts, pairs, union_inputs: union, diverging })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{check, fpga::parse_stream, fpga_fsm::extract_fsm};

    /// A 2-state toggle: `state := go ? hi : 0`, width 2, input `go`.
    fn toggle(hi: u32) -> String {
        format!(
            r#"{{"schema":"aria-ir-json/v1","id":0,"name":"t",
              "ports":[{{"id":0,"value":10,"name":"go","ty":{{"t":"bit"}},"dir":"input","clock_domain":0}}],
              "clock_domains":[],"annotations":[],
              "nodes":[{{"id":1,"name":"state","kind":{{"k":"register","ty":{{"t":"uint","n":2}},"clock_domain":0,
                "reset_value":{{"e":"lit","lit":{{"l":"uint","value":"0","width":2}}}},"enable":null,
                "next":{{"e":"mux","cond":{{"e":"ref","value":10}},
                  "true":{{"e":"lit","lit":{{"l":"uint","value":"{hi}","width":2}}}},
                  "false":{{"e":"lit","lit":{{"l":"uint","value":"0","width":2}}}}}}}}}}],
              "timing":{{}}}}"#
        )
    }

    fn fsm(src: &str) -> FsmExtract {
        let m = &parse_stream(src).unwrap()[0];
        extract_fsm(m).unwrap().unwrap()
    }

    #[test]
    fn identical_machines_are_equivalent() {
        let a = fsm(&toggle(1));
        let b = fsm(&toggle(1));
        let p = build_product(&a, &b).unwrap();
        assert!(p.diverging.is_empty(), "identical FSMs must be equivalent");
        let r = check::check(&p.lts, check::DEFAULT_BOUND);
        assert!(r.safe());
    }

    #[test]
    fn differing_machines_diverge_with_counterexample() {
        // `go ? 1 : 0` vs `go ? 2 : 0`: on go=1 they reach 1 vs 2 → diverge.
        let a = fsm(&toggle(1));
        let b = fsm(&toggle(2));
        let p = build_product(&a, &b).unwrap();
        assert!(!p.diverging.is_empty(), "differing FSMs must diverge");
        assert!(p.diverging.iter().any(|&(x, y)| x != y));
        let r = check::check(&p.lts, check::DEFAULT_BOUND);
        assert!(!r.safe(), "the checker must report the divergence as a violation");
    }

    #[test]
    fn product_initial_is_the_reset_pair() {
        let a = fsm(&toggle(1));
        let b = fsm(&toggle(1));
        let p = build_product(&a, &b).unwrap();
        assert_eq!(p.pairs[0], (0, 0)); // both reset to 0
        assert_eq!(p.union_inputs, vec!["go".to_string()]);
    }
}
