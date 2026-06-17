//! FPGA dataflow flow-safety (PLAN-fpga Phase D, slice ③).
//!
//! Project an Aria-HDL `Fifo` node onto leanlift's `PtNet` so the existing Petri
//! checker (`check.rs`) and `lean.rs::emit_petri` (sorry-free upper-bound proof)
//! ride unchanged. The FIFO is modelled by two complementary places —
//! `occ` (occupied slots) and `free` (free slots) — with `occ + free = depth`
//! conserved by enqueue/dequeue, plus a **pure-loss** `leak` transition (empty
//! post — the plan's channel-loss shape). The safety property is the overflow
//! bound `occ ≤ depth`: it rides the conserved mass and **survives loss** (a leak
//! only ever DECREASES the total), exactly the `link.model.toml` pattern proved
//! elsewhere — now extracted mechanically from the hardware IR.

use super::ir::{BoundProp, PtNet, PtTrans};
use super::fpga::Json;

pub struct FifoNet {
    pub name: String,
    pub depth: u32,
    pub is_cdc: bool,
    /// Source/destination clock-domain ids (differ ⇒ a CDC FIFO).
    pub src_clock: u64,
    pub dst_clock: u64,
    pub net: PtNet,
}

/// Number of reachable markings of `fifo_net(depth)` = `{(occ,free) : occ+free ≤
/// depth}` = `(depth+1)(depth+2)/2`. Used to size the explicit-state BFS bound (and
/// to skip it for very deep FIFOs — `prove` certifies those symbolically).
pub fn reachable_markings(depth: u32) -> u64 {
    let d = depth as u64;
    (d + 1) * (d + 2) / 2
}

/// Build the canonical bounded-FIFO Petri net for a given `depth`.
///
/// places `[occ, free]`, init `occ=0, free=depth`; transitions:
///   * `enqueue`  free → occ   (blocked when full: `free = 0`)
///   * `dequeue`  occ  → free
///   * `leak`     occ  → ∅      (pure loss: an item vanishes, total decreases)
/// conserved = `[occ, free]` ⇒ proven bound `occ ≤ depth`, monotone under loss.
///
/// Scope: this certifies the OVERFLOW upper bound `occ ≤ depth` only. The net
/// guards `dequeue`/`leak` by `occ ≥ 1` so it cannot underflow, but underflow-
/// freedom (no read-when-empty) is NOT a proved theorem here — it is out of scope.
/// The `write_enable`/`read_enable` signals are deliberately left unconstrained, so
/// this net OVER-approximates the real FIFO (enqueue may fire whenever a slot is
/// free) — sound for an upper bound: it cannot miss a real overflow.
fn fifo_net(depth: u32) -> PtNet {
    PtNet {
        places: vec!["occ".into(), "free".into()],
        transitions: vec![
            PtTrans { name: "enqueue".into(), pre: vec![0, 1], post: vec![1, 0] },
            PtTrans { name: "dequeue".into(), pre: vec![1, 0], post: vec![0, 1] },
            PtTrans { name: "leak".into(), pre: vec![1, 0], post: vec![0, 0] },
        ],
        initial: vec![0, depth],
        bound: depth,
        bounds: vec![BoundProp { name: "fifo_no_overflow".into(), places: vec![0], max: depth }],
        conserved: Some(vec![0, 1]),
    }
}

/// Extract every `Fifo` node in a module as a flow-safety obligation. `Err` on a
/// malformed fifo node (missing/oversized depth) — fail-closed.
pub fn extract_fifos(module: &Json) -> Result<Vec<FifoNet>, String> {
    let nodes = match module.get("nodes").and_then(Json::as_arr) {
        Some(n) => n,
        None => return Ok(Vec::new()),
    };
    let mut out = Vec::new();
    let mut anon = 0;
    for n in nodes {
        let kind = match n.get("kind") {
            Some(k) if k.str_field("k") == Some("fifo") => k,
            _ => continue,
        };
        let depth = kind
            .get("depth")
            .and_then(Json::as_u64)
            .ok_or("fifo: missing/invalid `depth`")?;
        // A depth-0 FIFO is degenerate. The upper cap bounds the SYMBOLIC proof's
        // literals; the explicit-state `check` sizes its own BFS bound per FIFO and
        // defers very deep ones to `prove` (see check_cmd) — it does not rely on
        // this cap keeping the state space within DEFAULT_BOUND.
        if depth == 0 || depth > 65_536 {
            return Err(format!("fifo `depth` {depth} out of range (1..=65536)"));
        }
        let name = n.str_field("name").map(String::from).unwrap_or_else(|| {
            anon += 1;
            format!("fifo{anon}")
        });
        let is_cdc = kind.get("is_cdc").and_then(Json::as_bool).unwrap_or(false);
        let src_clock = kind.get("src_clock").and_then(Json::as_u64).unwrap_or(0);
        let dst_clock = kind.get("dst_clock").and_then(Json::as_u64).unwrap_or(0);
        out.push(FifoNet { name, depth: depth as u32, is_cdc, src_clock, dst_clock, net: fifo_net(depth as u32) });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{check, lean};

    fn one_fifo(depth: u32, is_cdc: bool) -> String {
        format!(
            r#"{{"schema":"aria-ir-json/v1","id":0,"name":"buf",
              "ports":[],"clock_domains":[],"annotations":[],
              "nodes":[{{"id":1,"name":"q","kind":{{"k":"fifo","data_ty":{{"t":"bits","n":8}},"depth":{depth},
                "src_clock":0,"dst_clock":{dst},"write_data":2,"write_enable":3,"read_enable":4,"is_cdc":{is_cdc}}}}}],
              "timing":{{}}}}"#,
            dst = if is_cdc { 1 } else { 0 }
        )
    }

    fn extract(src: &str) -> Vec<FifoNet> {
        let m = &crate::models::fpga::parse_stream(src).unwrap()[0];
        extract_fifos(m).unwrap()
    }

    #[test]
    fn extracts_fifo_with_depth_and_cdc() {
        let f = &extract(&one_fifo(4, true))[0];
        assert_eq!(f.depth, 4);
        assert!(f.is_cdc);
        assert_ne!(f.src_clock, f.dst_clock);
        assert_eq!(f.net.initial, vec![0, 4]); // occ=0, free=4
        assert_eq!(f.net.bounds[0].max, 4);
    }

    #[test]
    fn bound_holds_and_check_is_safe() {
        let f = &extract(&one_fifo(4, false))[0];
        let r = check::check(&f.net, check::DEFAULT_BOUND);
        assert!(r.safe(), "occ ≤ depth must hold in every reachable marking");
        // occ can reach exactly `depth` (a full FIFO) but never exceed it.
        assert!(!r.truncated);
    }

    #[test]
    fn leak_is_pure_loss_and_preserves_the_bound() {
        // The `leak` transition is pure loss (empty post): it must reduce the
        // total, so the upper bound survives it.
        let f = &extract(&one_fifo(3, false))[0];
        let leak = f.net.transitions.iter().find(|t| t.name == "leak").unwrap();
        assert!(leak.is_loss(), "leak must be a pure-loss transition");
        let r = check::check(&f.net, check::DEFAULT_BOUND);
        assert!(r.safe());
    }

    #[test]
    fn reachable_markings_matches_bfs() {
        // The closed form must equal the actual reachable set the BFS explores.
        for depth in [1u32, 2, 4, 7, 16] {
            let f = &extract(&one_fifo(depth, false))[0];
            let r = check::check(&f.net, check::DEFAULT_BOUND);
            assert_eq!(r.reachable as u64, reachable_markings(depth), "depth {depth}");
            assert!(!r.truncated);
        }
    }

    #[test]
    fn deep_fifo_extracts_for_symbolic_prove() {
        // A deep FIFO (beyond the old 4096 cap) still extracts — `prove` handles it
        // symbolically even though the explicit `check` would defer it.
        let f = extract(&one_fifo(10_000, false));
        assert_eq!(f[0].depth, 10_000);
        assert!(reachable_markings(10_000) > 500_000); // explicit check would defer
    }

    #[test]
    fn malformed_fifo_depth_is_refused() {
        let m = &crate::models::fpga::parse_stream(&one_fifo(0, false)).unwrap()[0];
        assert!(extract_fifos(m).is_err());
    }

    #[test]
    fn emit_petri_proof_skeleton_present() {
        let f = &extract(&one_fifo(4, false))[0];
        let src = lean::emit_petri(&f.net, "Fpga_buf_q");
        assert!(src.contains("def total"));
        assert!(src.contains("≤ 4")); // bound B = depth
        assert!(src.contains("theorem"));
    }

    #[test]
    fn tight_bound_is_violated_teeth() {
        // teeth: assert occ ≤ depth-1 (too tight). A full FIFO (occ = depth) then
        // violates it — the checker must catch the reachable overflow.
        let mut f = extract(&one_fifo(4, false)).pop().unwrap();
        f.net.bounds[0].max = 3; // occ ≤ 3, but occ can reach 4
        let r = check::check(&f.net, check::DEFAULT_BOUND);
        assert!(!r.safe(), "a too-tight bound must be violated by a full FIFO");
        assert!(r.violations.iter().any(|(_, why)| why.contains("fifo_no_overflow")));
    }
}
