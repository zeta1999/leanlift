//! PNML (ISO/IEC 15909-2, Petri Net Markup Language) → PT-net (`PtNet`). The
//! standard-format input for the Petri family (PLAN-models §2.6): `lift model
//! check db.pnml` is detected from the `<pnml>` root and reuses the Phase-2
//! checker. Supported subset: `<place>` with `<initialMarking>`, `<transition>`,
//! and `<arc source= target=>` with an optional `<inscription>` weight.
//!
//! PNML carries no safety property, so an imported net has no `[[bound]]` — `check`
//! gives reachability + deadlock + the loss/conservation classification (the most
//! useful analysis for a standard net). A bound/conserved subsystem for an M3
//! proof is authored in the native `*.model.toml` form.

use super::ir::{PtNet, PtTrans};
use super::xml::Node;
use std::collections::HashMap;

/// Build a PT-net from a parsed `<pnml>` element.
pub fn to_net(root: &Node) -> Result<PtNet, String> {
    let mut places_n: Vec<&Node> = Vec::new();
    root.descendants("place", &mut places_n);
    let mut trans_n: Vec<&Node> = Vec::new();
    root.descendants("transition", &mut trans_n);
    let mut arcs_n: Vec<&Node> = Vec::new();
    root.descendants("arc", &mut arcs_n);
    if places_n.is_empty() {
        return Err("PNML has no <place> elements".into());
    }

    let places: Vec<String> = places_n
        .iter()
        .map(|p| p.attr("id").map(str::to_string).ok_or("PNML <place> missing `id`".to_string()))
        .collect::<Result<_, String>>()?;
    let pindex: HashMap<&str, usize> = places.iter().enumerate().map(|(i, p)| (p.as_str(), i)).collect();

    let mut initial = vec![0u32; places.len()];
    for (i, p) in places_n.iter().enumerate() {
        if let Some(im) = p.children("initialMarking").next() {
            initial[i] = marking_value(im);
        }
    }

    let tids: Vec<String> = trans_n
        .iter()
        .map(|t| t.attr("id").map(str::to_string).ok_or("PNML <transition> missing `id`".to_string()))
        .collect::<Result<_, String>>()?;
    let tindex: HashMap<&str, usize> = tids.iter().enumerate().map(|(i, t)| (t.as_str(), i)).collect();

    let mut pre: Vec<Vec<u32>> = vec![vec![0; places.len()]; tids.len()];
    let mut post: Vec<Vec<u32>> = vec![vec![0; places.len()]; tids.len()];
    for a in &arcs_n {
        let src = a.attr("source").ok_or("PNML <arc> missing `source`")?;
        let dst = a.attr("target").ok_or("PNML <arc> missing `target`")?;
        let w = a.children("inscription").next().map(marking_value).unwrap_or(1);
        if let (Some(&p), Some(&t)) = (pindex.get(src), tindex.get(dst)) {
            pre[t][p] += w; // place → transition (consumed)
        } else if let (Some(&t), Some(&p)) = (tindex.get(src), pindex.get(dst)) {
            post[t][p] += w; // transition → place (produced)
        } else {
            return Err(format!("PNML <arc> {src}→{dst} does not connect a place and a transition"));
        }
    }

    let transitions: Vec<PtTrans> = tids
        .into_iter()
        .enumerate()
        .map(|(i, name)| PtTrans { name, pre: pre[i].clone(), post: post[i].clone() })
        .collect();

    Ok(PtNet { places, transitions, initial, bound: 8, bounds: Vec::new(), conserved: None })
}

/// Read the integer in an `<initialMarking>`/`<inscription>`: either a child
/// `<text>N</text>` (P/T dialect) or a `value="N"` attribute. Non-numeric → 0.
fn marking_value(n: &Node) -> u32 {
    if let Some(t) = n.children("text").next() {
        return t.text.trim().parse().unwrap_or(0);
    }
    if let Some(v) = n.attr("value") {
        // some dialects use "Default,1" or just "1"
        return v.rsplit(',').next().unwrap_or(v).trim().parse().unwrap_or(0);
    }
    n.text.trim().parse().unwrap_or(0)
}
