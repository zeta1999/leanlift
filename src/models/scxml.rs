//! SCXML (W3C State Chart XML) → FSM (`Lts`). The "standard format just works as
//! input" half of the UX bar (PLAN-models §1.5, §8): `lift model check
//! mission.scxml` is detected and handled with no conversion step.
//!
//! Supported subset: `<scxml initial="…">` with `<state id>` / `<final id>`
//! (flattened — nested/compound hierarchy is treated as a flat id set) and
//! `<transition event="…" target="…">`. A safety property is authored in-file
//! with the convention `forbid="true"` on a `<state>` (so the one-file path
//! stays intact). Eventless transitions and multiple targets are not modelled
//! (the first target is taken; a transition with no `event` is skipped with no
//! effect on the result).

use super::ir::Lts;
use super::xml::Node;
use std::collections::HashMap;

/// Build an FSM `Lts` from a parsed `<scxml>` element.
pub fn to_lts(root: &Node) -> Result<Lts, String> {
    // Collect every state/final id (flattened over any nesting).
    let mut state_nodes: Vec<&Node> = Vec::new();
    root.descendants("state", &mut state_nodes);
    root.descendants("final", &mut state_nodes);
    if state_nodes.is_empty() {
        return Err("SCXML has no <state>/<final> elements".into());
    }

    // Warn loudly if the chart is hierarchical: we flatten it to a flat id set,
    // which does NOT capture compound/parallel SCXML semantics (entering a
    // compound state enters its initial child). Silent flattening would give
    // wrong results; make it visible.
    let hierarchical = state_nodes.iter().any(|n| {
        n.children("state").next().is_some()
            || n.children("parallel").next().is_some()
            || n.children("final").next().is_some()
    });
    if hierarchical {
        eprintln!(
            "  warning: SCXML has compound/parallel states — flattening to a flat id set; \
             hierarchical entry semantics are NOT modelled (results may be incomplete)"
        );
    }

    let mut states: Vec<String> = Vec::new();
    for n in &state_nodes {
        let id = n.attr("id").ok_or("SCXML <state>/<final> is missing `id`")?.to_string();
        if !states.contains(&id) {
            states.push(id);
        }
    }

    let initial = root
        .attr("initial")
        .map(|s| s.split_whitespace().next().unwrap_or(s).to_string())
        .unwrap_or_else(|| states[0].clone());
    if !states.contains(&initial) {
        return Err(format!("SCXML `initial` state `{initial}` is not declared"));
    }

    let mut alphabet: Vec<String> = Vec::new();
    let mut transitions: HashMap<(String, String), String> = HashMap::new();
    for n in &state_nodes {
        let from = n.attr("id").unwrap().to_string();
        for t in n.children("transition") {
            let event = match t.attr("event") {
                Some(e) if !e.trim().is_empty() => e.trim().to_string(),
                _ => continue, // eventless / automatic transitions are not modelled
            };
            let to = match t.attr("target") {
                Some(tg) => tg.split_whitespace().next().unwrap_or(tg).to_string(),
                None => continue,
            };
            if !states.contains(&to) {
                return Err(format!("SCXML transition targets undeclared state `{to}`"));
            }
            if !alphabet.contains(&event) {
                alphabet.push(event.clone());
            }
            if transitions.insert((from.clone(), event.clone()), to).is_some() {
                return Err(format!("SCXML: ({from}, {event}) is non-deterministic"));
            }
        }
    }

    // Safety property: states marked `forbid="true"`.
    let forbid: Vec<String> = state_nodes
        .iter()
        .filter(|n| n.attr("forbid") == Some("true"))
        .map(|n| n.attr("id").unwrap().to_string())
        .collect();

    Ok(Lts { family: "fsm", states, alphabet, initial, transitions, forbid })
}
