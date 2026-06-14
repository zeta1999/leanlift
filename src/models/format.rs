//! Native `*.model.toml` → DTS-IR, with **content auto-detection** so the
//! one-command path needs no `--kind` (PLAN-models §0.4, §8 UX bar). The family
//! is read from an explicit `kind = "..."` if present, else inferred from the
//! file's shape: `places` ⇒ a Petri net, `states` ⇒ an FSM. Phase 0 lands the
//! FSM builder; PT-net/CPN/SPN builders slot in here behind the same detector.
//!
//! The FSM authoring shape (easy by design — docs/SPEC-models.md §9):
//!
//! ```toml
//! kind    = "fsm"          # optional; inferred from `states`
//! initial = "idle"
//! states  = ["idle", "run", "error"]
//!
//! [[transition]]
//! from = "idle"
//! on   = "start"
//! to   = "run"
//!
//! [[forbid]]               # optional safety property: these must be unreachable
//! state = "error"
//! ```

use super::ir::Lts;
use super::toml::{self, Doc};
use std::collections::HashMap;

/// The detected family. Phase 0 builds FSMs; the rest are recognised so the CLI
/// can give a precise "not yet implemented" rather than a confusing parse error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Family {
    Fsm,
    Petri,
    Cpn,
    Bt,
    Spn,
}

impl Family {
    pub fn tag(self) -> &'static str {
        match self {
            Family::Fsm => "fsm",
            Family::Petri => "petri",
            Family::Cpn => "cpn",
            Family::Bt => "bt",
            Family::Spn => "spn",
        }
    }
}

/// Auto-detect the family from an explicit `kind` or the document's shape.
pub fn detect(doc: &Doc) -> Result<Family, String> {
    if let Some(v) = doc.scalar("kind") {
        return match v.as_str("kind")? {
            "fsm" => Ok(Family::Fsm),
            "petri" | "pt" | "ptnet" => Ok(Family::Petri),
            "cpn" => Ok(Family::Cpn),
            "bt" => Ok(Family::Bt),
            "spn" | "gspn" => Ok(Family::Spn),
            other => Err(format!("unknown kind `{other}` (have: fsm, petri, cpn, bt, spn)")),
        };
    }
    // Shape inference: places ⇒ Petri-family, states ⇒ FSM.
    if doc.scalar("places").is_some() {
        return Ok(Family::Petri);
    }
    if doc.scalar("states").is_some() {
        return Ok(Family::Fsm);
    }
    Err("cannot detect model family: no `kind`, `states`, or `places`".into())
}

/// Parse a source string into an FSM `Lts`. A document with a `machines` array
/// is built as the **synchronous (alphabetised) product** of its components and
/// flattened to a single `Lts` (so the checker and the Lean exporter both see
/// one transition system); otherwise it is a single flat FSM. (Detection is the
/// caller's job so the CLI can report the family before building.)
pub fn parse_fsm(src: &str) -> Result<Lts, String> {
    let doc = toml::parse(src)?;
    if doc.scalar("machines").is_some() {
        build_fsm_product(&doc)
    } else {
        build_fsm(&doc)
    }
}

/// Synchronous alphabetised product of two FSMs, mirroring `fsm.py`'s `product`
/// and the Lean `Fsm.prodStep`+`Fsm.lift`: a shared event fires iff BOTH accept
/// (one blocks ⇒ blocked); a private event moves its owner and self-loops the
/// other. Product states are encoded `"a|b"` (kept as `String` so the result is
/// a homogeneous, exportable `Lts`). Generalises to N machines by folding.
fn product(a: &Lts, b: &Lts) -> Lts {
    let mut alphabet = a.alphabet.clone();
    for e in &b.alphabet {
        if !alphabet.contains(e) {
            alphabet.push(e.clone());
        }
    }
    let mut states = Vec::new();
    let mut transitions = HashMap::new();
    for sa in &a.states {
        for sb in &b.states {
            let s = format!("{sa}|{sb}");
            states.push(s.clone());
            for e in &alphabet {
                // Private events: the non-owner self-loops (= Fsm.lift).
                let na = if a.alphabet.contains(e) {
                    a.transitions.get(&(sa.clone(), e.clone())).cloned()
                } else {
                    Some(sa.clone())
                };
                let nb = if b.alphabet.contains(e) {
                    b.transitions.get(&(sb.clone(), e.clone())).cloned()
                } else {
                    Some(sb.clone())
                };
                if let (Some(na), Some(nb)) = (na, nb) {
                    transitions.insert((s.clone(), e.clone()), format!("{na}|{nb}"));
                }
            }
        }
    }
    Lts {
        family: "fsm",
        states,
        alphabet,
        initial: format!("{}|{}", a.initial, b.initial),
        transitions,
        forbid: Vec::new(), // set by the caller (forbidden product states)
    }
}

fn build_fsm_product(doc: &Doc) -> Result<Lts, String> {
    let machines = doc.scalar("machines").unwrap().as_arr("machines")?.to_vec();
    if machines.len() < 2 {
        return Err("`machines` needs at least two component names".into());
    }
    let inits = doc
        .scalar("initial")
        .ok_or("product FSM requires an `initial` array (one state per machine)")?
        .as_arr("initial")?
        .to_vec();
    if inits.len() != machines.len() {
        return Err(format!(
            "`initial` has {} entries but `machines` has {}",
            inits.len(),
            machines.len()
        ));
    }

    // Build each component from its `machine`-tagged transitions.
    let mut comps: Vec<Lts> = Vec::new();
    for (mi, name) in machines.iter().enumerate() {
        let mut states: Vec<String> = vec![inits[mi].clone()];
        let mut alphabet: Vec<String> = Vec::new();
        let mut transitions = HashMap::new();
        for (i, t) in doc.table("transition").iter().enumerate() {
            if field(t, "machine", i)? != *name {
                continue;
            }
            let from = field(t, "from", i)?;
            let on = field(t, "on", i)?;
            let to = field(t, "to", i)?;
            for s in [&from, &to] {
                if !states.contains(s) {
                    states.push(s.clone());
                }
            }
            if !alphabet.contains(&on) {
                alphabet.push(on.clone());
            }
            if transitions.insert((from.clone(), on.clone()), to).is_some() {
                return Err(format!("{name}: ({from}, {on}) is non-deterministic"));
            }
        }
        if alphabet.is_empty() {
            return Err(format!("machine `{name}` has no transitions"));
        }
        comps.push(Lts { family: "fsm", states, alphabet, initial: inits[mi].clone(), transitions, forbid: Vec::new() });
    }

    // Fold the components into one flat product.
    let mut acc = comps.remove(0);
    for c in &comps {
        acc = product(&acc, c);
    }

    // Forbidden product states: each `[[forbid]]` names one state per machine.
    let mut forbid = Vec::new();
    for (i, f) in doc.table("forbid").iter().enumerate() {
        let parts: Vec<String> = machines
            .iter()
            .map(|m| field(f, m, i))
            .collect::<Result<_, String>>()?;
        let joined = parts.join("|");
        if !acc.states.contains(&joined) {
            return Err(format!("forbid {i}: product state `{joined}` does not exist"));
        }
        forbid.push(joined);
    }
    acc.forbid = forbid;
    Ok(acc)
}

fn build_fsm(doc: &Doc) -> Result<Lts, String> {
    let states: Vec<String> = doc
        .scalar("states")
        .ok_or("FSM requires a `states` array")?
        .as_arr("states")?
        .to_vec();
    if states.is_empty() {
        return Err("FSM `states` is empty".into());
    }
    let initial = doc
        .scalar("initial")
        .ok_or("FSM requires an `initial` state")?
        .as_str("initial")?
        .to_string();
    if !states.contains(&initial) {
        return Err(format!("`initial` state `{initial}` is not in `states`"));
    }

    let mut alphabet: Vec<String> = Vec::new();
    let mut transitions: HashMap<(String, String), String> = HashMap::new();
    for (i, t) in doc.table("transition").iter().enumerate() {
        let from = field(t, "from", i)?;
        let on = field(t, "on", i)?;
        let to = field(t, "to", i)?;
        for (name, s) in [("from", &from), ("to", &to)] {
            if !states.contains(s) {
                return Err(format!("transition {i}: `{name}` state `{s}` is not in `states`"));
            }
        }
        if !alphabet.contains(&on) {
            alphabet.push(on.clone());
        }
        if transitions.insert((from.clone(), on.clone()), to).is_some() {
            return Err(format!(
                "transition {i}: ({from}, {on}) is non-deterministic (already defined)"
            ));
        }
    }

    let forbid: Vec<String> = doc
        .table("forbid")
        .iter()
        .enumerate()
        .map(|(i, f)| {
            let s = field(f, "state", i)?;
            if !states.contains(&s) {
                return Err(format!("forbid {i}: state `{s}` is not in `states`"));
            }
            Ok(s)
        })
        .collect::<Result<_, String>>()?;

    Ok(Lts { family: "fsm", states, alphabet, initial, transitions, forbid })
}

fn field(t: &HashMap<String, toml::Value>, key: &str, i: usize) -> Result<String, String> {
    Ok(t.get(key)
        .ok_or_else(|| format!("[[transition/forbid]] {i}: missing `{key}`"))?
        .as_str(key)?
        .to_string())
}
