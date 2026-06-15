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

use super::ir::{BoundProp, Lts, PtNet, PtTrans};
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
    Tasks,
}

impl Family {
    pub fn tag(self) -> &'static str {
        match self {
            Family::Fsm => "fsm",
            Family::Petri => "petri",
            Family::Cpn => "cpn",
            Family::Bt => "bt",
            Family::Spn => "spn",
            Family::Tasks => "tasks",
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
            "tasks" | "taskset" => Ok(Family::Tasks),
            other => Err(format!("unknown kind `{other}` (have: fsm, petri, cpn, bt, spn, tasks)")),
        };
    }
    if !doc.table("task").is_empty() {
        return Ok(Family::Tasks);
    }
    // Shape inference: `[[colour]]` ⇒ CPN, a `tree` ⇒ BT, `places` ⇒
    // Petri-family, `states`/`machines` ⇒ FSM.
    if !doc.table("colour").is_empty() {
        return Ok(Family::Cpn);
    }
    if doc.scalar("tree").is_some() {
        return Ok(Family::Bt);
    }
    if doc.scalar("places").is_some() {
        return Ok(Family::Petri);
    }
    if doc.scalar("states").is_some() || doc.scalar("machines").is_some() {
        return Ok(Family::Fsm);
    }
    Err("cannot detect model family: no `kind`, `states`, `machines`, `places`, or `tree`".into())
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
pub(super) fn product(a: &Lts, b: &Lts) -> Lts {
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

/// Parse a `*.model.toml` PT-net (Phase 2). Shape:
///
/// ```toml
/// kind    = "petri"
/// places  = ["free", "csA", "csB", "relA", "relB"]
/// initial = "free:1"          # a marking: comma-separated place:count
/// bound   = "8"               # optional per-place cap (default 8)
///
/// [[transition]]
/// name = "acqA"
/// pre  = "free:1"
/// post = "csA:1"
///
/// [[transition]]              # pure-loss: post is empty
/// name = "lossA"
/// pre  = "relA:1"
/// post = ""
///
/// [[bound]]                   # safety: sum(places) ≤ max
/// name   = "mutex"
/// places = ["csA", "csB"]
/// max    = "1"
/// ```
pub fn parse_petri(src: &str) -> Result<PtNet, String> {
    let doc = toml::parse(src)?;
    build_petri(&doc)
}

fn build_petri(doc: &Doc) -> Result<PtNet, String> {
    let places: Vec<String> = doc
        .scalar("places")
        .ok_or("PT-net requires a `places` array")?
        .as_arr("places")?
        .to_vec();
    if places.is_empty() {
        return Err("PT-net `places` is empty".into());
    }
    let index = |p: &str| places.iter().position(|x| x == p);

    let initial = parse_marking(
        doc.scalar("initial").ok_or("PT-net requires an `initial` marking")?.as_str("initial")?,
        &places,
        &index,
    )?;

    let bound: u32 = match doc.scalar("bound") {
        Some(v) => v.as_str("bound")?.parse().map_err(|_| "`bound` must be a positive integer")?,
        None => 8,
    };

    let mut transitions = Vec::new();
    for (i, t) in doc.table("transition").iter().enumerate() {
        let name = field(t, "name", i)?;
        let pre = parse_marking(t.get("pre").map(|v| v.as_str("pre")).transpose()?.unwrap_or(""), &places, &index)?;
        let post = parse_marking(t.get("post").map(|v| v.as_str("post")).transpose()?.unwrap_or(""), &places, &index)?;
        transitions.push(PtTrans { name, pre, post });
    }
    if transitions.is_empty() {
        return Err("PT-net has no transitions".into());
    }

    let mut bounds = Vec::new();
    for (i, b) in doc.table("bound").iter().enumerate() {
        let name = field(b, "name", i)?;
        let max: u32 = field(b, "max", i)?.parse().map_err(|_| format!("bound {i}: `max` must be an integer"))?;
        let idxs: Vec<usize> = b
            .get("places")
            .ok_or_else(|| format!("bound {i}: missing `places`"))?
            .as_arr("places")?
            .iter()
            .map(|p| index(p).ok_or_else(|| format!("bound {i}: place `{p}` not declared")))
            .collect::<Result<_, String>>()?;
        bounds.push(BoundProp { name, places: idxs, max });
    }

    // Optional conserved subsystem for the inductive place invariant; default
    // (omitted) = all places.
    let conserved = match doc.scalar("conserved") {
        Some(v) => {
            let idxs: Vec<usize> = v
                .as_arr("conserved")?
                .iter()
                .map(|p| index(p).ok_or_else(|| format!("conserved: place `{p}` not declared")))
                .collect::<Result<_, String>>()?;
            Some(idxs)
        }
        None => None,
    };

    Ok(PtNet { places, transitions, initial, bound, bounds, conserved })
}

/// Parse a marking / pre / post: `"free:1,csA:2"` → counts aligned to `places`.
/// The empty string is the zero marking (used for pure-loss `post`).
fn parse_marking(
    s: &str,
    places: &[String],
    index: &impl Fn(&str) -> Option<usize>,
) -> Result<Vec<u32>, String> {
    let mut m = vec![0u32; places.len()];
    for piece in s.split(',') {
        let p = piece.trim();
        if p.is_empty() {
            continue;
        }
        let (place, count) = p
            .split_once(':')
            .ok_or_else(|| format!("marking entry `{p}` must be `place:count`"))?;
        let i = index(place.trim()).ok_or_else(|| format!("marking: place `{place}` not declared"))?;
        m[i] = count.trim().parse().map_err(|_| format!("marking: bad count in `{p}`"))?;
    }
    Ok(m)
}

fn field(t: &HashMap<String, toml::Value>, key: &str, i: usize) -> Result<String, String> {
    Ok(t.get(key)
        .ok_or_else(|| format!("[[transition/forbid]] {i}: missing `{key}`"))?
        .as_str(key)?
        .to_string())
}
