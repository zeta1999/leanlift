//! Behaviour trees (PLAN-models §3) — compiled to an `Lts` so the Phase-1 check
//! and Lean export apply **unchanged** (the reuse payoff, §3.3). A BT here is a
//! reactive tree over a finite boolean **blackboard**:
//!
//!   * `cond:v` / `cond:!v` — a Condition: Success iff `v` is (not) set.
//!   * `act:name` — an Action with a guard (precondition) and an effect (a set
//!     of blackboard literals to establish). Ticking it returns:
//!       - Success  if the effect already holds (nothing to do),
//!       - Running  if the guard holds — it applies the effect this tick,
//!       - Failure  otherwise.
//!   * `seq(…)` (Sequence) and `fallback(…)` (Selector): the standard reactive
//!     semantics — the first child that returns Running halts the tick (that
//!     action executed), a Sequence fails on the first Failure, a Fallback
//!     succeeds on the first Success.
//!
//! One tick from a blackboard yields at most one executing action ⇒ one LTS
//! transition (labelled by the action). The state space is the reachable
//! blackboard valuations; a tick that returns Success/Failure with no action is
//! a terminal (quiescent) state. Decorators and Parallel are deferred (§3, the
//! reactive seq/fallback core covers the worked example).

use super::ir::Lts;
use super::toml::{self, Doc};
use std::collections::{HashMap, VecDeque};

/// A blackboard literal: variable index and the truth value required/established.
type Lit = (usize, bool);

enum Node {
    Seq(Vec<Node>),
    Fallback(Vec<Node>),
    Cond { var: usize, want: bool },
    Action(usize),
}

struct ActionDef {
    name: String,
    guard: Vec<Lit>,
    effect: Vec<Lit>,
}

enum Tick {
    Success,
    Failure,
    Running { action: String, next: Vec<bool> },
}

/// Compile a `*.model.toml` behaviour tree into a flat `Lts` (family `bt`).
pub fn compile(doc: &Doc) -> Result<Lts, String> {
    let vars: Vec<String> = doc
        .scalar("vars")
        .ok_or("BT requires a `vars` array (the boolean blackboard)")?
        .as_arr("vars")?
        .to_vec();
    if vars.is_empty() {
        return Err("BT `vars` is empty".into());
    }
    let index = |v: &str| vars.iter().position(|x| x == v);

    // Actions.
    let mut actions: Vec<ActionDef> = Vec::new();
    for (i, a) in doc.table("action").iter().enumerate() {
        let name = a
            .get("name")
            .ok_or_else(|| format!("action {i}: missing `name`"))?
            .as_str("name")?
            .to_string();
        let guard = parse_lits(a.get("guard").map(|v| v.as_str("guard")).transpose()?.unwrap_or(""), &index)?;
        let effect = parse_lits(a.get("effect").map(|v| v.as_str("effect")).transpose()?.unwrap_or(""), &index)?;
        actions.push(ActionDef { name, guard, effect });
    }
    let action_idx = |name: &str| actions.iter().position(|a| a.name == name);

    // Tree.
    let tree_src = doc.scalar("tree").ok_or("BT requires a `tree`")?.as_str("tree")?;
    let root = parse_tree(tree_src, &index, &action_idx)?;

    // Initial blackboard: the listed vars are true, the rest false.
    let mut init = vec![false; vars.len()];
    if let Some(v) = doc.scalar("initial") {
        for name in v.as_arr("initial")? {
            let i = index(name).ok_or_else(|| format!("initial: var `{name}` not declared"))?;
            init[i] = true;
        }
    }

    // Forbidden valuations: each `[[forbid]]` is a conjunction of literals
    // (`true = [...]`, `false = [...]`); a state matching any clause is unsafe.
    let mut forbid_clauses: Vec<Vec<Lit>> = Vec::new();
    for (i, f) in doc.table("forbid").iter().enumerate() {
        let mut lits = Vec::new();
        for (key, want) in [("true", true), ("false", false)] {
            if let Some(v) = f.get(key) {
                for name in v.as_arr(key)? {
                    let vi = index(name).ok_or_else(|| format!("forbid {i}: var `{name}` not declared"))?;
                    lits.push((vi, want));
                }
            }
        }
        if lits.is_empty() {
            return Err(format!("forbid {i}: needs a `true` and/or `false` literal list"));
        }
        forbid_clauses.push(lits);
    }

    // BFS the blackboard reachability, building the LTS as we go.
    let name_of = |bb: &[bool]| -> String {
        let on: Vec<&str> = vars.iter().zip(bb).filter(|(_, &b)| b).map(|(v, _)| v.as_str()).collect();
        if on.is_empty() { "none".to_string() } else { on.join("_") }
    };
    let forbidden = |bb: &[bool]| forbid_clauses.iter().any(|c| c.iter().all(|&(v, w)| bb[v] == w));

    let mut states: Vec<String> = Vec::new();
    let mut alphabet: Vec<String> = Vec::new();
    let mut transitions: HashMap<(String, String), String> = HashMap::new();
    let mut forbid: Vec<String> = Vec::new();
    let mut seen: HashMap<Vec<bool>, String> = HashMap::new();
    let mut queue: VecDeque<Vec<bool>> = VecDeque::new();

    seen.insert(init.clone(), name_of(&init));
    states.push(name_of(&init));
    if forbidden(&init) {
        forbid.push(name_of(&init));
    }
    queue.push_back(init.clone());

    while let Some(bb) = queue.pop_front() {
        if let Tick::Running { action, next } = tick(&root, &bb, &actions) {
            let from = name_of(&bb);
            let to = name_of(&next);
            if !alphabet.contains(&action) {
                alphabet.push(action.clone());
            }
            transitions.insert((from, action), to.clone());
            if !seen.contains_key(&next) {
                seen.insert(next.clone(), to.clone());
                states.push(to.clone());
                if forbidden(&next) {
                    forbid.push(to);
                }
                queue.push_back(next);
            }
        }
        // Success/Failure ⇒ quiescent (terminal) state, no outgoing edge.
    }

    Ok(Lts { family: "bt", states, alphabet, initial: name_of(&init), transitions, forbid })
}

/// Tick a node against blackboard `bb`. Returns Running (with the executing
/// action and the new blackboard) the moment an action fires.
fn tick(node: &Node, bb: &[bool], actions: &[ActionDef]) -> Tick {
    match node {
        Node::Cond { var, want } => {
            if bb[*var] == *want {
                Tick::Success
            } else {
                Tick::Failure
            }
        }
        Node::Action(i) => {
            let a = &actions[*i];
            if a.effect.iter().all(|&(v, w)| bb[v] == w) {
                Tick::Success // effect already established
            } else if a.guard.iter().all(|&(v, w)| bb[v] == w) {
                let mut next = bb.to_vec();
                for &(v, w) in &a.effect {
                    next[v] = w;
                }
                Tick::Running { action: a.name.clone(), next }
            } else {
                Tick::Failure
            }
        }
        Node::Seq(children) => {
            for c in children {
                match tick(c, bb, actions) {
                    Tick::Failure => return Tick::Failure,
                    r @ Tick::Running { .. } => return r,
                    Tick::Success => {}
                }
            }
            Tick::Success
        }
        Node::Fallback(children) => {
            for c in children {
                match tick(c, bb, actions) {
                    Tick::Success => return Tick::Success,
                    r @ Tick::Running { .. } => return r,
                    Tick::Failure => {}
                }
            }
            Tick::Failure
        }
    }
}

// --- the tiny tree DSL parser ------------------------------------------------ //

fn parse_tree(
    src: &str,
    index: &impl Fn(&str) -> Option<usize>,
    action_idx: &impl Fn(&str) -> Option<usize>,
) -> Result<Node, String> {
    let toks = tokenize(src);
    let mut pos = 0;
    let node = parse_node(&toks, &mut pos, index, action_idx)?;
    if pos != toks.len() {
        return Err(format!("tree: unexpected trailing tokens near `{}`", toks[pos]));
    }
    Ok(node)
}

fn tokenize(src: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut cur = String::new();
    for c in src.chars() {
        if "(),:!".contains(c) {
            if !cur.trim().is_empty() {
                toks.push(cur.trim().to_string());
            }
            cur.clear();
            toks.push(c.to_string());
        } else if c.is_whitespace() {
            if !cur.trim().is_empty() {
                toks.push(cur.trim().to_string());
            }
            cur.clear();
        } else {
            cur.push(c);
        }
    }
    if !cur.trim().is_empty() {
        toks.push(cur.trim().to_string());
    }
    toks
}

fn parse_node(
    toks: &[String],
    pos: &mut usize,
    index: &impl Fn(&str) -> Option<usize>,
    action_idx: &impl Fn(&str) -> Option<usize>,
) -> Result<Node, String> {
    let head = toks.get(*pos).ok_or("tree: unexpected end")?.clone();
    *pos += 1;
    match head.as_str() {
        "seq" | "sequence" => Ok(Node::Seq(parse_children(toks, pos, index, action_idx)?)),
        "fallback" | "fb" | "sel" | "selector" => {
            Ok(Node::Fallback(parse_children(toks, pos, index, action_idx)?))
        }
        "cond" | "condition" => {
            expect(toks, pos, ":")?;
            let mut want = true;
            if toks.get(*pos).map(|s| s.as_str()) == Some("!") {
                want = false;
                *pos += 1;
            }
            let name = toks.get(*pos).ok_or("cond: expected a variable")?.clone();
            *pos += 1;
            let var = index(&name).ok_or_else(|| format!("cond: var `{name}` not declared"))?;
            Ok(Node::Cond { var, want })
        }
        "act" | "action" => {
            expect(toks, pos, ":")?;
            let name = toks.get(*pos).ok_or("act: expected a name")?.clone();
            *pos += 1;
            let i = action_idx(&name).ok_or_else(|| format!("act: no [[action]] named `{name}`"))?;
            Ok(Node::Action(i))
        }
        other => Err(format!("tree: expected a node, found `{other}`")),
    }
}

fn parse_children(
    toks: &[String],
    pos: &mut usize,
    index: &impl Fn(&str) -> Option<usize>,
    action_idx: &impl Fn(&str) -> Option<usize>,
) -> Result<Vec<Node>, String> {
    expect(toks, pos, "(")?;
    let mut children = Vec::new();
    loop {
        children.push(parse_node(toks, pos, index, action_idx)?);
        match toks.get(*pos).map(|s| s.as_str()) {
            Some(",") => {
                *pos += 1;
            }
            Some(")") => {
                *pos += 1;
                break;
            }
            _ => return Err("tree: expected `,` or `)`".into()),
        }
    }
    if children.is_empty() {
        return Err("tree: empty child list".into());
    }
    Ok(children)
}

fn expect(toks: &[String], pos: &mut usize, want: &str) -> Result<(), String> {
    if toks.get(*pos).map(|s| s.as_str()) == Some(want) {
        *pos += 1;
        Ok(())
    } else {
        Err(format!("tree: expected `{want}`"))
    }
}

/// Parse a literal list: `"atGoal=false, lost=true"` or `"lost, !atGoal"`.
fn parse_lits(s: &str, index: &impl Fn(&str) -> Option<usize>) -> Result<Vec<Lit>, String> {
    let mut out = Vec::new();
    for piece in s.split(',') {
        let p = piece.trim();
        if p.is_empty() {
            continue;
        }
        let (name, want) = if let Some(rest) = p.strip_prefix('!') {
            (rest.trim(), false)
        } else if let Some((n, v)) = p.split_once('=') {
            let want = match v.trim() {
                "true" | "1" => true,
                "false" | "0" => false,
                other => return Err(format!("literal `{p}`: value must be true/false, found `{other}`")),
            };
            (n.trim(), want)
        } else {
            (p, true)
        };
        let i = index(name).ok_or_else(|| format!("literal `{p}`: var `{name}` not declared"))?;
        out.push((i, want));
    }
    Ok(out)
}

/// Convenience for the CLI: parse a BT source string straight to its `Lts`.
pub fn parse_bt(src: &str) -> Result<Lts, String> {
    let doc = toml::parse(src)?;
    compile(&doc)
}
