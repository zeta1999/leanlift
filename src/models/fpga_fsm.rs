//! FPGA control-FSM extraction (PLAN-fpga Phase F, slice ②).
//!
//! Project an Aria-HDL control FSM — a single state `Register` whose `next` is a
//! priority `Mux`/`CaseMux` tree over input guards — onto leanlift's `Lts`, so
//! the existing `check.rs` (reachability / dead-state / deadlock / safety) and
//! `lean.rs::emit_fsm` (sorry-free Lean) ride unchanged.
//!
//! The projection is **mechanical, total, and exact**: a small interpreter
//! evaluates the `next` expression tree for every (current state, input
//! valuation), so the transition relation is the hardware's, not an abstraction.
//! Input valuations that induce the *same* whole-state transition are merged into
//! one `Event` (behavioural dedup) to keep the alphabet — and the Lean case split
//! — small. The safety property comes from the IR's own `assert always P` formal
//! properties: a reachable state where `P` is false is `forbid`-den. Everything
//! that cannot be evaluated purely on the state (guards referencing inputs, ops
//! we do not model) is REFUSED, never silently mis-evaluated — fail-closed.

use super::fpga::Json;
use super::ir::Lts;
use std::collections::{HashMap, HashSet};

/// Cap on the input-bit fan-out for exhaustive valuation (2^k). A control FSM has
/// a handful of guard inputs; past this we refuse rather than blow up.
const MAX_INPUT_BITS: u32 = 16;
/// Cap on the reachable state-value set (guards a non-terminating arithmetic
/// `next`, e.g. a free-running counter mis-detected as a control FSM).
const MAX_STATES: usize = 4096;

pub struct FsmExtract {
    pub lts: Lts,
    pub reg_name: String,
    pub reg_width: u32,
    /// State VALUES, parallel to the `q{idx}` names in `lts.states`.
    pub state_values: Vec<i64>,
    /// Input port names used as guard bits, in id order.
    pub inputs: Vec<String>,
    /// Formal `assert always P` properties that were usable as state safety.
    pub safety_used: usize,
    /// Properties skipped because they reference inputs / aren't state-only.
    pub safety_skipped: usize,
    /// The forbidden state VALUES (those a usable property rules out).
    pub forbidden_values: Vec<i64>,
    /// Reset (initial) state value — the Moore machine's start state.
    pub reset: i64,
    /// Guard-input names in `moore_step` valuation-bit order (bit `i` ⇔ this name).
    pub moore_inputs: Vec<String>,
    /// The full Moore step table: `(state value, valuation index over moore_inputs)
    /// → next state value`. The observable output of a state IS its value.
    pub moore_step: HashMap<(i64, u64), i64>,
}

/// What a value-id resolves to during evaluation.
struct Resolver<'a> {
    state_id: u64,
    inputs: HashSet<u64>,
    wires: HashMap<u64, &'a Json>, // value-id → defining expression
}

struct Env<'a> {
    state: i64,
    assign: &'a HashMap<u64, i64>,
}

/// Extract the control FSM from one IR-JSON module object. `Ok(None)` means "no
/// single-register control FSM here" (not an error — e.g. a pure datapath).
pub fn extract_fsm(module: &Json) -> Result<Option<FsmExtract>, String> {
    let nodes = module.get("nodes").and_then(Json::as_arr).ok_or("module: missing `nodes`")?;

    // Collect registers and wires by their value-id (== node `id`).
    let mut regs: Vec<(&Json, u64, String)> = Vec::new();
    let mut wires: HashMap<u64, &Json> = HashMap::new();
    for n in nodes {
        let id = n.get("id").and_then(Json::as_u64).ok_or("node: missing `id`")?;
        let kind = n.get("kind").ok_or("node: missing `kind`")?;
        match kind.str_field("k") {
            Some("register") => {
                let name = n.str_field("name").unwrap_or("state").to_string();
                regs.push((kind, id, name));
            }
            Some("wire") => {
                if let Some(expr) = kind.get("expr") {
                    wires.insert(id, expr);
                }
            }
            _ => {}
        }
    }
    // A single-register module is the control-FSM shape F handles. Zero registers
    // (pure datapath) or several (a multi-register datapath/cache) are simply "not
    // a control FSM" — SKIP, don't fail. Errors below are reserved for a recognized
    // single-register FSM we cannot soundly project (fail-closed).
    if regs.len() != 1 {
        return Ok(None);
    }
    let (reg_kind, state_id, reg_name) = (regs[0].0, regs[0].1, regs[0].2.clone());

    // Register width (uint<n>) — the next value is masked to it (hardware wrap).
    let reg_width = reg_kind
        .get("ty")
        .and_then(|t| t.get("n"))
        .and_then(Json::as_u64)
        .unwrap_or(0) as u32;
    if reg_width == 0 || reg_width > 63 {
        return Err(format!("register `{reg_name}`: unsupported width {reg_width} (need 1..=63-bit)"));
    }
    let mask: i64 = if reg_width >= 63 { i64::MAX } else { (1i64 << reg_width) - 1 };

    let next = reg_kind.get("next").ok_or_else(|| format!("register `{reg_name}`: missing `next`"))?;
    let reset_expr = reg_kind.get("reset_value");

    // Input ports (by value-id) and their bit-ness.
    let ports = module.get("ports").and_then(Json::as_arr).ok_or("module: missing `ports`")?;
    let mut input_ids: HashMap<u64, String> = HashMap::new();
    let mut input_is_bit: HashMap<u64, bool> = HashMap::new();
    for p in ports {
        if p.str_field("dir") == Some("input") {
            if let Some(vid) = p.get("value").and_then(Json::as_u64) {
                let nm = p.str_field("name").unwrap_or("in").to_string();
                let is_bit = p.get("ty").and_then(|t| t.str_field("t")) == Some("bit");
                input_ids.insert(vid, nm);
                input_is_bit.insert(vid, is_bit);
            }
        }
    }

    // Which inputs actually appear in `next` (the guard bits we enumerate).
    let mut used_inputs: HashSet<u64> = HashSet::new();
    collect_input_refs(next, &input_ids, &mut used_inputs);
    // Refuse non-bit guard inputs: enumerating only {0,1} would be unsound.
    for id in &used_inputs {
        if input_is_bit.get(id) != Some(&true) {
            return Err(format!(
                "FSM guard references non-bit input `{}` — exhaustive valuation would be unsound",
                input_ids.get(id).cloned().unwrap_or_default()
            ));
        }
    }
    let mut guard_inputs: Vec<u64> = used_inputs.iter().copied().collect();
    guard_inputs.sort_unstable();
    let k = guard_inputs.len() as u32;
    if k > MAX_INPUT_BITS {
        return Err(format!("FSM has {k} guard input bits (> {MAX_INPUT_BITS}); refuse exhaustive 2^k valuation"));
    }

    let resolver = Resolver { state_id, inputs: used_inputs.clone(), wires };

    // Reset state value (a literal expr; evaluate with an empty environment).
    let empty: HashMap<u64, i64> = HashMap::new();
    let reset = match reset_expr {
        Some(e) => eval(e, &resolver, &Env { state: 0, assign: &empty })? & mask,
        None => 0,
    };

    // Reachability fixpoint: from reset, fire every input valuation.
    let combos = 1u64 << k;
    let mut state_set: Vec<i64> = vec![reset];
    let mut seen: HashSet<i64> = HashSet::from([reset]);
    let mut idx = 0;
    while idx < state_set.len() {
        let s = state_set[idx];
        idx += 1;
        for a in 0..combos {
            let assign = valuation(a, &guard_inputs);
            let t = eval(next, &resolver, &Env { state: s, assign: &assign })? & mask;
            if seen.insert(t) {
                if state_set.len() >= MAX_STATES {
                    return Err(format!("FSM state set exceeded {MAX_STATES} — not a finite control FSM?"));
                }
                state_set.push(t);
            }
        }
    }
    state_set.sort_unstable();
    let val_to_idx: HashMap<i64, usize> = state_set.iter().enumerate().map(|(i, &v)| (v, i)).collect();
    let name_of = |v: i64| format!("q{}", val_to_idx[&v]);

    // Behavioural dedup of input valuations: two valuations that map EVERY state
    // to the same successor are one Event. Behaviour = the successor vector.
    // The full (state, valuation) → next table is ALSO captured (`moore_step`) for
    // the equivalence engine (Phase E), keyed by the raw valuation index `a` over
    // `guard_inputs` (id order = `moore_inputs`).
    let mut behaviour_to_event: HashMap<Vec<i64>, String> = HashMap::new();
    let mut events: Vec<String> = Vec::new();
    let mut transitions: HashMap<(String, String), String> = HashMap::new();
    let mut moore_step: HashMap<(i64, u64), i64> = HashMap::new();
    for a in 0..combos {
        let assign = valuation(a, &guard_inputs);
        let mut behaviour = Vec::with_capacity(state_set.len());
        for &s in &state_set {
            let t = eval(next, &resolver, &Env { state: s, assign: &assign })? & mask;
            behaviour.push(t);
            moore_step.insert((s, a), t);
        }
        let ev = behaviour_to_event
            .entry(behaviour.clone())
            .or_insert_with(|| {
                let e = format!("ev{}", events.len());
                events.push(e.clone());
                e
            })
            .clone();
        for (i, &s) in state_set.iter().enumerate() {
            transitions.insert((name_of(s), ev.clone()), name_of(behaviour[i]));
        }
    }

    // Safety: forbid reachable states ruled out by a usable `assert always P`.
    let (forbidden_values, safety_used, safety_skipped) =
        derive_forbidden(nodes, &resolver, state_id, &state_set)?;
    let forbid: Vec<String> = forbidden_values.iter().map(|&v| name_of(v)).collect();

    let states: Vec<String> = (0..state_set.len()).map(|i| format!("q{i}")).collect();
    let lts = Lts {
        family: "fsm",
        states,
        alphabet: events,
        initial: name_of(reset),
        transitions,
        forbid,
    };

    // Guard-input names in valuation-bit order (id order) — the key order for
    // `moore_step`'s valuation index.
    let moore_inputs: Vec<String> = guard_inputs.iter().map(|id| input_ids[id].clone()).collect();
    let mut inputs = moore_inputs.clone();
    inputs.sort();
    Ok(Some(FsmExtract {
        lts,
        reg_name,
        reg_width,
        state_values: state_set,
        inputs,
        safety_used,
        safety_skipped,
        forbidden_values,
        reset,
        moore_inputs,
        moore_step,
    }))
}

/// Derive the forbidden state VALUES from `assert always P` (and `never P`)
/// formal properties that reference ONLY the state register. Returns
/// (forbidden values, #usable properties, #skipped properties).
fn derive_forbidden(
    nodes: &[Json],
    resolver: &Resolver,
    state_id: u64,
    state_set: &[i64],
) -> Result<(Vec<i64>, usize, usize), String> {
    let mut forbidden: Vec<i64> = Vec::new();
    let (mut used, mut skipped) = (0usize, 0usize);
    let empty: HashMap<u64, i64> = HashMap::new();
    for n in nodes {
        let kind = match n.get("kind") {
            Some(k) if k.str_field("k") == Some("formal_property") => k,
            _ => continue,
        };
        let prop = match kind.get("property") {
            Some(p) => p,
            None => continue,
        };
        let pkind = prop.str_field("kind").unwrap_or("");
        let temporal = prop.get("temporal").and_then(|t| t.str_field("tt")).unwrap_or("");
        // Only `assert`/`never` with an `always` temporal are state-safety here.
        if !(matches!(pkind, "assert" | "never") && temporal == "always") {
            continue;
        }
        let expr = match prop.get("expr") {
            Some(e) => e,
            None => continue,
        };
        // Usable only if it references ONLY the state register (no inputs/wires).
        if !references_only_state(expr, state_id, resolver) {
            skipped += 1;
            continue;
        }
        // Evaluate P at every state value. A malformed/unsupported property expr is
        // SKIPPED (we prove less) — it must not abort the whole FSM's check.
        let mut local = Vec::new();
        let mut evaluable = true;
        for &v in state_set {
            match eval(expr, resolver, &Env { state: v, assign: &empty }) {
                Ok(p) => {
                    // `assert P` forbids ¬P; `never P` forbids P.
                    let bad = if pkind == "never" { p != 0 } else { p == 0 };
                    if bad {
                        local.push(v);
                    }
                }
                Err(_) => {
                    evaluable = false;
                    break;
                }
            }
        }
        if !evaluable {
            skipped += 1;
            continue;
        }
        used += 1;
        for v in local {
            if !forbidden.contains(&v) {
                forbidden.push(v);
            }
        }
    }
    forbidden.sort_unstable();
    Ok((forbidden, used, skipped))
}

/// True iff `expr` references the state register and NOTHING else that varies
/// (no inputs, no wires) — so it can be evaluated purely on the state value.
fn references_only_state(expr: &Json, state_id: u64, r: &Resolver) -> bool {
    let mut ok = true;
    walk_refs(expr, &mut |id| {
        if id != state_id && (r.inputs.contains(&id) || r.wires.contains_key(&id)) {
            // a wire could be state-only too, but to stay sound we only accept the
            // bare state register here (wires may fan in inputs).
            ok = false;
        } else if id != state_id && !r.wires.contains_key(&id) {
            ok = false; // an unknown ref — refuse
        }
    });
    ok
}

fn collect_input_refs(expr: &Json, inputs: &HashMap<u64, String>, out: &mut HashSet<u64>) {
    walk_refs(expr, &mut |id| {
        if inputs.contains_key(&id) {
            out.insert(id);
        }
    });
}

/// Visit every `ref` value-id in an expression tree.
fn walk_refs(expr: &Json, f: &mut impl FnMut(u64)) {
    match expr {
        Json::Obj(kvs) => {
            if expr.str_field("e") == Some("ref") {
                if let Some(id) = expr.get("value").and_then(Json::as_u64) {
                    f(id);
                }
            }
            for (_, v) in kvs {
                walk_refs(v, f);
            }
        }
        Json::Arr(a) => {
            for v in a {
                walk_refs(v, f);
            }
        }
        _ => {}
    }
}

/// Map a valuation index `a` to the per-input-id bit assignment.
fn valuation(a: u64, guard_inputs: &[u64]) -> HashMap<u64, i64> {
    guard_inputs
        .iter()
        .enumerate()
        .map(|(bit, &id)| (id, ((a >> bit) & 1) as i64))
        .collect()
}

/// Wrap an arithmetic/bitwise result to its IR-declared type width. uint<n> masks
/// to n bits (correct hardware wrap); `bit` to 1 bit. A missing or non-unsigned
/// type (e.g. signed `int`, which would need sign-extension to compare correctly)
/// is REFUSED — fail-closed, never a silent mis-evaluation.
fn mask_arith(e: &Json, raw: i64) -> Result<i64, String> {
    let ty = e.get("ty").ok_or("arithmetic result has no declared type — cannot wrap to width")?;
    match ty.str_field("t") {
        Some("uint") => {
            let n = ty.get("n").and_then(Json::as_u64).ok_or("uint result missing width")?;
            if n == 0 || n > 63 {
                return Err(format!("uint result width {n} out of range (1..=63)"));
            }
            Ok(raw & ((1i64 << n) - 1))
        }
        Some("bit") => Ok(raw & 1),
        Some(other) => Err(format!("arithmetic result type `{other}` not modeled (signed/other) — refuse")),
        None => Err("arithmetic result type tag missing".into()),
    }
}

/// Evaluate an IR expression to an integer (booleans as 0/1). Refuses anything it
/// cannot model exactly (fail-closed): an unknown op or an unresolved ref errors.
fn eval(e: &Json, r: &Resolver, env: &Env) -> Result<i64, String> {
    match e.str_field("e") {
        Some("lit") => {
            let lit = e.get("lit").ok_or("lit: missing payload")?;
            let v = lit.str_field("value").ok_or("lit: missing value")?;
            match v {
                "true" => Ok(1),
                "false" => Ok(0),
                _ => v.parse::<i64>().map_err(|_| format!("lit: non-integer value `{v}`")),
            }
        }
        Some("ref") => {
            let id = e.get("value").and_then(Json::as_u64).ok_or("ref: missing value-id")?;
            if id == r.state_id {
                Ok(env.state)
            } else if r.inputs.contains(&id) {
                Ok(*env.assign.get(&id).unwrap_or(&0))
            } else if let Some(w) = r.wires.get(&id) {
                eval(w, r, env)
            } else {
                Err(format!("ref: unresolved value-id {id}"))
            }
        }
        Some("mux") => {
            let c = eval(e.get("cond").ok_or("mux: missing cond")?, r, env)?;
            let branch = if c != 0 { "true" } else { "false" };
            eval(e.get(branch).ok_or("mux: missing branch")?, r, env)
        }
        Some("binop") => {
            let l = eval(e.get("lhs").ok_or("binop: missing lhs")?, r, env)?;
            let rr = eval(e.get("rhs").ok_or("binop: missing rhs")?, r, env)?;
            let op = e.str_field("op").ok_or("binop: missing op")?;
            // Comparisons / logic yield a clean 0/1 boolean (no width to mask).
            // Arithmetic / bitwise must wrap to the result's DECLARED uint width —
            // computing them in raw i64 would let a wrapped subtraction (e.g.
            // `2 - 5` in uint<3> = 5, not -3) flip a downstream comparison and hide
            // a reachable illegal state. `mask_arith` refuses any untyped/signed
            // result (fail-closed) rather than mis-evaluate.
            Ok(match op {
                "eq" => (l == rr) as i64,
                "ne" => (l != rr) as i64,
                "lt" => (l < rr) as i64,
                "le" => (l <= rr) as i64,
                "gt" => (l > rr) as i64,
                "ge" => (l >= rr) as i64,
                "logic_and" => ((l != 0) && (rr != 0)) as i64,
                "logic_or" => ((l != 0) || (rr != 0)) as i64,
                "add" => mask_arith(e, l.wrapping_add(rr))?,
                "sub" => mask_arith(e, l.wrapping_sub(rr))?,
                "mul" => mask_arith(e, l.wrapping_mul(rr))?,
                "and" => mask_arith(e, l & rr)?,
                "or" => mask_arith(e, l | rr)?,
                "xor" => mask_arith(e, l ^ rr)?,
                "shl" => mask_arith(e, l.wrapping_shl(rr as u32))?,
                "shr" => mask_arith(e, l.wrapping_shr(rr as u32))?,
                other => return Err(format!("binop: unsupported op `{other}`")),
            })
        }
        Some("unop") => {
            let v = eval(
                e.get("operand").or_else(|| e.get("value")).ok_or("unop: missing operand")?,
                r,
                env,
            )?;
            let op = e.str_field("op").ok_or("unop: missing op")?;
            Ok(match op {
                "logic_not" | "not" => (v == 0) as i64,
                "bitnot" => mask_arith(e, !v)?,
                "neg" => mask_arith(e, v.wrapping_neg())?,
                other => return Err(format!("unop: unsupported op `{other}`")),
            })
        }
        Some("cast") | Some("resize") => {
            eval(e.get("value").or_else(|| e.get("expr")).ok_or("cast: missing inner")?, r, env)
        }
        Some(other) => Err(format!("unsupported expression `{other}` in FSM")),
        None => Err("expression: missing `e` tag".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{check, fpga::parse_stream};

    /// A single-register FSM: `state := go ? <hi> : 0`, width 2, with
    /// `assert always state <= 1`. With hi=1 it is safe; hi=3 reaches an illegal
    /// state. `gtype` is the guard input's type (`bit` unless overriding).
    fn fsm(hi: u32, gtype: &str) -> String {
        format!(
            r#"{{"schema":"aria-ir-json/v1","id":0,"name":"toggle",
              "ports":[{{"id":0,"value":10,"name":"go","ty":{{"t":"{gtype}"}},"dir":"input","clock_domain":0}}],
              "clock_domains":[],"annotations":[],
              "nodes":[
                {{"id":1,"name":"state","kind":{{"k":"register","ty":{{"t":"uint","n":2}},"clock_domain":0,
                  "reset_value":{{"e":"lit","lit":{{"l":"uint","value":"0","width":2}}}},"enable":null,
                  "next":{{"e":"mux","cond":{{"e":"ref","value":10}},
                    "true":{{"e":"lit","lit":{{"l":"uint","value":"{hi}","width":2}}}},
                    "false":{{"e":"lit","lit":{{"l":"uint","value":"0","width":2}}}}}}}}}},
                {{"id":2,"name":"p","kind":{{"k":"formal_property","property":{{"kind":"assert","temporal":{{"tt":"always"}},
                  "expr":{{"e":"binop","op":"le","lhs":{{"e":"ref","value":1}},"rhs":{{"e":"lit","lit":{{"l":"uint","value":"1","width":32}}}},"ty":{{"t":"bit"}}}},"name":"safe"}}}}}}
              ],
              "timing":{{}}}}"#
        )
    }

    fn extract(src: &str) -> Option<FsmExtract> {
        let m = &parse_stream(src).unwrap()[0];
        extract_fsm(m).unwrap()
    }

    #[test]
    fn safe_fsm_has_no_forbidden_and_check_passes() {
        let f = extract(&fsm(1, "bit")).unwrap();
        assert_eq!(f.state_values, vec![0, 1]);
        assert!(f.forbidden_values.is_empty());
        assert_eq!(f.safety_used, 1);
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(r.safe());
        assert!(r.violations.is_empty());
    }

    #[test]
    fn illegal_state_is_forbidden_and_check_catches_it() {
        // teeth: `state := go ? 3 : 0` reaches 3, which violates `state <= 1`.
        let f = extract(&fsm(3, "bit")).unwrap();
        assert!(f.state_values.contains(&3));
        assert_eq!(f.forbidden_values, vec![3], "state 3 must be forbidden by `state<=1`");
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(!r.safe(), "a reachable illegal state must fail the M1 check");
        assert!(r.violations.iter().any(|(s, _)| f.lts.forbid.contains(s)));
    }

    #[test]
    fn non_bit_guard_input_is_refused_fail_closed() {
        // A guard over a non-bit input cannot be exhaustively (0/1) enumerated.
        let m = &parse_stream(&fsm(1, "uint")).unwrap()[0];
        assert!(extract_fsm(m).is_err());
    }

    #[test]
    fn non_fsm_module_is_skipped_not_failed() {
        // Zero registers ⇒ not a control FSM ⇒ Ok(None) (skip), not an error.
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"comb","ports":[],"clock_domains":[],
          "annotations":[],"nodes":[{"id":1,"name":"w","kind":{"k":"wire","ty":{"t":"bit"},"expr":{"e":"lit","lit":{"l":"uint","value":"1","width":1}}}}],"timing":{}}"#;
        assert!(extract(src).is_none());
    }

    #[test]
    fn uint_wrap_arithmetic_into_comparison_is_caught() {
        // teeth for CRITICAL-1: register uint<3>, reset=2,
        //   next = mux((state - 5) > 0, then 7, else 0),  assert always state <= 5.
        // In uint<3>, 2-5 wraps to 5; 5>0 ⇒ next=7 (reachable, ILLEGAL). A signed
        // i64 eval would compute 2-5=-3, -3>0 false ⇒ never reach 7 ⇒ false SAFE.
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"wrap",
          "ports":[],"clock_domains":[],"annotations":[],
          "nodes":[
            {"id":1,"name":"state","kind":{"k":"register","ty":{"t":"uint","n":3},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"uint","value":"2","width":3}},"enable":null,
              "next":{"e":"mux",
                "cond":{"e":"binop","op":"gt","ty":{"t":"bit"},
                  "lhs":{"e":"binop","op":"sub","ty":{"t":"uint","n":3},
                    "lhs":{"e":"ref","value":1},"rhs":{"e":"lit","lit":{"l":"uint","value":"5","width":3}}},
                  "rhs":{"e":"lit","lit":{"l":"uint","value":"0","width":3}}},
                "true":{"e":"lit","lit":{"l":"uint","value":"7","width":3}},
                "false":{"e":"lit","lit":{"l":"uint","value":"0","width":3}}}}},
            {"id":2,"name":"p","kind":{"k":"formal_property","property":{"kind":"assert","temporal":{"tt":"always"},
              "expr":{"e":"binop","op":"le","ty":{"t":"bit"},"lhs":{"e":"ref","value":1},"rhs":{"e":"lit","lit":{"l":"uint","value":"5","width":32}}},"name":"safe"}}}
          ],"timing":{}}"#;
        let f = extract(src).unwrap();
        assert!(f.state_values.contains(&7), "uint wrap must make state 7 reachable");
        assert_eq!(f.forbidden_values, vec![7]);
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(!r.safe(), "the wrapped-arithmetic illegal state must FAIL the check");
    }

    #[test]
    fn untyped_arithmetic_is_refused_fail_closed() {
        // An arithmetic result with no declared type cannot be wrapped to a width.
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"notype",
          "ports":[],"clock_domains":[],"annotations":[],
          "nodes":[{"id":1,"name":"state","kind":{"k":"register","ty":{"t":"uint","n":3},"clock_domain":0,
            "reset_value":{"e":"lit","lit":{"l":"uint","value":"0","width":3}},"enable":null,
            "next":{"e":"binop","op":"add","lhs":{"e":"ref","value":1},"rhs":{"e":"lit","lit":{"l":"uint","value":"1","width":3}}}}}],
          "timing":{}}"#;
        let m = &parse_stream(src).unwrap()[0];
        assert!(extract_fsm(m).is_err(), "untyped arithmetic must be refused, not guessed");
    }

    #[test]
    fn malformed_state_property_is_skipped_not_fatal() {
        // A state-only property with a missing rhs must be skipped; the FSM (and
        // any valid properties) still check. Here the only property is malformed,
        // so the FSM extracts with zero usable safety properties.
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"toggle",
          "ports":[{"id":0,"value":10,"name":"go","ty":{"t":"bit"},"dir":"input","clock_domain":0}],
          "clock_domains":[],"annotations":[],
          "nodes":[
            {"id":1,"name":"state","kind":{"k":"register","ty":{"t":"uint","n":2},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"uint","value":"0","width":2}},"enable":null,
              "next":{"e":"mux","cond":{"e":"ref","value":10},
                "true":{"e":"lit","lit":{"l":"uint","value":"1","width":2}},
                "false":{"e":"lit","lit":{"l":"uint","value":"0","width":2}}}}},
            {"id":2,"name":"bad","kind":{"k":"formal_property","property":{"kind":"assert","temporal":{"tt":"always"},
              "expr":{"e":"binop","op":"le","ty":{"t":"bit"},"lhs":{"e":"ref","value":1}},"name":"oops"}}}
          ],"timing":{}}"#;
        let f = extract(src).unwrap();
        assert_eq!(f.safety_used, 0);
        assert!(f.safety_skipped >= 1);
        assert!(f.forbidden_values.is_empty());
        let r = check::check(&f.lts, check::DEFAULT_BOUND); // still checkable
        assert!(r.safe());
    }

    #[test]
    fn emits_well_formed_lean_for_extracted_fsm() {
        // F2: the extracted Lts feeds lean::emit_fsm unchanged — check the proof
        // skeleton is present (full elaboration is the Lean-gated CI step).
        use crate::models::lean;
        let f = extract(&fsm(1, "bit")).unwrap();
        let src = lean::emit_fsm(&f.lts, "Fpga_toggle");
        assert!(src.contains("namespace Fpga_toggle"));
        assert!(src.contains("inductive State"));
        assert!(src.contains("theorem safety"));
        assert!(src.contains("#print axioms Fpga_toggle.safety"));
    }

    #[test]
    fn real_tcp_fsm_extracts_and_dedups_events() {
        let src = std::fs::read_to_string("examples/fpga/tcp_ip.aria.json").unwrap();
        let m = parse_stream(&src).unwrap();
        let tcp = m.iter().find(|x| x.str_field("name") == Some("tcp_fsm")).unwrap();
        let f = extract_fsm(tcp).unwrap().unwrap();
        assert_eq!(f.state_values.len(), 7); // CLOSED + 6 reachable
        assert_eq!(f.inputs.len(), 6);
        assert!(f.lts.alphabet.len() < 64, "behavioural dedup must shrink 2^6 valuations");
        assert_eq!(f.safety_used, 1); // state<=10
        assert!(f.safety_skipped >= 1); // the rst_in-referencing property
        assert!(f.forbidden_values.is_empty()); // never exceeds 10
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(r.safe());
    }
}
