//! FPGA control-FSM extraction (PLAN-fpga Phase F, slice ② + F3).
//!
//! Project an Aria-HDL control FSM onto leanlift's `Lts`, so the existing
//! `check.rs` (reachability / dead-state / deadlock / safety) and
//! `lean.rs::emit_fsm` (sorry-free Lean) ride unchanged.
//!
//! The FSM state is the **tuple of every state `Register`** in the module —
//! one register is the common control-FSM shape; several registers form a
//! *product* (composite) machine. The composite state is encoded as a single
//! bit-packed `i64`: register `i` occupies `[offset_i, offset_i+width_i)`, with
//! offsets the running sum of widths. With one register the offset is 0, so the
//! packed value IS the register value — a strict generalization that leaves the
//! single-register behaviour (and every downstream consumer keyed on the packed
//! `i64`: `moore_step`, `state_values`, `forbidden_values`, the equivalence
//! product, the Lean emit) bit-for-bit identical.
//!
//! The projection is **mechanical, total, and exact**: a small interpreter
//! evaluates each register's `next` expression tree for every (composite state,
//! input valuation), so the joint transition relation is the hardware's, not an
//! abstraction. A `ref` to register `j` reads its slice out of the packed state.
//! Input valuations that induce the *same* whole-state transition are merged into
//! one `Event` (behavioural dedup) to keep the alphabet — and the Lean case split
//! — small. The safety property comes from the IR's own `assert always P` formal
//! properties: a reachable state where `P` is false is `forbid`-den; a property
//! may reference any subset of the registers. Everything that cannot be evaluated
//! purely on the registers (guards referencing inputs, ops we do not model) is
//! REFUSED, never silently mis-evaluated — fail-closed.

use super::fpga::Json;
use super::ir::Lts;
use std::collections::{HashMap, HashSet};

/// Cap on the input-bit fan-out for exhaustive valuation (2^k). A control FSM has
/// a handful of guard inputs; past this we refuse rather than blow up.
const MAX_INPUT_BITS: u32 = 16;
/// Cap on the reachable state-value set (guards a non-terminating arithmetic
/// `next`, e.g. a free-running counter mis-detected as a control FSM).
const MAX_STATES: usize = 4096;
/// Cap on the total composite width. The packed state must fit in a positive
/// `i64`; we also refuse pathologically wide products (a datapath, not a control
/// FSM). 63 bits keeps the top bit clear so the packed value is never negative.
const MAX_COMPOSITE_BITS: u32 = 63;
/// Recursion-depth cap for expression evaluation. A real expression tree is
/// shallow; this only ever trips on a (malformed) combinational wire cycle
/// (`w1 := w2`, `w2 := w1`), which we then REFUSE rather than overflow the stack.
const MAX_EVAL_DEPTH: u32 = 1024;

/// One register's extraction metadata, gathered once and reused for reset, the
/// joint transition, and reachability.
struct RegMeta<'a> {
    width: u32,
    offset: u32,
    next: &'a Json,
    reset: Option<&'a Json>,
    /// `enable` gate, if non-null. The register updates to `next` only when this
    /// is true, otherwise it HOLDS its current value. `None` ⇒ always enabled.
    enable: Option<&'a Json>,
}

/// One register composing the (possibly product) state, in packing order.
pub struct RegInfo {
    /// Register name (for diagnostics).
    pub name: String,
    /// Declared `uint<width>` width; the register's `next` is masked to it.
    pub width: u32,
    /// Bit offset of this register's slice within the packed composite value.
    pub offset: u32,
}

pub struct FsmExtract {
    pub lts: Lts,
    /// Registers composing the state, in packing (value-id) order. One entry is
    /// the classic single control FSM; several form a product machine.
    pub regs: Vec<RegInfo>,
    /// State VALUES (bit-packed composites), parallel to the `q{idx}` names in
    /// `lts.states`.
    pub state_values: Vec<i64>,
    /// Input port names used as guard bits, in id order.
    pub inputs: Vec<String>,
    /// Formal `assert always P` properties that were usable as state safety.
    pub safety_used: usize,
    /// Properties skipped because they reference inputs / aren't state-only.
    pub safety_skipped: usize,
    /// The forbidden state VALUES (those a usable property rules out).
    pub forbidden_values: Vec<i64>,
    /// Reset (initial) composite state value — the Moore machine's start state.
    pub reset: i64,
    /// Guard-input names in `moore_step` valuation-bit order (bit `i` ⇔ this name).
    pub moore_inputs: Vec<String>,
    /// The full Moore step table: `(state value, valuation index over moore_inputs)
    /// → next state value`. The observable output of a state IS its value.
    pub moore_step: HashMap<(i64, u64), i64>,
}

impl FsmExtract {
    /// One-line description of the state register(s) for `info`/diagnostics.
    pub fn reg_desc(&self) -> String {
        if self.regs.len() == 1 {
            format!("register `{}` (uint<{}>)", self.regs[0].name, self.regs[0].width)
        } else {
            let parts: Vec<String> = self
                .regs
                .iter()
                .map(|r| format!("`{}`:uint<{}>@[{}..{})", r.name, r.width, r.offset, r.offset + r.width))
                .collect();
            let total: u32 = self.regs.iter().map(|r| r.width).sum();
            format!("product of {} registers [{}] ({}-bit composite)", self.regs.len(), parts.join(", "), total)
        }
    }
}

/// What a value-id resolves to during evaluation.
struct Resolver<'a> {
    /// Register value-id → (width, packing offset). A `ref` to one reads its
    /// slice out of the packed composite state.
    regs: HashMap<u64, (u32, u32)>,
    inputs: HashSet<u64>,
    wires: HashMap<u64, &'a Json>, // value-id → defining expression
}

struct Env<'a> {
    /// Bit-packed composite state value.
    packed: i64,
    assign: &'a HashMap<u64, i64>,
}

/// Mask for a `uint<width>` value (low `width` bits).
fn width_mask(width: u32) -> i64 {
    if width >= 63 { i64::MAX } else { (1i64 << width) - 1 }
}

/// Extract the control FSM from one IR-JSON module object. `Ok(None)` means "no
/// control FSM here" (not an error — a pure datapath with zero state registers).
pub fn extract_fsm(module: &Json) -> Result<Option<FsmExtract>, String> {
    let nodes = module.get("nodes").and_then(Json::as_arr).ok_or("module: missing `nodes`")?;

    // Collect registers and wires by their value-id (== node `id`), in id order.
    let mut reg_nodes: Vec<(&Json, u64, String)> = Vec::new();
    let mut wires: HashMap<u64, &Json> = HashMap::new();
    for n in nodes {
        let id = n.get("id").and_then(Json::as_u64).ok_or("node: missing `id`")?;
        let kind = n.get("kind").ok_or("node: missing `kind`")?;
        match kind.str_field("k") {
            Some("register") => {
                let name = n.str_field("name").unwrap_or("state").to_string();
                reg_nodes.push((kind, id, name));
            }
            Some("wire") => {
                if let Some(expr) = kind.get("expr") {
                    wires.insert(id, expr);
                }
            }
            _ => {}
        }
    }
    // Zero registers (pure datapath / combinational) ⇒ "not a control FSM" — SKIP,
    // don't fail. Errors below are reserved for a recognized state machine we
    // cannot soundly project (fail-closed).
    if reg_nodes.is_empty() {
        return Ok(None);
    }
    // Pack registers in id order (deterministic, matches IR declaration order).
    reg_nodes.sort_by_key(|(_, id, _)| *id);

    // Build the packing layout and the resolver's register slice map. A register
    // must be `uint<n>` with 1 ≤ n ≤ 63; the running offset is the sum of widths.
    let mut regs: Vec<RegInfo> = Vec::new();
    let mut reg_slices: HashMap<u64, (u32, u32)> = HashMap::new();
    let mut reg_meta: Vec<RegMeta> = Vec::new();
    let mut offset = 0u32;
    for (reg_kind, id, name) in &reg_nodes {
        // State must be a maskable unsigned integer: `uint<1..=63>` or `bit`
        // (= uint<1>). A wide (`>63`) or non-integer (array/memory/struct) register
        // is a DATAPATH, not a control-FSM state — SKIP the whole module (`Ok(None)`,
        // make no claim), don't fail. A malformed integer register (uint with width
        // 0 / missing `n`) is an IR error → Err (loud, fail-closed).
        let ty = reg_kind.get("ty");
        let width = match ty.and_then(|t| t.str_field("t")) {
            Some("bit") => 1u32,
            Some("uint") => {
                let n = ty
                    .and_then(|t| t.get("n"))
                    .and_then(Json::as_u64)
                    .ok_or_else(|| format!("register `{name}`: uint state missing width `n`"))?
                    as u32;
                if n == 0 {
                    return Err(format!("register `{name}`: uint state width 0 (malformed)"));
                }
                if n > 63 {
                    return Ok(None); // wide datapath register — not a control FSM
                }
                n
            }
            _ => return Ok(None), // non-integer state (datapath) — not a control FSM
        };
        let next = reg_kind.get("next").ok_or_else(|| format!("register `{name}`: missing `next`"))?;
        let reset_expr = reg_kind.get("reset_value");
        // `enable`: a JSON `null` (or absent) means "always enabled". A non-null
        // expression GATES the update — modeled exactly below as `next` when true,
        // hold otherwise. We must read it, or a gated register that holds a safe
        // value would be modeled as always-advancing (a different machine).
        let enable = match reg_kind.get("enable") {
            Some(Json::Null) | None => None,
            Some(e) => Some(e),
        };
        reg_slices.insert(*id, (width, offset));
        reg_meta.push(RegMeta { width, offset, next, reset: reset_expr, enable });
        regs.push(RegInfo { name: name.clone(), width, offset });
        offset += width;
    }
    let total_bits = offset;
    if total_bits > MAX_COMPOSITE_BITS {
        // A wide multi-register module is a datapath, not a control FSM — SKIP
        // (make no claim), matching the per-register wide-datapath path above and
        // the pre-F3 "not an FSM" behaviour. Reachability would also blow past
        // MAX_STATES anyway. This is sound: an un-projected module is never SAFE.
        return Ok(None);
    }

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

    // Which inputs actually appear in ANY register's `next` (the guard bits we
    // enumerate — the union over the product).
    let mut used_inputs: HashSet<u64> = HashSet::new();
    for rm in &reg_meta {
        collect_input_refs(rm.next, &input_ids, &mut used_inputs);
        if let Some(en) = rm.enable {
            collect_input_refs(en, &input_ids, &mut used_inputs);
        }
    }
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

    let resolver = Resolver { regs: reg_slices, inputs: used_inputs.clone(), wires };

    // Reset state value: each register's `reset_value` must be a constant — it may
    // not reference another register, an input, or a wire (which could fan in an
    // input). Such a reset is REFUSED (fail-closed) rather than mis-evaluated
    // against a zero environment. Pack the per-register resets into the composite.
    let empty: HashMap<u64, i64> = HashMap::new();
    let dummy = Env { packed: 0, assign: &empty };
    let mut reset = 0i64;
    for (rm, info) in reg_meta.iter().zip(&regs) {
        let name = &info.name;
        let v = match rm.reset {
            Some(e) => {
                if expr_references_dynamic(e, &resolver) {
                    return Err(format!("register `{name}`: reset value references a register/input/wire (not a constant) — refuse"));
                }
                eval(e, &resolver, &dummy, 0)? & width_mask(rm.width)
            }
            None => 0,
        };
        reset |= v << rm.offset;
    }

    // The joint transition: evaluate every register's `next` against the current
    // packed state + input valuation, mask each to its width, repack. A gated
    // register (`enable`) takes `next` only when enable is true; otherwise it
    // HOLDS its current slice — modeled exactly, never assumed always-on.
    let step = |packed: i64, assign: &HashMap<u64, i64>| -> Result<i64, String> {
        let mut np = 0i64;
        for rm in &reg_meta {
            let env = Env { packed, assign };
            let enabled = match rm.enable {
                Some(en) => eval(en, &resolver, &env, 0)? != 0,
                None => true,
            };
            let v = if enabled {
                eval(rm.next, &resolver, &env, 0)? & width_mask(rm.width)
            } else {
                (packed >> rm.offset) & width_mask(rm.width) // hold current value
            };
            np |= v << rm.offset;
        }
        Ok(np)
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
            let t = step(s, &assign)?;
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
            let t = step(s, &assign)?;
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
        derive_forbidden(nodes, &resolver, &state_set)?;
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
        regs,
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
/// formal properties that reference ONLY the state register(s). Returns
/// (forbidden values, #usable properties, #skipped properties).
fn derive_forbidden(
    nodes: &[Json],
    resolver: &Resolver,
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
        // Usable only if it references ONLY state registers (no inputs/wires).
        if !references_only_regs(expr, resolver) {
            skipped += 1;
            continue;
        }
        // Evaluate P at every composite state value. A malformed/unsupported
        // property expr is SKIPPED (we prove less) — it must not abort the whole
        // FSM's check.
        let mut local = Vec::new();
        let mut evaluable = true;
        for &v in state_set {
            match eval(expr, resolver, &Env { packed: v, assign: &empty }, 0) {
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

/// True iff `expr` references the state register(s) and NOTHING else that varies
/// (no inputs, no wires) — so it can be evaluated purely on the packed state.
fn references_only_regs(expr: &Json, r: &Resolver) -> bool {
    let mut ok = true;
    walk_refs(expr, &mut |id| {
        if r.regs.contains_key(&id) {
            // a state register — fine.
        } else if r.inputs.contains(&id) || r.wires.contains_key(&id) {
            // an input, or a wire that may fan in inputs — refuse (stay sound).
            ok = false;
        } else {
            // an unknown ref — refuse.
            ok = false;
        }
    });
    ok
}

/// True iff `expr` references any register / input / wire (i.e. is NOT a pure
/// constant). Used to refuse non-constant reset values fail-closed.
fn expr_references_dynamic(expr: &Json, r: &Resolver) -> bool {
    let mut dynamic = false;
    walk_refs(expr, &mut |id| {
        if r.regs.contains_key(&id) || r.inputs.contains(&id) || r.wires.contains_key(&id) {
            dynamic = true;
        } else {
            // an unknown ref is also not a constant we can trust — treat as dynamic.
            dynamic = true;
        }
    });
    dynamic
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
/// `depth` bounds wire-dereference recursion so a malformed combinational wire
/// cycle is REFUSED rather than overflowing the stack.
fn eval(e: &Json, r: &Resolver, env: &Env, depth: u32) -> Result<i64, String> {
    if depth > MAX_EVAL_DEPTH {
        return Err("expression nesting exceeded depth cap (combinational wire cycle?) — refuse".into());
    }
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
            if let Some(&(width, off)) = r.regs.get(&id) {
                // Read this register's slice out of the packed composite state.
                Ok((env.packed >> off) & width_mask(width))
            } else if r.inputs.contains(&id) {
                Ok(*env.assign.get(&id).unwrap_or(&0))
            } else if let Some(w) = r.wires.get(&id) {
                eval(w, r, env, depth + 1)
            } else {
                Err(format!("ref: unresolved value-id {id}"))
            }
        }
        Some("mux") => {
            let c = eval(e.get("cond").ok_or("mux: missing cond")?, r, env, depth + 1)?;
            let branch = if c != 0 { "true" } else { "false" };
            eval(e.get(branch).ok_or("mux: missing branch")?, r, env, depth + 1)
        }
        Some("binop") => {
            let l = eval(e.get("lhs").ok_or("binop: missing lhs")?, r, env, depth + 1)?;
            let rr = eval(e.get("rhs").ok_or("binop: missing rhs")?, r, env, depth + 1)?;
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
                depth + 1,
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
            eval(e.get("value").or_else(|| e.get("expr")).ok_or("cast: missing inner")?, r, env, depth + 1)
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
        assert_eq!(f.regs.len(), 1);
        assert_eq!(f.regs[0].offset, 0); // single register packs at offset 0
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

    // ───────────────────────── F3: multi-register (product) FSMs ──────────────

    /// A two-register product machine. `a:uint<2>` counts toward 2 when `inc`;
    /// `b:uint<2>` mirrors `a` (`b := a`). The joint `next` of `b` READS `a`, so
    /// the product transition must evaluate registers against the SAME packed
    /// pre-state. `bad` chooses whether the safety property is violated:
    ///   safe : `assert always b <= a`  (b trails a by one cycle, always ≤)  → holds
    ///   teeth: `assert always a == b`  (false — they differ for one cycle)  → fails
    fn product_fsm(prop_expr: &str) -> String {
        format!(
            r#"{{"schema":"aria-ir-json/v1","id":0,"name":"prod",
              "ports":[{{"id":0,"value":10,"name":"inc","ty":{{"t":"bit"}},"dir":"input","clock_domain":0}}],
              "clock_domains":[],"annotations":[],
              "nodes":[
                {{"id":1,"name":"a","kind":{{"k":"register","ty":{{"t":"uint","n":2}},"clock_domain":0,
                  "reset_value":{{"e":"lit","lit":{{"l":"uint","value":"0","width":2}}}},"enable":null,
                  "next":{{"e":"mux","cond":{{"e":"binop","op":"logic_and","ty":{{"t":"bit"}},
                      "lhs":{{"e":"ref","value":10}},
                      "rhs":{{"e":"binop","op":"lt","ty":{{"t":"bit"}},"lhs":{{"e":"ref","value":1}},"rhs":{{"e":"lit","lit":{{"l":"uint","value":"2","width":2}}}}}}}},
                    "true":{{"e":"binop","op":"add","ty":{{"t":"uint","n":2}},"lhs":{{"e":"ref","value":1}},"rhs":{{"e":"lit","lit":{{"l":"uint","value":"1","width":2}}}}}},
                    "false":{{"e":"ref","value":1}}}}}}}},
                {{"id":2,"name":"b","kind":{{"k":"register","ty":{{"t":"uint","n":2}},"clock_domain":0,
                  "reset_value":{{"e":"lit","lit":{{"l":"uint","value":"0","width":2}}}},"enable":null,
                  "next":{{"e":"ref","value":1}}}}}},
                {{"id":3,"name":"p","kind":{{"k":"formal_property","property":{{"kind":"assert","temporal":{{"tt":"always"}},
                  "expr":{prop_expr},"name":"safe"}}}}}}
              ],
              "timing":{{}}}}"#
        )
    }

    #[test]
    fn product_fsm_packs_two_registers_and_reads_cross_register_next() {
        // `b <= a` always holds (b is last cycle's a, a only grows). Verifies the
        // composite packing AND that b's `next` (which refs a) reads the shared
        // pre-state, not b's own value.
        let prop = r#"{"e":"binop","op":"le","ty":{"t":"bit"},"lhs":{"e":"ref","value":2},"rhs":{"e":"ref","value":1}}"#;
        let f = extract(&product_fsm(prop)).unwrap();
        assert_eq!(f.regs.len(), 2, "two registers form the product");
        assert_eq!(f.regs[0].name, "a");
        assert_eq!(f.regs[0].offset, 0);
        assert_eq!(f.regs[1].name, "b");
        assert_eq!(f.regs[1].offset, 2, "b packs above a's 2 bits");
        // Reachable composite states: (a,b) with a∈0..=2, b trailing. Pack = a | b<<2.
        // Reset (0,0)=0. Each is well within 2^4.
        assert!(f.state_values.iter().all(|&v| (0..16).contains(&v)));
        assert_eq!(f.reset, 0);
        assert_eq!(f.safety_used, 1);
        assert!(f.forbidden_values.is_empty(), "b<=a holds on all reachable states");
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(r.safe(), "the product machine satisfies b<=a");
    }

    #[test]
    fn product_fsm_safety_violation_is_caught() {
        // teeth: `a == b` is FALSE — after `inc`, a becomes 1 while b is still 0
        // (b mirrors a with one cycle of latency). The composite check must find a
        // reachable state where a≠b and forbid it.
        let prop = r#"{"e":"binop","op":"eq","ty":{"t":"bit"},"lhs":{"e":"ref","value":1},"rhs":{"e":"ref","value":2}}"#;
        let f = extract(&product_fsm(prop)).unwrap();
        assert_eq!(f.regs.len(), 2);
        assert!(!f.forbidden_values.is_empty(), "a≠b states must be forbidden");
        // A forbidden state has a (low 2 bits) ≠ b (next 2 bits).
        for &v in &f.forbidden_values {
            let a = v & 0b11;
            let b = (v >> 2) & 0b11;
            assert_ne!(a, b, "forbidden composite {v:#06b} must have a≠b");
        }
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(!r.safe(), "a reachable a≠b state must FAIL the composite check");
    }

    #[test]
    fn product_fsm_emits_sound_lean() {
        use crate::models::lean;
        let prop = r#"{"e":"binop","op":"le","ty":{"t":"bit"},"lhs":{"e":"ref","value":2},"rhs":{"e":"ref","value":1}}"#;
        let f = extract(&product_fsm(prop)).unwrap();
        let src = lean::emit_fsm(&f.lts, "Fpga_prod");
        assert!(src.contains("inductive State"));
        assert!(src.contains("theorem safety"));
        assert!(src.contains("#print axioms Fpga_prod.safety"));
    }

    #[test]
    fn wide_composite_is_skipped_as_datapath() {
        // Two uint<32> registers = 64 bits > 63 — too wide to be a control FSM, so
        // the module is SKIPPED (Ok(None), no claim), not failed. An un-projected
        // module is never reported SAFE, so this is sound — and it doesn't turn a
        // legitimate datapath (e.g. an address cache) into a CI failure.
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"wide",
          "ports":[],"clock_domains":[],"annotations":[],
          "nodes":[
            {"id":1,"name":"a","kind":{"k":"register","ty":{"t":"uint","n":32},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"uint","value":"0","width":32}},"enable":null,"next":{"e":"ref","value":1}}},
            {"id":2,"name":"b","kind":{"k":"register","ty":{"t":"uint","n":32},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"uint","value":"0","width":32}},"enable":null,"next":{"e":"ref","value":2}}}
          ],"timing":{}}"#;
        let m = &parse_stream(src).unwrap()[0];
        assert!(extract_fsm(m).unwrap().is_none(), "64-bit composite is a datapath — skip, not fail");
    }

    #[test]
    fn bit_register_is_supported_as_uint1() {
        // A `bit` flag register paired with a small uint counter is a valid control
        // FSM (composite = 1 + 2 = 3 bits). `flag := go` (a one-bit register),
        // `cnt := go ? cnt+1 : cnt` (uint<2>, wraps). Property `cnt <= 3` always
        // holds (uint<2> max). Exercises bit-register packing at offset 0.
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"flagcnt",
          "ports":[{"id":0,"value":10,"name":"go","ty":{"t":"bit"},"dir":"input","clock_domain":0}],
          "clock_domains":[],"annotations":[],
          "nodes":[
            {"id":1,"name":"flag","kind":{"k":"register","ty":{"t":"bit"},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"bit","value":"false","width":1}},"enable":null,
              "next":{"e":"ref","value":10}}},
            {"id":2,"name":"cnt","kind":{"k":"register","ty":{"t":"uint","n":2},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"uint","value":"0","width":2}},"enable":null,
              "next":{"e":"mux","cond":{"e":"ref","value":10},
                "true":{"e":"binop","op":"add","ty":{"t":"uint","n":2},"lhs":{"e":"ref","value":2},"rhs":{"e":"lit","lit":{"l":"uint","value":"1","width":2}}},
                "false":{"e":"ref","value":2}}}},
            {"id":3,"name":"p","kind":{"k":"formal_property","property":{"kind":"assert","temporal":{"tt":"always"},
              "expr":{"e":"binop","op":"le","ty":{"t":"bit"},"lhs":{"e":"ref","value":2},"rhs":{"e":"lit","lit":{"l":"uint","value":"3","width":32}}},"name":"safe"}}}
          ],"timing":{}}"#;
        let f = extract(src).unwrap();
        assert_eq!(f.regs.len(), 2);
        assert_eq!(f.regs[0].name, "flag");
        assert_eq!(f.regs[0].width, 1, "bit register is uint<1>");
        assert_eq!(f.regs[1].offset, 1, "cnt packs above the 1-bit flag");
        assert!(f.forbidden_values.is_empty());
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(r.safe());
    }

    #[test]
    fn enable_gate_holds_value_when_low() {
        // A gated counter: `state` (uint<2>) increments ONLY when `en` is high,
        // otherwise HOLDS. With `assert always state <= 2`, the design is safe iff
        // the gate is honoured: next=state+1 unconditionally would reach 3.
        //   next  = mux(state < 2, state+1, state)   (saturating-ish, but...)
        // To make the gate decisive we use a plain +1 (wraps in uint<2>): without
        // the enable model, state cycles 0→1→2→3→0 and 3 violates `state<=2`.
        // WITH the enable gate, when en=0 the register holds — but en is a free
        // input, so the reachable set under exhaustive valuation STILL includes the
        // en=1 path 0→1→2→3. So a wrapping counter is reachable either way; instead
        // make `next` itself safe and prove the HOLD path is modeled: reset=2,
        // next = 0 (would drop to 0), enable=en. Property: `state >= 2` is false at
        // 0. If the hold is modeled, en=0 keeps state=2 (safe) AND en=1 moves to 0
        // (forbidden) ⇒ VIOLATION must be found (teeth that the en=1 path exists).
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"gated",
          "ports":[{"id":0,"value":10,"name":"en","ty":{"t":"bit"},"dir":"input","clock_domain":0}],
          "clock_domains":[],"annotations":[],
          "nodes":[
            {"id":1,"name":"state","kind":{"k":"register","ty":{"t":"uint","n":2},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"uint","value":"2","width":2}},
              "enable":{"e":"ref","value":10},
              "next":{"e":"lit","lit":{"l":"uint","value":"0","width":2}}}},
            {"id":2,"name":"p","kind":{"k":"formal_property","property":{"kind":"assert","temporal":{"tt":"always"},
              "expr":{"e":"binop","op":"ge","ty":{"t":"bit"},"lhs":{"e":"ref","value":1},"rhs":{"e":"lit","lit":{"l":"uint","value":"2","width":32}}},"name":"hold"}}}
          ],"timing":{}}"#;
        let f = extract(src).unwrap();
        // Reset 2 is held when en=0; dropped to 0 when en=1. Both reachable.
        assert!(f.state_values.contains(&2), "held value (en=0) must be reachable");
        assert!(f.state_values.contains(&0), "en=1 path to 0 must be reachable");
        assert_eq!(f.forbidden_values, vec![0], "state 0 violates state>=2");
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(!r.safe(), "the en=1 path reaches a forbidden state");
    }

    #[test]
    fn enable_gate_makes_design_safe_when_it_should() {
        // Mirror: reset=2, next=3 (illegal), enable = constant false (en held low
        // by a literal `false`). With the gate modeled, the register NEVER advances
        // to 3, so `assert always state <= 2` holds. Without the gate it would be a
        // false VIOLATION (3 wrongly reachable). enable is a literal so there are
        // zero guard inputs — the hold is the only behaviour.
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"frozen",
          "ports":[],"clock_domains":[],"annotations":[],
          "nodes":[
            {"id":1,"name":"state","kind":{"k":"register","ty":{"t":"uint","n":2},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"uint","value":"2","width":2}},
              "enable":{"e":"lit","lit":{"l":"bit","value":"false","width":1}},
              "next":{"e":"lit","lit":{"l":"uint","value":"3","width":2}}}},
            {"id":2,"name":"p","kind":{"k":"formal_property","property":{"kind":"assert","temporal":{"tt":"always"},
              "expr":{"e":"binop","op":"le","ty":{"t":"bit"},"lhs":{"e":"ref","value":1},"rhs":{"e":"lit","lit":{"l":"uint","value":"2","width":32}}},"name":"safe"}}}
          ],"timing":{}}"#;
        let f = extract(src).unwrap();
        assert_eq!(f.state_values, vec![2], "a frozen register has exactly its reset state");
        assert!(f.forbidden_values.is_empty(), "illegal next=3 is never taken (enable low)");
        let r = check::check(&f.lts, check::DEFAULT_BOUND);
        assert!(r.safe());
    }

    #[test]
    fn null_enable_is_always_on_unchanged() {
        // Regression: the existing single-register fixtures carry `"enable":null`
        // (always-on). The toggle FSM must extract identically to before.
        let f = extract(&fsm(1, "bit")).unwrap();
        assert_eq!(f.state_values, vec![0, 1]);
        assert!(f.forbidden_values.is_empty());
    }

    #[test]
    fn non_constant_reset_is_refused() {
        // A reset that references another register is not a constant — refuse
        // rather than evaluate against a zero environment (which would silently
        // pick the wrong initial state).
        let src = r#"{"schema":"aria-ir-json/v1","id":0,"name":"rst",
          "ports":[],"clock_domains":[],"annotations":[],
          "nodes":[
            {"id":1,"name":"a","kind":{"k":"register","ty":{"t":"uint","n":2},"clock_domain":0,
              "reset_value":{"e":"lit","lit":{"l":"uint","value":"1","width":2}},"enable":null,"next":{"e":"ref","value":1}}},
            {"id":2,"name":"b","kind":{"k":"register","ty":{"t":"uint","n":2},"clock_domain":0,
              "reset_value":{"e":"ref","value":1},"enable":null,"next":{"e":"ref","value":2}}}
          ],"timing":{}}"#;
        let m = &parse_stream(src).unwrap()[0];
        assert!(extract_fsm(m).is_err(), "non-constant reset must be refused");
    }
}
