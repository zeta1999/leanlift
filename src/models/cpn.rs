//! Coloured Petri nets (PLAN-models §4, Jensen LNCS 803) — **unfolded** to a
//! PT-net over finite colour sets (§4.3), so the Phase-2 checker and Lean
//! exporter apply unchanged and M3 comes free (§4.4 path a). The unfolding is
//! the standard semantics-preserving one: each (place, colour-value) becomes a
//! PT place, and each (transition, variable-binding) becomes a PT transition —
//! so the unfolded reachability graph IS the coloured occurrence graph.
//!
//! The compact authoring shape (one coloured transition stands for |bindings|
//! PT transitions — Jensen's compactness lesson):
//!
//! ```toml
//! kind = "cpn"
//!
//! [[colour]]
//! name   = "Proc"
//! values = ["p1", "p2", "p3"]
//!
//! [[place]]
//! name   = "idle"
//! colour = "Proc"
//! init   = "p1, p2, p3"      # a coloured marking (multiset of values)
//!
//! [[transition]]
//! name = "acquire"
//! var  = "p:Proc"            # one bound variable ranging over a colour set
//! pre  = "idle(p), lock(lk)"
//! post = "crit(p)"
//!
//! [[bound]]                  # safety over ALL colours of a place
//! place     = "crit"
//! max       = "1"
//! conserved = ["crit", "lock"]   # the place-invariant subsystem
//! ```
//!
//! Scope: one bound variable per transition, single-token arcs (a variable or a
//! constant value). Guards, tuple/product colours, subset-by-predicate, and
//! broadcast multiset arcs (Jensen's `Mes(s)`) are deferred — so the genuine
//! distributed-database net is a further step; this delivers the coloured-mutex
//! end to end.

use super::ir::{BoundProp, PtNet, PtTrans};
use super::toml;
use std::collections::HashMap;

struct Place {
    name: String,
    colour: String,
    init: Vec<String>, // multiset of colour values
}

struct CTrans {
    name: String,
    var: Option<(String, String)>, // (variable, colour)
    pre: Vec<Arc>,
    post: Vec<Arc>,
}

struct Arc {
    place: String,
    expr: String, // a variable name or a constant colour value
}

/// Parse + unfold a CPN source string to a PT-net, returning the net and the
/// compactness note (coloured size → unfolded size).
pub fn unfold(src: &str) -> Result<(PtNet, Vec<String>), String> {
    let doc = toml::parse(src)?;

    // Colour sets.
    let mut colours: HashMap<String, Vec<String>> = HashMap::new();
    for (i, c) in doc.table("colour").iter().enumerate() {
        let name = cfield(c, "name", i)?;
        let values: Vec<String> = c
            .get("values")
            .ok_or_else(|| format!("colour {i}: missing `values`"))?
            .as_arr("values")?
            .to_vec();
        if values.is_empty() {
            return Err(format!("colour `{name}` is empty"));
        }
        colours.insert(name, values);
    }
    if colours.is_empty() {
        return Err("CPN requires at least one [[colour]]".into());
    }

    // Places.
    let mut places: Vec<Place> = Vec::new();
    for (i, p) in doc.table("place").iter().enumerate() {
        let name = cfield(p, "name", i)?;
        let colour = cfield(p, "colour", i)?;
        let cvals = colours
            .get(&colour)
            .ok_or_else(|| format!("place `{name}`: unknown colour `{colour}`"))?;
        let init: Vec<String> = p
            .get("init")
            .map(|v| v.as_str("init"))
            .transpose()?
            .unwrap_or("")
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();
        for v in &init {
            if !cvals.contains(v) {
                return Err(format!("place `{name}`: init value `{v}` not in colour `{colour}`"));
            }
        }
        places.push(Place { name, colour, init });
    }
    if places.is_empty() {
        return Err("CPN requires at least one [[place]]".into());
    }

    // Transitions.
    let mut ctrans: Vec<CTrans> = Vec::new();
    for (i, t) in doc.table("transition").iter().enumerate() {
        let name = cfield(t, "name", i)?;
        let var = match t.get("var") {
            Some(v) => {
                let s = v.as_str("var")?;
                let (var, col) = s
                    .split_once(':')
                    .ok_or_else(|| format!("transition `{name}`: `var` must be `name:Colour`"))?;
                if !colours.contains_key(col.trim()) {
                    return Err(format!("transition `{name}`: unknown colour `{}`", col.trim()));
                }
                Some((var.trim().to_string(), col.trim().to_string()))
            }
            None => None,
        };
        let pre = parse_arcs(t.get("pre").map(|v| v.as_str("pre")).transpose()?.unwrap_or(""), &name)?;
        let post = parse_arcs(t.get("post").map(|v| v.as_str("post")).transpose()?.unwrap_or(""), &name)?;
        ctrans.push(CTrans { name, var, pre, post });
    }

    // --- unfold ------------------------------------------------------------- //
    // PT places: one per (coloured place, colour value), in declaration order.
    let mut pt_places: Vec<String> = Vec::new();
    let mut pindex: HashMap<(String, String), usize> = HashMap::new();
    for p in &places {
        for v in &colours[&p.colour] {
            pindex.insert((p.name.clone(), v.clone()), pt_places.len());
            pt_places.push(format!("{}_{}", p.name, v));
        }
    }
    let place_colour: HashMap<&str, &str> = places.iter().map(|p| (p.name.as_str(), p.colour.as_str())).collect();

    // initial marking.
    let mut initial = vec![0u32; pt_places.len()];
    for p in &places {
        for v in &p.init {
            initial[pindex[&(p.name.clone(), v.clone())]] += 1;
        }
    }

    // Resolve an arc expression under a binding to a (place-index) for a 1-token
    // arc. `expr` is the bound variable (→ its value) or a constant colour value.
    let resolve = |arc: &Arc, binding: &Option<(String, String)>| -> Result<usize, String> {
        let colour = *place_colour
            .get(arc.place.as_str())
            .ok_or_else(|| format!("arc references unknown place `{}`", arc.place))?;
        let value = match binding {
            // the bound variable resolves to its value under this binding
            Some((var, val)) if *var == arc.expr => val.clone(),
            // otherwise it must be a constant value of this place's colour
            _ => {
                if !colours[colour].contains(&arc.expr) {
                    return Err(format!(
                        "arc `{}({})`: `{}` is neither the bound variable nor a value of colour `{colour}`",
                        arc.place, arc.expr, arc.expr
                    ));
                }
                arc.expr.clone()
            }
        };
        pindex
            .get(&(arc.place.clone(), value.clone()))
            .copied()
            .ok_or_else(|| format!("arc `{}({})`: no such place/colour", arc.place, value))
    };

    // PT transitions: one per (transition, binding of its variable).
    let mut pt_trans: Vec<PtTrans> = Vec::new();
    for t in &ctrans {
        let bindings: Vec<Option<(String, String)>> = match &t.var {
            Some((var, col)) => colours[col]
                .iter()
                .map(|v| Some((var.clone(), v.clone())))
                .collect(),
            None => vec![None],
        };
        for binding in &bindings {
            let mut pre = vec![0u32; pt_places.len()];
            let mut post = vec![0u32; pt_places.len()];
            for a in &t.pre {
                pre[resolve(a, binding)?] += 1;
            }
            for a in &t.post {
                post[resolve(a, binding)?] += 1;
            }
            let suffix = binding.as_ref().map(|(_, v)| format!("_{v}")).unwrap_or_default();
            pt_trans.push(PtTrans { name: format!("{}{}", t.name, suffix), pre, post });
        }
    }

    // bounds + conserved (coloured place names → all their unfolded indices).
    let expand = |pname: &str| -> Result<Vec<usize>, String> {
        let colour = *place_colour
            .get(pname)
            .ok_or_else(|| format!("`{pname}` is not a declared place"))?;
        Ok(colours[colour].iter().map(|v| pindex[&(pname.to_string(), v.clone())]).collect())
    };

    let mut bounds = Vec::new();
    for (i, bd) in doc.table("bound").iter().enumerate() {
        let name = cfield(bd, "name", i).unwrap_or_else(|_| format!("bound{i}"));
        let place = cfield(bd, "place", i)?;
        let max: u32 = cfield(bd, "max", i)?.parse().map_err(|_| format!("bound {i}: bad `max`"))?;
        bounds.push(BoundProp { name, places: expand(&place)?, max });
    }

    let conserved = match doc.scalar("conserved") {
        Some(v) => {
            let mut idxs = Vec::new();
            for pname in v.as_arr("conserved")? {
                idxs.extend(expand(pname)?);
            }
            Some(idxs)
        }
        None => None,
    };

    let note = format!(
        "CPN compactness: {} coloured place(s) / {} transition(s) → unfolded {} PT place(s) / {} PT transition(s)",
        places.len(),
        ctrans.len(),
        pt_places.len(),
        pt_trans.len()
    );

    let net = PtNet {
        places: pt_places,
        transitions: pt_trans,
        initial,
        bound: 8,
        bounds,
        conserved,
    };
    Ok((net, vec![note]))
}

fn parse_arcs(s: &str, tname: &str) -> Result<Vec<Arc>, String> {
    let mut arcs = Vec::new();
    let mut rest = s.trim();
    while !rest.is_empty() {
        let open = rest.find('(').ok_or_else(|| format!("transition `{tname}`: arc `{rest}` must be place(expr)"))?;
        let close = rest.find(')').ok_or_else(|| format!("transition `{tname}`: missing `)` in `{rest}`"))?;
        let place = rest[..open].trim().to_string();
        let expr = rest[open + 1..close].trim().to_string();
        if place.is_empty() || expr.is_empty() {
            return Err(format!("transition `{tname}`: malformed arc `{rest}`"));
        }
        arcs.push(Arc { place, expr });
        rest = rest[close + 1..].trim_start();
        rest = rest.strip_prefix(',').unwrap_or(rest).trim_start();
    }
    Ok(arcs)
}

fn cfield(t: &HashMap<String, toml::Value>, key: &str, i: usize) -> Result<String, String> {
    Ok(t.get(key)
        .ok_or_else(|| format!("[[…]] entry {i}: missing `{key}`"))?
        .as_str(key)?
        .to_string())
}
