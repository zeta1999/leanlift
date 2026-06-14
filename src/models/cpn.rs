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
use super::toml::{self, Doc};
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

/// A parsed coloured net (the intermediate structure shared by the unfolder and
/// the independent occurrence-graph simulator that cross-checks it).
struct Cpn {
    colours: HashMap<String, Vec<String>>,
    places: Vec<Place>,
    transitions: Vec<CTrans>,
}

/// Parse + unfold a CPN source string to a PT-net, returning the net and the
/// compactness note (coloured size → unfolded size).
pub fn unfold(src: &str) -> Result<(PtNet, Vec<String>), String> {
    let doc = toml::parse(src)?;
    let cpn = parse_cpn(&doc)?;
    let (net, _origin) = unfold_cpn(&cpn, &doc)?;
    let note = format!(
        "CPN compactness: {} coloured place(s) / {} transition(s) → unfolded {} PT place(s) / {} PT transition(s)",
        cpn.places.len(),
        cpn.transitions.len(),
        net.places.len(),
        net.transitions.len()
    );
    Ok((net, vec![note]))
}

/// Parse the coloured structure (colours, typed places, transitions/arcs).
fn parse_cpn(doc: &Doc) -> Result<Cpn, String> {
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

    let mut transitions: Vec<CTrans> = Vec::new();
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
        transitions.push(CTrans { name, var, pre, post });
    }

    Ok(Cpn { colours, places, transitions })
}

/// Unfold a parsed CPN to a PT-net. Also returns the `(place, value)` ORIGIN of
/// each PT place (parallel to `net.places`), so a PT marking can be read back as
/// a coloured marking — the bridge the differential test uses.
fn unfold_cpn(cpn: &Cpn, doc: &Doc) -> Result<(PtNet, Vec<(String, String)>), String> {
    let Cpn { colours, places, transitions: ctrans } = cpn;

    // PT places: one per (coloured place, colour value), in declaration order.
    let mut pt_places: Vec<String> = Vec::new();
    let mut origin: Vec<(String, String)> = Vec::new();
    let mut pindex: HashMap<(String, String), usize> = HashMap::new();
    for p in places {
        for v in &colours[&p.colour] {
            pindex.insert((p.name.clone(), v.clone()), pt_places.len());
            pt_places.push(format!("{}_{}", p.name, v));
            origin.push((p.name.clone(), v.clone()));
        }
    }
    let place_colour: HashMap<&str, &str> = places.iter().map(|p| (p.name.as_str(), p.colour.as_str())).collect();

    let mut initial = vec![0u32; pt_places.len()];
    for p in places {
        for v in &p.init {
            initial[pindex[&(p.name.clone(), v.clone())]] += 1;
        }
    }

    let resolve = |arc: &Arc, binding: &Option<(String, String)>| -> Result<usize, String> {
        let colour = *place_colour
            .get(arc.place.as_str())
            .ok_or_else(|| format!("arc references unknown place `{}`", arc.place))?;
        let value = match binding {
            Some((var, val)) if *var == arc.expr => val.clone(),
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

    let mut pt_trans: Vec<PtTrans> = Vec::new();
    for t in ctrans {
        let bindings: Vec<Option<(String, String)>> = match &t.var {
            Some((var, col)) => colours[col].iter().map(|v| Some((var.clone(), v.clone()))).collect(),
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

    let net = PtNet { places: pt_places, transitions: pt_trans, initial, bound: 8, bounds, conserved };
    Ok((net, origin))
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

/// The coloured occurrence graph — an INDEPENDENT simulator (PLAN-verification
/// §2): it computes enabling/firing directly over coloured markings (multisets
/// of `(place, value)` tokens), *without* going through the unfolder's
/// `PtTrans`/`pindex`. Returns the set of reachable coloured markings in a
/// canonical encoding that the unfolded PT-net's reachable markings can be
/// compared against. A bug in the unfolding logic ⇒ the two sets differ.
#[cfg(test)]
fn occurrence_graph(cpn: &Cpn) -> Result<std::collections::HashSet<String>, String> {
    use std::collections::{BTreeMap, HashSet};
    type Marking = BTreeMap<(String, String), u32>;

    let place_colour: HashMap<&str, &str> =
        cpn.places.iter().map(|p| (p.name.as_str(), p.colour.as_str())).collect();

    // Resolve an arc+binding to a (place, value) token — reimplemented here,
    // sharing nothing with the unfolder beyond the parsed structure.
    let resolve = |arc: &Arc, b: &Option<(String, String)>| -> Result<(String, String), String> {
        let colour = *place_colour
            .get(arc.place.as_str())
            .ok_or_else(|| format!("unknown place `{}`", arc.place))?;
        let value = match b {
            Some((var, val)) if *var == arc.expr => val.clone(),
            _ => {
                if !cpn.colours[colour].contains(&arc.expr) {
                    return Err(format!("arc `{}({})`: not a variable or colour value", arc.place, arc.expr));
                }
                arc.expr.clone()
            }
        };
        Ok((arc.place.clone(), value))
    };
    let canon = |m: &Marking| {
        m.iter().filter(|(_, &c)| c > 0).map(|((p, v), c)| format!("{p}|{v}={c}")).collect::<Vec<_>>().join(",")
    };

    let mut init: Marking = BTreeMap::new();
    for p in &cpn.places {
        for v in &p.init {
            *init.entry((p.name.clone(), v.clone())).or_insert(0) += 1;
        }
    }

    let mut seen: HashSet<String> = HashSet::new();
    let mut stack = vec![init.clone()];
    seen.insert(canon(&init));
    while let Some(m) = stack.pop() {
        for t in &cpn.transitions {
            let bindings: Vec<Option<(String, String)>> = match &t.var {
                Some((var, col)) => cpn.colours[col].iter().map(|v| Some((var.clone(), v.clone()))).collect(),
                None => vec![None],
            };
            for b in &bindings {
                // pre/post as multisets of (place, value) tokens.
                let mut pre: Marking = BTreeMap::new();
                for a in &t.pre {
                    *pre.entry(resolve(a, b)?).or_insert(0) += 1;
                }
                let enabled = pre.iter().all(|(pv, &c)| *m.get(pv).unwrap_or(&0) >= c);
                if !enabled {
                    continue;
                }
                let mut m2 = m.clone();
                for (pv, &c) in &pre {
                    *m2.get_mut(pv).unwrap() -= c;
                }
                for a in &t.post {
                    *m2.entry(resolve(a, b)?).or_insert(0) += 1;
                }
                let key = canon(&m2);
                if seen.insert(key) {
                    stack.push(m2);
                }
            }
        }
    }
    Ok(seen)
}

#[cfg(test)]
mod tests {
    use super::super::ir::Model;
    use super::*;
    use std::collections::HashSet;

    /// The unfolded PT-net's reachable markings, encoded in the SAME canonical
    /// `(place, value)` form as `occurrence_graph` (via the unfold origin).
    fn unfolded_reachable(net: &PtNet, origin: &[(String, String)]) -> HashSet<String> {
        let canon = |s: &String| {
            let counts = PtNet::decode(s);
            let mut pairs: Vec<String> = (0..origin.len())
                .filter(|&i| counts[i] > 0)
                .map(|i| format!("{}|{}={}", origin[i].0, origin[i].1, counts[i]))
                .collect();
            pairs.sort();
            pairs.join(",")
        };
        // Independent BFS over the unfolded net (PtNet's Model impl).
        let mut seen = HashSet::new();
        let mut stack = vec![net.initial()];
        seen.insert(net.initial());
        while let Some(s) = stack.pop() {
            for a in net.enabled(&s) {
                if let Some(t) = net.step(&s, &a) {
                    if seen.insert(t.clone()) {
                        stack.push(t);
                    }
                }
            }
        }
        seen.iter().map(|s| canon(s)).collect()
    }

    /// THE differential (PLAN-verification §2, the unfolder is the prime suspect):
    /// the coloured occurrence graph must equal the unfolded PT-net's reachable
    /// graph. Re-parses from a TOML source so parsing is shared but the unfolding
    /// logic and the coloured simulator are independent.
    fn assert_unfold_equiv(src: &str) {
        let doc = toml::parse(src).expect("parse");
        let cpn = parse_cpn(&doc).expect("cpn");
        let (net, origin) = unfold_cpn(&cpn, &doc).expect("unfold");
        let coloured = occurrence_graph(&cpn).expect("occurrence graph");
        let unfolded = unfolded_reachable(&net, &origin);
        assert_eq!(coloured, unfolded, "unfold ≢ coloured for:\n{src}");
        assert!(!coloured.is_empty());
    }

    #[test]
    fn resource_unfold_equiv() {
        assert_unfold_equiv(&std::fs::read_to_string("examples/models/resource.model.toml").unwrap());
    }

    #[test]
    fn synthetic_unfold_equiv() {
        // A two-colour producer/consumer with a constant-valued lock arc.
        let prodcons = r#"
kind = "cpn"
[[colour]]
name = "Job"
values = ["x", "y"]
[[colour]]
name = "Slot"
values = ["s"]
[[place]]
name = "queue"
colour = "Job"
init = "x, y"
[[place]]
name = "done"
colour = "Job"
init = ""
[[place]]
name = "slot"
colour = "Slot"
init = "s"
[[transition]]
name = "process"
var = "j:Job"
pre = "queue(j), slot(s)"
post = "done(j), slot(s)"
"#;
        assert_unfold_equiv(prodcons);

        // A ring: each job advances to the "next" — exercises constant arcs and
        // multiple reachable markings.
        let ring = r#"
kind = "cpn"
[[colour]]
name = "P"
values = ["a", "b", "c"]
[[place]]
name = "at"
colour = "P"
init = "a"
[[transition]]
name = "ab"
pre = "at(a)"
post = "at(b)"
[[transition]]
name = "bc"
pre = "at(b)"
post = "at(c)"
[[transition]]
name = "ca"
pre = "at(c)"
post = "at(a)"
"#;
        assert_unfold_equiv(ring);
    }
}
