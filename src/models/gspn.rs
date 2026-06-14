//! Generalized Stochastic Petri nets → CTMC (PLAN-models §5, day49). A GSPN's
//! reachability graph IS a Continuous-Time Markov Chain over the **tangible**
//! markings; immediate (zero-time) transitions make a marking **vanishing** and
//! are eliminated by folding their weighted paths into the rates between
//! tangibles. We then solve the CTMC numerically — **numpy-free, pure Rust**:
//! absorption probabilities and expected time via the embedded jump chain, and
//! transient distributions by **uniformization**. This is the M2 trust anchor
//! when no PRISM binary is present (the closed-form cross-checks in the recipe
//! validate it).
//!
//! Authoring shape (`*.model.toml`, `kind = "gspn"`): places, an `initial`
//! marking, named `[[param]]`s (with arithmetic value expressions), `[[transition]]`s
//! tagged `immediate`(weight) or `timed`(rate-expression) with optional
//! `inhibit` places, and `[[query]]`s (`prob` / `etime` / `transient`).

use super::toml::{self, Doc};
use std::collections::HashMap;

pub struct GTrans {
    /// Parsed for diagnostics / a future labelled PRISM export; the explicit
    /// CTMC export aggregates edges per source state, so it is not read there.
    #[allow(dead_code)]
    pub name: String,
    pub immediate: bool,
    pub rate_or_weight: f64,
    pub pre: Vec<u32>,
    pub post: Vec<u32>,
    pub inhibit: Vec<usize>,
}

pub struct Query {
    pub name: String,
    pub compute: Compute,
    pub target: Option<usize>, // place index
    pub time: Option<f64>,
}

pub enum Compute {
    Prob,
    Etime,
    Transient,
}

pub struct Gspn {
    pub places: Vec<String>,
    pub transitions: Vec<GTrans>,
    pub initial: Vec<u32>,
    pub mode: String,
    pub queries: Vec<Query>,
}

fn enc(m: &[u32]) -> String {
    m.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",")
}
fn dec(s: &str) -> Vec<u32> {
    s.split(',').map(|x| x.parse().unwrap_or(0)).collect()
}

impl Gspn {
    fn enabled_at(&self, m: &[u32], t: &GTrans) -> bool {
        t.pre.iter().zip(m).all(|(&c, &h)| c <= h) && t.inhibit.iter().all(|&p| m[p] == 0)
    }
    fn fire(&self, m: &[u32], t: &GTrans) -> Vec<u32> {
        (0..self.places.len()).map(|i| m[i] - t.pre[i] + t.post[i]).collect()
    }
    fn is_vanishing(&self, m: &[u32]) -> bool {
        self.transitions.iter().any(|t| t.immediate && self.enabled_at(m, t))
    }

    /// All reachable markings (vanishing + tangible), as encoded strings.
    fn all_markings(&self) -> Vec<String> {
        let mut seen: HashMap<String, ()> = HashMap::new();
        let mut order = Vec::new();
        let mut stack = vec![enc(&self.initial)];
        seen.insert(enc(&self.initial), ());
        while let Some(s) = stack.pop() {
            order.push(s.clone());
            let m = dec(&s);
            for t in &self.transitions {
                if self.enabled_at(&m, t) {
                    let n = enc(&self.fire(&m, t));
                    if seen.insert(n.clone(), ()).is_none() {
                        stack.push(n);
                    }
                }
            }
        }
        order
    }

    /// Probability distribution over TANGIBLE markings entered from `m`,
    /// following immediate (weighted) choices through vanishing markings.
    fn reach_tangible(&self, m: &[u32], out: &mut HashMap<String, f64>, prob: f64, depth: u32) {
        if depth > 10_000 {
            return; // immediate-loop guard (timeless trap)
        }
        if !self.is_vanishing(m) {
            *out.entry(enc(m)).or_insert(0.0) += prob;
            return;
        }
        let imm: Vec<&GTrans> = self.transitions.iter().filter(|t| t.immediate && self.enabled_at(m, t)).collect();
        let wtot: f64 = imm.iter().map(|t| t.rate_or_weight).sum();
        for t in imm {
            let branch = t.rate_or_weight / wtot;
            let next = self.fire(m, t);
            self.reach_tangible(&next, out, prob * branch, depth + 1);
        }
    }

    fn tangible_dist(&self, m: &[u32]) -> HashMap<String, f64> {
        let mut out = HashMap::new();
        self.reach_tangible(m, &mut out, 1.0, 0);
        out
    }

    /// Build the tangible-marking CTMC generator `Q`. Returns (tangible states,
    /// Q). `Q[i][j]` = rate i→j (i≠j); `Q[i][i] = −Σ_{j≠i} Q[i][j]`.
    pub fn ctmc(&self) -> (Vec<String>, Vec<Vec<f64>>) {
        let mut tang: Vec<String> = self
            .all_markings()
            .into_iter()
            .filter(|s| !self.is_vanishing(&dec(s)))
            .collect();
        tang.sort();
        tang.dedup();
        let idx: HashMap<&str, usize> = tang.iter().enumerate().map(|(i, s)| (s.as_str(), i)).collect();
        let n = tang.len();
        let mut q = vec![vec![0.0f64; n]; n];
        for (i, s) in tang.iter().enumerate() {
            let m = dec(s);
            for t in &self.transitions {
                if !t.immediate && self.enabled_at(&m, t) {
                    let r = t.rate_or_weight;
                    for (mt, w) in self.tangible_dist(&self.fire(&m, t)) {
                        if mt != *s {
                            q[i][idx[mt.as_str()]] += r * w;
                        }
                    }
                }
            }
        }
        for i in 0..n {
            let off: f64 = (0..n).filter(|&j| j != i).map(|j| q[i][j]).sum();
            q[i][i] = -off;
        }
        (tang, q)
    }

    /// The tangible distribution the chain starts in (the initial marking may be
    /// vanishing — e.g. an instant `send`).
    fn start_dist(&self, tang: &[String]) -> Vec<(usize, f64)> {
        let pos: HashMap<&str, usize> = tang.iter().enumerate().map(|(i, s)| (s.as_str(), i)).collect();
        self.tangible_dist(&self.initial).into_iter().map(|(s, p)| (pos[s.as_str()], p)).collect()
    }

    /// The dominant tangible start index (for the PRISM `init`). For the dock
    /// the initial `send` is deterministic, so this is the single start.
    pub fn dominant_start(&self, tang: &[String]) -> usize {
        self.start_dist(tang)
            .into_iter()
            .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .map(|(i, _)| i)
            .unwrap_or(0)
    }

    /// Evaluate one query over the CTMC, combining over the start distribution.
    pub fn evaluate(&self, q: &Query, tang: &[String], gen: &[Vec<f64>]) -> f64 {
        let start = self.start_dist(tang);
        match q.compute {
            Compute::Prob => {
                let tgt = q.target.expect("prob query needs a target");
                start.iter().map(|&(s, w)| w * prob_reach(gen, tang, s, tgt)).sum()
            }
            Compute::Etime => start.iter().map(|&(s, w)| w * expected_time(gen, s)).sum(),
            Compute::Transient => {
                let tgt = q.target.expect("transient query needs a target");
                let t = q.time.expect("transient query needs a time");
                start
                    .iter()
                    .map(|&(s, w)| {
                        let pi = transient(gen, s, t);
                        let mass: f64 = tang
                            .iter()
                            .enumerate()
                            .filter(|(_, m)| dec(m)[tgt] > 0)
                            .map(|(j, _)| pi[j])
                            .sum();
                        w * mass
                    })
                    .sum()
            }
        }
    }
}

// --- CTMC solvers (pure Rust f64) -------------------------------------------- //

fn absorbing(q: &[Vec<f64>]) -> Vec<bool> {
    q.iter().map(|row| row.iter().all(|&x| x.abs() < 1e-15)).collect()
}

/// Solve `A x = b` by Gaussian elimination with partial pivoting.
fn solve(mut a: Vec<Vec<f64>>, mut b: Vec<f64>) -> Vec<f64> {
    let n = b.len();
    for col in 0..n {
        let piv = (col..n).max_by(|&i, &j| a[i][col].abs().partial_cmp(&a[j][col].abs()).unwrap()).unwrap();
        a.swap(col, piv);
        b.swap(col, piv);
        let d = a[col][col];
        if d.abs() < 1e-18 {
            continue; // (near-)singular; leave row — should not happen for these chains
        }
        for row in (col + 1)..n {
            let f = a[row][col] / d;
            if f != 0.0 {
                for k in col..n {
                    a[row][k] -= f * a[col][k];
                }
                b[row] -= f * b[col];
            }
        }
    }
    let mut x = vec![0.0; n];
    for i in (0..n).rev() {
        let mut s = b[i];
        for k in (i + 1)..n {
            s -= a[i][k] * x[k];
        }
        x[i] = if a[i][i].abs() < 1e-18 { 0.0 } else { s / a[i][i] };
    }
    x
}

/// Indices of transient (non-absorbing) states.
fn transient_states(absorb: &[bool]) -> Vec<usize> {
    (0..absorb.len()).filter(|&i| !absorb[i]).collect()
}

/// P(absorb in `target`-bearing states | start), via the embedded jump chain:
/// solve `(I − P_TT) x = P_TA` on the transient block, then sum the absorbing
/// states whose marking satisfies the target (a `freed` CLASS, like CSL `F φ`).
fn prob_reach(q: &[Vec<f64>], tang: &[String], start: usize, target: usize) -> f64 {
    let absorb = absorbing(q);
    if absorb[start] {
        return if dec(&tang[start])[target] > 0 { 1.0 } else { 0.0 };
    }
    let tr = transient_states(&absorb);
    let tpos: HashMap<usize, usize> = tr.iter().enumerate().map(|(k, &i)| (i, k)).collect();
    let m = tr.len();
    // embedded jump chain on transient rows (no self-jump: P[i][i] = 0)
    let jump = |i: usize, j: usize| if i == j { 0.0 } else { -q[i][j] / q[i][i] }; // q[i][i] < 0
    // (I − P_TT)
    let mut a = vec![vec![0.0; m]; m];
    for (r, &i) in tr.iter().enumerate() {
        for (c, &j) in tr.iter().enumerate() {
            a[r][c] = (if r == c { 1.0 } else { 0.0 }) - jump(i, j);
        }
    }
    // RHS: total one-step prob into target-bearing absorbing states.
    let b: Vec<f64> = tr
        .iter()
        .map(|&i| {
            (0..q.len())
                .filter(|&j| absorb[j] && dec(&tang[j])[target] > 0)
                .map(|j| jump(i, j))
                .sum()
        })
        .collect();
    let x = solve(a, b);
    x[tpos[&start]]
}

/// E[time to absorption | start]: `(I − P_TT) t = h`, `h_i = 1/(−Q_ii)`.
fn expected_time(q: &[Vec<f64>], start: usize) -> f64 {
    let absorb = absorbing(q);
    if absorb[start] {
        return 0.0;
    }
    let tr = transient_states(&absorb);
    let tpos: HashMap<usize, usize> = tr.iter().enumerate().map(|(k, &i)| (i, k)).collect();
    let m = tr.len();
    let jump = |i: usize, j: usize| if i == j { 0.0 } else { -q[i][j] / q[i][i] };
    let mut a = vec![vec![0.0; m]; m];
    for (r, &i) in tr.iter().enumerate() {
        for (c, &j) in tr.iter().enumerate() {
            a[r][c] = (if r == c { 1.0 } else { 0.0 }) - jump(i, j);
        }
    }
    let h: Vec<f64> = tr.iter().map(|&i| 1.0 / -q[i][i]).collect();
    let t = solve(a, h);
    t[tpos[&start]]
}

/// π(time) from `start` by uniformization: `Λ = max −Qᵢᵢ`, `Punif = I + Q/Λ`,
/// `π(t) = Σ_k e^{−Λt}(Λt)^k/k! · π₀ Punifᵏ`, truncated when the Poisson tail
/// is negligible.
fn transient(q: &[Vec<f64>], start: usize, time: f64) -> Vec<f64> {
    let n = q.len();
    let lam = (0..n).map(|i| -q[i][i]).fold(0.0f64, f64::max).max(1e-12);
    let punif: Vec<Vec<f64>> = (0..n)
        .map(|i| (0..n).map(|j| (if i == j { 1.0 } else { 0.0 }) + q[i][j] / lam).collect())
        .collect();
    let lt = lam * time;
    let mut vec0 = vec![0.0; n];
    vec0[start] = 1.0;
    let mut term = (-lt).exp(); // k = 0 weight
    let mut pi: Vec<f64> = vec0.iter().map(|&v| term * v).collect();
    let mut vec = vec0;
    let mut acc = term;
    let mut k = 0u32;
    while (1.0 - acc) > 1e-12 && k < 100_000 {
        k += 1;
        // vec = vec * Punif  (row-vector times matrix)
        let mut nv = vec![0.0; n];
        for i in 0..n {
            if vec[i] != 0.0 {
                for j in 0..n {
                    nv[j] += vec[i] * punif[i][j];
                }
            }
        }
        vec = nv;
        term *= lt / k as f64;
        for j in 0..n {
            pi[j] += term * vec[j];
        }
        acc += term;
    }
    pi
}

// --- parsing ----------------------------------------------------------------- //

pub fn parse(src: &str) -> Result<Gspn, String> {
    let doc = toml::parse(src)?;
    build(&doc)
}

fn build(doc: &Doc) -> Result<Gspn, String> {
    let places: Vec<String> = doc
        .scalar("places")
        .ok_or("GSPN requires a `places` array")?
        .as_arr("places")?
        .to_vec();
    if places.is_empty() {
        return Err("GSPN `places` is empty".into());
    }
    let index = |p: &str| places.iter().position(|x| x == p);

    let mode = doc.scalar("mode").and_then(|v| v.as_str("mode").ok()).unwrap_or("lease").to_string();

    // params (evaluated in declaration order; later may reference earlier).
    let mut params: HashMap<String, f64> = HashMap::new();
    for (i, p) in doc.table("param").iter().enumerate() {
        let name = p.get("name").ok_or_else(|| format!("param {i}: missing `name`"))?.as_str("name")?.to_string();
        let expr = p.get("value").ok_or_else(|| format!("param {i}: missing `value`"))?.as_str("value")?;
        let v = eval_expr(expr, &params).map_err(|e| format!("param `{name}`: {e}"))?;
        params.insert(name, v);
    }

    let initial = parse_marking(
        doc.scalar("initial").ok_or("GSPN requires an `initial` marking")?.as_str("initial")?,
        &places,
        &index,
    )?;

    let mut transitions = Vec::new();
    for (i, t) in doc.table("transition").iter().enumerate() {
        let name = t.get("name").ok_or_else(|| format!("transition {i}: missing `name`"))?.as_str("name")?.to_string();
        let kind = t.get("kind").ok_or_else(|| format!("transition `{name}`: missing `kind`"))?.as_str("kind")?;
        let immediate = match kind {
            "immediate" => true,
            "timed" => false,
            other => return Err(format!("transition `{name}`: kind must be immediate/timed, found `{other}`")),
        };
        let rate_or_weight = if immediate {
            t.get("weight").map(|v| v.as_str("weight")).transpose()?.map(|s| eval_expr(s, &params)).transpose().map_err(|e| format!("transition `{name}`: {e}"))?.unwrap_or(1.0)
        } else {
            let s = t.get("rate").ok_or_else(|| format!("timed transition `{name}`: missing `rate`"))?.as_str("rate")?;
            eval_expr(s, &params).map_err(|e| format!("transition `{name}`: {e}"))?
        };
        let pre = parse_marking(t.get("pre").map(|v| v.as_str("pre")).transpose()?.unwrap_or(""), &places, &index)?;
        let post = parse_marking(t.get("post").map(|v| v.as_str("post")).transpose()?.unwrap_or(""), &places, &index)?;
        let inhibit: Vec<usize> = t
            .get("inhibit")
            .map(|v| v.as_str("inhibit"))
            .transpose()?
            .unwrap_or("")
            .split(',')
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .map(|p| index(p).ok_or_else(|| format!("transition `{name}`: inhibit place `{p}` not declared")))
            .collect::<Result<_, String>>()?;
        transitions.push(GTrans { name, immediate, rate_or_weight, pre, post, inhibit });
    }
    if transitions.is_empty() {
        return Err("GSPN has no transitions".into());
    }

    let mut queries = Vec::new();
    for (i, qd) in doc.table("query").iter().enumerate() {
        let name = qd.get("name").map(|v| v.as_str("name")).transpose()?.unwrap_or("query").to_string();
        let compute = match qd.get("compute").ok_or_else(|| format!("query {i}: missing `compute`"))?.as_str("compute")? {
            "prob" => Compute::Prob,
            "etime" => Compute::Etime,
            "transient" => Compute::Transient,
            other => return Err(format!("query {i}: compute must be prob/etime/transient, found `{other}`")),
        };
        let target = qd.get("target").map(|v| v.as_str("target")).transpose()?.map(|p| index(p).ok_or_else(|| format!("query {i}: target place `{p}` not declared"))).transpose()?;
        let time = qd.get("time").map(|v| v.as_str("time")).transpose()?.map(|s| s.parse::<f64>().map_err(|_| format!("query {i}: bad `time`"))).transpose()?;
        queries.push(Query { name, compute, target, time });
    }

    Ok(Gspn { places, transitions, initial, mode, queries })
}

fn parse_marking(s: &str, places: &[String], index: &impl Fn(&str) -> Option<usize>) -> Result<Vec<u32>, String> {
    let mut m = vec![0u32; places.len()];
    for piece in s.split(',') {
        let p = piece.trim();
        if p.is_empty() {
            continue;
        }
        let (place, count) = p.split_once(':').ok_or_else(|| format!("marking `{p}` must be place:count"))?;
        let i = index(place.trim()).ok_or_else(|| format!("marking: place `{place}` not declared"))?;
        m[i] = count.trim().parse().map_err(|_| format!("marking: bad count in `{p}`"))?;
    }
    Ok(m)
}

// --- a tiny arithmetic evaluator for rate/param expressions ------------------ //

fn eval_expr(s: &str, vars: &HashMap<String, f64>) -> Result<f64, String> {
    let toks = lex(s);
    let mut p = 0;
    let v = expr(&toks, &mut p, vars)?;
    if p != toks.len() {
        return Err(format!("unexpected token in `{s}`"));
    }
    Ok(v)
}

fn lex(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        if "+-*/()".contains(c) {
            if !cur.trim().is_empty() {
                out.push(cur.trim().to_string());
            }
            cur.clear();
            out.push(c.to_string());
        } else if c.is_whitespace() {
            if !cur.trim().is_empty() {
                out.push(cur.trim().to_string());
            }
            cur.clear();
        } else {
            cur.push(c);
        }
    }
    if !cur.trim().is_empty() {
        out.push(cur.trim().to_string());
    }
    out
}

fn expr(t: &[String], p: &mut usize, vars: &HashMap<String, f64>) -> Result<f64, String> {
    let mut v = term(t, p, vars)?;
    while let Some(op) = t.get(*p) {
        match op.as_str() {
            "+" => { *p += 1; v += term(t, p, vars)?; }
            "-" => { *p += 1; v -= term(t, p, vars)?; }
            _ => break,
        }
    }
    Ok(v)
}

fn term(t: &[String], p: &mut usize, vars: &HashMap<String, f64>) -> Result<f64, String> {
    let mut v = factor(t, p, vars)?;
    while let Some(op) = t.get(*p) {
        match op.as_str() {
            "*" => { *p += 1; v *= factor(t, p, vars)?; }
            "/" => { *p += 1; v /= factor(t, p, vars)?; }
            _ => break,
        }
    }
    Ok(v)
}

fn factor(t: &[String], p: &mut usize, vars: &HashMap<String, f64>) -> Result<f64, String> {
    let tok = t.get(*p).ok_or("unexpected end of expression")?.clone();
    *p += 1;
    match tok.as_str() {
        "(" => {
            let v = expr(t, p, vars)?;
            if t.get(*p).map(|s| s.as_str()) != Some(")") {
                return Err("expected `)`".into());
            }
            *p += 1;
            Ok(v)
        }
        "-" => Ok(-factor(t, p, vars)?),
        s => {
            if let Ok(n) = s.parse::<f64>() {
                Ok(n)
            } else {
                vars.get(s).copied().ok_or_else(|| format!("unknown identifier `{s}`"))
            }
        }
    }
}
