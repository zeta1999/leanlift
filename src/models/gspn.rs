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

use super::ir::{BoundProp, PtNet, PtTrans};
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
    pub trans: Option<usize>,  // transition index (throughput)
    pub time: Option<f64>,     // transient horizon, or the level for `Full`
}

pub enum Compute {
    // Transient / absorption (the original GSPN queries).
    Prob,
    Etime,
    Transient,
    // Steady-state queued-performance metrics (PLAN-perf-demo §D2). Defined on an
    // ERGODIC tangible CTMC (no absorbing state); evaluate to NaN otherwise.
    Mean,       // E[tokens in `target` place]  (queue length L)
    Throughput, // steady firing rate of `trans` (departures X); W = L/X via Little
    Full,       // P(tokens in `target` ≥ `time`)  (overflow / blocking)
}

pub struct Gspn {
    pub places: Vec<String>,
    pub transitions: Vec<GTrans>,
    pub initial: Vec<u32>,
    pub mode: String,
    pub queries: Vec<Query>,
    /// Conserved place subset for the qualitative place-invariant proof (the
    /// underlying P/T-net view); declared `conserved = [...]`, default all places.
    pub conserved: Option<Vec<usize>>,
    /// Declared upper-bound safety properties (`sum(places) ≤ max`), proved in
    /// Lean as a corollary of the conserved-mass invariant (`lift model prove`).
    pub bounds: Vec<BoundProp>,
}

impl Gspn {
    /// The underlying P/T-net view (qualitative): drop rates / immediate-vs-timed
    /// / inhibitor arcs, keep pre/post. SOUND for an UPPER-BOUND place invariant —
    /// ignoring inhibitors only ADMITS more firings, so a bound proved on this
    /// (larger) reachable set holds on the real, inhibited net too. Feeds
    /// `lean::emit_petri` for the model→Lean qualitative proof (PLAN-perf-demo).
    pub fn to_ptnet(&self) -> PtNet {
        let transitions = self
            .transitions
            .iter()
            .map(|t| PtTrans { name: t.name.clone(), pre: t.pre.clone(), post: t.post.clone() })
            .collect();
        PtNet {
            places: self.places.clone(),
            transitions,
            initial: self.initial.clone(),
            bound: 64,
            bounds: self.bounds.clone(),
            conserved: self.conserved.clone(),
        }
    }
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

    /// Detect an immediate-transition cycle among vanishing markings (a "timeless
    /// trap"): the CTMC is then ill-defined and vanishing elimination would
    /// silently drop probability mass. Fail loudly instead. DFS (three-colour)
    /// over the immediate-only edge graph restricted to vanishing markings.
    pub fn has_immediate_cycle(&self) -> bool {
        let mut color: HashMap<String, u8> = HashMap::new(); // 0=unseen 1=on-stack 2=done
        for n in self.all_markings() {
            if self.is_vanishing(&dec(&n)) && color.get(&n).copied().unwrap_or(0) == 0 {
                if self.imm_dfs(&n, &mut color) {
                    return true;
                }
            }
        }
        false
    }

    fn imm_dfs(&self, node: &str, color: &mut HashMap<String, u8>) -> bool {
        color.insert(node.to_string(), 1);
        let m = dec(node);
        for t in &self.transitions {
            if t.immediate && self.enabled_at(&m, t) {
                let to = enc(&self.fire(&m, t));
                if self.is_vanishing(&dec(&to)) {
                    match color.get(&to).copied().unwrap_or(0) {
                        1 => return true, // back-edge into the current stack → cycle
                        0 if self.imm_dfs(&to, color) => return true,
                        _ => {}
                    }
                }
            }
        }
        color.insert(node.to_string(), 2);
        false
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
            // --- steady-state metrics (ergodic chain only) ------------------ //
            Compute::Mean | Compute::Throughput | Compute::Full => {
                // Steady state is start-independent, but it requires ergodicity:
                // an absorbing tangible state means no stationary law over it.
                if absorbing(gen).iter().any(|&a| a) {
                    return f64::NAN;
                }
                let pi = steady_state(gen);
                match q.compute {
                    Compute::Mean => {
                        let tgt = q.target.expect("mean query needs a target place");
                        tang.iter().enumerate().map(|(j, m)| pi[j] * dec(m)[tgt] as f64).sum()
                    }
                    Compute::Full => {
                        let tgt = q.target.expect("full query needs a target place");
                        let level = q.time.expect("full query needs a `time` level") as u32;
                        tang.iter().enumerate().filter(|(_, m)| dec(m)[tgt] >= level).map(|(j, _)| pi[j]).sum()
                    }
                    Compute::Throughput => {
                        let ti = q.trans.expect("throughput query needs a transition");
                        let t = &self.transitions[ti];
                        tang.iter()
                            .enumerate()
                            .filter(|(_, m)| self.enabled_at(&dec(m), t))
                            .map(|(j, _)| pi[j] * t.rate_or_weight)
                            .sum()
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    /// Stochastic-simulation (SSA / Gillespie) estimate of the steady-state query
    /// values — the EMPIRICAL cross-check of the analytic CTMC (PLAN-perf-demo
    /// §D4). Timed transitions race (exponential with their rate); immediate
    /// transitions fire in zero time (vanishing). `mean`/`full` are time-averaged
    /// over tangible sojourns; `throughput` is firings ÷ simulated time.
    pub(crate) fn simulate(&self, queries: &[Query], horizon: f64, seed: u64) -> Vec<f64> {
        let mut rng = SsaRng(seed | 1);
        let mut m = self.initial.clone();
        self.settle_immediate(&mut m, &mut rng);
        let mut t = 0.0f64;
        let mut acc = vec![0.0f64; queries.len()];
        let mut fires = vec![0u64; self.transitions.len()];
        while t < horizon {
            let timed: Vec<(usize, f64)> = self
                .transitions
                .iter()
                .enumerate()
                .filter(|(_, tr)| !tr.immediate && self.enabled_at(&m, tr))
                .map(|(i, tr)| (i, tr.rate_or_weight))
                .collect();
            let rtot: f64 = timed.iter().map(|&(_, r)| r).sum();
            if rtot <= 0.0 {
                break; // absorbing / deadlock
            }
            let dt = -(1.0 - rng.f()).ln() / rtot; // exponential sojourn
            for (qi, q) in queries.iter().enumerate() {
                acc[qi] += dt * self.sample_metric(q, &m);
            }
            let mut x = rng.f() * rtot;
            let mut chosen = timed[0].0;
            for &(i, r) in &timed {
                if x < r {
                    chosen = i;
                    break;
                }
                x -= r;
            }
            fires[chosen] += 1;
            m = self.fire(&m, &self.transitions[chosen]);
            self.settle_immediate(&mut m, &mut rng);
            t += dt;
        }
        queries
            .iter()
            .enumerate()
            .map(|(qi, q)| match q.compute {
                Compute::Throughput => fires[q.trans.expect("throughput needs a transition")] as f64 / t,
                _ => acc[qi] / t,
            })
            .collect()
    }

    /// Fire enabled immediate transitions (weighted choice) until none remain —
    /// the simulation's vanishing-marking resolution. Bounded to break timeless
    /// traps.
    fn settle_immediate(&self, m: &mut Vec<u32>, rng: &mut SsaRng) {
        for _ in 0..10_000 {
            let imm: Vec<(usize, f64)> = self
                .transitions
                .iter()
                .enumerate()
                .filter(|(_, tr)| tr.immediate && self.enabled_at(m, tr))
                .map(|(i, tr)| (i, tr.rate_or_weight))
                .collect();
            if imm.is_empty() {
                return;
            }
            let wtot: f64 = imm.iter().map(|&(_, w)| w).sum();
            let mut x = rng.f() * wtot;
            let mut chosen = imm[0].0;
            for &(i, w) in &imm {
                if x < w {
                    chosen = i;
                    break;
                }
                x -= w;
            }
            *m = self.fire(m, &self.transitions[chosen]);
        }
    }

    /// The instantaneous contribution of `q` at marking `m` (for time-averaging).
    fn sample_metric(&self, q: &Query, m: &[u32]) -> f64 {
        match q.compute {
            Compute::Mean => m[q.target.expect("mean target")] as f64,
            Compute::Full => {
                let lvl = q.time.expect("full level") as u32;
                if m[q.target.expect("full target")] >= lvl {
                    1.0
                } else {
                    0.0
                }
            }
            _ => 0.0, // throughput is firing-count based, not time-averaged
        }
    }
}

/// A tiny xorshift PRNG for the SSA simulator (uniform [0,1)); deterministic per
/// seed so simulation cross-checks are reproducible.
struct SsaRng(u64);
impl SsaRng {
    fn f(&mut self) -> f64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 11) as f64 / (1u64 << 53) as f64
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

/// Stationary distribution π of an IRREDUCIBLE CTMC generator `q` (πQ = 0,
/// Σπ = 1), by the **GTH (Grassmann–Taksar–Heyman) state-reduction** algorithm:
/// Gaussian elimination performed with NO subtractions — every update sums
/// non-negative quantities — so it is numerically stable even for stiff
/// generators (PLAN-perf-demo §D1, the steady-state mode the queued performance
/// metrics need). `q` must be conservative: `q[i][j] ≥ 0` off-diagonal, each row
/// summing to 0; the diagonal is never read. Drives the queued-performance
/// metrics (`mean`/`throughput`/`full`) in `evaluate` (PLAN-perf-demo §D2).
pub(crate) fn steady_state(q: &[Vec<f64>]) -> Vec<f64> {
    let n = q.len();
    if n == 0 {
        return Vec::new();
    }
    if n == 1 {
        return vec![1.0];
    }
    // Work on a copy of the off-diagonal rates; the diagonal is unused.
    let mut a: Vec<Vec<f64>> = q.iter().map(|r| r.clone()).collect();

    // Reduction: fold state `e` into the survivors {0..e-1}, e = n-1 … 1.
    for e in (1..n).rev() {
        let s: f64 = (0..e).map(|j| a[e][j]).sum(); // outflow of e into survivors
        if s <= 0.0 {
            continue; // not reachable among survivors (shouldn't happen if irreducible)
        }
        // Fold the detour through e: q[i][j] += rate(i→e) · prob(e→j). Uses the
        // RAW column rate a[i][e] and the RAW row a[e][j], dividing by s — only
        // sums of non-negative terms, so no cancellation (GTH's stability).
        for i in 0..e {
            let aie = a[i][e];
            if aie != 0.0 {
                for j in 0..e {
                    a[i][j] += aie * a[e][j] / s;
                }
            }
        }
        // Normalise the column for the back-substitution: prob(i→e).
        for i in 0..e {
            a[i][e] /= s;
        }
    }

    // Back-substitution: π over states 0..n-1 (unnormalised), then normalise.
    let mut pi = vec![0.0; n];
    pi[0] = 1.0;
    for k in 1..n {
        pi[k] = (0..k).map(|i| pi[i] * a[i][k]).sum();
    }
    let total: f64 = pi.iter().sum();
    if total > 0.0 {
        for x in pi.iter_mut() {
            *x /= total;
        }
    }
    pi
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

/// No-override convenience entry (used by the test suite; production goes through
/// `parse_with` so `--set` can override params).
#[allow(dead_code)]
pub fn parse(src: &str) -> Result<Gspn, String> {
    parse_with(src, &HashMap::new())
}

/// Like `parse`, but `overrides` replace named `[[param]]` values before
/// evaluation — so dependent params recompute (e.g. overriding `p` recomputes
/// `mu_l = mu_d·p/(1-p)`). Backs `lift model … --set name=value`, the knob the
/// performance sweep turns (PLAN-perf-demo §D3).
pub fn parse_with(src: &str, overrides: &HashMap<String, f64>) -> Result<Gspn, String> {
    let doc = toml::parse(src)?;
    build_with(&doc, overrides)
}

fn build_with(doc: &Doc, overrides: &HashMap<String, f64>) -> Result<Gspn, String> {
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
        // An override replaces the file value (dependents still recompute below).
        let v = match overrides.get(&name) {
            Some(&ov) => ov,
            None => eval_expr(expr, &params).map_err(|e| format!("param `{name}`: {e}"))?,
        };
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
            "mean" => Compute::Mean,
            "throughput" => Compute::Throughput,
            "full" => Compute::Full,
            other => {
                return Err(format!(
                    "query {i}: compute must be prob/etime/transient/mean/throughput/full, found `{other}`"
                ))
            }
        };
        let target = qd.get("target").map(|v| v.as_str("target")).transpose()?.map(|p| index(p).ok_or_else(|| format!("query {i}: target place `{p}` not declared"))).transpose()?;
        let trans = qd
            .get("transition")
            .map(|v| v.as_str("transition"))
            .transpose()?
            .map(|tn| {
                transitions
                    .iter()
                    .position(|t| t.name == tn)
                    .ok_or_else(|| format!("query {i}: transition `{tn}` not declared"))
            })
            .transpose()?;
        let time = qd.get("time").map(|v| v.as_str("time")).transpose()?.map(|s| s.parse::<f64>().map_err(|_| format!("query {i}: bad `time`"))).transpose()?;
        queries.push(Query { name, compute, target, trans, time });
    }

    // Qualitative-proof declarations (the underlying P/T-net view): an optional
    // conserved subsystem and declared upper-bound safety properties.
    let conserved = match doc.scalar("conserved") {
        Some(v) => Some(
            v.as_arr("conserved")?
                .iter()
                .map(|p| index(p).ok_or_else(|| format!("conserved: place `{p}` not declared")))
                .collect::<Result<_, String>>()?,
        ),
        None => None,
    };
    let mut bounds = Vec::new();
    for (i, b) in doc.table("bound").iter().enumerate() {
        let name = b.get("name").map(|v| v.as_str("name")).transpose()?.unwrap_or("bound").to_string();
        let max: u32 = b
            .get("max")
            .ok_or_else(|| format!("bound {i}: missing `max`"))?
            .as_str("max")?
            .parse()
            .map_err(|_| format!("bound {i}: `max` must be an integer"))?;
        let idxs: Vec<usize> = b
            .get("places")
            .ok_or_else(|| format!("bound {i}: missing `places`"))?
            .as_arr("places")?
            .iter()
            .map(|p| index(p).ok_or_else(|| format!("bound {i}: place `{p}` not declared")))
            .collect::<Result<_, String>>()?;
        bounds.push(BoundProp { name, places: idxs, max });
    }

    Ok(Gspn { places, transitions, initial, mode, queries, conserved, bounds })
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

#[cfg(test)]
mod tests {
    use super::*;

    fn eval(src: &str, name: &str) -> f64 {
        let net = parse(src).expect("parse");
        let (tang, q) = net.ctmc();
        let qy = net.queries.iter().find(|x| x.name == name).expect("query");
        net.evaluate(qy, &tang, &q)
    }

    /// `K` budget tokens; `mode` lease|giveup. The day49 dock GSPN as a string.
    fn dock(k: u32, p: f64, mode: &str) -> String {
        let abort = if mode == "giveup" {
            "[[transition]]\nname=\"abort\"\nkind=\"timed\"\nrate=\"mu_l\"\npre=\"inflight:1\"\ninhibit=\"budget\"\npost=\"stuck:1\"\n"
        } else {
            ""
        };
        format!(
            "kind=\"gspn\"\nmode=\"{mode}\"\nplaces=[\"holding\",\"inflight\",\"freed\",\"budget\",\"stuck\"]\n\
             initial=\"holding:1, budget:{k}\"\n\
             [[param]]\nname=\"mu_d\"\nvalue=\"1.0\"\n[[param]]\nname=\"p\"\nvalue=\"{p}\"\n\
             [[param]]\nname=\"mu_l\"\nvalue=\"mu_d * p / (1 - p)\"\n\
             [[transition]]\nname=\"send\"\nkind=\"immediate\"\nweight=\"1.0\"\npre=\"holding:1\"\npost=\"inflight:1\"\n\
             [[transition]]\nname=\"deliver\"\nkind=\"timed\"\nrate=\"mu_d\"\npre=\"inflight:1\"\npost=\"freed:1\"\n\
             [[transition]]\nname=\"lose\"\nkind=\"timed\"\nrate=\"mu_l\"\npre=\"inflight:1, budget:1\"\npost=\"holding:1\"\n\
             {abort}\
             [[query]]\nname=\"P\"\ncompute=\"prob\"\ntarget=\"freed\"\n\
             [[query]]\nname=\"E\"\ncompute=\"etime\"\n\
             [[query]]\nname=\"T\"\ncompute=\"transient\"\ntarget=\"freed\"\ntime=\"5\"\n"
        )
    }

    #[test]
    fn lease_absorbs_with_probability_one() {
        // Lease: delivery is forced ⇒ P(freed)=1, E[time]=1/μd=1 (indep. of K,p).
        for &k in &[0u32, 1, 3, 5] {
            for &p in &[0.2, 0.5, 0.8] {
                let s = dock(k, p, "lease");
                assert!((eval(&s, "P") - 1.0).abs() < 1e-9, "P lease K={k} p={p}");
                assert!((eval(&s, "E") - 1.0).abs() < 1e-9, "E lease K={k} p={p}");
            }
        }
    }

    #[test]
    fn lease_transient_matches_exponential() {
        // P(freed ≤ T) = 1 − e^(−μd·T), μd=1, T=5.
        let s = dock(3, 0.5, "lease");
        let expected = 1.0 - (-5.0f64).exp();
        assert!((eval(&s, "T") - expected).abs() < 1e-4);
    }

    #[test]
    fn giveup_coverage_closed_form() {
        // Giveup: P(freed) = 1 − p^(K+1) (the day48 coverage).
        for &k in &[0u32, 1, 3, 5] {
            for &p in &[0.2, 0.5, 0.8] {
                let s = dock(k, p, "giveup");
                let expected = 1.0 - p.powi(k as i32 + 1);
                assert!((eval(&s, "P") - expected).abs() < 1e-9, "coverage K={k} p={p}");
            }
        }
    }

    #[test]
    fn detects_immediate_cycle() {
        // Two immediate transitions a→b, b→a form a timeless trap.
        let looped = "kind=\"gspn\"\nplaces=[\"a\",\"b\"]\ninitial=\"a:1\"\n\
            [[transition]]\nname=\"ab\"\nkind=\"immediate\"\nweight=\"1\"\npre=\"a:1\"\npost=\"b:1\"\n\
            [[transition]]\nname=\"ba\"\nkind=\"immediate\"\nweight=\"1\"\npre=\"b:1\"\npost=\"a:1\"\n";
        assert!(parse(looped).unwrap().has_immediate_cycle());
        // The dock GSPN (one immediate `send` into a tangible marking) has none.
        assert!(!parse(&dock(3, 0.5, "lease")).unwrap().has_immediate_cycle());
    }

    #[test]
    fn expr_evaluator() {
        let mut v = HashMap::new();
        v.insert("a".to_string(), 2.0);
        assert_eq!(eval_expr("1 + 2 * 3", &v).unwrap(), 7.0);
        assert_eq!(eval_expr("(1 + 2) * 3", &v).unwrap(), 9.0);
        assert_eq!(eval_expr("a * a / (1 - 0.5)", &v).unwrap(), 8.0);
        assert!(eval_expr("nope", &v).is_err());
    }

    // --- V1.4: CTMC solver outputs finite & in range (PLAN-verification) ----- //

    /// A tiny seeded xorshift PRNG (test-local; mirrors proptest.rs's).
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn upto(&mut self, n: usize) -> usize {
            (self.next() as usize) % n.max(1)
        }
        /// A float in [0, 1).
        fn f(&mut self) -> f64 {
            (self.next() >> 11) as f64 / (1u64 << 53) as f64
        }
    }

    /// A random, well-posed absorbing CTMC generator: states `0` and `n-1` are
    /// absorbing (rows all zero); only `n-1` "bears the target" (place 0). Every
    /// transient state has a forced positive rate to `n-1`, so absorption is a.s.
    /// reachable ⇒ `expected_time` is finite and `prob_reach` is well-defined.
    /// Returns `(q, tang, transient_indices)`.
    fn random_generator(r: &mut Rng) -> (Vec<Vec<f64>>, Vec<String>, Vec<usize>) {
        let n = 3 + r.upto(3); // 3..=5
        let mut q = vec![vec![0.0; n]; n];
        for i in 1..n - 1 {
            // forced exit toward the absorber n-1 (guarantees absorption)
            q[i][n - 1] = 0.1 + r.f();
            // optional rate to the other absorber 0
            q[i][0] = r.f();
            // rates among transient states
            for j in 1..n - 1 {
                if j != i && r.upto(2) == 0 {
                    q[i][j] = r.f();
                }
            }
            let off: f64 = (0..n).filter(|&j| j != i).map(|j| q[i][j]).sum();
            q[i][i] = -off;
        }
        // tang: only state n-1 carries a token in place 0 ("freed"); rest empty.
        let tang: Vec<String> = (0..n).map(|i| if i == n - 1 { "1".to_string() } else { "0".to_string() }).collect();
        let trans: Vec<usize> = (1..n - 1).collect();
        (q, tang, trans)
    }

    #[test]
    fn ctmc_outputs_finite_and_in_range() {
        let mut r = Rng(0xC7_3C_5E_9A_11_22_33_44);
        let mut nontrivial = 0u32; // prob strictly inside (0,1) ⇒ non-vacuous
        for _ in 0..2000 {
            let (q, tang, trans) = random_generator(&mut r);
            for &start in &trans {
                // prob_reach ∈ [0,1], finite.
                let p = prob_reach(&q, &tang, start, 0);
                assert!(p.is_finite(), "prob_reach not finite: {p}");
                assert!((-1e-9..=1.0 + 1e-9).contains(&p), "prob_reach out of [0,1]: {p}");
                if (0.01..=0.99).contains(&p) {
                    nontrivial += 1;
                }
                // expected_time finite and ≥ 0.
                let et = expected_time(&q, start);
                assert!(et.is_finite() && et >= -1e-9, "expected_time bad: {et}");
                // transient: a sub-distribution (each ∈[0,1], Σ ≤ 1), all finite.
                for &t in &[0.0, 0.5, 3.0] {
                    let pi = transient(&q, start, t);
                    let mut sum = 0.0;
                    for &x in &pi {
                        assert!(x.is_finite(), "transient entry not finite: {x}");
                        assert!((-1e-9..=1.0 + 1e-6).contains(&x), "transient entry out of [0,1]: {x}");
                        sum += x;
                    }
                    assert!(sum <= 1.0 + 1e-6, "transient mass > 1: {sum}");
                    if t == 0.0 {
                        assert!((pi[start] - 1.0).abs() < 1e-9, "π(0) not a point mass at start");
                    }
                }
            }
        }
        assert!(nontrivial > 100, "CTMC test near-vacuous: only {nontrivial} probs strictly in (0,1)");
    }

    #[test]
    fn solve_never_panics_on_finite_input() {
        // `solve` must not panic on any finite k×k system (it may return garbage
        // for a singular matrix, but must not crash). Random, often-singular.
        use std::panic::{self, AssertUnwindSafe};
        let prev = panic::take_hook();
        panic::set_hook(Box::new(|_| {}));
        let mut r = Rng(0x5A_5A_0F_F0_DE_AD_BE_EF);
        let mut failed: Option<String> = None;
        'outer: for _ in 0..3000 {
            let k = 1 + r.upto(5);
            let a: Vec<Vec<f64>> = (0..k)
                .map(|_| (0..k).map(|_| (r.f() - 0.5) * if r.upto(4) == 0 { 0.0 } else { 10.0 }).collect())
                .collect();
            let b: Vec<f64> = (0..k).map(|_| (r.f() - 0.5) * 10.0).collect();
            if panic::catch_unwind(AssertUnwindSafe(|| {
                let x = solve(a.clone(), b.clone());
                x.len()
            }))
            .is_err()
            {
                failed = Some(format!("solve panicked on k={k}"));
                break 'outer;
            }
        }
        panic::set_hook(prev);
        assert!(failed.is_none(), "{}", failed.unwrap());
    }

    // --- D1: steady-state solver (PLAN-perf-demo) --------------------------- //

    /// The M/M/1/K generator: birth rate λ (i→i+1, i<K), death rate μ (i→i-1).
    fn mm1k(lambda: f64, mu: f64, k: usize) -> Vec<Vec<f64>> {
        let n = k + 1;
        let mut q = vec![vec![0.0; n]; n];
        for i in 0..n {
            if i < k {
                q[i][i + 1] = lambda;
                q[i][i] -= lambda;
            }
            if i > 0 {
                q[i][i - 1] = mu;
                q[i][i] -= mu;
            }
        }
        q
    }

    #[test]
    fn steady_state_matches_mm1k_closed_form() {
        // π_i = ρ^i (1-ρ)/(1-ρ^{K+1}), ρ=λ/μ — the textbook M/M/1/K stationary.
        for &(lambda, mu) in &[(0.5, 1.0), (0.9, 1.0), (0.3, 1.2), (1.5, 1.0)] {
            for &k in &[1usize, 2, 5, 10] {
                let pi = steady_state(&mm1k(lambda, mu, k));
                let rho = lambda / mu;
                let pi0 = (1.0 - rho) / (1.0 - rho.powi(k as i32 + 1));
                for (i, &p) in pi.iter().enumerate() {
                    let want = rho.powi(i as i32) * pi0;
                    assert!((p - want).abs() < 1e-9, "λ={lambda} μ={mu} K={k} i={i}: {p} vs {want}");
                }
            }
        }
    }

    /// A random irreducible birth–death generator (always has a unique π).
    fn random_bd(r: &mut Rng, n: usize) -> Vec<Vec<f64>> {
        let mut q = vec![vec![0.0; n]; n];
        for i in 0..n {
            if i + 1 < n {
                let lam = 0.1 + r.f();
                q[i][i + 1] = lam;
                q[i][i] -= lam;
            }
            if i > 0 {
                let mu = 0.1 + r.f();
                q[i][i - 1] = mu;
                q[i][i] -= mu;
            }
        }
        q
    }

    #[test]
    fn queued_metrics_match_mm1k() {
        // M/M/1/K as an ergodic GSPN: jobs `q` + free slots `s` (q+s=K), arrive
        // (λ, needs a slot) / serve (μ). Validate the D2 steady-state metrics —
        // mean (L), throughput (X), P(full) — vs the M/M/1/K closed form, plus
        // flow balance (X = admitted arrivals) and Little's law.
        let src = |lam: f64, mu: f64, k: u32| {
            format!(
                "kind=\"gspn\"\nplaces=[\"q\",\"s\"]\ninitial=\"s:{k}\"\n\
                 [[param]]\nname=\"lam\"\nvalue=\"{lam}\"\n[[param]]\nname=\"mu\"\nvalue=\"{mu}\"\n\
                 [[transition]]\nname=\"arrive\"\nkind=\"timed\"\nrate=\"lam\"\npre=\"s:1\"\npost=\"q:1\"\n\
                 [[transition]]\nname=\"serve\"\nkind=\"timed\"\nrate=\"mu\"\npre=\"q:1\"\npost=\"s:1\"\n\
                 [[query]]\nname=\"L\"\ncompute=\"mean\"\ntarget=\"q\"\n\
                 [[query]]\nname=\"X\"\ncompute=\"throughput\"\ntransition=\"serve\"\n\
                 [[query]]\nname=\"Pfull\"\ncompute=\"full\"\ntarget=\"q\"\ntime=\"{k}\"\n"
            )
        };
        for &(lam, mu) in &[(0.5, 1.0), (0.9, 1.0), (0.3, 1.5)] {
            for &k in &[1u32, 3, 6] {
                let net = parse(&src(lam, mu, k)).expect("parse");
                let (tang, gen) = net.ctmc();
                let val = |name: &str| {
                    let qq = net.queries.iter().find(|x| x.name == name).unwrap();
                    net.evaluate(qq, &tang, &gen)
                };
                let rho = lam / mu;
                let pi0 = (1.0 - rho) / (1.0 - rho.powi(k as i32 + 1));
                let pi = |i: u32| rho.powi(i as i32) * pi0;
                let l_cf: f64 = (0..=k).map(|i| i as f64 * pi(i)).sum();
                assert!((val("L") - l_cf).abs() < 1e-6, "L λ={lam} μ={mu} K={k}: {} vs {l_cf}", val("L"));
                assert!((val("X") - mu * (1.0 - pi(0))).abs() < 1e-6, "X (=μ·P(q≥1))");
                assert!((val("X") - lam * (1.0 - pi(k))).abs() < 1e-6, "flow balance X=λ(1−π_K)");
                assert!((val("Pfull") - pi(k)).abs() < 1e-6, "Pfull = π_K");
                let w = val("L") / val("X"); // Little
                assert!(w > 0.0 && w.is_finite(), "Little W finite");
            }
        }
    }

    #[test]
    fn simulation_matches_analytic_link() {
        // D4 empirical cross-check: SSA simulation of the link model must agree
        // with the analytic CTMC steady-state metrics — in BOTH the stable
        // (p=0.3) and congested (p=0.9) regimes. (Monte-Carlo tolerance.)
        let src = std::fs::read_to_string("examples/models/link.model.toml").expect("read link model");
        for &p in &[0.3f64, 0.9] {
            let mut ov = HashMap::new();
            ov.insert("p".to_string(), p);
            let net = parse_with(&src, &ov).expect("parse");
            let (tang, gen) = net.ctmc();
            let analytic: Vec<f64> = net.queries.iter().map(|q| net.evaluate(q, &tang, &gen)).collect();
            let sim = net.simulate(&net.queries, 300_000.0, 0xC0FFEE ^ (p * 1000.0) as u64);
            for (i, q) in net.queries.iter().enumerate() {
                let (a, s) = (analytic[i], sim[i]);
                let tol = (0.08 * a.abs()).max(0.03); // 8% relative, abs floor
                assert!((a - s).abs() <= tol, "{} (p={p}): analytic {a:.4} vs sim {s:.4} (tol {tol:.4})", q.name);
            }
        }
    }

    #[test]
    fn steady_metric_on_absorbing_chain_is_nan() {
        // A steady-state metric is undefined on a non-ergodic chain (absorbing
        // state) ⇒ NaN, never a bogus number. The dock-gspn `freed` is absorbing.
        let net = parse(&dock(3, 0.5, "lease")).unwrap();
        let (tang, gen) = net.ctmc();
        let qq = Query { name: "L".into(), compute: Compute::Mean, target: Some(0), trans: None, time: None };
        assert!(net.evaluate(&qq, &tang, &gen).is_nan());
    }

    #[test]
    fn steady_state_is_a_valid_stationary_distribution() {
        let mut r = Rng(0xD15_7B_17_10_5EE_DA7Au64);
        for _ in 0..2000 {
            let n = 2 + r.upto(6); // 2..=7 states
            let q = random_bd(&mut r, n);
            let pi = steady_state(&q);
            // (1) a probability vector
            assert!((pi.iter().sum::<f64>() - 1.0).abs() < 1e-9, "Σπ ≠ 1");
            assert!(pi.iter().all(|&p| p >= -1e-12 && p.is_finite()), "π not ≥ 0 / finite");
            // (2) the defining equation πQ = 0 (every column residual ~ 0)
            for j in 0..n {
                let resid: f64 = (0..n).map(|i| pi[i] * q[i][j]).sum();
                assert!(resid.abs() < 1e-9, "πQ residual {resid} in col {j}");
            }
            // (3) detailed balance for birth–death: π_i·λ_i = π_{i+1}·μ_{i+1}
            for i in 0..n - 1 {
                let up = pi[i] * q[i][i + 1];
                let down = pi[i + 1] * q[i + 1][i];
                assert!((up - down).abs() < 1e-9, "detailed balance broken at {i}");
            }
        }
    }
}
