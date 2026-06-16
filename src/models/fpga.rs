//! FPGA frontend — ingest an Aria-HDL **IR-JSON** export (`aria-hdl
//! --emit-ir-json`, schema `aria-ir-json/v1`) and project it onto leanlift's
//! verification families. See `docs/PLAN-fpga.md` and `docs/FORMATS-fpga.md`.
//!
//! Phase B (this slice): a dependency-free JSON reader (sibling to `xml.rs`) and
//! the `lift fpga` dispatch with the `info` verb — a faithful **round-trip echo**
//! that proves we ingest everything, including module-level `annotations` and
//! `FormalProperty` nodes. The family projections (FSM / Petri / tasks / qnet)
//! and the verbs `check` / `prove` / `timing` / `equiv` land in later phases
//! behind this same path.

use std::path::PathBuf;
use std::process::exit;

// ===================================================================
// A minimal, dependency-free JSON reader (SPEC §13: no deps).
// ===================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    /// Object field by key.
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(kvs) => kvs.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    pub fn as_arr(&self) -> Option<&[Json]> {
        match self {
            Json::Arr(a) => Some(a),
            _ => None,
        }
    }
    #[allow(dead_code)] // used by the Phase D/F projections (is_cdc, signed, …)
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Json::Bool(b) => Some(*b),
            _ => None,
        }
    }
    /// Numbers may be encoded as bare JSON numbers OR (for wide ints / Hz, to
    /// dodge f64 precision loss) as numeric strings. Accept both.
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            // A bare JSON number must be a non-negative integer within exact f64
            // range (≤ 2^53); beyond that `as u64` would silently saturate and
            // fractionals would silently truncate — both reject (return None).
            // Wide values (Hz, u128/i128/u64 literals) arrive as strings instead.
            Json::Num(n)
                if n.is_finite() && *n >= 0.0 && *n == n.trunc() && *n <= 9_007_199_254_740_992.0 =>
            {
                Some(*n as u64)
            }
            Json::Str(s) => s.parse::<u64>().ok(),
            _ => None,
        }
    }
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Json::Num(n) => Some(*n),
            Json::Str(s) => s.parse::<f64>().ok(),
            _ => None,
        }
    }
    /// Convenience: a string-typed field by key.
    pub fn str_field(&self, key: &str) -> Option<&str> {
        self.get(key).and_then(Json::as_str)
    }
}

/// Parse a stream of top-level JSON values (the emitter writes one object per
/// module, concatenated). Returns them in order.
pub fn parse_stream(src: &str) -> Result<Vec<Json>, String> {
    let b: Vec<char> = src.chars().collect();
    let mut p = Parser { b: &b, i: 0, depth: 0 };
    let mut out = Vec::new();
    p.skip_ws();
    while p.i < b.len() {
        out.push(p.value()?);
        p.skip_ws();
    }
    if out.is_empty() {
        return Err("empty input: no JSON value".into());
    }
    Ok(out)
}

/// Guard against unbounded recursion: truncated/adversarial input must return an
/// `Err`, never overflow the stack and abort the process.
const MAX_DEPTH: usize = 512;

struct Parser<'a> {
    b: &'a [char],
    i: usize,
    depth: usize,
}

impl Parser<'_> {
    fn skip_ws(&mut self) {
        while self.i < self.b.len() && self.b[self.i].is_whitespace() {
            self.i += 1;
        }
    }

    fn value(&mut self) -> Result<Json, String> {
        self.skip_ws();
        if self.i >= self.b.len() {
            return Err("unexpected end of input".into());
        }
        match self.b[self.i] {
            '{' | '[' => {
                // Bound nesting at the two recursion points; abort cleanly past MAX_DEPTH.
                self.depth += 1;
                if self.depth > MAX_DEPTH {
                    return Err(format!("nesting too deep (> {MAX_DEPTH}) at {}", self.i));
                }
                let r = if self.b[self.i] == '{' { self.object() } else { self.array() };
                self.depth -= 1;
                r
            }
            '"' => Ok(Json::Str(self.string()?)),
            't' | 'f' => self.boolean(),
            'n' => self.null(),
            c if c == '-' || c.is_ascii_digit() => self.number(),
            c => Err(format!("unexpected character `{c}` at {}", self.i)),
        }
    }

    fn object(&mut self) -> Result<Json, String> {
        self.i += 1; // '{'
        let mut kvs = Vec::new();
        self.skip_ws();
        if self.i < self.b.len() && self.b[self.i] == '}' {
            self.i += 1;
            return Ok(Json::Obj(kvs));
        }
        loop {
            self.skip_ws();
            if self.i >= self.b.len() || self.b[self.i] != '"' {
                return Err(format!("expected object key string at {}", self.i));
            }
            let key = self.string()?;
            self.skip_ws();
            if self.i >= self.b.len() || self.b[self.i] != ':' {
                return Err(format!("expected `:` after key `{key}`"));
            }
            self.i += 1; // ':'
            let val = self.value()?;
            kvs.push((key, val));
            self.skip_ws();
            match self.b.get(self.i) {
                Some(',') => {
                    self.i += 1;
                }
                Some('}') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected `,` or `}}` in object at {}", self.i)),
            }
        }
        Ok(Json::Obj(kvs))
    }

    fn array(&mut self) -> Result<Json, String> {
        self.i += 1; // '['
        let mut items = Vec::new();
        self.skip_ws();
        if self.i < self.b.len() && self.b[self.i] == ']' {
            self.i += 1;
            return Ok(Json::Arr(items));
        }
        loop {
            let val = self.value()?;
            items.push(val);
            self.skip_ws();
            match self.b.get(self.i) {
                Some(',') => {
                    self.i += 1;
                }
                Some(']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected `,` or `]` in array at {}", self.i)),
            }
        }
        Ok(Json::Arr(items))
    }

    fn string(&mut self) -> Result<String, String> {
        self.i += 1; // opening quote
        let mut s = String::new();
        while self.i < self.b.len() {
            let c = self.b[self.i];
            self.i += 1;
            match c {
                '"' => return Ok(s),
                '\\' => {
                    let e = self.b.get(self.i).copied().ok_or("unterminated escape")?;
                    self.i += 1;
                    match e {
                        '"' => s.push('"'),
                        '\\' => s.push('\\'),
                        '/' => s.push('/'),
                        'n' => s.push('\n'),
                        'r' => s.push('\r'),
                        't' => s.push('\t'),
                        'b' => s.push('\u{0008}'),
                        'f' => s.push('\u{000C}'),
                        'u' => {
                            let hex: String = self.b.get(self.i..self.i + 4).ok_or("short \\u")?.iter().collect();
                            self.i += 4;
                            let cp = u32::from_str_radix(&hex, 16).map_err(|_| "bad \\u hex")?;
                            s.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
                        }
                        o => return Err(format!("bad escape `\\{o}`")),
                    }
                }
                c => s.push(c),
            }
        }
        Err("unterminated string".into())
    }

    fn number(&mut self) -> Result<Json, String> {
        let start = self.i;
        while self.i < self.b.len() {
            let c = self.b[self.i];
            if c.is_ascii_digit() || matches!(c, '-' | '+' | '.' | 'e' | 'E') {
                self.i += 1;
            } else {
                break;
            }
        }
        let lit: String = self.b[start..self.i].iter().collect();
        lit.parse::<f64>().map(Json::Num).map_err(|_| format!("bad number `{lit}`"))
    }

    fn boolean(&mut self) -> Result<Json, String> {
        if self.lit("true") {
            Ok(Json::Bool(true))
        } else if self.lit("false") {
            Ok(Json::Bool(false))
        } else {
            Err(format!("bad literal at {}", self.i))
        }
    }

    fn null(&mut self) -> Result<Json, String> {
        if self.lit("null") {
            Ok(Json::Null)
        } else {
            Err(format!("bad literal at {}", self.i))
        }
    }

    fn lit(&mut self, word: &str) -> bool {
        let w: Vec<char> = word.chars().collect();
        if self.i + w.len() <= self.b.len() && self.b[self.i..self.i + w.len()] == w[..] {
            self.i += w.len();
            true
        } else {
            false
        }
    }
}

// ===================================================================
// Aria IR-JSON — a typed view of the bridge (the parts leanlift needs).
// ===================================================================

const SCHEMA: &str = "aria-ir-json/v1";

pub struct AriaModule {
    pub name: String,
    pub id: u64,
    pub annotations: Vec<(String, String)>, // (kind, value-as-string)
    pub ports_in: usize,
    pub ports_out: usize,
    pub clock_domains: Vec<(String, Option<u64>)>, // (name, freq_hz)
    pub node_kinds: Vec<String>,                    // kind tag per node, in order
    pub formals: Vec<FormalSummary>,
    pub pipeline: Option<PipelineSummary>,
    pub target_period_ns: Option<f64>,
    pub critical_path_ns: Option<f64>,
    /// C-slowing factor from `TimingInfo` (1 = not C-slowed). The number of
    /// independent computation streams interleaved through one physical datapath.
    pub c_slow_factor: u64,
}

pub struct FormalSummary {
    pub kind: String,
    pub temporal: String,
    pub name: Option<String>,
}

pub struct PipelineSummary {
    pub num_stages: u64,
    pub latency: u64,
    pub initiation_interval: u64,
    pub flow_control: String,
    /// Per-stage estimated combinational delay (ns), in stage order. `None` where
    /// Aria did not estimate it (common). Used to cross-check `critical_path_ns`.
    pub stage_delays: Vec<Option<f64>>,
}

/// Project a parsed JSON module object into the typed view, validating the schema.
pub fn read_module(v: &Json) -> Result<AriaModule, String> {
    let schema = v.str_field("schema").ok_or("missing `schema` field")?;
    if schema != SCHEMA {
        return Err(format!("unsupported schema `{schema}` (expected `{SCHEMA}`)"));
    }
    let name = v.str_field("name").ok_or("missing module `name`")?.to_string();
    let id = v.get("id").and_then(Json::as_u64).ok_or("missing module `id`")?;

    let annotations = v
        .get("annotations")
        .and_then(Json::as_arr)
        .ok_or("missing `annotations` array")?
        .iter()
        .map(|a| {
            let kind = a.str_field("kind").unwrap_or("?").to_string();
            let val = match a.get("value") {
                Some(Json::Str(s)) => s.clone(),
                Some(Json::Num(n)) => format!("{n}"),
                Some(Json::Bool(b)) => b.to_string(),
                _ => String::new(),
            };
            (kind, val)
        })
        .collect();

    let mut ports_in = 0;
    let mut ports_out = 0;
    for p in v.get("ports").and_then(Json::as_arr).ok_or("missing `ports` array")? {
        match p.str_field("dir") {
            Some("input") => ports_in += 1,
            Some("output") => ports_out += 1,
            _ => {}
        }
    }

    let clock_domains = v
        .get("clock_domains")
        .and_then(Json::as_arr)
        .ok_or("missing `clock_domains` array")?
        .iter()
        .map(|c| {
            let n = c.str_field("name").unwrap_or("?").to_string();
            let f = c.get("freq_hz").and_then(Json::as_u64);
            (n, f)
        })
        .collect();

    let nodes = v.get("nodes").and_then(Json::as_arr).ok_or("missing `nodes` array")?;
    let mut node_kinds = Vec::with_capacity(nodes.len());
    let mut formals = Vec::new();
    for n in nodes {
        let kind = n.get("kind").and_then(|k| k.str_field("k")).unwrap_or("?").to_string();
        if kind == "formal_property" {
            if let Some(prop) = n.get("kind").and_then(|k| k.get("property")) {
                formals.push(FormalSummary {
                    kind: prop.str_field("kind").unwrap_or("?").to_string(),
                    temporal: prop
                        .get("temporal")
                        .and_then(|t| t.str_field("tt"))
                        .unwrap_or("?")
                        .to_string(),
                    name: prop.str_field("name").map(String::from),
                });
            }
        }
        node_kinds.push(kind);
    }

    let pipeline = v.get("pipeline").filter(|p| **p != Json::Null).map(|p| PipelineSummary {
        num_stages: p.get("num_stages").and_then(Json::as_u64).unwrap_or(0),
        latency: p.get("latency").and_then(Json::as_u64).unwrap_or(0),
        initiation_interval: p.get("initiation_interval").and_then(Json::as_u64).unwrap_or(0),
        flow_control: p
            .get("flow_control")
            .and_then(|f| f.str_field("fc"))
            .unwrap_or("?")
            .to_string(),
        stage_delays: p
            .get("stages")
            .and_then(Json::as_arr)
            .map(|ss| ss.iter().map(|s| s.get("comb_delay_ns").and_then(Json::as_f64)).collect())
            .unwrap_or_default(),
    });

    let timing = v.get("timing");
    let target_period_ns = timing.and_then(|t| t.get("target_period_ns")).and_then(Json::as_f64);
    let critical_path_ns = timing.and_then(|t| t.get("critical_path_ns")).and_then(Json::as_f64);
    let c_slow_factor = timing.and_then(|t| t.get("c_slow_factor")).and_then(Json::as_u64).unwrap_or(1).max(1);

    Ok(AriaModule {
        name,
        id,
        annotations,
        ports_in,
        ports_out,
        clock_domains,
        node_kinds,
        formals,
        pipeline,
        target_period_ns,
        critical_path_ns,
        c_slow_factor,
    })
}

/// Parse a whole IR-JSON file (possibly several modules) into typed views.
pub fn read_file(src: &str) -> Result<Vec<AriaModule>, String> {
    parse_stream(src)?.iter().map(read_module).collect()
}

impl AriaModule {
    /// Resolve the module's clock frequency (Hz): the `@clock_freq` annotation if
    /// present, else the first clock domain that declares a `freq_hz`. `None` if
    /// the design states no clock — then only cycle-counts (not wall-clock ns) and
    /// no timing-closure verdict are available.
    pub fn clock_freq_hz(&self) -> Option<u64> {
        if let Some((_, v)) = self.annotations.iter().find(|(k, _)| k == "clock_freq") {
            if let Ok(hz) = v.parse::<u64>() {
                return Some(hz);
            }
        }
        self.clock_domains.iter().find_map(|(_, f)| *f)
    }
}

// ===================================================================
// T1 — pipeline timing certificate (PLAN-fpga Phase T).
//
// Project an Aria `PipelineInfo` (+ `@clock_freq` + `TimingInfo`) onto a HARD
// latency/timing-closure obligation. Every number here is mechanical and is
// CROSS-CHECKED against an independent source (the No-LLM ledger, T1):
//
//   * timing closure  — the binding constraint `critical_path_ns ≤ clock_period`.
//     Where Aria also gives per-stage `comb_delay_ns`, we re-derive the critical
//     path as `max(stage delay)` and assert it agrees with Aria's `critical_path_ns`
//     (two independent derivations of the same number).
//   * hard latency    — `latency` cycles ⇒ `latency × clock_period` ns. For a
//     feed-forward pipeline (II = 1) the cycle latency must equal `num_stages`
//     (one register delay per stage); we assert that independent identity.
//   * fold feasibility — a C-slowed datapath interleaves `c_slow_factor`
//     INDEPENDENT computation streams through ONE physical datapath, one slot per
//     `II` cycles. That is a genuine TDM scheduling question (NOT a spatial
//     pipeline — those stages run in parallel and need no scheduling proof), so we
//     REUSE `rt.rs` RTA: `c_slow_factor` unit-cost lanes with period = deadline =
//     II. It is feasible iff `c_slow_factor ≤ II` (RTA finds WCRT = c_slow_factor).
//     This is a real cross-check of two IR fields — over-folding (more streams than
//     slots) is caught — not a tautology. For the common case (c_slow=1, II=1) it
//     is one lane, trivially feasible.
//
// Where two independent sources for a number exist, they are RECONCILED, never
// silently preferred: clock period (@clock_freq vs target_period_ns) and the
// critical path (max stage-delay vs Aria's critical_path_ns). Any disagreement
// FAILS the certificate (fail-closed) rather than trusting one source.
// ===================================================================

use super::rt;

/// Guard against absurd/garbage IR: an II or C-slow factor past this is treated as
/// malformed (fail-closed) rather than truncated to u32 or used to size a Vec.
const MAX_FOLD: u64 = 1 << 16;

pub struct TimingCert {
    pub module: String,
    pub num_stages: u64,
    pub latency_cycles: u64,
    pub ii: u64,
    pub c_slow_factor: u64,
    pub clk_period_ns: Option<f64>,
    pub critical_path_ns: Option<f64>,
    /// Independent critical path = max per-stage comb delay, when all stages
    /// carry an estimate; `None` if any stage delay is missing.
    pub derived_critical_ns: Option<f64>,
    /// `Some(true/false)` once a critical path and clock period are both known.
    pub closes_timing: Option<bool>,
    /// True when closure rests on an INDEPENDENTLY-derived critical path (every
    /// stage annotated); false when it can only trust Aria's `critical_path_ns`.
    pub closure_independent: bool,
    /// Hard end-to-end latency budget in ns (`latency × clk_period`), when clocked.
    pub latency_ns: Option<f64>,
    /// Feed-forward note (II = 1): `latency` vs `num_stages`. `None` if II≠1.
    /// Equal = clean single-register stages; greater = benign (multi-cycle stages);
    /// less = a real inconsistency (can't traverse N stages in < N cycles).
    pub latency_vs_depth: Option<std::cmp::Ordering>,
    /// RTA verdict on the C-slow fold (`c_slow_factor` lanes ≤ II slots).
    pub fold_schedulable: bool,
    /// Set when the two critical-path derivations disagree.
    pub critical_mismatch: bool,
    /// Set when @clock_freq and target_period_ns disagree on the clock period.
    pub period_mismatch: bool,
    /// Set when II or c_slow_factor is past `MAX_FOLD` (malformed IR).
    pub fold_malformed: bool,
}

impl TimingCert {
    /// Fail-closed: certified iff closure does not VIOLATE, the fold is schedulable
    /// and well-formed, latency is not impossibly small, and no cross-check
    /// disagreed. Unknown closure (no critical-path/clock) and "trusts Aria"
    /// (no per-stage breakdown) are WARNINGS, not failures.
    pub fn ok(&self) -> bool {
        self.closes_timing != Some(false)
            && self.fold_schedulable
            && !self.fold_malformed
            && !self.critical_mismatch
            && !self.period_mismatch
            && self.latency_vs_depth != Some(std::cmp::Ordering::Less)
    }
}

/// Build the timing certificate for a module, or `None` if it has no pipeline.
pub fn certify_timing(m: &AriaModule) -> Option<TimingCert> {
    let p = m.pipeline.as_ref()?;
    let ii = p.initiation_interval.max(1);
    let c_slow = m.c_slow_factor.max(1);

    // Clock period (ns) from two independent sources — reconcile them. @clock_freq
    // is the design constraint; target_period_ns is Aria's recorded target. If both
    // exist and disagree (> 1 ps), the IR is inconsistent ⇒ fail-closed.
    let freq_period = m.clock_freq_hz().map(|hz| 1.0e9 / hz as f64);
    let period_mismatch = match (freq_period, m.target_period_ns) {
        (Some(a), Some(b)) => (a - b).abs() > 1e-3,
        _ => false,
    };
    let clk_period_ns = freq_period.or(m.target_period_ns);

    // Independent critical path: max per-stage combinational delay, but only when
    // EVERY stage carries an estimate (else the max would understate the path).
    let derived_critical_ns = if !p.stage_delays.is_empty() && p.stage_delays.iter().all(Option::is_some) {
        p.stage_delays.iter().filter_map(|d| *d).fold(f64::NEG_INFINITY, f64::max).into()
    } else {
        None
    };

    // Cross-check the two critical-path derivations when both exist (1 ps tol).
    let critical_mismatch = match (derived_critical_ns, m.critical_path_ns) {
        (Some(d), Some(a)) => (d - a).abs() > 1e-3,
        _ => false,
    };

    // Timing closure: the slowest path must fit in one clock period. Prefer the
    // independently-derived critical path; fall back to Aria's reported one (and
    // record that the closure then rests on a single, un-cross-checked source).
    let crit = derived_critical_ns.or(m.critical_path_ns);
    let closure_independent = derived_critical_ns.is_some();
    let closes_timing = match (crit, clk_period_ns) {
        (Some(c), Some(t)) => Some(c <= t + 1e-9),
        _ => None,
    };

    let latency_ns = clk_period_ns.map(|t| p.latency as f64 * t);

    // Feed-forward relation (II = 1 only): latency vs pipeline depth.
    let latency_vs_depth = (ii == 1).then(|| p.latency.cmp(&p.num_stages));

    // Fold feasibility via RTA (rt.rs): `c_slow_factor` lanes contend for II slots.
    // Guard absurd sizes (truncation / Vec blow-up) as malformed, fail-closed.
    let fold_malformed = ii > MAX_FOLD || c_slow > MAX_FOLD;
    let fold_schedulable = if fold_malformed {
        false
    } else {
        let ts = rt::TaskSet {
            policy: rt::Policy::Rm,
            tasks: (0..c_slow)
                .map(|k| rt::Task { name: format!("stream{k}"), c: 1, t: ii as u32, d: ii as u32 })
                .collect(),
        };
        rt::analyze(&ts).schedulable
    };

    Some(TimingCert {
        module: m.name.clone(),
        num_stages: p.num_stages,
        latency_cycles: p.latency,
        ii,
        c_slow_factor: c_slow,
        clk_period_ns,
        critical_path_ns: m.critical_path_ns,
        derived_critical_ns,
        closes_timing,
        closure_independent,
        latency_ns,
        latency_vs_depth,
        fold_schedulable,
        critical_mismatch,
        period_mismatch,
        fold_malformed,
    })
}

// ===================================================================
// T2 — pipeline throughput / backpressure (PLAN-fpga Phase T, reuse qnet.rs).
//
// Project a streaming pipeline onto an open tandem Jackson network: one M/M/1
// station per stage, service rate μᵢ = 1/comb_delayᵢ (the intrinsic rate of that
// stage's logic), external offered load λ⁰ = clock_freq / II at stage 0, tandem
// routing (stage i → i+1, last exits). REUSE `qnet.rs` for the traffic-equation
// solve, the bottleneck station, and the stability verdict.
//
// HARD facts (deterministic): the max sustainable throughput is `min μᵢ =
// 1/critical_path`; the bottleneck is the slowest stage; the pipeline is stable
// at the offered load iff every ρᵢ < 1 — which is timing closure restated, so we
// CROSS-CHECK that the qnet bottleneck station IS the critical-path (max-delay)
// stage. The per-stage mean occupancy Lᵢ is the SOFT/stochastic companion (an
// M/M/1 upper bound; a synchronous pipeline's deterministic timing is no worse) —
// the provably-safe ⊊ probably-safe boundary, now under a clock.
//
// When Aria gives no per-stage `comb_delay_ns` (common), there is no asymmetry to
// place a bottleneck, so we report the balanced-pipeline throughput clock_freq/II
// directly and do NOT fabricate a qnet — sound by omission, not by guessing.
// ===================================================================

use super::qnet;

pub struct ThroughputCert {
    pub module: String,
    pub ii: u64,
    /// Offered input rate (items/s) = clock_freq / II, when clocked.
    pub offered: Option<f64>,
    /// Max sustainable throughput (items/s) = min stage rate, when per-stage rates known.
    pub max_sustainable: Option<f64>,
    /// Per-stage (name-or-index, service-rate items/s) when per-stage delays exist.
    pub stage_rates: Vec<(String, f64)>,
    /// qnet verdict, when a network was built (per-stage rates available).
    pub qnet: Option<QNetVerdict>,
    /// Index of the critical-path (max-delay) stage, when per-stage delays exist.
    pub critical_stage: Option<usize>,
    /// Set when the qnet bottleneck disagrees with the critical-path stage.
    pub bottleneck_mismatch: bool,
}

pub struct QNetVerdict {
    pub stable: bool,
    pub bottleneck: usize,
    pub throughput: f64,
    /// Per-stage (name, ρ, mean occupancy L) — L is the soft M/M/1 companion.
    pub stations: Vec<(String, f64, f64)>,
}

impl ThroughputCert {
    /// Stable at the offered load AND the bottleneck cross-check agrees. With no
    /// per-stage rates, stability is the trivial II ≥ 1 (always true) — reported,
    /// not failed.
    pub fn ok(&self) -> bool {
        !self.bottleneck_mismatch && self.qnet.as_ref().map(|q| q.stable).unwrap_or(true)
    }
}

pub fn certify_throughput(m: &AriaModule) -> Option<ThroughputCert> {
    let p = m.pipeline.as_ref()?;
    let ii = p.initiation_interval.max(1);
    let clk_hz = m.clock_freq_hz().map(|hz| hz as f64).or_else(|| m.target_period_ns.map(|t| 1.0e9 / t));
    let offered = clk_hz.map(|f| f / ii as f64);

    // Per-stage service rates require every stage's comb_delay (>0).
    let have_rates = !p.stage_delays.is_empty()
        && p.stage_delays.iter().all(|d| matches!(d, Some(x) if *x > 0.0));

    if !have_rates {
        // Balanced fallback: no asymmetry, throughput = clock_freq/II, no bottleneck.
        return Some(ThroughputCert {
            module: m.name.clone(),
            ii,
            offered,
            max_sustainable: offered, // balanced ⇒ sustainable == offered
            stage_rates: Vec::new(),
            qnet: None,
            critical_stage: None,
            bottleneck_mismatch: false,
        });
    }

    let delays: Vec<f64> = p.stage_delays.iter().map(|d| d.unwrap()).collect();
    let rates: Vec<f64> = delays.iter().map(|d| 1.0e9 / d).collect(); // items/s
    let max_sustainable = rates.iter().cloned().fold(f64::INFINITY, f64::min);
    let max_delay = delays.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    // First-wins, matching qnet's bottleneck convention (`rho > max_rho`), so the
    // two never disagree on ties.
    let n = delays.len();
    let mut crit = 0;
    for i in 1..n {
        if delays[i] > delays[crit] {
            crit = i;
        }
    }
    let critical_stage = Some(crit);

    // Build the Jackson net only when there is a real offered load. With no clock
    // (offered = None) the queueing model has no input and "stability" is vacuous —
    // report the per-stage rates but do NOT assert a stability verdict.
    let stage_rates = (0..n).map(|i| (format!("stage{i}"), rates[i])).collect();
    let Some(lam) = offered.filter(|o| *o > 0.0) else {
        return Some(ThroughputCert {
            module: m.name.clone(),
            ii,
            offered,
            max_sustainable: Some(max_sustainable),
            stage_rates,
            qnet: None,
            critical_stage,
            bottleneck_mismatch: false,
        });
    };

    let stations: Vec<qnet::Station> = (0..n)
        .map(|i| qnet::Station {
            name: format!("stage{i}"),
            mu: rates[i],
            servers: 1,
            lambda0: if i == 0 { lam } else { 0.0 },
        })
        .collect();
    // Tandem routing: stage i → i+1; the last stage exits the network.
    let mut routing = vec![vec![0.0; n]; n];
    for i in 0..n - 1 {
        routing[i][i + 1] = 1.0;
    }
    let net = qnet::QNet { stations, routing };

    let (qv, bottleneck_mismatch) = match qnet::analyze(&net) {
        Ok(rep) => {
            // VALUE-based consistency check (robust to ties): the station qnet calls
            // the bottleneck must be one of the genuinely-slowest (max-delay) stages.
            // A disagreement here would mean the traffic-equation solve mis-weighted
            // the tandem — a plumbing bug — so it fails closed.
            let mismatch = (delays[rep.bottleneck] - max_delay).abs() > 1e-9;
            let stations = rep
                .stations
                .iter()
                .map(|s| (s.name.clone(), s.rho, s.l))
                .collect();
            (
                Some(QNetVerdict { stable: rep.stable, bottleneck: rep.bottleneck, throughput: rep.throughput, stations }),
                mismatch,
            )
        }
        // A non-physical network (shouldn't happen for an open tandem) is not a
        // verdict; treat the qnet as unavailable rather than a false pass/fail.
        Err(_) => (None, false),
    };
    Some(ThroughputCert {
        module: m.name.clone(),
        ii,
        offered,
        max_sustainable: Some(max_sustainable),
        stage_rates,
        qnet: qv,
        critical_stage,
        bottleneck_mismatch,
    })
}

// ===================================================================
// CLI: `lift fpga …`
// ===================================================================

fn usage() -> ! {
    eprintln!(
        "usage:\n\
        \x20 lift fpga info <design.aria.json>\n\
        \x20     ingest an Aria-HDL IR-JSON export and echo a faithful summary\n\
        \x20     (modules, ports, clock domains, annotations, formal properties,\n\
        \x20     pipeline + timing). Phase B round-trip check.\n\
        \x20 lift fpga timing <design.aria.json>\n\
        \x20     certify each pipeline's HARD latency + timing closure (clock\n\
        \x20     period vs critical path), cross-checked; RTA fold check on II.\n\
        \x20     Exit 1 if any pipeline violates closure / a cross-check disagrees.\n\
        \x20 lift fpga throughput <design.aria.json>\n\
        \x20     project each pipeline → a Jackson network (reuse qnet): max\n\
        \x20     sustainable rate, bottleneck stage (cross-checked vs critical\n\
        \x20     path), stability at the offered load, per-stage occupancy.\n\
        \x20     Exit 1 if a pipeline is unstable / the bottleneck disagrees.\n\
        \x20 (planned: lift fpga check|prove|equiv — see docs/PLAN-fpga.md)\n"
    );
    exit(2);
}

pub fn main(mut argv: Vec<String>) {
    // Accept `lift fpga info <file>` and the bare `lift fpga <file>` form.
    let verb = match argv.first().map(String::as_str) {
        Some("info") => {
            argv.remove(0);
            "info"
        }
        Some("timing") => {
            argv.remove(0);
            "timing"
        }
        Some("throughput") => {
            argv.remove(0);
            "throughput"
        }
        Some(s) if !s.starts_with('-') => "info",
        _ => usage(),
    };
    match verb {
        "info" => info_cmd(argv),
        "timing" => timing_cmd(argv),
        "throughput" => throughput_cmd(argv),
        _ => usage(),
    }
}

/// Shared positional-file argument parsing for the single-file verbs.
fn one_file(a: Vec<String>) -> String {
    let mut file: Option<String> = None;
    for arg in &a {
        if arg.starts_with("--") {
            eprintln!("unknown flag: {arg}");
            usage();
        } else if file.is_some() {
            usage();
        } else {
            file = Some(arg.clone());
        }
    }
    file.unwrap_or_else(|| usage())
}

fn load(path: &str) -> Vec<AriaModule> {
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("error reading {path}: {e}");
        exit(2);
    });
    read_file(&src).unwrap_or_else(|e| {
        eprintln!("error: {path}: {e}");
        exit(1);
    })
}

fn timing_cmd(a: Vec<String>) {
    let path = one_file(a);
    let modules = load(&path);

    let mut certs = Vec::new();
    for m in &modules {
        if let Some(c) = certify_timing(m) {
            certs.push(c);
        }
    }
    if certs.is_empty() {
        eprintln!("no pipelined modules in {path} (nothing to certify)");
        exit(2);
    }

    println!("leanlift FPGA timing certificate — {path}");
    println!("════════════════════════════════════════════════════");
    let mut all_ok = true;
    for c in &certs {
        all_ok &= c.ok();
        println!();
        println!("pipeline `{}` — {} stages, II {}, C-slow {}", c.module, c.num_stages, c.ii, c.c_slow_factor);

        // Hard latency bound.
        match (c.clk_period_ns, c.latency_ns) {
            (Some(t), Some(ns)) => {
                let mhz = 1.0e3 / t; // f(MHz) = 1e9/period(ns) / 1e6 = 1e3/period(ns)
                println!(
                    "  hard latency : {} cycle(s) = {:.3} ns  (clk {:.3} ns, {:.1} MHz)",
                    c.latency_cycles, ns, t, mhz
                );
            }
            _ => println!("  hard latency : {} cycle(s)  (no clock stated — cycles only)", c.latency_cycles),
        }
        if c.period_mismatch {
            println!("    ✗ DISAGREE : @clock_freq period ≠ Aria target_period_ns — inconsistent IR");
        }
        if let Some(ord) = c.latency_vs_depth {
            use std::cmp::Ordering::*;
            let note = match ord {
                Equal => "latency == depth (clean single-register stages) ✓".to_string(),
                Greater => format!("latency {} > depth {} (multi-cycle stages — ok)", c.latency_cycles, c.num_stages),
                Less => format!("latency {} < depth {} — IMPOSSIBLE ✗", c.latency_cycles, c.num_stages),
            };
            println!("    cross-check: {note}");
        }

        // Timing closure.
        match (c.derived_critical_ns.or(c.critical_path_ns), c.clk_period_ns, c.closes_timing) {
            (Some(crit), Some(t), Some(ok)) => {
                let basis = if c.closure_independent { "max stage-delay" } else { "Aria critical-path (trusted, no per-stage breakdown)" };
                println!(
                    "  closure      : {} {:.3} ns {} clock {:.3} ns → {}",
                    basis,
                    crit,
                    if ok { "≤" } else { ">" },
                    t,
                    if ok { "CLOSES" } else { "VIOLATED" }
                );
            }
            _ => println!("  closure      : unknown (no critical-path / clock estimate) — WARN"),
        }
        // Independent critical-path cross-check (only when stages are fully annotated).
        if let (Some(d), Some(a)) = (c.derived_critical_ns, c.critical_path_ns) {
            println!(
                "    cross-check: max stage-delay {:.3} ns vs Aria critical-path {:.3} ns {}",
                d,
                a,
                if c.critical_mismatch { "✗ DISAGREE" } else { "✓" }
            );
        }

        // RTA fold feasibility (rt.rs): c_slow_factor streams contend for II slots.
        if c.fold_malformed {
            println!("  fold (RTA)   : II/C-slow past {MAX_FOLD} — malformed IR ✗");
        } else {
            println!(
                "  fold (RTA)   : {} stream(s) @ {} slot(s)/frame → {}",
                c.c_slow_factor,
                c.ii,
                if c.fold_schedulable { "schedulable ✓" } else { "OVER-FOLDED ✗" }
            );
        }

        let verdict = if !c.ok() {
            "FAILED"
        } else if c.closes_timing == Some(true) && !c.closure_independent {
            "CERTIFIED (closure trusts Aria critical-path)"
        } else {
            "CERTIFIED"
        };
        println!("  verdict      : {verdict}");
    }

    println!();
    println!("{}/{} pipeline(s) certified", certs.iter().filter(|c| c.ok()).count(), certs.len());
    if !all_ok {
        exit(1);
    }
}

/// Human-readable rate (items/s) with a G/M/k/plain tier so sub-MHz rates don't
/// underflow to `0.000`.
fn rate_str(r: f64) -> String {
    if r >= 1.0e9 {
        format!("{:.3} Gitems/s", r / 1.0e9)
    } else if r >= 1.0e6 {
        format!("{:.3} Mitems/s", r / 1.0e6)
    } else if r >= 1.0e3 {
        format!("{:.3} kitems/s", r / 1.0e3)
    } else {
        format!("{r:.3} items/s")
    }
}

fn throughput_cmd(a: Vec<String>) {
    let path = one_file(a);
    let modules = load(&path);

    let certs: Vec<_> = modules.iter().filter_map(certify_throughput).collect();
    if certs.is_empty() {
        eprintln!("no pipelined modules in {path} (nothing to analyze)");
        exit(2);
    }

    println!("leanlift FPGA throughput certificate — {path}");
    println!("════════════════════════════════════════════════════");
    let mut all_ok = true;
    for c in &certs {
        all_ok &= c.ok();
        println!();
        println!("pipeline `{}` — II {}", c.module, c.ii);
        match c.offered {
            Some(o) => println!("  offered load : {} (clock / II)", rate_str(o)),
            None => println!("  offered load : (no clock stated)"),
        }
        match c.max_sustainable {
            Some(s) => println!("  sustainable  : {} (min stage rate = 1/critical-path)", rate_str(s)),
            None => println!("  sustainable  : unknown"),
        }
        if c.stage_rates.is_empty() {
            println!("  model        : balanced (no per-stage delays) — bottleneck is II");
        } else if let Some(q) = &c.qnet {
            println!("  qnet (Jackson tandem, {} stations):", q.stations.len());
            for (i, (name, rho, l)) in q.stations.iter().enumerate() {
                let mark = if i == q.bottleneck { "  ← bottleneck" } else { "" };
                println!("    {name}: ρ={rho:.3}, L={l:.3}{mark}");
            }
            // ρ < 1 here IS per-stage timing closure (μ = 1/comb_delay, λ = clock/II);
            // L is the SOFT M/M/1 companion (an upper bound — deterministic timing
            // is no worse), not a probabilistic safety margin.
            println!(
                "  stability    : {} (ρ<1 = per-stage closure; throughput {})",
                if q.stable { "STABLE ✓" } else { "SATURATED ✗" },
                rate_str(q.throughput)
            );
            if let Some(cs) = c.critical_stage {
                println!(
                    "    cross-check: qnet bottleneck stage{} is a slowest stage (critical-path stage{}) {}",
                    q.bottleneck,
                    cs,
                    if c.bottleneck_mismatch { "✗ DISAGREE" } else { "✓" }
                );
            }
        } else {
            // per-stage rates known but no offered load (no clock) — no qnet built.
            println!("  model        : per-stage rates known, no offered load — stability not assessed");
        }
        println!("  verdict      : {}", if c.ok() { "CERTIFIED" } else { "FAILED" });
    }

    println!();
    println!("{}/{} pipeline(s) certified", certs.iter().filter(|c| c.ok()).count(), certs.len());
    if !all_ok {
        exit(1);
    }
}

fn info_cmd(a: Vec<String>) {
    let path = one_file(a);
    let modules = load(&path);

    println!("aria-ir-json: {} module(s) from {}", modules.len(), path);
    for m in &modules {
        println!();
        println!("module {} (id {})", m.name, m.id);
        println!("  ports: {} in, {} out", m.ports_in, m.ports_out);
        let cds: Vec<String> = m
            .clock_domains
            .iter()
            .map(|(n, f)| match f {
                Some(hz) => format!("{n}@{}MHz", *hz as f64 / 1e6),
                None => n.clone(),
            })
            .collect();
        println!("  clock domains: [{}]", cds.join(", "));
        if m.annotations.is_empty() {
            println!("  annotations: (none)");
        } else {
            let anns: Vec<String> = m.annotations.iter().map(|(k, v)| format!("{k}={v}")).collect();
            println!("  annotations: {}", anns.join(", "));
        }
        // node-kind histogram
        let mut hist: Vec<(String, usize)> = Vec::new();
        for k in &m.node_kinds {
            match hist.iter_mut().find(|(kk, _)| kk == k) {
                Some((_, c)) => *c += 1,
                None => hist.push((k.clone(), 1)),
            }
        }
        let kinds: Vec<String> = hist.iter().map(|(k, c)| format!("{k}×{c}")).collect();
        println!("  nodes ({}): {}", m.node_kinds.len(), kinds.join(", "));
        if m.formals.is_empty() {
            println!("  formal properties: (none)");
        } else {
            println!("  formal properties: {}", m.formals.len());
            for f in &m.formals {
                let nm = f.name.as_deref().unwrap_or("(unnamed)");
                println!("    - {} {} {}", f.kind, f.temporal, nm);
            }
        }
        if let Some(p) = &m.pipeline {
            println!(
                "  pipeline: {} stages, latency {} cyc, II {}, flow {}",
                p.num_stages, p.latency, p.initiation_interval, p.flow_control
            );
        }
        match (m.target_period_ns, m.critical_path_ns) {
            (Some(t), Some(c)) => println!("  timing: target {t}ns, critical-path {c}ns"),
            (Some(t), None) => println!("  timing: target {t}ns"),
            (None, Some(c)) => println!("  timing: critical-path {c}ns"),
            (None, None) => {}
        }
    }

    // A machine-readable echo, mirroring `model-report.json`.
    let report = PathBuf::from("fpga-report.json");
    let mut j = String::from("{\n");
    j.push_str(&format!("  \"schema\": \"{SCHEMA}\",\n"));
    j.push_str(&format!("  \"modules\": {},\n", modules.len()));
    j.push_str("  \"names\": [");
    let names: Vec<String> = modules.iter().map(|m| json_str(&m.name)).collect();
    j.push_str(&names.join(", "));
    j.push_str("],\n");
    let total_formals: usize = modules.iter().map(|m| m.formals.len()).sum();
    j.push_str(&format!("  \"formal_properties\": {total_formals}\n"));
    j.push_str("}\n");
    let _ = std::fs::write(&report, j);
}

/// JSON-escape and quote a string (for the `fpga-report.json` echo).
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = r#"
    {
      "schema": "aria-ir-json/v1",
      "id": 3,
      "name": "tx",
      "ports": [
        {"id": 0, "value": 1, "name": "go", "ty": {"t": "bit"}, "dir": "input", "clock_domain": 0},
        {"id": 1, "value": 9, "name": "out", "ty": {"t": "bits", "n": 8}, "dir": "output", "clock_domain": 0}
      ],
      "clock_domains": [
        {"id": 0, "name": "main", "clock_signal": 0, "reset_signal": null, "freq_hz": "125000000"}
      ],
      "annotations": [
        {"kind": "clock_freq", "value": "125000000"},
        {"kind": "max_error", "value": 0.001}
      ],
      "nodes": [
        {"id": 2, "name": "state", "kind": {"k": "register", "ty": {"t": "bit"}, "clock_domain": 0, "reset_value": null, "enable": null, "next": {"e": "ref", "value": 1}}},
        {"id": 3, "name": "p", "kind": {"k": "formal_property", "property": {"kind": "assert", "temporal": {"tt": "always"}, "expr": {"e": "ref", "value": 2}, "name": "safe"}}}
      ],
      "pipeline": {"id": 0, "num_stages": 3, "latency": 5, "initiation_interval": 1, "flow_control": {"fc": "ready_valid"}, "stages": []},
      "systolic": null,
      "timing": {"c_slow_factor": 1, "target_period_ns": 8.0, "critical_path_ns": 6.5, "retiming_weights": [], "buffers": []}
    }
    "#;

    #[test]
    fn parses_wide_int_as_string_and_number() {
        let v = &parse_stream(SAMPLE).unwrap()[0];
        // freq_hz given as a string must read back as a u64.
        assert_eq!(v.get("clock_domains").unwrap().as_arr().unwrap()[0].get("freq_hz").unwrap().as_u64(), Some(125_000_000));
    }

    #[test]
    fn reads_annotations_and_formals() {
        let m = &read_file(SAMPLE).unwrap()[0];
        assert_eq!(m.name, "tx");
        assert_eq!(m.ports_in, 1);
        assert_eq!(m.ports_out, 1);
        assert_eq!(m.annotations.len(), 2);
        assert!(m.annotations.iter().any(|(k, v)| k == "clock_freq" && v == "125000000"));
        assert!(m.annotations.iter().any(|(k, _)| k == "max_error"));
        assert_eq!(m.formals.len(), 1);
        assert_eq!(m.formals[0].kind, "assert");
        assert_eq!(m.formals[0].temporal, "always");
        assert_eq!(m.formals[0].name.as_deref(), Some("safe"));
        let p = m.pipeline.as_ref().unwrap();
        assert_eq!(p.num_stages, 3);
        assert_eq!(p.latency, 5);
        assert_eq!(p.flow_control, "ready_valid");
        assert_eq!(m.target_period_ns, Some(8.0));
    }

    #[test]
    fn rejects_wrong_schema() {
        let bad = r#"{"schema": "nope", "id": 0, "name": "x", "ports": [], "clock_domains": [], "annotations": [], "nodes": [], "timing": {}}"#;
        assert!(read_file(bad).is_err());
    }

    #[test]
    fn parses_multi_module_stream() {
        let two = format!("{SAMPLE}\n{SAMPLE}");
        assert_eq!(read_file(&two).unwrap().len(), 2);
    }

    #[test]
    fn deep_nesting_errs_not_panics() {
        // Adversarial/truncated input must return Err, never overflow the stack.
        let deep = "[".repeat(100_000);
        assert!(parse_stream(&deep).is_err());
    }

    // ---- T1: timing certificate ----------------------------------------

    /// A pipeline with per-stage delays, a clock, and a healthy closure margin.
    fn pipe_json(ii: u64, latency: u64, stages: &[f64], crit: f64, period: f64, freq_hz: &str) -> String {
        pipe_json_full(ii, 1, latency, stages, crit, period, freq_hz)
    }

    /// Full knobs: also the C-slow factor (for the fold) and the period source.
    #[allow(clippy::too_many_arguments)]
    fn pipe_json_full(ii: u64, c_slow: u64, latency: u64, stages: &[f64], crit: f64, period: f64, freq_hz: &str) -> String {
        let stage_arr: Vec<String> = stages
            .iter()
            .enumerate()
            .map(|(i, d)| format!(r#"{{"index": {i}, "name": null, "comb_delay_ns": {d}, "lut_count": null, "reg_count": 0, "forwarded_values": []}}"#))
            .collect();
        let freq_ann = if freq_hz.is_empty() {
            String::new()
        } else {
            format!(r#"{{"kind": "clock_freq", "value": "{freq_hz}"}}"#)
        };
        format!(
            r#"{{
              "schema": "aria-ir-json/v1", "id": 0, "name": "p",
              "ports": [], "clock_domains": [],
              "annotations": [{freq_ann}],
              "nodes": [],
              "pipeline": {{"id": 0, "num_stages": {n}, "latency": {latency},
                "initiation_interval": {ii}, "flow_control": {{"fc": "none"}},
                "stages": [{stages_joined}]}},
              "systolic": null,
              "timing": {{"c_slow_factor": {c_slow}, "target_period_ns": {period}, "critical_path_ns": {crit}, "retiming_weights": [], "buffers": []}}
            }}"#,
            n = stages.len(),
            stages_joined = stage_arr.join(", "),
        )
    }

    #[test]
    fn timing_closes_with_margin() {
        use std::cmp::Ordering;
        // 125 MHz ⇒ 8 ns period; slowest stage 2 ns ⇒ closes with room.
        let j = pipe_json(1, 2, &[1.5, 2.0], 2.0, 8.0, "125000000");
        let m = &read_file(&j).unwrap()[0];
        let c = certify_timing(m).unwrap();
        assert_eq!(c.clk_period_ns, Some(8.0));
        assert_eq!(c.closes_timing, Some(true));
        assert!(c.closure_independent); // every stage annotated
        assert_eq!(c.derived_critical_ns, Some(2.0)); // max(1.5, 2.0)
        assert!(!c.critical_mismatch); // 2.0 == Aria 2.0
        assert!(!c.period_mismatch); // 8 ns == 1e9/125e6
        assert_eq!(c.latency_ns, Some(16.0)); // 2 cycles × 8 ns
        assert_eq!(c.latency_vs_depth, Some(Ordering::Equal)); // II=1, latency==num_stages
        assert!(c.fold_schedulable);
        assert!(c.ok());
    }

    #[test]
    fn timing_violation_when_stage_slower_than_clock() {
        // 500 MHz ⇒ 2 ns period; a 3 ns stage cannot close — teeth.
        let j = pipe_json(1, 2, &[3.0, 1.0], 3.0, 2.0, "500000000");
        let c = certify_timing(&read_file(&j).unwrap()[0]).unwrap();
        assert_eq!(c.closes_timing, Some(false));
        assert!(!c.ok(), "a path slower than the clock must FAIL the certificate");
    }

    #[test]
    fn critical_path_cross_check_disagreement_flags() {
        // Aria says critical-path 1.0 ns but the stages' max is 5 ns — the two
        // derivations disagree, so the certificate must refuse (no silent accept).
        let j = pipe_json(1, 2, &[5.0, 2.0], 1.0, 8.0, "125000000");
        let c = certify_timing(&read_file(&j).unwrap()[0]).unwrap();
        assert!(c.critical_mismatch);
        assert!(!c.ok());
    }

    #[test]
    fn period_cross_check_disagreement_flags() {
        // @clock_freq 125 MHz ⇒ 8 ns, but Aria target_period_ns says 4 ns. A stale
        // frequency annotation must NOT silently win — the disagreement fails closed.
        let j = pipe_json(1, 2, &[1.0, 1.0], 1.0, 4.0, "125000000");
        let c = certify_timing(&read_file(&j).unwrap()[0]).unwrap();
        assert!(c.period_mismatch);
        assert!(!c.ok());
    }

    #[test]
    fn feedforward_latency_below_depth_is_impossible() {
        // II=1 but latency (1) < num_stages (2): cannot traverse 2 stages in 1 cycle.
        let j = pipe_json(1, 1, &[1.0, 1.0], 1.0, 8.0, "125000000");
        let c = certify_timing(&read_file(&j).unwrap()[0]).unwrap();
        assert_eq!(c.latency_vs_depth, Some(std::cmp::Ordering::Less));
        assert!(!c.ok());
    }

    #[test]
    fn feedforward_latency_above_depth_is_benign() {
        // II=1, latency (5) > num_stages (2): legitimate multi-cycle stages, not a
        // failure. Must NOT false-reject a correct design.
        let j = pipe_json(1, 5, &[1.0, 1.0], 1.0, 8.0, "125000000");
        let c = certify_timing(&read_file(&j).unwrap()[0]).unwrap();
        assert_eq!(c.latency_vs_depth, Some(std::cmp::Ordering::Greater));
        assert!(c.ok(), "multi-cycle stages (latency > depth) are valid");
    }

    #[test]
    fn cslow_fold_consistent_is_schedulable() {
        // C-slow 4 interleaved through II=4 slots: exactly one slot per stream ⇒ feasible.
        let j = pipe_json_full(4, 4, 4, &[1.0, 1.0, 1.0, 1.0], 1.0, 8.0, "125000000");
        let c = certify_timing(&read_file(&j).unwrap()[0]).unwrap();
        assert_eq!(c.c_slow_factor, 4);
        assert_eq!(c.ii, 4);
        assert!(c.fold_schedulable);
        assert_eq!(c.latency_vs_depth, None); // only checked for II=1
        assert!(c.ok());
    }

    #[test]
    fn cslow_overfold_is_caught() {
        // C-slow 4 streams but only II=2 slots/frame: two streams miss their slot.
        // The fold (RTA) must find this OVER-FOLDED — a real, non-tautological check.
        let j = pipe_json_full(2, 4, 2, &[1.0, 1.0], 1.0, 8.0, "125000000");
        let c = certify_timing(&read_file(&j).unwrap()[0]).unwrap();
        assert_eq!(c.c_slow_factor, 4);
        assert_eq!(c.ii, 2);
        assert!(!c.fold_schedulable, "4 streams cannot share 2 slots/frame");
        assert!(!c.ok());
    }

    #[test]
    fn malformed_huge_fold_fails_closed() {
        // An absurd II must be rejected as malformed, never truncated to u32 or used
        // to allocate a giant Vec.
        let j = pipe_json_full(5_000_000_000, 1, 2, &[1.0, 1.0], 1.0, 8.0, "125000000");
        let c = certify_timing(&read_file(&j).unwrap()[0]).unwrap();
        assert!(c.fold_malformed);
        assert!(!c.ok());
    }

    // ---- T2: throughput / qnet -----------------------------------------

    #[test]
    fn throughput_balanced_fallback_no_stage_delays() {
        // pipeline_demo-shaped: no per-stage delays ⇒ balanced model, no qnet.
        let j = pipe_json(1, 2, &[], 0.8, 8.0, "125000000");
        let c = certify_throughput(&read_file(&j).unwrap()[0]).unwrap();
        assert!(c.qnet.is_none());
        assert!(c.stage_rates.is_empty());
        assert_eq!(c.offered, Some(125_000_000.0)); // 125 MHz / II 1
        assert!(c.ok());
    }

    #[test]
    fn throughput_bottleneck_is_critical_path_stage() {
        // Three stages, slowest is stage 1 (4 ns ⇒ slowest ⇒ critical path). The
        // qnet bottleneck MUST coincide with the critical-path stage.
        let j = pipe_json(1, 3, &[2.0, 4.0, 1.0], 4.0, 8.0, "125000000");
        let c = certify_throughput(&read_file(&j).unwrap()[0]).unwrap();
        let q = c.qnet.as_ref().unwrap();
        assert_eq!(q.bottleneck, 1);
        assert_eq!(c.critical_stage, Some(1));
        assert!(!c.bottleneck_mismatch);
        // Max sustainable = 1/4ns = 250 Mitems/s; offered 125 M < 250 M ⇒ stable.
        assert!((c.max_sustainable.unwrap() - 250_000_000.0).abs() < 1.0);
        assert!(q.stable);
        assert!(c.ok());
    }

    #[test]
    fn throughput_two_equal_slowest_stages_not_false_rejected() {
        // Two stages tie for slowest (5 ns each). The qnet bottleneck (first-wins)
        // and the critical-path stage must NOT be reported as disagreeing — a
        // value-based cross-check, robust to ties. Regression for the index
        // tie-break bug (qnet first-wins vs max_by last-wins).
        let j = pipe_json(1, 3, &[5.0, 5.0, 1.0], 5.0, 8.0, "125000000");
        let c = certify_throughput(&read_file(&j).unwrap()[0]).unwrap();
        assert!(!c.bottleneck_mismatch, "tied slowest stages must not false-reject");
        assert!(c.ok());
    }

    #[test]
    fn throughput_per_stage_rates_without_clock_skips_stability() {
        // Per-stage delays present but no clock at all (no @clock_freq, no
        // target_period_ns) ⇒ no offered load ⇒ no qnet, stability not asserted,
        // but the design is not falsely rejected either.
        let j = r#"{
          "schema": "aria-ir-json/v1", "id": 0, "name": "p",
          "ports": [], "clock_domains": [], "annotations": [], "nodes": [],
          "pipeline": {"id": 0, "num_stages": 2, "latency": 2, "initiation_interval": 1, "flow_control": {"fc": "none"},
            "stages": [{"index":0,"name":null,"comb_delay_ns":2.0,"lut_count":null,"reg_count":0,"forwarded_values":[]},
                       {"index":1,"name":null,"comb_delay_ns":1.0,"lut_count":null,"reg_count":0,"forwarded_values":[]}]},
          "systolic": null,
          "timing": {"c_slow_factor": 1, "target_period_ns": null, "critical_path_ns": 2.0, "retiming_weights": [], "buffers": []}
        }"#;
        let c = certify_throughput(&read_file(j).unwrap()[0]).unwrap();
        assert!(c.offered.is_none());
        assert!(c.qnet.is_none());
        assert_eq!(c.critical_stage, Some(0)); // 2 ns stage is slowest
        assert!(c.ok());
    }

    #[test]
    fn throughput_saturates_when_offered_exceeds_a_stage() {
        // 1 GHz offered (II 1) but stage 0 caps at 1/2ns = 500 Mitems/s ⇒ ρ>1 ⇒
        // SATURATED. (1 GHz clock here is an intentionally over-driven stress.)
        let j = pipe_json(1, 2, &[2.0, 0.5], 2.0, 1.0, "1000000000");
        let c = certify_throughput(&read_file(&j).unwrap()[0]).unwrap();
        let q = c.qnet.as_ref().unwrap();
        assert!(!q.stable, "a stage slower than the offered rate must saturate");
        assert!(!c.ok());
    }

    #[test]
    fn real_pipeline_demo_fixture_certifies() {
        // The committed faithful fixture (Aria `pipeline_demo.ahdl`): mac closes at
        // 125 MHz with a 0.8 ns critical path; no per-stage delays, so the critical
        // cross-check is skipped (not a mismatch).
        let src = std::fs::read_to_string("examples/fpga/pipeline_demo.aria.json").unwrap();
        let mods = read_file(&src).unwrap();
        let mac = mods.iter().find(|m| m.name == "mac").unwrap();
        let c = certify_timing(mac).unwrap();
        assert_eq!(c.closes_timing, Some(true)); // 0.8 ns ≤ 8 ns
        assert!(!c.critical_mismatch);
        assert!(c.ok());
    }

    #[test]
    fn as_u64_rejects_nonintegral_and_overflow() {
        // Bare numbers: integral & within exact-f64 range only.
        assert_eq!(Json::Num(3.0).as_u64(), Some(3));
        assert_eq!(Json::Num(3.9).as_u64(), None);          // fractional → reject
        assert_eq!(Json::Num(-1.0).as_u64(), None);         // negative → reject
        assert_eq!(Json::Num(1e30).as_u64(), None);         // > 2^53 → reject (no saturation)
        // Wide values still round-trip exactly through the string form.
        assert_eq!(Json::Str("18446744073709551615".into()).as_u64(), Some(u64::MAX));
    }
}
