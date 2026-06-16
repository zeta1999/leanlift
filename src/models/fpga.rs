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
    });

    let timing = v.get("timing");
    let target_period_ns = timing.and_then(|t| t.get("target_period_ns")).and_then(Json::as_f64);
    let critical_path_ns = timing.and_then(|t| t.get("critical_path_ns")).and_then(Json::as_f64);

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
    })
}

/// Parse a whole IR-JSON file (possibly several modules) into typed views.
pub fn read_file(src: &str) -> Result<Vec<AriaModule>, String> {
    parse_stream(src)?.iter().map(read_module).collect()
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
        \x20 (planned: lift fpga check|prove|timing|equiv — see docs/PLAN-fpga.md)\n"
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
        Some(s) if !s.starts_with('-') => "info",
        _ => usage(),
    };
    match verb {
        "info" => info_cmd(argv),
        _ => usage(),
    }
}

fn info_cmd(a: Vec<String>) {
    let mut file: Option<String> = None;
    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
            s if s.starts_with("--") => {
                eprintln!("unknown flag: {s}");
                usage();
            }
            _ => {
                if file.is_some() {
                    usage();
                }
                file = Some(a[i].clone());
            }
        }
        i += 1;
    }
    let path = file.unwrap_or_else(|| usage());
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("error reading {path}: {e}");
        exit(2);
    });
    let modules = read_file(&src).unwrap_or_else(|e| {
        eprintln!("error: {path}: {e}");
        exit(1);
    });

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
