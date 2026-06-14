//! A deliberately tiny TOML subset — enough for `*.model.toml` authoring, no
//! dependency (SPEC §13 keeps the build offline-safe). We support exactly what
//! the model DSL needs and reject the rest with a line-numbered error:
//!
//!   * line comments  `# …`           (whole-line only)
//!   * scalars        `key = "str"`   and bare `key = ident`
//!   * arrays         `key = ["a", "b"]`  (string/ident elements)
//!   * arrays-of-tables `[[name]]` opening a block of `key = value` lines
//!
//! Top-level `key = value` go in `scalars`; lines after a `[[name]]` header go
//! into the most recent table of that name. That is all CPN/SPN will need too
//! (a marking is just `pre = ["a", "a", "b"]`, a multiset as repeats).

use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum Value {
    Str(String),
    Arr(Vec<String>),
}

impl Value {
    /// The scalar string, or an error naming `what` for diagnostics.
    pub fn as_str(&self, what: &str) -> Result<&str, String> {
        match self {
            Value::Str(s) => Ok(s),
            Value::Arr(_) => Err(format!("`{what}` must be a string, found an array")),
        }
    }
    /// The array, or an error naming `what`.
    pub fn as_arr(&self, what: &str) -> Result<&[String], String> {
        match self {
            Value::Arr(a) => Ok(a),
            Value::Str(_) => Err(format!("`{what}` must be an array, found a string")),
        }
    }
}

#[derive(Debug, Default)]
pub struct Doc {
    pub scalars: HashMap<String, Value>,
    pub tables: HashMap<String, Vec<HashMap<String, Value>>>,
}

impl Doc {
    pub fn scalar(&self, key: &str) -> Option<&Value> {
        self.scalars.get(key)
    }
    pub fn table(&self, name: &str) -> &[HashMap<String, Value>] {
        self.tables.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

/// Parse the subset. `cur` tracks the table block we are filling (None = top).
pub fn parse(src: &str) -> Result<Doc, String> {
    let mut doc = Doc::default();
    let mut cur: Option<String> = None;

    let lines: Vec<&str> = src.lines().collect();
    let mut n = 0;
    while n < lines.len() {
        let raw = lines[n];
        let ln = n + 1;

        // Multi-line triple-quoted value: `key = """ … """` spanning lines. We
        // accumulate raw lines (no comment-strip) until the closing `"""`.
        if let Some((key, after)) = split_triple(raw) {
            let mut body = String::new();
            if let Some(end) = after.find("\"\"\"") {
                body.push_str(&after[..end]); // closes on the same line
            } else {
                body.push_str(after);
                loop {
                    n += 1;
                    if n >= lines.len() {
                        return Err(format!("line {ln}: unterminated `\"\"\"` string"));
                    }
                    if let Some(end) = lines[n].find("\"\"\"") {
                        body.push('\n');
                        body.push_str(&lines[n][..end]);
                        break;
                    } else {
                        body.push('\n');
                        body.push_str(lines[n]);
                    }
                }
            }
            insert(&mut doc, &cur, key.trim().to_string(), Value::Str(body));
            n += 1;
            continue;
        }

        let line = strip_comment(raw).trim();
        if line.is_empty() {
            n += 1;
            continue;
        }

        if let Some(rest) = line.strip_prefix("[[") {
            let name = rest
                .strip_suffix("]]")
                .ok_or_else(|| format!("line {ln}: expected `]]` to close table header"))?
                .trim()
                .to_string();
            if name.is_empty() {
                return Err(format!("line {ln}: empty table name"));
            }
            doc.tables.entry(name.clone()).or_default().push(HashMap::new());
            cur = Some(name);
            n += 1;
            continue;
        }

        let eq = line
            .find('=')
            .ok_or_else(|| format!("line {ln}: expected `key = value`"))?;
        let key = line[..eq].trim().to_string();
        let val = parse_value(line[eq + 1..].trim(), ln)?;
        if key.is_empty() {
            return Err(format!("line {ln}: empty key"));
        }
        insert(&mut doc, &cur, key, val);
        n += 1;
    }
    Ok(doc)
}

/// Insert a `key = value` into the current table block (if inside one) or the
/// top-level scalars.
fn insert(doc: &mut Doc, cur: &Option<String>, key: String, val: Value) {
    match cur {
        Some(name) => {
            let block = doc.tables.get_mut(name).and_then(|v| v.last_mut()).unwrap();
            block.insert(key, val);
        }
        None => {
            doc.scalars.insert(key, val);
        }
    }
}

/// If `raw` is `key = """…`, return `(key, rest-after-the-opening-triple-quote)`.
fn split_triple(raw: &str) -> Option<(&str, &str)> {
    let eq = raw.find('=')?;
    let (key, rhs) = (raw[..eq].trim_start(), raw[eq + 1..].trim_start());
    // Reject if the `=` is inside brackets/quotes (cheap guard: keys are bare).
    if key.is_empty() || key.contains(['[', '"', '#']) {
        return None;
    }
    rhs.strip_prefix("\"\"\"").map(|rest| (key, rest))
}

/// Drop a `#` comment, but not one inside a quoted string. Whole-line and
/// trailing comments are both handled here.
fn strip_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let (mut in_s, mut in_d) = (false, false);
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'\'' if !in_d => in_s = !in_s,
            b'"' if !in_s => in_d = !in_d,
            b'#' if !in_s && !in_d => return &line[..i],
            _ => {}
        }
    }
    line
}

fn parse_value(s: &str, ln: usize) -> Result<Value, String> {
    if let Some(inner) = s.strip_prefix('[') {
        let inner = inner
            .strip_suffix(']')
            .ok_or_else(|| format!("line {ln}: expected `]` to close array"))?;
        let mut out = Vec::new();
        for piece in inner.split(',') {
            let p = piece.trim();
            if p.is_empty() {
                continue; // tolerate trailing comma / empty array
            }
            out.push(unquote(p, ln)?);
        }
        Ok(Value::Arr(out))
    } else {
        Ok(Value::Str(unquote(s, ln)?))
    }
}

/// Strip matching surrounding quotes; a bare token is taken verbatim.
fn unquote(s: &str, ln: usize) -> Result<String, String> {
    let b = s.as_bytes();
    if b.len() >= 2 && (b[0] == b'"' || b[0] == b'\'') && b[b.len() - 1] == b[0] {
        Ok(s[1..s.len() - 1].to_string())
    } else if s.contains('"') || s.contains('\'') {
        Err(format!("line {ln}: unbalanced quote in `{s}`"))
    } else {
        Ok(s.to_string())
    }
}
