//! A minimal, dependency-free XML reader — just enough for the standard
//! behavioural formats (SCXML now; PNML/BT-XML later). No namespaces beyond
//! prefix-stripping, no DTD, no entities beyond the five predefined ones. The
//! project is intentionally dependency-free (SPEC §13), so this mirrors the tiny
//! `toml.rs` reader.
//!
//! Returns a tree of `Node { tag, attrs, children, text }`. Comments,
//! `<?xml …?>` declarations, and `<!DOCTYPE …>` are skipped; namespace prefixes
//! (`sc:state` → `state`) are stripped.

#[derive(Debug, Default)]
pub struct Node {
    pub tag: String,
    pub attrs: Vec<(String, String)>,
    pub children: Vec<Node>,
    pub text: String,
}

impl Node {
    pub fn attr(&self, key: &str) -> Option<&str> {
        self.attrs.iter().find(|(k, _)| k == key).map(|(_, v)| v.as_str())
    }
    /// All direct children with the given tag.
    pub fn children(&self, tag: &str) -> impl Iterator<Item = &Node> {
        let tag = tag.to_string();
        self.children.iter().filter(move |c| c.tag == tag)
    }
    /// Recursively collect all descendants (and self) with the given tag.
    pub fn descendants<'a>(&'a self, tag: &str, out: &mut Vec<&'a Node>) {
        if self.tag == tag {
            out.push(self);
        }
        for c in &self.children {
            c.descendants(tag, out);
        }
    }
}

/// Parse a document, returning its root element.
pub fn parse(src: &str) -> Result<Node, String> {
    let b: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut stack: Vec<Node> = Vec::new();
    let mut root: Option<Node> = None;

    while i < b.len() {
        if b[i] == '<' {
            // Skip <?...?>, <!-- ... -->, <!...>.
            if starts(&b, i, "<?") {
                i = find(&b, i, "?>").map(|j| j + 2).ok_or("unterminated <?…?>")?;
                continue;
            }
            if starts(&b, i, "<!--") {
                i = find(&b, i, "-->").map(|j| j + 3).ok_or("unterminated comment")?;
                continue;
            }
            if starts(&b, i, "<!") {
                i = find(&b, i, ">").map(|j| j + 1).ok_or("unterminated <!…>")?;
                continue;
            }
            if starts(&b, i, "</") {
                // Closing tag — pop and attach to parent.
                let end = find(&b, i, ">").ok_or("unterminated closing tag")?;
                i = end + 1;
                let node = stack.pop().ok_or("closing tag without an open element")?;
                if let Some(parent) = stack.last_mut() {
                    parent.children.push(node);
                } else {
                    root = Some(node);
                }
                continue;
            }
            // Opening (or self-closing) tag.
            let end = find(&b, i, ">").ok_or("unterminated tag")?;
            let raw: String = b[i + 1..end].iter().collect();
            i = end + 1;
            let self_closing = raw.trim_end().ends_with('/');
            let inner = raw.trim_end().trim_end_matches('/').trim();
            let (tag, attrs) = parse_tag(inner);
            let node = Node { tag, attrs, children: Vec::new(), text: String::new() };
            if self_closing {
                if let Some(parent) = stack.last_mut() {
                    parent.children.push(node);
                } else {
                    root = Some(node);
                }
            } else {
                stack.push(node);
            }
        } else {
            // Text content up to the next '<' — accrues to the open element.
            let start = i;
            while i < b.len() && b[i] != '<' {
                i += 1;
            }
            let text: String = b[start..i].iter().collect();
            let text = decode(text.trim());
            if !text.is_empty() {
                if let Some(node) = stack.last_mut() {
                    node.text.push_str(&text);
                }
            }
        }
    }
    root.ok_or_else(|| "no root element".into())
}

/// Parse `tag attr="v" attr2='v2'` → (tag, attrs), stripping any `ns:` prefix.
fn parse_tag(s: &str) -> (String, Vec<(String, String)>) {
    let mut chars = s.char_indices().peekable();
    // tag name = up to first whitespace
    let mut name_end = s.len();
    for (idx, c) in s.char_indices() {
        if c.is_whitespace() {
            name_end = idx;
            break;
        }
    }
    let tag = strip_ns(&s[..name_end]);
    let mut attrs = Vec::new();
    let rest = &s[name_end..];
    let rb: Vec<char> = rest.chars().collect();
    let mut j = 0;
    while j < rb.len() {
        while j < rb.len() && rb[j].is_whitespace() {
            j += 1;
        }
        let kstart = j;
        while j < rb.len() && rb[j] != '=' && !rb[j].is_whitespace() {
            j += 1;
        }
        if kstart == j {
            break;
        }
        let key: String = rb[kstart..j].iter().collect();
        while j < rb.len() && (rb[j].is_whitespace() || rb[j] == '=') {
            j += 1;
        }
        if j >= rb.len() {
            break;
        }
        let quote = rb[j];
        if quote != '"' && quote != '\'' {
            break;
        }
        j += 1;
        let vstart = j;
        while j < rb.len() && rb[j] != quote {
            j += 1;
        }
        let val: String = rb[vstart..j].iter().collect();
        j += 1; // skip closing quote
        attrs.push((strip_ns(&key), decode(&val)));
    }
    let _ = &mut chars;
    (tag, attrs)
}

fn strip_ns(s: &str) -> String {
    s.rsplit(':').next().unwrap_or(s).to_string()
}

fn starts(b: &[char], i: usize, pat: &str) -> bool {
    let p: Vec<char> = pat.chars().collect();
    i + p.len() <= b.len() && b[i..i + p.len()] == p[..]
}

fn find(b: &[char], from: usize, pat: &str) -> Option<usize> {
    let p: Vec<char> = pat.chars().collect();
    (from..b.len().saturating_sub(p.len() - 1)).find(|&k| b[k..k + p.len()] == p[..])
}

/// Decode the five predefined XML entities.
fn decode(s: &str) -> String {
    s.replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
        .replace("&amp;", "&")
}
