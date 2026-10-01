//! The pattern file format: chunks separated by a line holding only `---`.

use std::collections::HashSet;

/// The chunks of a pattern file: the pieces between lines that are just `---`.
pub fn split_chunks(content: &str) -> Vec<String> {
    let mut chunks = Vec::new();
    let mut current: Vec<&str> = Vec::new();
    for line in content.lines() {
        if line.trim() == "---" {
            chunks.push(current.join("\n"));
            current.clear();
        } else {
            current.push(line);
        }
    }
    chunks.push(current.join("\n"));
    chunks
}

/// A pattern file holding `chunks` (empty ones dropped), the inverse of
/// [`split_chunks`]: each chunk on lines of its own, separated by `---`.
pub fn join_chunks<S: AsRef<str>>(chunks: &[S]) -> String {
    let kept: Vec<&str> = chunks
        .iter()
        .map(|c| c.as_ref())
        .filter(|c| !c.trim().is_empty())
        .map(|c| c.trim_matches('\n'))
        .collect();
    if kept.is_empty() {
        String::new()
    } else {
        kept.join("\n\n---\n\n") + "\n"
    }
}

/// What makes two chunks the same pattern: the pattern as the printer writes
/// it, so comments, blank lines and spacing do not count.  A chunk that does
/// not parse is compared by its text without comments, its whitespace
/// collapsed.
pub fn chunk_key(text: &str) -> String {
    let collapse = |line: &str| line.split_whitespace().collect::<Vec<_>>().join(" ");
    let lines: Vec<String> = match super::parse_pattern(text) {
        Ok(pattern) => super::format_pattern(&pattern).lines().map(collapse).collect(),
        Err(_) => text.lines().map(|line| collapse(&super::parser::strip_comment(line))).collect(),
    };
    lines.into_iter().filter(|line| !line.is_empty()).collect::<Vec<_>>().join("\n")
}

/// The patterns already present, for telling which chunks of a pattern file
/// are new (see [`chunk_key`]).
#[derive(Default)]
pub struct ChunkSet {
    keys: HashSet<String>,
}

impl ChunkSet {
    pub fn new<S: AsRef<str>>(present: impl IntoIterator<Item = S>) -> ChunkSet {
        ChunkSet { keys: present.into_iter().map(|text| chunk_key(text.as_ref())).collect() }
    }

    /// Adds `chunk`; false when the same pattern was already present.
    pub fn insert(&mut self, chunk: &str) -> bool {
        self.keys.insert(chunk_key(chunk))
    }
}

fn directive<'a>(text: &'a str, name: &str) -> Option<&'a str> {
    for line in text.lines() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix(name) {
            let rest = rest.trim_start();
            if let Some(value) = rest.strip_prefix(':') {
                let value = value.trim();
                if !value.is_empty() {
                    return Some(value);
                }
            }
        }
    }
    None
}

/// A chunk's title: the rules chunk's name, or the function's name with its
/// parameter names (overloads share a name, so `string(s, other)` and
/// `string(s, str, n)` tell the constructors apart).
pub fn chunk_title(text: &str) -> String {
    if let Some(name) = directive(text, "rules") {
        return name.to_string();
    }
    if text.lines().any(|l| {
        let t = l.trim_start();
        t.strip_prefix("rewrite").map(|r| r.trim_start().starts_with(':')).unwrap_or(false)
    }) {
        return "rewrite rules".to_string();
    }
    let Some(sig) = directive(text, "signature") else { return "pattern".to_string() };
    // The name is the token right before the parameter list: backticked, or an
    // identifier that may be qualified (std::string::size, std::string::~string).
    let Some(open) = sig.find('(') else { return "pattern".to_string() };
    let head = sig[..open].trim_end();
    let name = if let Some(stripped) = head.strip_suffix('`') {
        match stripped.rfind('`') {
            Some(k) => stripped[k + 1..].to_string(),
            None => return "pattern".to_string(),
        }
    } else {
        let start = head
            .char_indices()
            .rev()
            .take_while(|(_, c)| c.is_alphanumeric() || *c == '_' || *c == ':' || *c == '~')
            .last()
            .map(|(i, _)| i);
        match start {
            Some(i) if i < head.len() => head[i..].to_string(),
            _ => return "pattern".to_string(),
        }
    };
    if name.is_empty() {
        return "pattern".to_string();
    }
    let Some(close) = sig.rfind(')') else { return "pattern".to_string() };
    if close <= open {
        return "pattern".to_string();
    }
    // A backticked type may hold commas.
    let mut params = String::new();
    let mut in_ticks = false;
    for c in sig[open + 1..close].chars() {
        if c == '`' {
            in_ticks = !in_ticks;
            if !in_ticks {
                params.push('T');
            }
        } else if !in_ticks {
            params.push(c);
        }
    }
    let names: Vec<String> = params
        .split(',')
        .filter_map(|piece| {
            piece
                .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .filter(|w| !w.is_empty())
                .next_back()
                .map(|w| w.to_string())
        })
        .collect();
    format!("{}({})", name, names.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn titles() {
        assert_eq!(
            chunk_title("signature: uint64_t `std::string::size`(`std::__1::string` const* s) __pure\n$ret = 1\n"),
            "std::string::size(s)"
        );
        assert_eq!(
            chunk_title("signature: void `std::string::string`(`std::__1::string`* s, char const* str, uint64_t n)\n"),
            "std::string::string(s, str, n)"
        );
        assert_eq!(chunk_title("signature: void `std::string::~string`(`std::__1::string`* s)\n"), "std::string::~string(s)");
        assert_eq!(chunk_title("signature: char const* my_accessor(`std::__1::string` const* s) __pure\n"), "my_accessor(s)");
        assert_eq!(chunk_title("signature: int f()\n"), "f()");
        assert_eq!(
            chunk_title("signature: size_t g(`std::vector<int, std::allocator<int>>` const* v, int i)\n"),
            "g(v, i)"
        );
        assert_eq!(chunk_title("rules: libc++ spellings\nrewrite: $a + -1 => $a - 1\n"), "libc++ spellings");
        assert_eq!(chunk_title("rewrite: $a + -1 => $a - 1\n"), "rewrite rules");
        assert_eq!(chunk_title("# nothing yet\n"), "pattern");
    }

    #[test]
    fn duplicates_ignore_comments_and_spacing() {
        let saved = "signature: int f(int a)\n$ret = $a + 1\n";
        let mut present = ChunkSet::new([saved]);
        // the same pattern, written differently
        assert!(!present.insert("# f, as the file has it\nsignature:  int f(int a)\n\n    $ret = ($a+1)   // add one\n"));
        // a different constant, a different type constraint, a different name
        assert!(present.insert("signature: int f(int a)\n$ret = $a + 2\n"));
        assert!(present.insert("signature: int f(int a)\n$a : int32_t\n$ret = $a + 1\n"));
        assert!(present.insert("signature: int g(int a)\n$ret = $a + 1\n"));
        // a chunk is a duplicate of one inserted before it
        assert!(!present.insert("signature: int g(int a)\n$ret = $a + 1 # again\n"));
        // rules chunks, and text that does not parse
        assert!(present.insert("rules: r\nrewrite: $a + -1 => $a - 1\n"));
        assert!(!present.insert("rules: r\nrewrite:   $a + -1  =>  $a - 1   # same\n"));
        assert!(present.insert("signature: int h(int a)\n$ret = $a +\n"));
        assert!(!present.insert("signature: int h(int a)  # still broken\n$ret = $a  +\n"));
    }

    #[test]
    fn round_trip() {
        let text = "a\n\n---\n\nb\n";
        let chunks = split_chunks(text);
        assert_eq!(chunks.len(), 2);
        assert_eq!(join_chunks(&chunks), text);
        assert_eq!(join_chunks(&["", "  \n"]), "");
        assert_eq!(join_chunks(&["a\n", "\nb"]), "a\n\n---\n\nb\n");
    }
}
