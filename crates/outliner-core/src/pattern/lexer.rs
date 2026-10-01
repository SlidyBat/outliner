//! Tokens of the pattern language.

use super::{PatternError, Result};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `$name`, without the dollar.
    Ph,
    Num,
    /// A quoted string, without the quotes.
    Str,
    /// A signed or unsigned operator: `s<`, `u>=`, `s>>`, `u/`, `s%`.
    Sop,
    /// An identifier, possibly qualified: `std::string::size`, `std::string::~string`.
    Ident,
    /// Punctuation: `...`, `=>`, `<<`, `>>`, `==`, `!=`, `<=`, `>=`, or a single character.
    Op,
    Eof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: Kind,
    pub text: String,
    pub col: usize,
}

fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}

fn is_ident_char(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

/// Tokenizes one line (or statement) of pattern text.
pub fn tokenize(text: &str, line: u32) -> Result<Vec<Token>> {
    let b = text.as_bytes();
    let mut tokens = Vec::new();
    let mut pos = 0;
    while pos < b.len() {
        let c = b[pos];
        let start = pos;
        if c.is_ascii_whitespace() {
            pos += 1;
            continue;
        }
        if c == b'$' && pos + 1 < b.len() && is_ident_start(b[pos + 1]) {
            pos += 1;
            while pos < b.len() && is_ident_char(b[pos]) {
                pos += 1;
            }
            tokens.push(Token { kind: Kind::Ph, text: text[start + 1..pos].to_string(), col: start });
            continue;
        }
        if c.is_ascii_digit() {
            if c == b'0' && pos + 1 < b.len() && (b[pos + 1] == b'x' || b[pos + 1] == b'X') {
                pos += 2;
                while pos < b.len() && b[pos].is_ascii_hexdigit() {
                    pos += 1;
                }
            } else {
                while pos < b.len() && b[pos].is_ascii_digit() {
                    pos += 1;
                }
            }
            tokens.push(Token { kind: Kind::Num, text: text[start..pos].to_string(), col: start });
            continue;
        }
        if c == b'"' {
            let end = text[pos + 1..].find('"').map(|k| pos + 1 + k);
            let Some(end) = end else {
                return Err(PatternError(format!("line {line}: unexpected character '\"'")));
            };
            tokens.push(Token { kind: Kind::Str, text: text[pos + 1..end].to_string(), col: start });
            pos = end + 1;
            continue;
        }
        // s<=, u>=, s>>, s<, u<, s>, u>, u/, s/, u%, s%
        if (c == b's' || c == b'u') && pos + 1 < b.len() {
            let rest = &text[pos + 1..];
            let op_len = if rest.starts_with("<=") || rest.starts_with(">=") || rest.starts_with(">>") {
                2
            } else if rest.starts_with(['<', '>', '/', '%']) {
                1
            } else {
                0
            };
            if op_len > 0 {
                pos += 1 + op_len;
                tokens.push(Token { kind: Kind::Sop, text: text[start..pos].to_string(), col: start });
                continue;
            }
        }
        if is_ident_start(c) {
            pos += 1;
            while pos < b.len() && is_ident_char(b[pos]) {
                pos += 1;
            }
            // qualified: ::name or ::~name
            loop {
                if pos + 2 < b.len() && b[pos] == b':' && b[pos + 1] == b':' {
                    let mut k = pos + 2;
                    if k < b.len() && b[k] == b'~' {
                        k += 1;
                    }
                    if k < b.len() && is_ident_start(b[k]) {
                        k += 1;
                        while k < b.len() && is_ident_char(b[k]) {
                            k += 1;
                        }
                        pos = k;
                        continue;
                    }
                }
                break;
            }
            tokens.push(Token { kind: Kind::Ident, text: text[start..pos].to_string(), col: start });
            continue;
        }
        let rest = &text[pos..];
        let op = ["...", "=>", "<<", ">>", "==", "!=", "<=", ">="]
            .iter()
            .find(|o| rest.starts_with(*o))
            .map(|o| o.len())
            .or_else(|| {
                if b"-+*&|^~()[],=.<>!/%".contains(&c) {
                    Some(1)
                } else {
                    None
                }
            });
        match op {
            Some(len) => {
                tokens.push(Token { kind: Kind::Op, text: text[pos..pos + len].to_string(), col: start });
                pos += len;
            }
            None => {
                let ch = text[pos..].chars().next().unwrap_or('?');
                return Err(PatternError(format!("line {line}: unexpected character {ch:?}")));
            }
        }
    }
    tokens.push(Token { kind: Kind::Eof, text: String::new(), col: text.len() });
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokens() {
        let toks = tokenize("$ret = call(std::string::~string, \"_memcmp\", 0x17) s< -1 ...", 1).unwrap();
        let texts: Vec<(Kind, &str)> = toks.iter().map(|t| (t.kind.clone(), t.text.as_str())).collect();
        assert_eq!(
            texts,
            vec![
                (Kind::Ph, "ret"),
                (Kind::Op, "="),
                (Kind::Ident, "call"),
                (Kind::Op, "("),
                (Kind::Ident, "std::string::~string"),
                (Kind::Op, ","),
                (Kind::Str, "_memcmp"),
                (Kind::Op, ","),
                (Kind::Num, "0x17"),
                (Kind::Op, ")"),
                (Kind::Sop, "s<"),
                (Kind::Op, "-"),
                (Kind::Num, "1"),
                (Kind::Op, "..."),
                (Kind::Eof, ""),
            ]
        );
        assert!(tokenize("$a @ 1", 3).is_err());
        let toks = tokenize("sx.q($b) => zx($b)", 1).unwrap();
        assert_eq!(toks[0].text, "sx");
        assert_eq!(toks[1].text, ".");
        assert!(toks.iter().any(|t| t.text == "=>"));
    }
}
