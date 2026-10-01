//! String literals of outlined calls.
//!
//! The compiler folds short string literals into immediate stores, so an
//! outlined constructor call gets its literal back as constant data (a
//! zero-extended register-sized value holding the characters, and a terminator
//! when there is room), the same form Binary Ninja uses for the literals of
//! its own `__builtin_strncpy` outlining.  Longer literals are passed as
//! pointers to the binary's own copy of the text.

pub const REGISTER_SIZES: [u16; 4] = [1, 2, 4, 8];

/// The constant-data size holding `text_length` characters: the smallest
/// register size that fits them (the recognizer reads the text up to the first
/// zero byte, so a terminator is implied where there is no room for one).
pub fn data_size(text_length: usize) -> Option<u16> {
    REGISTER_SIZES.iter().copied().find(|s| *s as usize >= text_length)
}

/// The text a constant-data buffer spells: printable ASCII followed only by
/// terminators, or None.
pub fn literal_text(raw: &[u8]) -> Option<String> {
    let end = raw.iter().rposition(|b| *b != 0).map(|i| i + 1).unwrap_or(0);
    let text = &raw[..end];
    if text.is_empty() || text.iter().any(|b| *b < 0x20 || *b > 0x7e) {
        return None;
    }
    Some(String::from_utf8_lossy(text).into_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes_and_text() {
        assert_eq!(data_size(1), Some(1));
        assert_eq!(data_size(3), Some(4));
        assert_eq!(data_size(8), Some(8));
        assert_eq!(data_size(9), None);
        assert_eq!(literal_text(b"cmd:\0\0\0\0"), Some("cmd:".to_string()));
        assert_eq!(literal_text(b"\0\0"), None);
        assert_eq!(literal_text(b"a\x01"), None);
    }
}
