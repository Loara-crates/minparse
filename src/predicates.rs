/// Tests if a character is alphabetic
pub fn is_alphabetic(c : char) -> bool {
    c.is_alphabetic()
}
/// Tests if a character belongs to the `0-9` interval
pub fn is_digit(c : char) -> bool {
    c.is_ascii_digit()
}
/// Tests if a character belongs to `0-9`, `a-f` or `A-F`
pub fn is_digit_hex(c : char) -> bool {
    c.is_ascii_hexdigit()
}
/// Tests is a character is an ASCII whitespace
pub fn is_whitespace(c : char) -> bool {
    c.is_ascii_whitespace()
}
/// Tests if a character is a newline character (U+000A, `\n`). Carriage return (U+000D, `\r`) is
/// not detected by this function because it is usually followed by the newline character.
pub fn is_newline(c : char) -> bool {
    c == '\n'
}
