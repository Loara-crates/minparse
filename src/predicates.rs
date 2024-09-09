/*
 * Minparser Simple parsing functions
 *
 * Copyright (C) 2024 Paolo De Donato
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */
/// Tests if a character is alphabetic
#[must_use]
pub fn is_alphabetic(c : char) -> bool {
    c.is_alphabetic()
}
/// Tests if a character belongs to the `0-9` interval
#[must_use]
pub const fn is_digit(c : char) -> bool {
    c.is_ascii_digit()
}
/// Tests if a character belongs to `0-9`, `a-f` or `A-F`
#[must_use]
pub const fn is_digit_hex(c : char) -> bool {
    c.is_ascii_hexdigit()
}
/// Tests is a character is an ASCII whitespace
#[must_use]
pub const fn is_whitespace(c : char) -> bool {
    c.is_ascii_whitespace()
}
/// Tests if a character is a newline character (U+000A, `\n`). Carriage return (U+000D, `\r`) is
/// not detected by this function because it is usually followed by the newline character.
#[must_use]
pub const fn is_newline(c : char) -> bool {
    c == '\n'
}
