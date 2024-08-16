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

//! Simple parsing tools
//!
//! This crate is a collection of objects and algorithms shared among different crates that needs
//! to implement a parser. 
//!
//! The [predicates] module contains some useful functions in order to analize ASCII and Unicode characters. 
//! Some of these functions are just wrappers of functions defined in the standard library.
//!
//! A [``Position``] is an object that identifies a (textual) *file* and a position inside it,
//! represented as a *line index* and a *column index*. The main role of a [Position] object is to
//! uniquely identify a single character or a (textual) token inside a file in order to allow the
//! user to easily find it.
//!
//! A [``Pos<T>``](Pos) is just an object containing a `T` object and a `Position`. Usually you set
//! `T` to be equal to `char` or to a custom token type.
//!
//! A [`DefLine`] is a sort of "iterator" that returns `Pos<Option<char>, FILE>` in
//! place of `Option<char>`. Moreover, it defines a lot of useful functions for parsing tokens from
//! a text source.
#![warn(missing_docs)]
#![no_std]

/// A collection of predicates for characters.
pub mod predicates;
mod pos;
mod defline;

pub use crate::pos::*;
pub use crate::defline::*; 
