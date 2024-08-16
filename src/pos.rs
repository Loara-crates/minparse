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
use core::convert::{AsRef, AsMut};
use core::ops::ControlFlow;

/// A position.
///
/// Characters in a text file can be organizes in a virtual grid in order to easily find characters
/// or parsing errors inside the file. Each file can be divided in multiple _lines_ separated by
/// line feed (U+000A) or carriage return + line feed (U+000D + U+000A).
///
/// To find a character then you need just the index of the line containing it (the first line has index `0`) 
/// and the character index inside thai line (also called the _column_).
///
/// Type `F` is any type that can be used to identify a text file, for example a
/// `String`, a `Path` or a custom type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Position<FILE = ()>{
    file : FILE,
    r : u32,
    c : u32,
}

impl<F> Position<F>{
    /// Create a new `Position` at specified `file`, `line` and `column` indices
    pub fn new_file(file : F, line : u32, column : u32) -> Self {
        Self{
            file,
            r : line,
            c : column,
        }
    }
    /// Create a new `Position` with `line=0` and `column=0`
    pub fn new_file_zero(file : F) -> Self {
        Self{
            file,
            r : 0,
            c : 0,
        }
    }
    /// Get the file identifier
    pub fn file(&self) -> &F {
        &self.file
    }
    /// Get the line number
    pub fn line(&self) -> u32 {
        self.r
    }
    /// Get the column number
    pub fn column(&self) -> u32 {
        self.c
    }
    /// Converts it to a reference
    pub fn make_ref<'a>(&'a self) -> Position<&'a F> {
        Position{
            file : &self.file,
            r : self.r,
            c : self.c,
        }
    }
}

impl<F> Position<F> where F : Default{
    /// Like [Position::new_file] but with `file` argument set to `F::default()`
    pub fn new(line : u32, column : u32) -> Self {
        Self::new_file(F::default(), line, column)
    }
    /// Like [Position::new_file_zero] but with `file` argument set to `F::default()`
    pub fn new_zero() -> Self {
        Self::new_file_zero(F::default())
    }
}

/// A positioned object, functionally equivalent to a struct containing an object of type `T` (the
/// wrapped object) and its position as a `Position<FILE>` object.
///
/// A parser uses characters inside a text file to create more complex objects. When the parsing
/// fails due to a syntax error you must inform the user about it, in particular you need to tell
/// the user where is the error.
///
/// This type associates to a type `T` (usually a token) a [Position] that allows the user to locate it inside
/// the file
#[derive(Clone, Copy, Debug)]
pub struct Pos<T, FILE = ()> {
    el : T,
    pos : Position<FILE>,
}

impl<T, F> AsRef<T> for Pos<T, F> {
    fn as_ref(&self) -> &T {
        &self.el
    }
}
impl<T, F> AsMut<T> for Pos<T, F> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.el
    }
}

impl<T, F> Pos<T, F> {
    /// Creates a new positioned object. See also [Posable::at]
    pub fn new(el : T, pos : Position<F>) -> Self {
        Self{el, pos}
    }
    /// Creates a new positioned object. See also [Posable::at_pos]
    pub fn new_pos(el : T, file : F, line : u32, column : u32) -> Self {
        Self{
            el,
            pos : Position{
                file,
                r : line,
                c : column,
            }
        }
    }
    /// Get the file identifier
    pub fn file(&self) -> &F {
        &self.pos.file
    }
    /// Get the line number
    pub fn line(&self) -> u32 {
        self.pos.r
    }
    /// Get the column number
    pub fn column(&self) -> u32 {
        self.pos.c
    }

    /// Moves the content to a different position
    pub fn mov<G>(self, pos : Position<G>) -> Pos<T, G> {
        Pos{el : self.el, pos}
    }
    /// Moves the content to a different position
    pub fn mov_to<U, G>(self, ot : Pos<U, G>) -> Pos<T, G> {
        self.mov(ot.pos)
    }
    ///Gets the position
    pub fn pos(&self) -> &Position<F> {
        &self.pos
    }
    ///Consumes the objects and returns the wrapped element
    pub fn take(self) -> T {
        self.el
    }
    ///Consumes the objects and returns the position
    pub fn take_pos(self) -> Position<F> {
        self.pos
    }
    ///Consumes the objects and returns both the wrapped element and the position
    pub fn take_all(self) -> (T, Position<F>) {
        (self.el, self.pos)
    }

    /// Tests the wrapped object
    pub fn test<TF : FnOnce(&T) -> bool>(&self, f : TF) -> bool {
        f(&self.el)
    }
    /// Tests both the wrapped object and its position
    pub fn test_pos<TF : FnOnce(&T, &Position<F>) -> bool>(&self, f : TF) -> bool {
        f(&self.el, &self.pos)
    }
    /// Apply `f` at the wrapped object
    pub fn map<U, MF : FnOnce(T) -> U>(self, f : MF) -> Pos<U, F> {
        Pos{
            el : f(self.el),
            pos : self.pos,
        }
    }
    /// Apply `f` at the wrapped object and its position
    pub fn map_pos<U, G, MF : FnOnce(T, Position<F>) -> (U, Position<G>)>(self, f : MF) -> Pos<U, G> {
        let (nel, npos) = f(self.el, self.pos);
        Pos{
            el : nel,
            pos : npos,
        }
    }

    /// Converts it to a reference
    pub fn make_ref<'a>(&'a self) -> Pos<&'a T, F> where F : Clone {
        Pos{
            el : &(self.el),
            pos : self.pos.clone(),
        }
    }
    /// Converts it to a mutable reference
    pub fn make_mut<'a>(&'a mut self) -> Pos<&'a mut T, F> where F : Clone {
        Pos{
            el : &mut(self.el),
            pos : self.pos.clone(),
        }
    }
}

impl<T, E, F> Pos<Result<T, E>, F> {
    /// Converts a `Pos<Result<T, E>, F>` into `Result<Pos<T, F>, Pos<E, F>>` that can be used with
    /// the `?` operator 
    pub fn throw(self) -> Result<Pos<T, F>, Pos<E, F>> {
        let pos = self.pos;
        match self.el {
            Ok(t) => Ok(Pos{
                el : t,
                pos,
            }),
            Err(e) => Err(Pos{
                el : e,
                pos,
            }),
        }
    }
    /// Converts a `Pos<Result<T, E>, F>` into `Result<Pos<T, F>, E>` that can be used with
    /// the `?` operator 
    pub fn throw_el(self) -> Result<Pos<T, F>, E> {
        match self.el {
            Ok(el) => Ok(Pos{el, pos : self.pos}),
            Err(e) => Err(e),
        }
    }
    /// Converts a `Pos<Result<T, E>, F>` into `Result<T, Pos<E, F>>` that can be used with
    /// the `?` operator 
    pub fn throw_err(self) -> Result<T, Pos<E, F>> {
        match self.el {
            Ok(t) => Ok(t),
            Err(el) => Err(Pos{el, pos : self.pos}),
        }
    }
}

impl<T, F> Pos<Option<T>, F> {
    /// Applies `Option::ok_or` to the wrapped object and then [Pos::throw] the resulting object
    pub fn ok_or<E>(self, err : E) -> Result<Pos<T, F>, Pos<E, F>> {
        self.map(|i| i.ok_or(err)).throw()
    }
    /// Applies `Option::ok_or` to the wrapped object and then [Pos::throw_err] the resulting
    /// object
    pub fn ok_or_err<E>(self, err : E) -> Result<T, Pos<E, F>> {
        self.map(|i| i.ok_or(err)).throw_err()
    }
}

impl<B, C, F> Pos<ControlFlow<B, C>, F> {
    /// Converts a `Pos<ControlFlow<B, C>, F>` into a `ControlFlow<Pos<B, F>, C>` by moving the
    /// resulting `Position` to the break case
    pub fn try_break(self) -> ControlFlow<Pos<B, F>, C> {
        let pos = self.pos;
        match self.el {
            ControlFlow::Break(b) => ControlFlow::Break(Pos::new(b, pos)),
            ControlFlow::Continue(c) => ControlFlow::Continue(c),
        }
    }
}
/// This trait allows you to easily create a `Pos<T, F>` object from a `T` object implementing the
/// `Posable` traits thanks to its methods [Posable::at] and [Posable::at_pos].
///
/// You don't need `T` to implement `Posable` in order to create a `Pos<T>`, this trait is useful
/// only if ypu prefer to use `t.at(pos)` in place of `Pos::new(t, pos)`.
pub trait Posable where Self : Sized{
    /// Creates a new `Pos<Self, F>` object. Calling `t.at(pos)` should be equivalent to call
    /// `Pos::new(t, pos)`
    fn at<F>(self, pos : Position<F>) -> Pos<Self, F> {
        Pos{el : self, pos}
    }
    /// Creates a new `Pos<Self, F>` object. Calling `t.at_pos(file, line, column)` should be equivalent 
    /// to call`Pos::new_pos(t, file, line, column)`
    fn at_pos<F>(self, file : F, line : u32, column : u32) -> Pos<Self, F> {
        Self::at(self, Position{file, r : line, c : column})
    }
}

impl<T : Posable> Posable for Option<T> {}
impl<T : Posable, E : Posable> Posable for Result<T, E> {}
impl Posable for char {}

