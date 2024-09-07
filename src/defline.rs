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
use core::ops::ControlFlow;
use crate::pos::{Pos, Position, Posable};
use core::iter::{Iterator, IntoIterator, Peekable};

/// An iterator wrapper that removes `\r` characters.
///
/// This crate assumes that `\n` separates lines, so if your iterator uses `\r\n` as line delimiter you
/// can use this wrapper to normalize it to `\n`.
pub struct NLIterator<I>{
    iter : I,
}

impl<I> NLIterator<I>{
    /// Creates a new `NLIterator` from an already existent iterator.
    pub fn new(iter : I) -> Self {
        Self {iter}
    }
}

impl<I> Iterator for NLIterator<I> where I : Iterator<Item = char>{
    type Item = char;

    fn next(&mut self) -> Option<char>{
        loop{
            match self.iter.next(){
                None => return None,
                Some(ch) => if ch != '\r' {
                    return Some(ch);
                },
            }
        }
    }
}

/// A sequential container that can accept new objects.
///
/// This trait is used by [DefLine::grab_cf] and similar methods in [DefLine].
pub trait Appender<T>{
    /// Creates a new empty container.
    fn new_empty() -> Self;
    /// Push a new object in the container.
    fn push(&mut self, i : T);
}
/// A sequential container with additional functionalities.
///
/// This trait is used by [DefLine::cap_ht_cf] and similar methods in [DefLine].
pub trait AppenderExt<T> : Appender<T>{
    /// Tests if the container is empty
    fn is_empty(&self) -> bool;
    /// Clears the container
    fn clear(&mut self);
    /// Pushes all the elements of `a` into `self` and then clears `a`.
    fn drain(&mut self, a : &mut Self);
}

#[cfg(feature = "alloc")]
impl Appender<char> for alloc::string::String{
    fn new_empty() -> Self{
        alloc::string::String::new()
    }
    fn push(&mut self, i : char){
        self.push(i)
    }
}
#[cfg(feature = "alloc")]
impl AppenderExt<char> for alloc::string::String{
    fn is_empty(&self) -> bool{
        (self as &Self).is_empty()
    }
    fn clear(&mut self){
        self.clear();
    }
    fn drain(&mut self, a : &mut Self){
        self.push_str(&a);
        a.clear();
    }
}
#[cfg(feature = "alloc")]
impl<T> Appender<T> for alloc::vec::Vec<T>{
    fn new_empty() -> Self{
        alloc::vec::Vec::new()
    }
    fn push(&mut self, i : T){
        self.push(i)
    }
}
#[cfg(feature = "alloc")]
impl<T> AppenderExt<T> for alloc::vec::Vec<T>{
    fn is_empty(&self) -> bool{
        (self as &Self).is_empty()
    }
    fn drain(&mut self, a : &mut Self){
        self.append(a);
        a.clear();
    }
    fn clear(&mut self){
        self.clear();
    }
}

/// An integer appender.
///
/// When `T` implements `Default`, `AddAssign<T>` and `MulAssign<usize>` then `NumAppender<T, N>`
/// implements `[``Appender<T>``] in the following way: if `self` contains `t` of type `T` then
/// [pushing](Appender::push) `s` in `self` updates `t` into `(t * N) + s`.
///
/// This struct is useful when you want to parse an integer from a text file.
pub struct NumAppender<T, const N : u32>(pub Option<T>);

impl<T, const N : u32> NumAppender<T, N>{
    /// Tests if it is empty.
    ///
    /// Returns `true` if and only if no value has been pushed.
    pub fn is_empty(&self) -> bool{
        self.0.is_none()
    }
}

impl<T, const N : u32> Appender<T> for NumAppender<T, N> where T : core::ops::AddAssign<T> + core::ops::MulAssign<u32>  {
    fn new_empty() -> Self{
        Self(None)
    }
    fn push(&mut self, i : T){
        if let Some(c) = &mut self.0 {
            *c *= N;
            *c += i;
        }
        else{
            self.0 = Some(i);
        }
    }
}

/// A positioned iterator
///
/// When `I` is a `char` iterator `DefLine<I, FILE>` provides the method
/// [next_pos](DefLine::next_pos) that returns the next available positioned character as
/// `Pos<Option<char>, FILE>` by calling `I::next`.
pub struct DefLine<I, FILE = ()>{
    iter : I,
    file : FILE,
    r : u32,
    c : u32,
}

impl<I, F> DefLine<I, F> {
    /// Applies `f` to the inner iterator `iter` of type `I` inside `self` to get a new 
    /// `DefLine` with `f(iter)` as `iter`.
    pub fn map_iter<J, MF : FnOnce(I) -> J>(self, f : MF) -> DefLine<J, F> {
        DefLine{
            iter : f(self.iter),
            file : self.file,
            r : self.r,
            c : self.c,
        }
    }
    /// Like [DefLine::map_iter] but also resets the position to the beginning.
    pub fn map_iter_reset<J, MF : FnOnce(I) -> J>(self, f : MF) -> DefLine<J, F> {
        DefLine{
            iter : f(self.iter),
            file : self.file,
            r : 0,
            c : 0,
        }
    }
}


impl<I, F> DefLine<I, F> where I : Iterator<Item = char>, F : Default + Clone {
    /// Like [DefLine::new_file] but with `F::default()` as file.
    pub fn new<J : IntoIterator<IntoIter = I>>(it : J) -> Self {
        Self::new_file(it, F::default())
    }
}


impl<I, F > DefLine<I, F> where I  : Iterator<Item = char>, F : Clone {
    /// Creates a new [DefLine] with the specified iterator and file.
    pub fn new_file<J>(it : J, f : F) -> Self where J : IntoIterator<IntoIter = I> {
        Self{
            iter : it.into_iter(),
            file : f,
            r : 0,
            c : 0,
        }
    }
    /// Same as `self.map_iter(I::peekable)`
    pub fn peekable(self) -> DefLine<Peekable<I>, F> {
        self.map_iter(I::peekable)
    }
    /// Advances the iterator and returns the next positioned value.
    ///
    /// When the iterator has finished the returned position follows the one that has been returned
    /// by the last character.
    pub fn next_pos(&mut self) -> Pos<Option<char>, F> {
        let p = Position::new_file(self.file.clone(), self.r, self.c);
        self.c += 1;

        match self.iter.next() {
            None => None.at(p),
            Some(ch) => {
                if ch == '\n' {
                    self.c = 0;
                    self.r += 1;
                }
                Some(ch).at(p)
            }
        }
    }
    /// Discards characters as long as [Self::next_pos] returns `Some(ch)` and `f(ch)` returns [``ControlFlow::Continue``](https://doc.rust-lang.org/stable/core/ops/enum.ControlFlow.html#variant.Continue). 
    ///
    /// When `f(ch)` returns [``ControlFlow::Break(t)``](https://doc.rust-lang.org/stable/core/ops/enum.ControlFlow.html#variant.Break) then this function will return `Some(t)`.
    pub fn next_pos_cf<T, MF : FnMut(char) -> ControlFlow<T>>(&mut self, mut f : MF) -> Pos<Option<T>, F> {
        loop {
            let (rs, pos) = self.next_pos().take_all();
            match rs {
                None => return Pos::new(None, pos),
                Some(ch) => match f(ch) {
                    ControlFlow::Break(c) => return Pos::new(Some(c), pos),
                    ControlFlow::Continue(_) => {}
                }
            }
        }
    }

    /// Like [DefLine::next_pos_cf] but discards characters as long as `f` returns `true`.
    pub fn next_pos_until<MF : FnMut(char) -> bool>(&mut self, mut f : MF) -> Pos<Option<char>, F> {
        self.next_pos_cf(|ch| if f(ch) {ControlFlow::Continue(())} else {ControlFlow::Break(ch)})
    }
    /// Next character discarding whitespaces and newline characters.
    ///
    /// Removes any whitespace according to
    /// [predicates::is_whitespace](crate::predicates::is_whitespace).
    pub fn next_no_spaces(&mut self) -> Pos<Option<char>, F>{
        self.next_pos_until(crate::predicates::is_whitespace)
    }
    /// Next character discarding whitespaces but not newline characters. 
    pub fn next_nl_no_spaces(&mut self) -> Pos<Option<char>, F>{
        self.next_pos_until(|c| crate::predicates::is_whitespace(c) && !crate::predicates::is_newline(c))
    }
}

impl<I, F> DefLine<Peekable<I>, F> where I : Iterator<Item = char>, F : Clone {
    /// Like [DefLine::next_pos] but doesn't remove the character from the underlying iterator.
    pub fn peek_pos(&mut self) -> Pos<Option<char>, F> {
        return Pos::new_pos(self.iter.peek().copied(), self.file.clone(), self.r, self.c);
    } 
    /// Like [DefLine::next_pos_cf] but when `f(ch)` returns [``ControlFlow::Break``](https://doc.rust-lang.org/stable/core/ops/enum.ControlFlow.html#variant.Break)
    /// then `ch` is not removed from the underlying iterator.
    pub fn peek_pos_cf<T, MF : FnMut(char) -> ControlFlow<T>>(&mut self, mut f : MF) -> Pos<Option<T>, F> {
        loop {
            let (rs, pos) = self.peek_pos().take_all();
            match rs {
                None => return Pos::new(None, pos),
                Some(ch) => match f(ch) {
                    ControlFlow::Break(c) => return Pos::new(Some(c), pos),
                    ControlFlow::Continue(_) => self.discard(),
                }
            }
        }
    }
    /// Like [DefLine::next_pos_until] but when `f(ch)` returns `false` then `ch` is not removed from
    /// the underlying iterator.
    pub fn peek_pos_until<MF : FnMut(char) -> bool>(&mut self, mut f : MF) -> Pos<Option<char>, F> {
        self.peek_pos_cf(|ch| if f(ch) {ControlFlow::Continue(())} else {ControlFlow::Break(ch)})
    }
    /// Discard the last character in the iterator
    pub fn discard(&mut self) {
        self.next_pos();
    }
    /// Appends characters to an accumulator.
    ///
    /// Every time [DefLine::peek_pos] returns `Some(ch)` and `f(ch)` returns
    /// ``ControlFlow::Continue(k)`` then `ch` is discarded and `k` is pushed into an accumulator of type `V`.
    /// When `f(ch)` returns instead `ControlFlow::Break` then `ch` is not discarded and the used
    /// accumulator is returned.
    pub fn grab_cf<V : Appender<K>, K, MF : FnMut(char) -> ControlFlow<(), K>>(&mut self, mut f : MF) -> Pos<V, F> {
        let mut ret = V::new_empty();
        let pos = self.peek_pos().pos().clone();
        loop {
            match self.peek_pos().take() {
                None => break,
                Some(ch) => {
                    match f(ch) {
                        ControlFlow::Continue(k) => {
                            ret.push(k);
                            self.discard();
                        }
                        ControlFlow::Break(_) => {
                            break;
                        }
                    }
                }
            }
        }
        return Pos::new(ret, pos);
    }
    /// Like [DefLine::grab_cf] but appends characters as long as `f` returns `true`.
    pub fn grab_until<V : Appender<char>, MF : FnMut(char) -> bool>(&mut self, mut f : MF) -> Pos<V, F>{
        self.grab_cf(|ch| if f(ch) {ControlFlow::Continue(ch)} else {ControlFlow::Break(())})
    }
    /// Gets a line
    pub fn get_line<V : Appender<char>>(&mut self) -> Pos<V, F>{
        self.grab_until(|ch| ch != '\n')
    }
    /// Removes leading and trailing characters.
    ///
    /// Every character returned by [DefLine::peek_pos] can be considered a *space* or a *nonspace*
    /// character depending on whether `sp` returns `true` or `false`. Until function `cf` returns
    /// `ControlFlow::Continue` retrieved characters are stores in a container of type `V` and when
    /// `cf` returns `ControlFlow::Break` then leading and trailing *spaces* are removed from the
    /// returned container.
    ///
    /// If the returned container is not empty then the returned position is exactly the position
    /// of the first *nonspace* appended character, otherwise it is the position of the first
    /// character that terminated the accumulation.
    pub fn cap_ht_cf<V : AppenderExt<K>, K, SP : FnMut(char) -> bool, CF : FnMut(char) -> ControlFlow<(), K>>(&mut self, mut sp : SP, mut cf : CF) -> Pos<V, F> {
        let mut ret = V::new_empty();
        let mut spcs = V::new_empty();

        let mut pos = None;

        while let Some(ch) = self.peek_pos().take() {
            match cf(ch) {
                ControlFlow::Break(_) => break,
                ControlFlow::Continue(k) => {
                    if sp(ch) {
                        spcs.push(k);
                    }
                    else{
                        if !ret.is_empty() {
                            ret.drain(&mut spcs);
                        }
                        else {
                            pos = Some(self.peek_pos().take_pos());
                        }
                        spcs.clear();
                        ret.push(k);
                    }
                    self.discard();
                }
            }
        }
        match pos {
            Some(pp) => return Pos::new(ret, pp),
            None => return Pos::new(ret, self.peek_pos().take_pos()),
        }
    }
    ///Removes leading and trailing whitespaces.
    ///
    ///See also [DefLine::cap_ht_cf] and [predicates::is_whitespace](crate::predicates::is_whitespace) for the used definition of
    ///whitespace.
    pub fn cap_spaces<V : AppenderExt<char>, CF : FnMut(char) -> ControlFlow<()>>(&mut self, mut f : CF) -> Pos<V, F> {
        self.cap_ht_cf(crate::predicates::is_whitespace, |ch| match f(ch) {
            ControlFlow::Break(_) => ControlFlow::Break(()),
            ControlFlow::Continue(_) => ControlFlow::Continue(ch),
        })
    }
    ///Gets a line and removes leading and trailing whitespaces.
    ///
    ///See also [DefLine::cap_ht_cf] and [predicate::is_whitespace](crate::predicates::is_whitespace) for the used definition of
    ///whitespace.
    pub fn get_line_cap<V : AppenderExt<char>>(&mut self) -> Pos<V, F> {
        self.cap_ht_cf(crate::predicates::is_whitespace, |x| if x == '\n' {ControlFlow::Break(())} else {ControlFlow::Continue(x)})
    }

    ///Parse an identifier.
    ///
    ///Gets an identifier defined as a contiguous sequence of alphabetic characters as defined in
    ///[predicates::is_alphabetic](crate::predicates::is_alphabetic).
    pub fn get_ident<V : Appender<char>>(&mut self) -> Pos<V, F> {
        self.grab_until(crate::predicates::is_alphabetic)
    }
    ///Parses a decimal number.
    pub fn get_num(&mut self) -> Pos<Option<u32>, F> {
        let ret = self.grab_cf::<NumAppender<u32, 10>, _, _>(|c| {
            match c.to_digit(10) {
                None => ControlFlow::Break(()),
                Some(n) => ControlFlow::Continue(n),
            }
        });
        ret.map(|t| t.0)
    }
    /// Parses an hexadecimal number (without the prefix).
    pub fn get_hex_num(&mut self) -> Pos<Option<u32>, F> {
        let ret = self.grab_cf::<NumAppender<u32, 16>, _, _>(|c| {
            match c.to_digit(16) {
                None => ControlFlow::Break(()),
                Some(n) => ControlFlow::Continue(n),
            }
        });
        ret.map(|t| t.0)
    }
    /// Peeks character by discarding whitespaces and newline characters.
    ///
    /// Removes any whitespace according to
    /// [predicates::is_whitespace](crate::predicates::is_whitespace).
    pub fn peek_no_spaces(&mut self) -> Pos<Option<char>, F>{
        self.peek_pos_until(crate::predicates::is_whitespace)
    }
    /// Peeks character by whitespaces but not newline characters. 
    pub fn peek_nl_no_spaces(&mut self) -> Pos<Option<char>, F>{
        self.peek_pos_until(|c| crate::predicates::is_whitespace(c) && !crate::predicates::is_newline(c))
    }
}

