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
use crate::pos::{Pos, Position, Posable, NoFile};
use core::iter::{Iterator, IntoIterator, Peekable, FusedIterator};

/// An iterator wrapper that removes `\r` characters.
///
/// This crate assumes that `\n` separates lines, so if your iterator uses `\r\n` as line delimiter you
/// can use this wrapper to normalize it to `\n`.
pub struct NLIterator<I>{
    iter : I,
}

impl<I> NLIterator<I>{
    /// Creates a new `NLIterator` from an already existent iterator.
    pub const fn new(iter : I) -> Self {
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        // This adapter can reduce our iterator length by a value known only at runtime
        (0, self.iter.size_hint().1)
    }
}

impl<I> FusedIterator for NLIterator<I> where I : FusedIterator + Iterator<Item = char> {}

/// A sequential container that can accept new objects.
///
/// This trait is used by [`DefLine::append_cf`] and similar methods in [`DefLine`].
pub trait Appender<T>{
    /// Creates a new empty container.
    fn new_empty() -> Self;
    /// Push a new object in the container.
    fn push(&mut self, i : T);
}
/// A sequential container with additional functionalities.
///
/// This trait is used by [`DefLine::append_trim_cf`] and similar methods in [`DefLine`].
pub trait AppenderExt<T> : Appender<T>{
    /// Tests if the container is empty
    fn is_empty(&self) -> bool;
    /// Clears the container
    fn clear(&mut self);
    /// Pushes all the elements of `a` into `self` and then clears `a`.
    fn append(&mut self, a : &mut Self);
}

#[cfg(feature = "alloc")]
impl Appender<char> for alloc::string::String{
    fn new_empty() -> Self{
        Self::new()
    }
    fn push(&mut self, i : char){
        self.push(i);
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
    fn append(&mut self, a : &mut Self){
        self.push_str(a);
        a.clear();  //push_str doesn't clear a unlike append in Vec
    }
}
#[cfg(feature = "alloc")]
impl<T> Appender<T> for alloc::vec::Vec<T>{
    fn new_empty() -> Self{
        Self::new()
    }
    fn push(&mut self, i : T){
        self.push(i);
    }
}
#[cfg(feature = "alloc")]
impl<T> AppenderExt<T> for alloc::vec::Vec<T>{
    fn is_empty(&self) -> bool{
        (self as &Self).is_empty()
    }
    fn append(&mut self, a : &mut Self){
        self.append(a);
    }
    fn clear(&mut self){
        self.clear();
    }
}
#[cfg(feature = "alloc")]
impl<T> Appender<T> for alloc::collections::LinkedList<T>{
    fn new_empty() -> Self{
        Self::new()
    }
    fn push(&mut self, i : T){
        self.push_back(i);
    }
}
#[cfg(feature = "alloc")]
impl<T> Appender<T> for alloc::collections::VecDeque<T>{
    fn new_empty() -> Self{
        Self::new()
    }
    fn push(&mut self, i : T){
        self.push_back(i);
    }
}
#[cfg(feature = "alloc")]
impl<T> AppenderExt<T> for alloc::collections::VecDeque<T>{
    fn is_empty(&self) -> bool{
        (self as &Self).is_empty()
    }
    fn append(&mut self, a : &mut Self){
        self.append(a);
    }
    fn clear(&mut self){
        self.clear();
    }
}

/// An integer appender.
///
/// When `T` implements `Default`, `AddAssign<T>` and `MulAssign<usize>` then `NumAppender<T, N>`
/// implements [``Appender<T>``] in the following way: if `self` contains `t` of type `T` then
/// [pushing](Appender::push) `s` in `self` updates `t` into `(t * N) + s`.
///
/// This struct is useful when you want to parse an integer from a text file.
pub struct NumAppender<T, const N : u32>(pub Option<T>);

impl<T, const N : u32> NumAppender<T, N>{
    /// Tests if it is empty.
    ///
    /// Returns `true` if and only if no value has been pushed.
    pub const fn is_empty(&self) -> bool{
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
/// [`DefLine::next_pos`] that returns the next available positioned character as
/// `Pos<Option<char>, FILE>` by calling `I::next`.
pub struct DefLine<I, FILE = NoFile> {
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
    /// Like [`DefLine::map_iter`] but also resets the position to the beginning.
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
    /// Like [`DefLine::new_file`] but with `F::default()` as file.
    pub fn new<J : IntoIterator<IntoIter = I>>(it : J) -> Self {
        Self::new_file(it, F::default())
    }
}


impl<I, F > DefLine<I, F> where I  : Iterator<Item = char>, F : Clone {
    /// Creates a new [`DefLine`] with the specified iterator and file.
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
    /// Discards characters as long as [`Self::next_pos`] returns `Some(ch)` and `f(ch)` returns [``ControlFlow::Continue``](https://doc.rust-lang.org/stable/core/ops/enum.ControlFlow.html#variant.Continue). 
    ///
    /// When `f(ch)` returns [``ControlFlow::Break(t)``](https://doc.rust-lang.org/stable/core/ops/enum.ControlFlow.html#variant.Break) then this function will return `Some(t)`.
    pub fn dig_char_cf<T, MF : FnMut(char) -> ControlFlow<T>>(&mut self, mut f : MF) -> Pos<Option<T>, F> {
        loop {
            let (rs, pos) = self.next_pos().take_all();
            match rs {
                None => return Pos::new(None, pos),
                Some(ch) => match f(ch) {
                    ControlFlow::Break(c) => return Pos::new(Some(c), pos),
                    ControlFlow::Continue(()) => {}
                }
            }
        }
    }

    /// Like [`DefLine::dig_char_cf`] but discards characters as long as `f` returns `true`.
    pub fn dig_char_until<MF : FnMut(char) -> bool>(&mut self, mut f : MF) -> Pos<Option<char>, F> {
        self.dig_char_cf(|ch| if f(ch) {ControlFlow::Continue(())} else {ControlFlow::Break(ch)})
    }
    /// Gets the first not-whitespace character.
    ///
    /// Removes any whitespace according to
    /// [`predicates::is_whitespace`](crate::predicates::is_whitespace).
    pub fn next_no_spaces(&mut self) -> Pos<Option<char>, F>{
        self.dig_char_until(crate::predicates::is_whitespace)
    }
    /// As [`Self::next_no_spaces`] but threats the `\n` character as not whitespace. 
    pub fn next_nl_no_spaces(&mut self) -> Pos<Option<char>, F>{
        self.dig_char_until(|c| crate::predicates::is_whitespace(c) && !crate::predicates::is_newline(c))
    }
    /// Appends characters to an accumulator.
    ///
    /// Every time [`Self::next_pos`] returns `Some(ch)` and `f(ch)` returns
    /// ``ControlFlow::Continue(k)`` then `k` is pushed into an accumulator of type `V`.
    /// When `f(ch)` returns instead `ControlFlow::Break(z)` then both `Some(z)` and the accumulator are
    /// returned. 
    ///
    /// Notice that, unlike [`Self::append_cf`], `ch` will always be discarded. 
    pub fn append_delim_cf<V : Appender<K>, K, Z, MF : FnMut(char) -> ControlFlow<Z, K>>(&mut self, mut f : MF) -> (Pos<V, F>, Pos<Option<Z>, F>) {
        let mut ret = V::new_empty();
        let (mut och, mut rpos) = self.next_pos().take_all();
        let pos = rpos.clone();
        let mut rz = None;
        while let Some(ch) = och {
                    match f(ch) {
                        ControlFlow::Continue(k) => {
                            ret.push(k);
                        }
                        ControlFlow::Break(z) => {
                            rz = Some(z);
                            break;
                        }
                    }
            (och, rpos) = self.next_pos().take_all();
        }
        (Pos::new(ret, pos), Pos::new(rz, rpos))
    }
    /// Like [`DefLine::append_delim_cf`] but appends characters as long as `f` returns `true`.
    pub fn append_delim_until<V : Appender<char>, MF : FnMut(char) -> bool>(&mut self, mut f : MF) -> (Pos<V, F>, Pos<Option<char>, F>){
        self.append_delim_cf(|ch| if f(ch) {ControlFlow::Continue(ch)} else {ControlFlow::Break(ch)})
    }
    /// Removes leading and trailing characters.
    ///
    /// Every character returned by [`DefLine::next_pos`] can be considered a *space* or a *nonspace*
    /// character depending on whether `sp` returns `true` or `false`. Until function `cf` returns
    /// `ControlFlow::Continue` retrieved characters are stores in a container of type `V` and when
    /// `cf` returns `ControlFlow::Break` then leading and trailing *spaces* are removed from the
    /// returned container.
    ///
    /// If the returned container is not empty then the returned position is exactly the position
    /// of the first *nonspace* appended character, otherwise it is the position of the first
    /// character that terminated the accumulation.
    pub fn append_delim_trim_cf<V : AppenderExt<K>, K, Z, SP : FnMut(char) -> bool, CF : FnMut(char) -> ControlFlow<Z, K>>(&mut self, mut sp : SP, mut cf : CF) -> (Pos<V, F>, Pos<Option<Z>, F>) {
        let mut ret = V::new_empty();
        let mut spcs = V::new_empty();

        let (mut och, mut cpos) = self.next_pos().take_all();
        let mut rz = None;

        let mut pos = None;

        while let Some(ch) = och {
            match cf(ch) {
                ControlFlow::Break(z) => {
                    rz = Some(z);
                    break;
                }
                ControlFlow::Continue(k) => {
                    if sp(ch) {
                        spcs.push(k);
                    }
                    else{
                        if ret.is_empty() {
                            pos = Some(cpos.clone());
                            spcs.clear();
                        }
                        else {
                            ret.append(&mut spcs);
                        }
                        ret.push(k);
                    }
                }
            }
            (och, cpos) = self.next_pos().take_all();
        }
        (Pos::new(ret, pos.unwrap_or_else(|| cpos.clone())), Pos::new(rz, cpos))
    }
    /// Like [`Self::append_delim_trim_cf`] but continue appending characters as long as `cf`
    /// returns `true`.
    pub fn append_delim_trim_until<V : AppenderExt<char>, SP : FnMut(char) -> bool, CF : FnMut(char) -> bool>(&mut self, sp : SP, mut cf : CF) -> (Pos<V, F>, Pos<Option<char>, F>) {
        self.append_delim_trim_cf(sp, |c| if cf(c) {ControlFlow::Continue(c)} else {ControlFlow::Break(c)})
    }
    /// Retrieves a line.
    ///
    /// A line is a sequence of characters terminated by a `\n` character or up to the end of the
    /// iterator. Notice that the eventual `\n` character is discarded and not added to the
    /// returned line.
    pub fn get_line<V : Appender<char>>(&mut self) -> Pos<V, F>{
        self.append_delim_until(|ch| ch != '\n').0
    }
    ///Gets a line and removes leading and trailing whitespaces.
    ///
    ///See also [`DefLine::append_delim_trim_cf`] and [`predicate::is_whitespace`](crate::predicates::is_whitespace) for the used definition of
    ///whitespace.
    pub fn get_line_trim<V : AppenderExt<char>>(&mut self) -> Pos<V, F> {
        self.append_delim_trim_until(crate::predicates::is_whitespace, |x| x != '\n' ).0
    }
}

impl<I, F> DefLine<Peekable<I>, F> where I : Iterator<Item = char>, F : Clone {
    /// Like [`DefLine::next_pos`] but doesn't remove the character from the underlying iterator.
    pub fn peek_pos(&mut self) -> Pos<Option<char>, F> {
        return Pos::new_pos(self.iter.peek().copied(), self.file.clone(), self.r, self.c);
    } 
    /// Like [`DefLine::dig_char_cf`] but when `f(ch)` returns [``ControlFlow::Break``](https://doc.rust-lang.org/stable/core/ops/enum.ControlFlow.html#variant.Break)
    /// then `ch` is not removed from the underlying iterator.
    pub fn dig_peek_cf<T, MF : FnMut(char) -> ControlFlow<T>>(&mut self, mut f : MF) -> Pos<Option<T>, F> {
        loop {
            let (rs, pos) = self.peek_pos().take_all();
            match rs {
                None => return Pos::new(None, pos),
                Some(ch) => match f(ch) {
                    ControlFlow::Break(c) => return Pos::new(Some(c), pos),
                    ControlFlow::Continue(()) => self.discard(),
                }
            }
        }
    }
    /// Like [`DefLine::dig_char_until`] but when `f(ch)` returns `false` then `ch` is not removed from
    /// the underlying iterator.
    pub fn dig_peek_until<MF : FnMut(char) -> bool>(&mut self, mut f : MF) -> Pos<Option<char>, F> {
        self.dig_peek_cf(|ch| if f(ch) {ControlFlow::Continue(())} else {ControlFlow::Break(ch)})
    }
    /// Discard the last character in the iterator
    pub fn discard(&mut self) {
        self.next_pos();
    }
    /// Appends characters to an accumulator.
    ///
    /// Every time [`DefLine::peek_pos`] returns `Some(ch)` and `f(ch)` returns
    /// ``ControlFlow::Continue(k)`` then `ch` is discarded and `k` is pushed into an accumulator of type `V`.
    /// When `f(ch)` returns instead `ControlFlow::Break` then `ch` is not discarded and the used
    /// accumulator is returned.
    pub fn append_cf<V : Appender<K>, K, MF : FnMut(char) -> ControlFlow<(), K>>(&mut self, mut f : MF) -> Pos<V, F> {
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
                        ControlFlow::Break(()) => {
                            break;
                        }
                    }
                }
            }
        }
        Pos::new(ret, pos)
    }
    /// Like [`DefLine::append_cf`] but appends characters as long as `f` returns `true`.
    ///
    /// Moreover, when `f(ch)` returns `true` then `ch` is not discarded from the unerlying
    /// iterator.
    pub fn append_until<V : Appender<char>, MF : FnMut(char) -> bool>(&mut self, mut f : MF) -> Pos<V, F>{
        self.append_cf(|ch| if f(ch) {ControlFlow::Continue(ch)} else {ControlFlow::Break(())})
    }
    /// Removes leading and trailing characters.
    ///
    /// Every character returned by [`DefLine::peek_pos`] can be considered a *space* or a *nonspace*
    /// character depending on whether `sp` returns `true` or `false`. Until function `cf` returns
    /// `ControlFlow::Continue` retrieved characters are stores in a container of type `V` and when
    /// `cf` returns `ControlFlow::Break` then leading and trailing *spaces* are removed from the
    /// returned container.
    ///
    /// If the returned container is not empty then the returned position is exactly the position
    /// of the first *nonspace* appended character, otherwise it is the position of the first
    /// character that terminated the accumulation.
    pub fn append_trim_cf<V : AppenderExt<K>, K, SP : FnMut(char) -> bool, CF : FnMut(char) -> ControlFlow<(), K>>(&mut self, mut sp : SP, mut cf : CF) -> Pos<V, F> {
        let mut ret = V::new_empty();
        let mut spcs = V::new_empty();

        let mut pos = None;

        while let Some(ch) = self.peek_pos().take() {
            match cf(ch) {
                ControlFlow::Break(()) => break,
                ControlFlow::Continue(k) => {
                    if sp(ch) {
                        spcs.push(k);
                    }
                    else{
                        if ret.is_empty() {
                            pos = Some(self.peek_pos().take_pos());
                            spcs.clear();
                        }
                        else {
                            ret.append(&mut spcs);
                        }
                        ret.push(k);
                    }
                    self.discard();
                }
            }
        }
        match pos {
            Some(pp) => Pos::new(ret, pp),
            None => Pos::new(ret, self.peek_pos().take_pos()),
        }
    }
    ///Removes leading and trailing whitespaces.
    ///
    ///See also [`DefLine::append_trim_cf`] and [`predicates::is_whitespace`](crate::predicates::is_whitespace) for the used definition of
    ///whitespace.
    pub fn trim_spaces_until<V : AppenderExt<char>, CF : FnMut(char) -> bool>(&mut self, mut f : CF) -> Pos<V, F> {
        self.append_trim_cf(crate::predicates::is_whitespace, |ch| if f(ch) {ControlFlow::Continue(ch)} else {ControlFlow::Break(())})
    }
    
    ///Parse an identifier by dircarding leading whitespaces and without changing line.
    ///
    ///Gets an identifier defined as a contiguous sequence of alphabetic characters as defined in
    ///[`predicates::is_alphabetic`](crate::predicates::is_alphabetic).
    pub fn get_ident<V : Appender<char>>(&mut self) -> Pos<V, F> {
        self.peek_spaces_nonl();
        self.append_until(crate::predicates::is_alphabetic)
    }
    ///Parses a decimal number and removes leading and trailing spaces in the same line.
    pub fn get_num_nonl(&mut self) -> Pos<Option<u32>, F> {
        self.peek_spaces_nonl();
        self.append_cf::<NumAppender<u32, 10>, _, _>(|c| c.to_digit(10).map_or(ControlFlow::Break(()), ControlFlow::Continue)).map(|t| t.0)
    }
    /// Peeks character by discarding whitespaces and newline characters.
    ///
    /// Removes any whitespace according to
    /// [`predicates::is_whitespace`](crate::predicates::is_whitespace).
    pub fn peek_spaces(&mut self) -> Pos<Option<char>, F>{
        self.dig_peek_until(crate::predicates::is_whitespace)
    }
    /// Peeks character by whitespaces but not newline characters. 
    pub fn peek_spaces_nonl(&mut self) -> Pos<Option<char>, F>{
        self.dig_peek_until(|c| crate::predicates::is_whitespace(c) && !crate::predicates::is_newline(c))
    }
}

