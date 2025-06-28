// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use ::core::iter::FusedIterator;

use super::*;
use ::quither_proc_macros::quither;

use ::core::iter::{Chain, Flatten};

#[quither]
impl<L, R> Quither<L, R> {
    #[deprecated(note = "This method's intention is unclear. Use `into_iter_chained()` instead.")]
    #[quither(has_either && !has_neither && !has_both)]
    pub fn into_iter(self) -> Either<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        self.map2(L::into_iter, R::into_iter)
    }

    #[deprecated(note = "This method's intention is unclear. Use `iter_chained()` instead.")]
    #[quither(has_either && !has_neither && !has_both)]
    pub fn iter(&self) -> Either<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    {
        self.as_ref()
            .map2(
                <&L as IntoIterator>::into_iter,
                <&R as IntoIterator>::into_iter,
            )
            .into()
    }

    #[deprecated(note = "This method's intention is unclear. Use `iter_chained_mut()` instead.")]
    #[quither(has_either && !has_neither && !has_both)]
    pub fn iter_mut(
        &mut self,
    ) -> Either<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    {
        self.as_mut()
            .map2(
                <&mut L as IntoIterator>::into_iter,
                <&mut R as IntoIterator>::into_iter,
            )
            .into()
    }

    #[deprecated(note = "This method's intention is unclear. Use `into_iter_either()` instead.")]
    #[quither(has_either && !has_neither && !has_both)]
    pub fn factor_into_iter(self) -> IterEither<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        self.map2(L::into_iter, R::into_iter).into()
    }

    #[deprecated(note = "This method's intention is unclear. Use `iter_chained()` instead.")]
    #[quither(has_either && !has_neither && !has_both)]
    pub fn factor_iter(
        &self,
    ) -> IterEither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    {
        self.as_ref()
            .map2(
                <&L as IntoIterator>::into_iter,
                <&R as IntoIterator>::into_iter,
            )
            .into()
    }

    #[deprecated(note = "This method's intention is unclear. Use `into_iter_chained()` instead.")]
    #[quither(has_either && !has_neither && !has_both)]
    pub fn factor_iter_mut(
        &mut self,
    ) -> IterEither<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    {
        self.as_mut()
            .map2(
                <&mut L as IntoIterator>::into_iter,
                <&mut R as IntoIterator>::into_iter,
            )
            .into()
    }

    /// Iterates all items from the left iterator, then all items from the right iterator.
    ///
    /// The returned iterator's `Item` type is the common item type of both iterators.
    /// **Left and right iterator item types must be the same.**
    /// Yields all items from the left, then all from the right (like [`chain`](std::iter::Iterator::chain)).
    ///
    /// # Sample
    ///
    /// ```rust
    /// use quither::Quither;
    ///
    /// let q = Quither::Both(vec![1, 2, 3], vec![4, 5]);
    /// let mut iter = q.into_iter_chained();
    ///
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), Some(4));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[quither(has_either || has_both)]
    pub fn into_iter_chained(self) -> ChainedIterator<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        self.map2(L::into_iter, R::into_iter).into()
    }

    /// Iterates all items from the left iterator, then all items from the right iterator by reference.
    ///
    /// The returned iterator's `Item` type is the common item type of both reference iterators.
    /// **Left and right iterator item types must be the same.**
    /// Yields all items from the left, then all from the right (like [`chain`](std::iter::Iterator::chain)).
    ///
    /// # Sample
    ///
    /// ```rust
    /// use quither::Quither;
    ///
    /// let q = Quither::Both(vec![1, 2, 3], vec![4, 5]);
    /// let mut iter = q.iter_chained();
    ///
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&3));
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), Some(&5));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[quither(has_either || has_both)]
    pub fn iter_chained(
        &self,
    ) -> ChainedIterator<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    {
        self.as_ref()
            .map2(
                <&L as IntoIterator>::into_iter,
                <&R as IntoIterator>::into_iter,
            )
            .into()
    }

    /// Iterates all items from the left iterator, then all items from the right iterator by mutable reference.
    ///
    /// The returned iterator's `Item` type is the common item type of both mutable reference iterators.
    /// **Left and right iterator item types must be the same.**
    /// Yields all items from the left, then all from the right (like [`chain`](std::iter::Iterator::chain)).
    #[quither(has_either || has_both)]
    pub fn iter_chained_mut(
        &mut self,
    ) -> ChainedIterator<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    {
        self.as_mut()
            .map2(
                <&mut L as IntoIterator>::into_iter,
                <&mut R as IntoIterator>::into_iter,
            )
            .into()
    }

    /// Iterates items from both iterators, wrapping each in `Either::Left` or `Either::Right`.
    ///
    /// The returned iterator's `Item` type is `Either<L::Item, R::Item>`.
    /// Yields all items from the left iterator as `Left`, then all items from the right iterator
    /// as `Right` (in order, like [`chain`](std::iter::Iterator::chain)).
    ///
    /// # Sample
    ///
    /// ```rust
    /// use quither::{Either, Quither};
    ///
    /// let q = Quither::Both(vec![1, 2, 3], vec!['a', 'b']);
    /// let mut iter = q.into_iter_either();
    ///
    /// assert_eq!(iter.next(), Some(Either::Left(1)));
    /// assert_eq!(iter.next(), Some(Either::Left(2)));
    /// assert_eq!(iter.next(), Some(Either::Left(3)));
    /// assert_eq!(iter.next(), Some(Either::Right('a')));
    /// assert_eq!(iter.next(), Some(Either::Right('b')));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[quither(has_either || has_both)]
    pub fn into_iter_either(self) -> IterIntoEither<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator,
    {
        self.map2(L::into_iter, R::into_iter).into()
    }

    /// Iterates items from both iterators by reference, wrapping each in
    /// `Either::Left` or `Either::Right`.
    ///
    /// The returned iterator's `Item` type is `Either<L::Item, R::Item>`.
    /// Yields all items from the left iterator as `Left`, then all items from the right iterator
    /// as `Right` (in order, like [`chain`](std::iter::Iterator::chain)).
    ///
    /// # Sample
    ///
    /// ```rust
    /// use quither::{Either, Quither};
    ///
    /// let q = Quither::Both(vec![1, 2, 3], vec!['a', 'b']);
    /// let mut iter = q.iter_either();
    ///
    /// assert_eq!(iter.next(), Some(Either::Left(&1)));
    /// assert_eq!(iter.next(), Some(Either::Left(&2)));
    /// assert_eq!(iter.next(), Some(Either::Left(&3)));
    /// assert_eq!(iter.next(), Some(Either::Right(&'a')));
    /// assert_eq!(iter.next(), Some(Either::Right(&'b')));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[quither(has_either || has_both)]
    pub fn iter_either(
        &self,
    ) -> IterIntoEither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator,
    {
        self.as_ref()
            .map2(
                <&L as IntoIterator>::into_iter,
                <&R as IntoIterator>::into_iter,
            )
            .into()
    }

    /// Iterates items from both iterators by mutable reference, wrapping each
    /// in `Either::Left` or `Either::Right`.
    ///
    /// The returned iterator's `Item` type is `Either<L::Item, R::Item>`.
    /// Yields all items from the left iterator as `Left`, then all items from the right iterator
    /// as `Right` (in order, like [`chain`](std::iter::Iterator::chain)).
    #[quither(has_either || has_both)]
    pub fn iter_either_mut(
        &mut self,
    ) -> IterIntoEither<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator,
    {
        self.as_mut()
            .map2(
                <&mut L as IntoIterator>::into_iter,
                <&mut R as IntoIterator>::into_iter,
            )
            .into()
    }

    /// Iterates items from both iterators in parallel, yielding `EitherOrBoth::Both(l, r)` if both have items,
    /// or `Left(l)`/`Right(r)` if only one side has items left.
    ///
    /// The returned iterator's `Item` type is `EitherOrBoth<L::Item, R::Item>`.
    ///
    /// # Sample
    ///
    /// ```rust
    /// use quither::{EitherOrBoth, Quither};
    ///
    /// let q = Quither::Both(vec![1, 2, 3], vec!['a', 'b']);
    /// let mut iter = q.into_iter_either_or_both();
    ///
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Both(1, 'a')));
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Both(2, 'b')));
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Left(3)));
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// Note: If the value is not `::Both`, this method behaves similarly to [`into_iter_either()`].
    #[quither(has_either || has_both)]
    pub fn into_iter_either_or_both(self) -> IterIntoEitherOrBoth<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator,
    {
        self.map2(L::into_iter, R::into_iter).into()
    }

    /// Iterates items from both iterators in parallel by reference, yielding `EitherOrBoth::Both(l, r)`
    /// if both have items, or `Left(l)`/`Right(r)` if only one side has items left.
    ///
    /// The returned iterator's `Item` type is `EitherOrBoth<L::Item, R::Item>`.
    ///
    /// # Sample
    ///
    /// ```rust
    /// use quither::{EitherOrBoth, Quither};
    ///
    /// let q = Quither::Both(vec![1, 2, 3], vec!['a', 'b']);
    /// let mut iter = q.iter_either_or_both();
    ///
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Both(&1, &'a')));
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Both(&2, &'b')));
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Left(&3)));
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// Note: If the value is not `::Both`, this method behaves similarly to [`iter_either()`].
    #[quither(has_either || has_both)]
    pub fn iter_either_or_both(
        &self,
    ) -> IterIntoEitherOrBoth<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator,
    {
        self.as_ref()
            .map2(
                <&L as IntoIterator>::into_iter,
                <&R as IntoIterator>::into_iter,
            )
            .into()
    }

    /// Iterates items from both iterators in parallel by mutable reference, yielding `EitherOrBoth::Both(l, r)`
    /// if both have items, or `Left(l)`/`Right(r)` if only one side has items left.
    ///
    /// The returned iterator's `Item` type is `EitherOrBoth<L::Item, R::Item>`.
    ///
    /// # Sample
    ///
    /// ```rust
    /// use quither::{EitherOrBoth, Quither};
    ///
    /// let q = Quither::Both(vec![1, 2, 3], vec!['a', 'b']);
    /// let mut iter = q.iter_either_or_both_mut();
    ///
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Both(&0, &'a')));
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Both(&1, &'b')));
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Left(&2)));
    /// assert_eq!(iter.next(), Some(EitherOrBoth::Right(&3)));
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// Note: If the value is not `::Both`, this method behaves similarly to [`iter_either()`].
    #[quither(has_either || has_both)]
    pub fn iter_either_or_both_mut(
        &mut self,
    ) -> IterIntoEitherOrBoth<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator,
    {
        self.as_mut()
            .map2(
                <&mut L as IntoIterator>::into_iter,
                <&mut R as IntoIterator>::into_iter,
            )
            .into()
    }

    /// Iterates pairs of items from both iterators as long as both have items (like [`zip`](std::iter::Iterator::zip)).
    ///
    /// The returned iterator's `Item` type is `Both<L::Item, R::Item>`.
    #[quither(has_either || has_both)]
    pub fn into_iter_both(self) -> IterIntoBoth<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator,
    {
        self.map2(L::into_iter, R::into_iter).into()
    }

    /// Iterates pairs of items from both iterators by reference as long as both have items
    /// (like [`zip`](std::iter::Iterator::zip)).
    ///
    /// The returned iterator's `Item` type is `Both<L::Item, R::Item>`.
    #[quither(has_either || has_both)]
    pub fn iter_both(
        &self,
    ) -> IterIntoBoth<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator,
    {
        self.as_ref()
            .map2(
                <&L as IntoIterator>::into_iter,
                <&R as IntoIterator>::into_iter,
            )
            .into()
    }

    /// Iterates pairs of items from both iterators by mutable reference as long as both have items
    /// (like [`zip`](std::iter::Iterator::zip)).
    ///
    /// The returned iterator's `Item` type is `Both<L::Item, R::Item>`.
    #[quither(has_either || has_both)]
    pub fn iter_both_mut(
        &mut self,
    ) -> IterIntoBoth<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator,
    {
        self.as_mut()
            .map2(
                <&mut L as IntoIterator>::into_iter,
                <&mut R as IntoIterator>::into_iter,
            )
            .into()
    }
}

/// `Iterator` implementation for the `Either` type that has the same item type iterators.
///
/// This trait implementation is provided for compatibility with `itertools`.
/// It is not recommended to use this trait implementation in new code,
/// because the definition of `Iterator` for `Either` is confusing --
/// should the item type be the common type of the two iterators,
/// or should it be the left & right (maybe different) item types wrapped in the `Either` enum?
///
/// This implementation works to return the item type of the common type of the two iterators,
/// but if you want that behavior, we recommend using the `.iter_chained()`-like methods and
/// `ChainedIterator` instead.
impl<L, R> Iterator for Either<L, R>
where
    L: Iterator,
    R: Iterator<Item = L::Item>,
{
    type Item = L::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Left(l) => l.next(),
            Self::Right(r) => r.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::Left(l) => l.size_hint(),
            Self::Right(r) => r.size_hint(),
        }
    }
}

impl<L, R> FusedIterator for Either<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator<Item = L::Item> + FusedIterator,
{
}

impl<L, R> ExactSizeIterator for Either<L, R>
where
    L: Iterator + ExactSizeIterator,
    R: Iterator<Item = L::Item> + ExactSizeIterator,
{
    fn len(&self) -> usize {
        match self {
            Self::Left(l) => l.len(),
            Self::Right(r) => r.len(),
        }
    }
}

impl<L, R> DoubleEndedIterator for Either<L, R>
where
    L: Iterator + DoubleEndedIterator,
    R: Iterator<Item = L::Item> + DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::Left(l) => l.next_back(),
            Self::Right(r) => r.next_back(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IterIntoEither<L, R>(Quither<L, R>)
where
    L: Iterator,
    R: Iterator;

/// An alias for `IterIntoEither` for compatibility with `itertools`.
pub type IterEither<L, R> = IterIntoEither<L, R>;

#[quither(has_either || has_both)]
impl<L, R> From<Quither<L, R>> for IterIntoEither<L, R>
where
    L: Iterator,
    R: Iterator,
{
    fn from(q: Quither<L, R>) -> Self {
        IterIntoEither(q.into())
    }
}

impl<L, R> Iterator for IterIntoEither<L, R>
where
    L: Iterator,
    R: Iterator,
{
    type Item = Either<L::Item, R::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(left) = self.0.as_mut().left() {
            if let Some(item) = left.next() {
                return Some(Either::Left(item));
            }
            self.0.clear_left();
        }
        if let Some(right) = self.0.as_mut().right() {
            if let Some(item) = right.next() {
                return Some(Either::Right(item));
            }
            self.0.clear_right();
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let left = self
            .0
            .as_ref()
            .left()
            .map_or((0, Some(0)), |l| l.size_hint());
        let right = self
            .0
            .as_ref()
            .right()
            .map_or((0, Some(0)), |r| r.size_hint());
        let lower = left.0.saturating_add(right.0);
        let upper = match (left.1, right.1) {
            (Some(l), Some(r)) => l.checked_add(r),
            _ => None,
        };
        (lower, upper)
    }
}

impl<L, R> FusedIterator for IterIntoEither<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator + FusedIterator,
{
}

impl<L, R> ExactSizeIterator for IterIntoEither<L, R>
where
    L: Iterator + ExactSizeIterator,
    R: Iterator + ExactSizeIterator,
{
}

impl<L, R> DoubleEndedIterator for IterIntoEither<L, R>
where
    L: Iterator + DoubleEndedIterator,
    R: Iterator + DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(right) = self.0.as_mut().right() {
            if let Some(item) = right.next_back() {
                return Some(Either::Right(item));
            }
            self.0.clear_right();
        }
        if let Some(left) = self.0.as_mut().left() {
            if let Some(item) = left.next_back() {
                return Some(Either::Left(item));
            }
            self.0.clear_left();
        }
        None
    }
}

#[derive(Debug, Clone)]
pub struct IterIntoEitherOrBoth<L, R>(Quither<L, R>)
where
    L: Iterator,
    R: Iterator;

#[quither(has_either || has_both)]
impl<L, R> From<Quither<L, R>> for IterIntoEitherOrBoth<L, R>
where
    L: Iterator,
    R: Iterator,
{
    fn from(q: Quither<L, R>) -> Self {
        IterIntoEitherOrBoth(q.into())
    }
}

impl<L, R> Iterator for IterIntoEitherOrBoth<L, R>
where
    L: Iterator,
    R: Iterator,
{
    type Item = EitherOrBoth<L::Item, R::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut result = Quither::Neither;
        if let Some(left) = self.0.as_mut().left() {
            if let Some(item) = left.next() {
                result.insert_left(item);
            } else {
                self.0.clear_left();
            }
        }
        if let Some(right) = self.0.as_mut().right() {
            if let Some(item) = right.next() {
                result.insert_right(item);
            } else {
                self.0.clear_right();
            }
        }
        result.factor_neither()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let left_size = self.0.as_ref().left().map_or((0, None), |l| l.size_hint());
        let right_size = self.0.as_ref().right().map_or((0, None), |r| r.size_hint());
        (
            usize::max(left_size.0, right_size.0),
            left_size.1.and_then(|left_max| {
                right_size
                    .1
                    .and_then(|right_max| Some(usize::max(left_max, right_max)))
            }),
        )
    }
}

impl<L, R> FusedIterator for IterIntoEitherOrBoth<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator + FusedIterator,
{
}

impl<L, R> ExactSizeIterator for IterIntoEitherOrBoth<L, R>
where
    L: Iterator + ExactSizeIterator,
    R: Iterator + ExactSizeIterator,
{
}

#[derive(Debug, Clone)]
pub struct IterIntoBoth<L, R>(Option<Both<L, R>>)
where
    L: Iterator,
    R: Iterator;

#[quither(has_either || has_both)]
impl<L, R> From<Quither<L, R>> for IterIntoBoth<L, R>
where
    L: Iterator,
    R: Iterator,
{
    fn from(q: Quither<L, R>) -> Self {
        IterIntoBoth(q.both().map(|(l, r)| Both::Both(l, r)))
    }
}

impl<L, R> Iterator for IterIntoBoth<L, R>
where
    L: Iterator,
    R: Iterator,
{
    type Item = Both<L::Item, R::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        let Some(both) = &mut self.0 else {
            return None;
        };
        match both {
            Both::Both(left, right) => {
                if let (Some(left_item), Some(right_item)) = (left.next(), right.next()) {
                    Some(Both::Both(left_item, right_item))
                } else {
                    None
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let Some(Both::Both(left, right)) = self.0.as_ref() else {
            return (0, Some(0));
        };
        let (left_lower, left_upper) = left.size_hint();
        let (right_lower, right_upper) = right.size_hint();
        (
            usize::min(left_lower, right_lower),
            match (left_upper, right_upper) {
                (Some(lu), Some(ru)) => Some(usize::min(lu, ru)),
                _ => None,
            },
        )
    }
}

impl<L, R> FusedIterator for IterIntoBoth<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator + FusedIterator,
{
}

impl<L, R> ExactSizeIterator for IterIntoBoth<L, R>
where
    L: Iterator + ExactSizeIterator,
    R: Iterator + ExactSizeIterator,
{
}

#[derive(Debug, Clone)]
pub struct ChainedIterator<L, R>(
    Chain<Flatten<::core::option::IntoIter<L>>, Flatten<::core::option::IntoIter<R>>>,
)
where
    L: Iterator,
    R: Iterator<Item = L::Item>;

#[quither(has_either || has_both)]
impl<L, R> From<Quither<L, R>> for ChainedIterator<L, R>
where
    L: Iterator,
    R: Iterator<Item = L::Item>,
{
    fn from(q: Quither<L, R>) -> Self {
        let (left, right) = q.left_and_right();
        ChainedIterator(
            left.into_iter()
                .flatten()
                .chain(right.into_iter().flatten()),
        )
    }
}

impl<L, R> Iterator for ChainedIterator<L, R>
where
    L: Iterator,
    R: Iterator<Item = L::Item>,
{
    type Item = L::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<L, R> FusedIterator for ChainedIterator<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator<Item = L::Item> + FusedIterator,
{
}

impl<L, R> DoubleEndedIterator for ChainedIterator<L, R>
where
    L: Iterator + DoubleEndedIterator,
    R: Iterator<Item = L::Item> + DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chained_iterators() {
        let mut q = Quither::Both(vec![0, 1], vec![2, 3, 4]);
        let v1: Vec<_> = q.iter_chained().cloned().collect();
        assert_eq!(v1, vec![0, 1, 2, 3, 4]);

        let v2: Vec<_> = q.iter_chained_mut().map(|x| *x).collect();
        assert_eq!(v2, v1);

        let v3: Vec<_> = q.into_iter_chained().collect();
        assert_eq!(v3, v1);
    }

    #[test]
    fn test_either_iterators() {
        let mut q = Quither::Both(vec![0, 1], vec![2, 3, 4]);
        let v1: Vec<_> = q.iter_either().collect();
        assert_eq!(
            v1,
            vec![
                Either::Left(&0),
                Either::Left(&1),
                Either::Right(&2),
                Either::Right(&3),
                Either::Right(&4),
            ]
        );

        let v2: Vec<_> = q.iter_either_mut().collect();
        assert_eq!(
            v2,
            vec![
                Either::Left(&0),
                Either::Left(&1),
                Either::Right(&2),
                Either::Right(&3),
                Either::Right(&4),
            ]
        );

        let v3: Vec<_> = q.into_iter_either().collect();
        assert_eq!(
            v3,
            vec![
                Either::Left(0),
                Either::Left(1),
                Either::Right(2),
                Either::Right(3),
                Either::Right(4)
            ]
        );
    }

    #[test]
    fn test_either_or_both_iterators() {
        let mut q = Quither::Both(vec![0, 1], vec![2, 3, 4]);
        let v1: Vec<_> = q.iter_either_or_both().collect();
        assert_eq!(
            v1,
            vec![
                EitherOrBoth::Both(&0, &2),
                EitherOrBoth::Both(&1, &3),
                EitherOrBoth::Right(&4),
            ]
        );

        let v2: Vec<_> = q.iter_either_or_both_mut().collect();
        assert_eq!(
            v2,
            vec![
                EitherOrBoth::Both(&0, &2),
                EitherOrBoth::Both(&1, &3),
                EitherOrBoth::Right(&4),
            ]
        );

        let v3: Vec<_> = q.into_iter_either_or_both().collect();
        assert_eq!(
            v3,
            vec![
                EitherOrBoth::Both(0, 2),
                EitherOrBoth::Both(1, 3),
                EitherOrBoth::Right(4),
            ]
        );
    }

    #[test]
    fn test_both_iterators() {
        let mut q = Quither::Both(vec![0, 1], vec![2, 3, 4]);
        let v1: Vec<_> = q.iter_both().collect();
        assert_eq!(v1, vec![Both::Both(&0, &2), Both::Both(&1, &3)]);

        let v2: Vec<_> = q.iter_both_mut().collect();
        assert_eq!(v2, vec![Both::Both(&0, &2), Both::Both(&1, &3)]);

        let v3: Vec<_> = q.into_iter_both().collect();
        assert_eq!(v3, vec![Both::Both(0, 2), Both::Both(1, 3)]);
    }
}
