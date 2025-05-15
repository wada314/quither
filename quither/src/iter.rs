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
use ::core::option::IntoIter as OptionIntoIter;

mod private {
    type _Foo1<A, B> = ::core::iter::Chain<A, B>;
    type _Foo2<A> = ::core::iter::Flatten<A>;
    type _Foo3<A> = ::core::option::IntoIter<A>;
}

#[quither]
impl<L, R> Quither<L, R> {
    /// Returns an iterator that chains the left and right iterators.
    ///
    /// Each variant is converted to its corresponding iterator. For the `Both` variant,
    /// all items from the left iterator are yielded first, followed by all items from the right iterator.
    /// The `Item` type must be the same for both sides.
    #[quither(has_either && !has_both)]
    pub fn chain_into_iter(self) -> Quither<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l.into_iter()),
            #[either]
            Self::Right(r) => Quither::Right(r.into_iter()),
            #[neither]
            Self::Neither => Quither::Neither,
        }
    }

    /// Returns an iterator that chains the left and right iterators.
    ///
    /// Each variant is converted to its corresponding iterator. For the `Both` variant,
    /// all items from the left iterator are yielded first, followed by all items from the right iterator.
    /// The `Item` type must be the same for both sides.
    #[quither(has_either && has_both)]
    pub fn chain_into_iter(
        self,
    ) -> Chain<Flatten<::core::option::IntoIter<L>>, Flatten<::core::option::IntoIter<R>>>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        let (left, right) = self.left_and_right();
        let left_iter = left.into_iter().flatten();
        let right_iter = right.into_iter().flatten();
        left_iter.chain(right_iter)
    }

    /// Returns an iterator that chains the left and right iterators.
    ///
    /// Each variant is converted to its corresponding iterator. For the `Both` variant,
    /// all items from the left iterator are yielded first, followed by all items from the right iterator.
    /// The `Item` type must be the same for both sides.
    #[quither(has_either && !has_both)]
    pub fn chain_iter(
        &self,
    ) -> Quither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l.into_iter()),
            #[either]
            Self::Right(r) => Quither::Right(r.into_iter()),
            #[neither]
            Self::Neither => Quither::Neither,
        }
    }

    /// Returns an iterator that chains the left and right iterators.
    ///
    /// Each variant is converted to its corresponding iterator. For the `Both` variant,
    /// all items from the left iterator are yielded first, followed by all items from the right iterator.
    /// The `Item` type must be the same for both sides.
    #[quither(has_either && has_both)]
    pub fn chain_iter(
        &self,
    ) -> Chain<Flatten<::core::option::IntoIter<&L>>, Flatten<::core::option::IntoIter<&R>>>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    {
        let (left, right) = self.as_ref().left_and_right();
        let left_iter = left.into_iter().flatten();
        let right_iter = right.into_iter().flatten();
        left_iter.chain(right_iter)
    }

    /// Returns an iterator that chains the left and right iterators.
    ///
    /// Each variant is converted to its corresponding iterator. For the `Both` variant,
    /// all items from the left iterator are yielded first, followed by all items from the right iterator.
    /// The `Item` type must be the same for both sides.
    #[quither(has_either && !has_both)]
    pub fn chain_iter_mut(
        &mut self,
    ) -> Quither<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l.into_iter()),
            #[either]
            Self::Right(r) => Quither::Right(r.into_iter()),
            #[neither]
            Self::Neither => Quither::Neither,
        }
    }

    /// Returns an iterator that chains the left and right iterators.
    ///
    /// Each variant is converted to its corresponding iterator. For the `Both` variant,
    /// all items from the left iterator are yielded first, followed by all items from the right iterator.
    /// The `Item` type must be the same for both sides.
    #[quither(has_either && has_both)]
    pub fn chain_iter_mut(
        &mut self,
    ) -> Chain<Flatten<::core::option::IntoIter<&mut L>>, Flatten<::core::option::IntoIter<&mut R>>>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    {
        let (left, right) = self.as_mut().left_and_right();
        let left_iter = left.into_iter().flatten();
        let right_iter = right.into_iter().flatten();
        left_iter.chain(right_iter)
    }

    /// Returns an iterator that yields an enum value representing items from the left and right iterators.
    ///
    /// The `Item` type of this iterator is an enum whose variants correspond to the possible states of the underlying iterators.
    /// For example, when iterating over a pair of iterators, the item may be `Both(l, r)` if both have items,
    /// or `Left(l)`/`Right(r)` if only one side has items left. The set of variants in the yielded item depends on the state of the iterators,
    /// and may differ from the enum type used to construct this iterator.
    #[quither(has_either || has_both)]
    pub fn factor_into_iter(
        self,
    ) -> IterIntoQuither<L::IntoIter, R::IntoIter, true, false, has_both>
    where
        L: IntoIterator,
        R: IntoIterator,
    {
        self.map2(L::into_iter, R::into_iter).into()
    }

    /// Returns an iterator that yields an enum value for each pair of items from the left and right iterators by reference.
    ///
    /// The returned iterator's `Item` type is an enum supporting `Left`, `Right`, and `Both` variants as needed,
    /// depending on which underlying iterators still have items. This allows handling cases where the two iterators
    /// have different lengths.
    #[quither(has_either || has_both)]
    pub fn factor_iter(
        &self,
    ) -> IterIntoQuither<
        <&L as IntoIterator>::IntoIter,
        <&R as IntoIterator>::IntoIter,
        true,
        false,
        has_both,
    >
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

    /// Returns an iterator that yields an enum value for each pair of items from the left and right iterators by mutable reference.
    ///
    /// The returned iterator's `Item` type is an enum supporting `Left`, `Right`, and `Both` variants as needed,
    /// depending on which underlying iterators still have items. This allows handling cases where the two iterators
    /// have different lengths.
    #[quither(has_either || has_both)]
    pub fn factor_iter_mut(
        &mut self,
    ) -> IterIntoQuither<
        <&mut L as IntoIterator>::IntoIter,
        <&mut R as IntoIterator>::IntoIter,
        true,
        false,
        has_both,
    >
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

    /// An iterator that yields Either::Left for all items from the left iterator, then Either::Right for all items from the right iterator.
    #[quither(has_either || has_both)]
    pub fn either_into_iter(self) -> IterIntoEither<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator,
    {
        IterIntoEither::new(
            self.map2(
                <L as IntoIterator>::into_iter,
                <R as IntoIterator>::into_iter,
            )
            .into(),
        )
    }

    #[deprecated(note = "Use `chain_into_iter` method instead, which has clearer naming")]
    #[quither(has_either && !has_both)]
    pub fn into_iter(self) -> Quither<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        self.chain_into_iter()
    }

    #[deprecated(note = "Use `chain_into_iter` method instead, which has clearer naming")]
    #[quither(has_either && has_both)]
    pub fn into_iter(
        self,
    ) -> Chain<Flatten<::core::option::IntoIter<L>>, Flatten<::core::option::IntoIter<R>>>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        self.chain_into_iter()
    }

    #[deprecated(note = "Use `chain_iter` method instead, which has clearer naming")]
    #[quither(has_either && !has_both)]
    pub fn iter(&self) -> Quither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    {
        self.chain_iter()
    }

    #[deprecated(note = "Use `chain_iter` method instead, which has clearer naming")]
    #[quither(has_either && has_both)]
    pub fn iter(
        &self,
    ) -> Chain<Flatten<::core::option::IntoIter<&L>>, Flatten<::core::option::IntoIter<&R>>>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    {
        self.chain_iter()
    }

    #[deprecated(note = "Use `chain_iter_mut` method instead, which has clearer naming")]
    #[quither(has_either && !has_both)]
    pub fn iter_mut(
        &mut self,
    ) -> Quither<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    {
        self.chain_iter_mut()
    }

    #[deprecated(note = "Use `chain_iter_mut` method instead, which has clearer naming")]
    #[quither(has_either && has_both)]
    pub fn iter_mut(
        &mut self,
    ) -> Chain<Flatten<::core::option::IntoIter<&mut L>>, Flatten<::core::option::IntoIter<&mut R>>>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    {
        self.chain_iter_mut()
    }
}

/// Implements `Iterator` for the enum, yielding items from the underlying iterator(s).
///
/// The `Item` type is the same as the item type of the left iterator. For each variant, yields items from the corresponding iterator.
/// For the `Neither` variant, always yields `None`.
#[quither(has_either && !has_both)]
impl<L, R> Iterator for Quither<L, R>
where
    L: Iterator,
    R: Iterator<Item = L::Item>,
{
    type Item = L::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            #[either]
            Self::Left(l) => l.next(),
            #[either]
            Self::Right(r) => r.next(),
            #[neither]
            Self::Neither => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            #[either]
            Self::Left(l) => l.size_hint(),
            #[either]
            Self::Right(r) => r.size_hint(),
            #[neither]
            Self::Neither => (0, Some(0)),
        }
    }
}

/// Implements `Iterator` for the enum, yielding items from the underlying iterator(s).
///
/// The `Item` type is the same as the item type of the left iterator. For the `Both` variant, yields all items from the left iterator first;
/// once the left iterator is exhausted, yields items from the right iterator. This is similar to `Iterator::chain`,
/// but always calls `next()` on the left iterator and checks for `None` on each call, which may have performance implications.
#[quither(has_both)]
impl<L, R> Iterator for Quither<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator<Item = L::Item>,
{
    type Item = L::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            #[either]
            Self::Left(l) => l.next(),
            #[either]
            Self::Right(r) => r.next(),
            #[neither]
            Self::Neither => None,
            #[both]
            Self::Both(l, r) => l.next().or_else(|| r.next()),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            #[either]
            Self::Left(l) => l.size_hint(),
            #[either]
            Self::Right(r) => r.size_hint(),
            #[neither]
            Self::Neither => (0, Some(0)),
            #[both]
            Self::Both(l, r) => {
                let (l_lower, l_upper) = l.size_hint();
                let (r_lower, r_upper) = r.size_hint();
                (
                    usize::saturating_add(l_lower, r_lower),
                    l_upper.and_then(|l_upper| {
                        r_upper.and_then(|r_upper| usize::checked_add(l_upper, r_upper))
                    }),
                )
            }
        }
    }
}

#[quither(has_either || has_both)]
impl<L, R> FusedIterator for Quither<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator<Item = L::Item> + FusedIterator,
{
}

#[quither(has_either && !has_both)]
impl<L, R> ExactSizeIterator for Quither<L, R>
where
    L: Iterator + ExactSizeIterator,
    R: Iterator<Item = L::Item> + ExactSizeIterator,
{
    fn len(&self) -> usize {
        match self {
            #[either]
            Self::Left(l) => l.len(),
            #[either]
            Self::Right(r) => r.len(),
            #[neither]
            Self::Neither => 0,
        }
    }
}

#[quither(has_either && !has_both)]
impl<L, R> DoubleEndedIterator for Quither<L, R>
where
    L: Iterator + DoubleEndedIterator,
    R: Iterator<Item = L::Item> + DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            #[either]
            Self::Left(l) => l.next_back(),
            #[either]
            Self::Right(r) => r.next_back(),
            #[neither]
            Self::Neither => None,
        }
    }
}

#[quither(has_both)]
impl<L, R> DoubleEndedIterator for Quither<L, R>
where
    L: Iterator + FusedIterator + DoubleEndedIterator,
    R: Iterator<Item = L::Item> + FusedIterator + DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            #[either]
            Self::Left(l) => l.next_back(),
            #[either]
            Self::Right(r) => r.next_back(),
            #[neither]
            Self::Neither => None,
            #[both]
            Self::Both(l, r) => r.next_back().or_else(|| l.next_back()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IterIntoEither<L, R>(Quither<L, R>)
where
    L: Iterator,
    R: Iterator;

#[quither(has_either || has_both)]
impl<L, R> Into<IterIntoEither<L, R>> for Quither<L, R>
where
    L: Iterator,
    R: Iterator,
{
    fn into(self) -> IterIntoEither<L, R> {
        IterIntoEither(self.into())
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
impl<L, R> Into<IterIntoEitherOrBoth<L, R>> for Quither<L, R>
where
    L: Iterator,
    R: Iterator,
{
    fn into(self) -> IterIntoEitherOrBoth<L, R> {
        IterIntoEitherOrBoth(self.into())
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
pub struct ChainedIterator<L, R>(
    Chain<Flatten<::core::option::IntoIter<L>>, Flatten<::core::option::IntoIter<R>>>,
)
where
    L: Iterator,
    R: Iterator<Item = L::Item>;

#[quither(has_either || has_both)]
impl<L, R> Into<ChainedIterator<L, R>> for Quither<L, R>
where
    L: Iterator,
    R: Iterator<Item = L::Item>,
{
    fn into(self) -> ChainedIterator<L, R> {
        let (left, right) = self.left_and_right();
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
}

impl<L, R> FusedIterator for ChainedIterator<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator<Item = L::Item> + FusedIterator,
{
}

impl<L, R> ExactSizeIterator for ChainedIterator<L, R>
where
    L: Iterator + ExactSizeIterator,
    R: Iterator<Item = L::Item> + ExactSizeIterator,
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
