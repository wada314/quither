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

#[quither]
impl<L, R> Quither<L, R> {
    /// Returns a `Quither` of iterators over the inner values.
    ///
    /// Each variant is mapped to its corresponding iterator using `IntoIterator`.
    /// The returned type is `Quither<L::IntoIter, R::IntoIter>`, where each variant
    /// contains the iterator for the inner value. The iterator's `Item` type is `L::Item`.
    #[quither(has_either && !has_both)]
    pub fn into_iter(self) -> Quither<L::IntoIter, R::IntoIter>
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

    /// Converts the inner value(s) into their corresponding iterators.
    ///
    /// For each variant, returns a `Quither` wrapping the result of `into_iter` on the inner value.
    /// If the variant is `Both`, both values are converted. The `Neither` variant yields `Quither::Neither`.
    ///
    /// # Both variant
    /// For the `Both` variant, this method behaves similarly to [`Iterator::chain`]:
    /// it yields all items from the left iterator, then from the right.  
    /// However, unlike `chain`, `Quither` cannot store state, so it always calls `next()`
    /// on the left iterator and checks if it is `None` before proceeding to the right.
    /// This may result in performance overhead, so using this method with the `Both` variant
    /// is discouraged for performance-critical code.
    #[quither(has_either && has_both)]
    pub fn into_iter(self) -> Quither<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
        L::IntoIter: FusedIterator,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l.into_iter()),
            #[either]
            Self::Right(r) => Quither::Right(r.into_iter()),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(l.into_iter(), r.into_iter()),
        }
    }

    /// Returns a `Quither` of iterators over references to the inner values.
    ///
    /// Each variant is mapped to an iterator over references using `IntoIterator`.
    /// The returned type is `Quither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>`,
    /// where each variant contains the iterator for the reference. The iterator's `Item` type is `<&L as IntoIterator>::Item`.
    #[quither(has_either && !has_both)]
    pub fn iter(&self) -> Quither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
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

    /// Returns a `Quither` of iterators over references to the inner values.
    ///
    /// Each variant is mapped to an iterator over references using `IntoIterator`.
    /// The returned type is `Quither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>`,
    /// where each variant contains the iterator for the reference. The iterator's `Item` type is `<&L as IntoIterator>::Item`.
    ///
    /// # Both variant
    /// For the `Both` variant, this method behaves similarly to [`Iterator::chain`]:
    /// it yields all items from the left iterator, then from the right.  
    /// However, unlike `chain`, `Quither` cannot store state, so it always calls `next()`
    /// on the left iterator and checks if it is `None` before proceeding to the right.
    /// This may result in performance overhead, so using this method with the `Both` variant
    /// is discouraged for performance-critical code.
    #[quither(has_either && has_both)]
    pub fn iter(&self) -> Quither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
        for<'a> <&'a L as IntoIterator>::IntoIter: FusedIterator,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l.into_iter()),
            #[either]
            Self::Right(r) => Quither::Right(r.into_iter()),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(l.into_iter(), r.into_iter()),
        }
    }

    /// Returns a `Quither` of iterators over mutable references to the inner values.
    ///
    /// Each variant is mapped to an iterator over mutable references using `IntoIterator`.
    /// The returned type is `Quither<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>`,
    /// where each variant contains the iterator for the mutable reference. The iterator's `Item` type is `<&mut L as IntoIterator>::Item`.
    #[quither(has_either && !has_both)]
    pub fn iter_mut(
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

    /// Returns a `Quither` of iterators over mutable references to the inner values.
    ///
    /// Each variant is mapped to an iterator over mutable references using `IntoIterator`.
    /// The returned type is `Quither<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>`,
    /// where each variant contains the iterator for the mutable reference. The iterator's `Item` type is `<&mut L as IntoIterator>::Item`.
    ///
    /// # Both variant
    /// For the `Both` variant, this method behaves similarly to [`Iterator::chain`]:
    /// it yields all items from the left iterator, then from the right.  
    /// However, unlike `chain`, `Quither` cannot store state, so it always calls `next()`
    /// on the left iterator and checks if it is `None` before proceeding to the right.
    /// This may result in performance overhead, so using this method with the `Both` variant
    /// is discouraged for performance-critical code.
    #[quither(has_either && has_both)]
    pub fn iter_mut(
        &mut self,
    ) -> Quither<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
        for<'a> <&'a mut L as IntoIterator>::IntoIter: FusedIterator,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l.into_iter()),
            #[either]
            Self::Right(r) => Quither::Right(r.into_iter()),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(l.into_iter(), r.into_iter()),
        }
    }

    /// Returns an iterator that yields an enum value representing items from the left and right iterators.
    ///
    /// The `Item` type of this iterator is an enum whose variants correspond to the possible states of the underlying iterators.
    /// For example, when iterating over a pair of iterators, the item may be `Both(l, r)` if both have items,
    /// or `Left(l)`/`Right(r)` if only one side has items left. The set of variants in the yielded item depends on the state of the iterators,
    /// and may differ from the enum type used to construct this iterator.
    #[quither(has_either || has_both)]
    pub fn factor_into_iter(self) -> IterQuither<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        IterQuither(self.map2(L::into_iter, R::into_iter))
    }

    /// Returns an iterator that yields an enum value for each pair of items from the left and right iterators by reference.
    ///
    /// The returned iterator's `Item` type is an enum supporting `Left`, `Right`, and `Both` variants as needed,
    /// depending on which underlying iterators still have items. This allows handling cases where the two iterators
    /// have different lengths.
    #[quither(has_either || has_both)]
    pub fn factor_iter(
        &self,
    ) -> IterQuither<<&L as IntoIterator>::IntoIter, <&R as IntoIterator>::IntoIter>
    where
        for<'a> &'a L: IntoIterator,
        for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    {
        IterQuither(self.as_ref().map2(
            <&L as IntoIterator>::into_iter,
            <&R as IntoIterator>::into_iter,
        ))
    }

    /// Returns an iterator that yields an enum value for each pair of items from the left and right iterators by mutable reference.
    ///
    /// The returned iterator's `Item` type is an enum supporting `Left`, `Right`, and `Both` variants as needed,
    /// depending on which underlying iterators still have items. This allows handling cases where the two iterators
    /// have different lengths.
    #[quither(has_either || has_both)]
    pub fn factor_iter_mut(
        &mut self,
    ) -> IterQuither<<&mut L as IntoIterator>::IntoIter, <&mut R as IntoIterator>::IntoIter>
    where
        for<'a> &'a mut L: IntoIterator,
        for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    {
        IterQuither(self.as_mut().map2(
            <&mut L as IntoIterator>::into_iter,
            <&mut R as IntoIterator>::into_iter,
        ))
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

/// An iterator that yields an enum value representing items from the left and right iterators.
///
/// The `Item` type of this iterator is an enum whose variants correspond to the possible states of the underlying iterators.
/// For example, when iterating over a pair of iterators, the item may be `Both(l, r)` if both have items,
/// or `Left(l)`/`Right(r)` if only one side has items left. The set of variants in the yielded item depends on the state of the iterators,
/// and may differ from the enum type used to construct this iterator.
#[quither(has_either || has_both)]
#[derive(Debug, Clone)]
pub struct IterQuither<L, R>(Quither<L, R>);

/// Returns the next item from the underlying iterators, wrapped in one of the variants.
///
/// The `Item` type of this iterator is an enum whose variants correspond to the possible states of the underlying iterators.
/// For example, when iterating a pair of iterators, this iterator yields `Both(l, r)` while both iterators yield items,
/// then `Left(l)` or `Right(r)` if only one side has items left. This allows handling cases where the two iterators have different lengths.
#[quither(has_either || has_both)]
impl<L, R> Iterator for IterQuither<L, R>
where
    L: Iterator,
    R: Iterator,
{
    type Item = Quither<L::Item, R::Item, { has_either || has_both }, has_neither, has_both>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            #[either]
            Quither::Left(l) => l.next().map(Self::Item::Left),
            #[either]
            Quither::Right(r) => r.next().map(Self::Item::Right),
            #[neither]
            Quither::Neither => None,
            #[both]
            Quither::Both(l, r) => match (l.next(), r.next()) {
                (Some(l), Some(r)) => Some(Self::Item::Both(l, r)),
                (Some(l), None) => Some(Self::Item::Left(l)),
                (None, Some(r)) => Some(Self::Item::Right(r)),
                (None, None) => None,
            },
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            #[either]
            Quither::Left(l) => l.size_hint(),
            #[either]
            Quither::Right(r) => r.size_hint(),
            #[neither]
            Quither::Neither => (0, Some(0)),
            #[both]
            Quither::Both(l, r) => {
                let (l_lower, l_upper) = l.size_hint();
                let (r_lower, r_upper) = r.size_hint();
                (
                    usize::min(l_lower, r_lower),
                    if let (Some(l_upper), Some(r_upper)) = (l_upper, r_upper) {
                        Some(usize::max(l_upper, r_upper))
                    } else {
                        None
                    },
                )
            }
        }
    }
}

#[quither(has_either || has_both)]
impl<L, R> FusedIterator for IterQuither<L, R>
where
    L: Iterator + FusedIterator,
    R: Iterator + FusedIterator,
{
}

#[quither(has_either || has_both)]
impl<L, R> ExactSizeIterator for IterQuither<L, R>
where
    L: Iterator + ExactSizeIterator,
    R: Iterator + ExactSizeIterator,
{
}
