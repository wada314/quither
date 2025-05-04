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

use super::*;
use ::quither_proc_macros::quither;

#[quither]
impl<L, R> Quither<L, R> {
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
}

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
}

#[quither]
pub struct IterQuither<L, R>(Quither<L, R>);

#[quither]
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
}
