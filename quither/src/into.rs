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
use quither_proc_macros::quither;

#[quither]
impl<L, R> Xither<L, R> {
    #[quither(!has_neither)]
    /// Converts to the left value, consuming self.
    ///
    /// Only available for types that do not include the `Neither` variant. If the value is `Left`, returns
    /// the inner value. If the value is `Right`, converts it into `L`. If the value is `Both`, returns the
    /// left value. Panics if called on `Neither`.
    pub fn into_left(self) -> L
    where
        R: Into<L>,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(r) => r.into(),
            #[neither]
            Self::Neither => unreachable!(),
            #[both]
            Self::Both(l, _) => l,
        }
    }

    #[quither(!has_neither)]
    /// Converts to the right value, consuming self.
    ///
    /// Only available for types that do not include the `Neither` variant. If the value is `Right`, returns
    /// the inner value. If the value is `Left`, converts it into `R`. If the value is `Both`, returns the
    /// right value. Panics if called on `Neither`.
    pub fn into_right(self) -> R
    where
        L: Into<R>,
    {
        match self {
            #[either]
            Self::Left(l) => l.into(),
            #[either]
            Self::Right(r) => r,
            #[neither]
            Self::Neither => unreachable!(),
            #[both]
            Self::Both(_, r) => r,
        }
    }
}

impl<L, R> Either<L, R> {
    /// Converts either variant into a common type using `Into`.
    ///
    /// Consumes self and converts the inner value to type T using `Into`, regardless of which variant is
    /// present. Both `L` and `R` must implement `Into<T>`.
    pub fn either_into<T>(self) -> T
    where
        L: Into<T>,
        R: Into<T>,
    {
        match self {
            Either::Left(l) => l.into(),
            Either::Right(r) => r.into(),
        }
    }
}
