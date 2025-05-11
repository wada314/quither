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
impl<L, R> Quither<L, R> {
    /// Factor out the `Neither` variant out from the type, converting the type into
    /// `Option<NewType>>`, where `NewType` is the type of the type excluding the `Neither` variant.
    ///
    /// Only available for types that include the Neither variant and at least one of Either or Both.
    /// Converts the value into an Option of a type that does not include the Neither variant. Returns
    /// None if the value is Neither; otherwise, returns Some with the corresponding variant.
    #[quither(has_neither && (has_either || has_both))]
    pub fn factor_neither(self) -> Option<Quither<L, R, has_either, false, has_both>> {
        match self {
            #[either]
            Self::Left(l) => Some(Quither::<L, R, has_either, false, has_both>::Left(l)),
            #[either]
            Self::Right(r) => Some(Quither::<L, R, has_either, false, has_both>::Right(r)),
            #[neither]
            Self::Neither => None,
            #[both]
            Self::Both(l, r) => Some(Quither::<L, R, has_either, false, has_both>::Both(l, r)),
        }
    }
}

#[quither]
impl<L, R> Quither<Option<L>, Option<R>> {
    /// Factors out None values from a pair of Options, returning None if both are None.
    ///
    /// For types of pairs of Option, this method returns an Option of a pair type without Option.
    /// If both values are None, returns None. If only one is Some, returns the corresponding variant.
    /// If both are Some, returns Both. The output type may differ from the input type depending on the
    /// variants present. See also the note about Both types returning EitherOrBoth.
    pub fn factor_none(
        self,
    ) -> Option<Quither<L, R, { has_both || has_either }, has_neither, has_both>> {
        #[allow(unused)]
        type Quither2<L, R> = Quither<L, R, { has_both || has_either }, has_neither, has_both>;
        match self {
            #[either]
            Self::Left(Some(l)) => Some(Quither2::Left(l)),
            #[either]
            Self::Right(Some(r)) => Some(Quither2::Right(r)),
            #[both]
            Self::Both(Some(l), Some(r)) => Some(Quither2::Both(l, r)),
            #[both]
            Self::Both(Some(l), None) => Some(Quither2::Left(l)),
            #[both]
            Self::Both(None, Some(r)) => Some(Quither2::Right(r)),
            _ => None,
        }
    }
}

impl<L, R, E> Either<Result<L, E>, Result<R, E>> {
    /// Factors out Err values, returning Ok if the value is Ok, or Err otherwise.
    ///
    /// Only available for types with two Result values. If either side is Err, returns Err. Otherwise,
    /// returns Ok with the corresponding variant.
    pub fn factor_err(self) -> Result<Either<L, R>, E> {
        match self {
            Either::Left(Ok(l)) => Ok(Either::Left(l)),
            Either::Right(Ok(r)) => Ok(Either::Right(r)),
            Either::Left(Err(e)) | Either::Right(Err(e)) => Err(e),
        }
    }
}

impl<T, L, R> Either<Result<T, L>, Result<T, R>> {
    /// Factors out Ok values, returning Ok if the value is Ok, or Err otherwise.
    ///
    /// Only available for types with two Result values. If either side is Ok, returns Ok. Otherwise,
    /// returns Err with the corresponding variant.
    pub fn factor_ok(self) -> Result<T, Either<L, R>> {
        match self {
            Either::Left(Err(e)) => Err(Either::Left(e)),
            Either::Right(Err(e)) => Err(Either::Right(e)),
            Either::Left(Ok(x)) | Either::Right(Ok(x)) => Ok(x),
        }
    }
}

impl<T, L, R> Either<(T, L), (T, R)> {
    /// Factors out the first value from a tuple, returning (first, pair of second values).
    ///
    /// For a pair of tuples, returns a tuple of the first value and a pair of the second values.
    pub fn factor_first(self) -> (T, Either<L, R>) {
        match self {
            Either::Left((t, l)) => (t, Either::Left(l)),
            Either::Right((t, r)) => (t, Either::Right(r)),
        }
    }
}

impl<T, L, R> Either<(L, T), (R, T)> {
    /// Factors out the second value from a tuple, returning (second, pair of first values).
    ///
    /// For a pair of tuples, returns a tuple of the second value and a pair of the first values.
    /// Factor out the second value (T) from the tuple, returning (T, Either<L, R>).
    pub fn factor_second(self) -> (T, Either<L, R>) {
        match self {
            Either::Left((l, t)) => (t, Either::Left(l)),
            Either::Right((r, t)) => (t, Either::Right(r)),
        }
    }
}
