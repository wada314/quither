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
    /// Factor out the `None` values out from the type.
    ///
    /// Note that for some types, this method returns a different type from the input type.
    /// For example, `Both` type's this method returns `EitherOrBoth` type because
    /// it is needed to handle the case where one of the values is `None`.
    ///
    /// TODO: Needs examples.
    pub fn factor_none(self) -> Option<Quither<L, R, has_both || has_either, has_neither, has_both>> {
        match self {
            #[either]
            Self::Left(Some(l)) => Some(Quither::<L, R, true, has_neither, has_both>::Left(l)),
            #[either]
            Self::Right(Some(r)) => Some(Quither::<L, R, true, has_neither, has_both>::Right(r)),
            #[both]
            Self::Both(Some(l), Some(r)) => {
                Some(Quither::<L, R, true, has_neither, has_both>::Both(l, r))
            }
            #[both]
            Self::Both(Some(l), None) => {
                Some(Quither::<L, R, true, has_neither, has_both>::Left(l))
            }
            #[both]
            Self::Both(None, Some(r)) => {
                Some(Quither::<L, R, true, has_neither, has_both>::Right(r))
            }
            _ => None,
        }
    }
}

impl<L, R, E> Either<Result<L, E>, Result<R, E>> {
    /// Factor out the `Err` values from the type.
    ///
    /// This method is only available for the `Either` type.
    pub fn factor_error(self) -> Result<Either<L, R>, E> {
        match self {
            Either::Left(Ok(l)) => Ok(Either::Left(l)),
            Either::Right(Ok(r)) => Ok(Either::Right(r)),
            Either::Left(Err(e)) | Either::Right(Err(e)) => Err(e),
        }
    }
}

impl<T, L, R> Either<Result<T, L>, Result<T, R>> {
    /// Factor out the `Ok` values from the type.
    ///
    /// This method is only available for the `Either` type.
    pub fn factor_ok(self) -> Result<T, Either<L, R>> {
        match self {
            Either::Left(Err(e)) => Err(Either::Left(e)),
            Either::Right(Err(e)) => Err(Either::Right(e)),
            Either::Left(Ok(x)) | Either::Right(Ok(x)) => Ok(x),
        }
    }
}

impl<T, L, R> Either<(T, L), (T, R)> {
    pub fn factor_first(self) -> (T, Either<L, R>) {
        match self {
            Either::Left((t, l)) => (t, Either::Left(l)),
            Either::Right((t, r)) => (t, Either::Right(r)),
        }
    }
}

impl<T, L, R> Either<(L, T), (R, T)> {
    /// Factor out the second value (T) from the tuple, returning (T, Either<L, R>).
    pub fn factor_second(self) -> (T, Either<L, R>) {
        match self {
            Either::Left((l, t)) => (t, Either::Left(l)),
            Either::Right((r, t)) => (t, Either::Right(r)),
        }
    }
}
