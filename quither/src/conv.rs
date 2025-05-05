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

impl<L, R> From<Result<R, L>> for Either<L, R> {
    fn from(result: Result<R, L>) -> Self {
        match result {
            Ok(r) => Either::Right(r),
            Err(l) => Either::Left(l),
        }
    }
}

/// Promotes a type without `Both` variant to a type with `Both` variant.
#[quither(has_both && (has_either || has_neither))]
impl<L, R> From<Quither<L, R, has_either, has_neither, false>> for Quither<L, R> {
    fn from(quither: Quither<L, R, has_either, has_neither, false>) -> Self {
        match quither {
            #[either]
            Quither::<L, R, has_either, has_neither, false>::Left(l) => Quither::Left(l),
            #[either]
            Quither::<L, R, has_either, has_neither, false>::Right(r) => Quither::Right(r),
            #[neither]
            Quither::<L, R, has_either, has_neither, false>::Neither => Quither::Neither,
        }
    }
}

/// Promotes a type without `Either` variant to a type with `Either` variant.
#[quither(has_either && (has_neither || has_both))]
impl<L, R> From<Quither<L, R, false, has_neither, has_both>> for Quither<L, R> {
    fn from(quither: Quither<L, R, false, has_neither, has_both>) -> Self {
        match quither {
            #[neither]
            Quither::<L, R, false, has_neither, has_both>::Neither => Quither::Neither,
            #[both]
            Quither::<L, R, false, has_neither, has_both>::Both(l, r) => Quither::Both(l, r),
        }
    }
}

/// Promotes a type without `Neither` variant to a type with `Neither` variant.
#[quither(has_neither && (has_either || has_both))]
impl<L, R> From<Quither<L, R, has_either, false, has_both>> for Quither<L, R> {
    fn from(quither: Quither<L, R, has_either, false, has_both>) -> Self {
        match quither {
            #[either]
            Quither::<L, R, has_either, false, has_both>::Left(l) => Quither::Left(l),
            #[either]
            Quither::<L, R, has_either, false, has_both>::Right(r) => Quither::Right(r),
            #[both]
            Quither::<L, R, has_either, false, has_both>::Both(l, r) => Quither::Both(l, r),
        }
    }
}

/// Promotes a type and adds `Both` and `Neither` variants.
impl<L, R> From<Either<L, R>> for Quither<L, R> {
    fn from(either: Either<L, R>) -> Self {
        match either {
            Either::Left(l) => Quither::Left(l),
            Either::Right(r) => Quither::Right(r),
        }
    }
}

/// Promotes a type and adds `Either` and `Both` variants.
impl<L, R> From<Neither> for Quither<L, R> {
    fn from(_neither: Neither) -> Self {
        Quither::Neither
    }
}

/// Promotes a type and adds `Either` and `Neither` variants.
impl<L, R> From<Both<L, R>> for Quither<L, R> {
    fn from(both: Both<L, R>) -> Self {
        match both {
            Both::Both(l, r) => Quither::Both(l, r),
        }
    }
}

/// Demotes a type with `Either` variant to a type without `Either` variant.
#[quither(!has_either && has_both)]
impl<L, R> TryFrom<Quither<L, R, true, has_neither, true>> for Quither<L, R> {
    type Error = Either<L, R>;
    fn try_from(quither: Quither<L, R, true, has_neither, true>) -> Result<Self, Self::Error> {
        match quither {
            Quither::<L, R, true, has_neither, true>::Left(l) => Err(Either::Left(l)),
            Quither::<L, R, true, has_neither, true>::Right(r) => Err(Either::Right(r)),
            #[neither]
            Quither::<L, R, true, has_neither, true>::Neither => Ok(Quither::Neither),
            Quither::<L, R, true, has_neither, true>::Both(l, r) => Ok(Quither::Both(l, r)),
        }
    }
}

/// Demotes a type with `Either` variant to a type without `Either` variant.
impl<L, R> TryFrom<EitherOrNeither<L, R>> for Neither {
    type Error = Either<L, R>;
    fn try_from(either_or_neither: EitherOrNeither<L, R>) -> Result<Self, Self::Error> {
        match either_or_neither {
            EitherOrNeither::Left(l) => Err(Either::Left(l)),
            EitherOrNeither::Right(r) => Err(Either::Right(r)),
            EitherOrNeither::Neither => Ok(Neither::Neither),
        }
    }
}

/// Demotes a type with `Neither` variant to a type without `Neither` variant.
#[quither(!has_neither)]
impl<L, R> TryFrom<Quither<L, R, has_either, true, has_both>> for Quither<L, R> {
    type Error = Neither;
    fn try_from(quither: Quither<L, R, has_either, true, has_both>) -> Result<Self, Self::Error> {
        match quither {
            #[either]
            Quither::<L, R, has_either, true, has_both>::Left(l) => Ok(Quither::Left(l)),
            #[either]
            Quither::<L, R, has_either, true, has_both>::Right(r) => Ok(Quither::Right(r)),
            Quither::<L, R, has_either, true, has_both>::Neither => Err(Neither::Neither),
            #[both]
            Quither::<L, R, has_either, true, has_both>::Both(l, r) => Ok(Quither::Both(l, r)),
        }
    }
}

/// Demotes a type with `Both` variant to a type without `Both` variant.
#[quither(!has_both && has_either)]
impl<L, R> TryFrom<Quither<L, R, true, has_neither, true>> for Quither<L, R> {
    type Error = Both<L, R>;
    fn try_from(quither: Quither<L, R, true, has_neither, true>) -> Result<Self, Self::Error> {
        match quither {
            Quither::<L, R, true, has_neither, true>::Left(l) => Ok(Quither::Left(l)),
            Quither::<L, R, true, has_neither, true>::Right(r) => Ok(Quither::Right(r)),
            #[neither]
            Quither::<L, R, true, has_neither, true>::Neither => Ok(Quither::Neither),
            Quither::<L, R, true, has_neither, true>::Both(l, r) => Err(Both::Both(l, r)),
        }
    }
}
