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
    /// Return left value or given value.
    #[quither(has_either || has_both)]
    pub fn left_or(self, #[allow(unused)] other: L) -> L {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(_) => other,
            #[neither]
            Self::Neither => other,
            #[both]
            Self::Both(l, _) => l,
        }
    }

    /// Return right value or given value.
    #[quither(has_either || has_both)]
    pub fn right_or(self, #[allow(unused)] other: R) -> R {
        match self {
            #[either]
            Self::Left(_) => other,
            #[either]
            Self::Right(r) => r,
            #[neither]
            Self::Neither => other,
            #[both]
            Self::Both(_, r) => r,
        }
    }

    /// Return the both values as a tuple, or the given value if either side is missing.
    #[quither(has_either || has_both)]
    pub fn both_or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
        match self {
            #[either]
            Self::Left(l2) => (l2, r),
            #[either]
            Self::Right(r2) => (l, r2),
            #[neither]
            Self::Neither => (l, r),
            #[both]
            Self::Both(l2, r2) => (l2, r2),
        }
    }

    /// Return left value or default value.
    #[quither(has_either || has_both)]
    pub fn left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[both]
            Self::Both(l, _) => l,
            #[allow(unused)]
            _ => L::default(),
        }
    }

    /// Return right value or default value.
    #[quither(has_either || has_both)]
    pub fn right_or_default(self) -> R
    where
        R: Default,
    {
        match self {
            #[either]
            Self::Right(r) => r,
            #[both]
            Self::Both(_, r) => r,
            #[allow(unused)]
            _ => R::default(),
        }
    }

    /// Return a tuple of both values, or the default values if either side is missing.
    #[quither(has_either || has_both)]
    pub fn both_or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            #[either]
            Self::Left(l) => (l, R::default()),
            #[either]
            Self::Right(r) => (L::default(), r),
            #[neither]
            Self::Neither => (L::default(), R::default()),
            #[both]
            Self::Both(l, r) => (l, r),
        }
    }

    /// Return left value or computes it from a closure.
    #[quither(has_either || has_both)]
    pub fn left_or_else<F>(self, #[allow(unused)] f: F) -> L
    where
        F: FnOnce() -> L,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(_) => f(),
            #[neither]
            Self::Neither => f(),
            #[both]
            Self::Both(l, _) => l,
        }
    }

    /// Return right value or computes it from a closure.
    #[quither(has_either || has_both)]
    pub fn right_or_else<F>(self, #[allow(unused)] f: F) -> R
    where
        F: FnOnce() -> R,
    {
        match self {
            #[either]
            Self::Left(_) => f(),
            #[either]
            Self::Right(r) => r,
            #[neither]
            Self::Neither => f(),
            #[both]
            Self::Both(_, r) => r,
        }
    }

    #[quither(has_either || has_both)]
    pub fn both_or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
    where
        F: FnOnce() -> L,
        G: FnOnce() -> R,
    {
        match self {
            #[either]
            Self::Left(l) => (l, g()),
            #[either]
            Self::Right(r) => (f(), r),
            #[neither]
            Self::Neither => (f(), g()),
            #[both]
            Self::Both(l, r) => (l, r),
        }
    }

    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    #[quither(has_either || has_both)]
    pub fn left_and_then<F, L2>(self, f: F) -> Quither<L2, R>
    where
        F: FnOnce(L) -> Quither<L2, R>,
    {
        match self {
            #[either]
            Self::Left(l) => f(l),
            #[either]
            Self::Right(r) => Quither::Right(r),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, _) => f(l),
        }
    }

    /// Apply the function `f` on the value in the right position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    #[quither(has_either || has_both)]
    pub fn right_and_then<F, R2>(self, f: F) -> Quither<L, R2>
    where
        F: FnOnce(R) -> Quither<L, R2>,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l),
            #[either]
            Self::Right(r) => f(r),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(_, r) => f(r),
        }
    }
}

/// `Either` type exclusive methods.
impl<L, R> Either<L, R> {
    pub fn either<F, G, T>(self, f: F, g: G) -> T
    where
        F: FnOnce(L) -> T,
        G: FnOnce(R) -> T,
    {
        match self {
            Either::Left(l) => f(l),
            Either::Right(r) => g(r),
        }
    }

    pub fn either_with<Ctx, F, G, T>(self, ctx: Ctx, f: F, g: G) -> T
    where
        F: FnOnce(Ctx, L) -> T,
        G: FnOnce(Ctx, R) -> T,
    {
        match self {
            Either::Left(l) => f(ctx, l),
            Either::Right(r) => g(ctx, r),
        }
    }
}

/// `EitherOrBoth` type exclusive methods.
impl<L, R> EitherOrBoth<L, R> {
    /// An alias for `EitherOrBoth::both_or`. For compatibility with `itertools::EitherOrBoth` type.
    pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
        self.both_or(l, r)
    }

    /// An alias for `EitherOrBoth::both_or_default`. For compatibility with `itertools::EitherOrBoth` type.
    pub fn or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        self.both_or_default()
    }

    /// An alias for `EitherOrBoth::both_or_else`. For compatibility with `itertools::EitherOrBoth` type.
    pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
    where
        F: FnOnce() -> L,
        G: FnOnce() -> R,
    {
        self.both_or_else(f, g)
    }
}
