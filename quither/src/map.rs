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
    /// Applies separate functions to each variant, transforming both sides.
    ///
    /// For types with `Either` or `Both` variants, applies `f` to the left value and `g` to the right
    /// value, returning a new pair type with the results. If `Both` is present, both functions are
    /// applied. If `Neither` is present, returns `Neither`.
    #[quither(has_either || has_both)]
    pub fn map2<F, G, L2, R2>(self, f: F, g: G) -> Quither<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(f(l)),
            #[either]
            Self::Right(r) => Quither::Right(g(r)),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(f(l), g(r)),
        }
    }

    /// Applies a function to the left value, leaving the right unchanged.
    ///
    /// For types with `Either` or `Both` variants, applies `f` to the left value. The right value is
    /// unchanged. If `Both` is present, only the left value is transformed. If `Neither` is present,
    /// returns `Neither`.
    #[quither(has_either || has_both)]
    pub fn map_left<F, L2>(self, f: F) -> Quither<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(f(l)),
            #[either]
            Self::Right(r) => Quither::Right(r),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(f(l), r),
        }
    }

    /// Applies a function to the right value, leaving the left unchanged.
    ///
    /// For types with `Either` or `Both` variants, applies `f` to the right value. The left value is
    /// unchanged. If `Both` is present, only the right value is transformed. If `Neither` is present,
    /// returns `Neither`.
    #[quither(has_either || has_both)]
    pub fn map_right<F, R2>(self, f: F) -> Quither<L, R2>
    where
        F: FnOnce(R) -> R2,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l),
            #[either]
            Self::Right(r) => Quither::Right(f(r)),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(l, f(r)),
        }
    }

    /// Applies functions to each variant with a shared context, for types without `Both`.
    ///
    /// For types with `Either` but not `Both`, applies `f` to the left value and `g` to the right value,
    /// both with the provided context. Returns a new pair type with the results. If `Neither` is
    /// present, returns `Neither`.
    #[quither(has_either && !has_both)]
    pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> Quither<L2, R2>
    where
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(f(ctx, l)),
            #[either]
            Self::Right(r) => Quither::Right(g(ctx, r)),
            #[neither]
            Self::Neither => Quither::Neither,
        }
    }

    /// Applies functions to each variant with a shared, clonable context, for types with `Both`.
    ///
    /// For types with `Either` and `Both`, applies `f` to the left value and `g` to the right value,
    /// both with a cloned context. If `Both` is present, both functions are applied with cloned
    /// contexts. If `Neither` is present, returns `Neither`.
    #[quither(has_either && has_both)]
    pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> Quither<L2, R2>
    where
        Ctx: Clone,
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(f(ctx, l)),
            #[either]
            Self::Right(r) => Quither::Right(g(ctx, r)),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(f(ctx.clone(), l), g(ctx.clone(), r)),
        }
    }
}

#[quither]
impl<T> Quither<T, T> {
    /// Applies a function to both values, for types with identical left and right types, without `Both`.
    ///
    /// For types with `Either` but not `Both`, applies `f` to both values. If `Neither` is present,
    /// returns `Neither`.
    #[quither(has_either && !has_both)]
    pub fn map<F, T2>(self, f: F) -> Quither<T2, T2>
    where
        F: FnOnce(T) -> T2,
    {
        match self {
            #[either]
            Quither::Left(l) => Quither::Left(f(l)),
            #[either]
            Quither::Right(r) => Quither::Right(f(r)),
            #[neither]
            Quither::Neither => Quither::Neither,
        }
    }

    /// Applies a function to both values, for types with identical left and right types, with `Both`.
    ///
    /// For types with `Either` and `Both`, applies `f` to both values. If `Both` is present, both values
    /// are transformed. If `Neither` is present, returns `Neither`.
    #[quither(has_either && has_both)]
    pub fn map<F, T2>(self, f: F) -> Quither<T2, T2>
    where
        F: Fn(T) -> T2,
    {
        match self {
            #[either]
            Quither::Left(l) => Quither::Left(f(l)),
            #[either]
            Quither::Right(r) => Quither::Right(f(r)),
            #[neither]
            Quither::Neither => Quither::Neither,
            #[both]
            Quither::Both(l, r) => Quither::Both(f(l), f(r)),
        }
    }
}

/// `Either` type exclusive methods.
impl<L, R> Either<L, R> {
    /// Applies separate functions to each variant, as an alias for `map2`.
    ///
    /// For compatibility with `itertools`-style APIs. Applies `f` to the left value and `g` to the
    /// right value, returning a new pair type with the results.
    pub fn map_either<F, G, L2, R2>(self, f: F, g: G) -> Either<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        Self::map2(self, f, g)
    }

    /// Applies functions to each variant with a shared context, as an alias for `map_with`.
    ///
    /// For compatibility with `itertools`-style APIs. Applies `f` to the left value and `g` to the
    /// right value, both with the provided context.
    pub fn map_either_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> Either<L2, R2>
    where
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        Self::map_with(self, ctx, f, g)
    }
}

/// `EitherOrBoth` type exclusive methods.
impl<L, R> EitherOrBoth<L, R> {
    /// Applies separate functions to each variant, as an alias for `map2`.
    ///
    /// For compatibility with `itertools`-style APIs. Applies `f` to the left value and `g` to the
    /// right value, returning a new pair type with the results.
    pub fn map_any<F, L2, G, R2>(self, f: F, g: G) -> EitherOrBoth<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        self.map2(f, g)
    }
}
