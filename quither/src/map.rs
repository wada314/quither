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
