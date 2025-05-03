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

//! "Quad-state Either": Quither. In other words, either-or-neither-or-both type.
//!
//! Quither is a type that represents four states:
//! - `Left(L)`
//! - `Right(R)`
//! - `Both(L, R)`
//! - `Neither`
//!
//! This crate also provides an arbitrary combination types of `Either`, `Neither`, and `Both`.
//! For example, `EitherOrBoth<L, R>` is a type that represents either a left (`Left(L)`) or right (`Right(R)`) or both (`Both(L, R)`).
//! These types have consistent APIs (as much as possible ☺) so that you can use them interchangeably.
//!
//! Each combination types implements the common methods greedily, even if it's not very useful for that type itself.
//! For example, `EitherOrNeither` type implements `is_both()` method, even if it always returns `false`.
//!

#![cfg_attr(not(feature = "use_std"), no_std)]

mod and_or_getters;
mod as_ref;
mod getters;

use ::quither_proc_macros::quither;
use ::replace_with::replace_with_or_abort;

// Pair types, essentially comibinations of `Either`, `Neither`, and `Both`.

/// An enum that represents either a left (`Left(L)`) or right (`Right(R)`) value.
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// An enum that represents a single `Neither` value.
pub enum Neither {
    Neither,
}

/// An enum that represents a pair of values (`Both(L, R)`).
pub enum Both<L, R> {
    Both(L, R),
}

/// An enum that represents either a left (`Left(L)`) or right (`Right(R)`) or neither (`Neither`).
pub enum EitherOrNeither<L, R> {
    Neither,
    Left(L),
    Right(R),
}

/// An enum that represents either a left (`Left(L)`) or right (`Right(R)`) or both (`Both(L, R)`).
pub enum EitherOrBoth<L, R> {
    Left(L),
    Right(R),
    Both(L, R),
}

/// An enum that represents a single `Neither` value or a pair of values (`Both(L, R)`).
pub enum NeitherOrBoth<L, R> {
    Neither,
    Both(L, R),
}

/// An enum that represents either an empty value, left value, right value, or both values.
pub enum Quither<L, R> {
    Neither,
    Left(L),
    Right(R),
    Both(L, R),
}

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

    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can "promote" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given value and return it.
    #[quither(!has_neither || has_either)]
    // ↑ means: (has_neither => has_either).
    // This is needed to do the variant promotion when inserting the left value into `Neither` variant.
    pub fn ensure_left(&mut self, l: L) -> &mut L {
        self.ensure_left_with(move || l)
    }

    #[quither(!has_neither || has_either)]
    pub fn ensure_right(&mut self, r: R) -> &mut R {
        self.ensure_right_with(move || r)
    }

    /// Ensure the left value is present. If possible, keep the right value too.
    ///
    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can \"promote\" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given closure's return value and return it.
    #[quither(!has_neither || has_either)]
    pub fn ensure_left_with<F>(&mut self, #[allow(unused)] f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[quither(has_either && has_both)]
            Self::Right(_) => {
                // Right => Both promotion.
                let new_l = f();
                replace_with_or_abort(self, move |this| {
                    let Self::Right(r) = this else { unreachable!() };
                    Self::Both(new_l, r)
                });
                let Self::Both(l, _) = self else {
                    unreachable!()
                };
                l
            }
            #[quither(has_either && !has_both)]
            Self::Right(_) => {
                // No promotion.
                *self = Self::Left(f());
                let Self::Left(l) = self else { unreachable!() };
                l
            }
            #[neither]
            Self::Neither => {
                // Neither => Left promotion.
                let new_l = f();
                replace_with_or_abort(self, move |this| {
                    let Self::Neither = this else { unreachable!() };
                    Self::Left(new_l)
                });
                let Self::Left(l) = self else { unreachable!() };
                l
            }
            #[both]
            Self::Both(l, _) => l,
        }
    }

    #[quither(!has_neither || has_either)]
    pub fn ensure_right_with<F>(&mut self, #[allow(unused)] f: F) -> &mut R
    where
        F: FnOnce() -> R,
    {
        match self {
            #[quither(has_either && has_both)]
            Self::Left(_) => {
                // Left => Both promotion.
                let new_r = f();
                replace_with_or_abort(self, move |this| {
                    let Self::Left(l) = this else { unreachable!() };
                    Self::Both(l, new_r)
                });
                let Self::Both(_, r) = self else {
                    unreachable!()
                };
                r
            }
            #[quither(has_either && !has_both)]
            Self::Left(_) => {
                // No promotion.
                *self = Self::Right(f());
                let Self::Right(r) = self else { unreachable!() };
                r
            }
            #[either]
            Self::Right(r) => r,
            #[neither]
            Self::Neither => {
                // Neither => Right promotion.
                let new_r = f();
                replace_with_or_abort(self, move |this| {
                    let Self::Neither = this else { unreachable!() };
                    Self::Right(new_r)
                });
                let Self::Right(r) = self else { unreachable!() };
                r
            }
            #[both]
            Self::Both(_, r) => r,
        }
    }

    #[quither(!has_neither)]
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

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn left_or_insert(&mut self, l: L) -> &mut L {
        self.left_or_insert_with(move || l)
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn right_or_insert(&mut self, r: R) -> &mut R {
        self.right_or_insert_with(move || r)
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    // ↑ means: (has_neither -> has_either) && (has_either -> has_both)
    pub fn left_or_insert_with<F>(&mut self, #[allow(unused)] f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(_) => {
                // Right => Both promotion. It is guaranteed that the `Both` variant is present
                // because of the method's attribute.
                replace_with_or_abort(self, move |this| {
                    let Self::Right(r) = this else { unreachable!() };
                    Self::Both(f(), r)
                });
                let Self::Both(l, _) = self else {
                    unreachable!()
                };
                l
            }
            #[neither]
            Self::Neither => {
                // Neither => Left promotion. It is guaranteed that the `Left` variant is present
                // because of the method's attribute.
                replace_with_or_abort(self, move |this| {
                    let Self::Neither = this else { unreachable!() };
                    Self::Left(f())
                });
                let Self::Left(l) = self else { unreachable!() };
                l
            }
            #[both]
            Self::Both(l, _) => l,
        }
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn right_or_insert_with<F>(&mut self, #[allow(unused)] f: F) -> &mut R
    where
        F: FnOnce() -> R,
    {
        match self {
            #[either]
            Self::Right(r) => r,
            #[either]
            Self::Left(_) => {
                // Left => Both promotion. It is guaranteed that the `Both` variant is present
                // because of the method's attribute.
                replace_with_or_abort(self, move |this| {
                    let Self::Left(l) = this else { unreachable!() };
                    Self::Both(l, f())
                });
                let Self::Both(_, r) = self else {
                    unreachable!()
                };
                r
            }
            #[neither]
            Self::Neither => {
                // Neither => Right promotion. It is guaranteed that the `Right` variant is present
                // because of the method's attribute.
                replace_with_or_abort(self, move |this| {
                    let Self::Neither = this else { unreachable!() };
                    Self::Right(f())
                });
                let Self::Right(r) = self else { unreachable!() };
                r
            }
            #[both]
            Self::Both(_, r) => r,
        }
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn insert_left(&mut self, #[allow(unused)] l: L) -> &mut L {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(_) => {
                replace_with_or_abort(self, move |this| {
                    let Self::Right(r) = this else { unreachable!() };
                    Self::Both(l, r)
                });
                let Self::Both(l, _) = self else {
                    unreachable!()
                };
                l
            }
            #[neither]
            Self::Neither => {
                replace_with_or_abort(self, move |_| Self::Left(l));
                let Self::Left(l) = self else { unreachable!() };
                l
            }
            #[both]
            Self::Both(l, _) => l,
        }
    }

    #[quither((!has_neither || has_either) && (!has_either || has_both))]
    pub fn insert_right(&mut self, #[allow(unused)] r: R) -> &mut R {
        match self {
            #[either]
            Self::Right(r) => r,
            #[either]
            Self::Left(_) => {
                replace_with_or_abort(self, move |this| {
                    let Self::Left(l) = this else { unreachable!() };
                    Self::Both(l, r)
                });
                let Self::Both(_, r) = self else {
                    unreachable!()
                };
                r
            }
            #[neither]
            Self::Neither => {
                replace_with_or_abort(self, move |_| Self::Right(r));
                let Self::Right(r) = self else { unreachable!() };
                r
            }
            #[both]
            Self::Both(_, r) => r,
        }
    }

    #[quither(has_both)]
    pub fn insert_both(
        &mut self,
        #[allow(unused)] l: L,
        #[allow(unused)] r: R,
    ) -> (&mut L, &mut R) {
        match self {
            #[either]
            Self::Left(_) => {
                replace_with_or_abort(self, move |this| {
                    let Self::Left(l) = this else { unreachable!() };
                    Self::Both(l, r)
                });
            }
            #[either]
            Self::Right(_) => {
                replace_with_or_abort(self, move |this| {
                    let Self::Right(r) = this else { unreachable!() };
                    Self::Both(l, r)
                });
            }
            #[neither]
            Self::Neither => {
                *self = Self::Both(l, r);
            }
            #[both]
            Self::Both(_, _) => (),
        };
        #[allow(irrefutable_let_patterns)]
        let Self::Both(l, r) = self else {
            unreachable!()
        };
        (l, r)
    }

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
    /// This method is only available in the type which is NOT containing `Neither` variant.
    /// (This is because I'm not sure whether I should return `None` or `Some(Neither)`).
    ///
    /// Note that for some types, this method returns a different type from the input type.
    /// For example, `Both` type's this method returns `EitherOrBoth` type.
    ///
    /// TODO: Needs examples.
    #[quither(!has_neither && (has_either || has_both))]
    pub fn factor_none(self) -> Option<Quither<L, R, true, false, has_both>> {
        match self {
            #[either]
            Self::Left(Some(l)) => Some(Quither::<L, R, true, false, has_both>::Left(l)),
            #[either]
            Self::Right(Some(r)) => Some(Quither::<L, R, true, false, has_both>::Right(r)),
            #[both]
            Self::Both(Some(l), Some(r)) => {
                Some(Quither::<L, R, true, false, has_both>::Both(l, r))
            }
            #[both]
            Self::Both(Some(l), None) => Some(Quither::<L, R, true, false, has_both>::Left(l)),
            #[both]
            Self::Both(None, Some(r)) => Some(Quither::<L, R, true, false, has_both>::Right(r)),
            #[quither(has_either || has_both)]
            _ => None,
        }
    }
}

#[quither]
impl<T> Quither<T, T> {
    /// Map the value of the type.
    ///
    /// Note for the type including the `Both` variant, the parameter closure
    /// `F` is called twice, so it is not `FnOnce` but `Fn`.
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

    /// Map the value of the type.
    ///
    /// Note for the type including the `Both` variant, the parameter closure
    /// `F` is called twice, so it is not `FnOnce` but `Fn`.
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

    /// An alias for `Either::map`. For compatibility with `itertools::Either` type.
    pub fn map_either<F, G, L2, R2>(self, f: F, g: G) -> Either<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        Self::map2(self, f, g)
    }

    /// An alias for `Either::map_with`. For compatibility with `itertools::Either` type.
    pub fn map_either_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> Either<L2, R2>
    where
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        Self::map_with(self, ctx, f, g)
    }
}

impl<T> Either<T, T> {
    pub fn into_inner(self) -> T {
        match self {
            Either::Left(l) => l,
            Either::Right(r) => r,
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

/// `EitherOrBoth` type exclusive methods.
impl<L, R> EitherOrBoth<L, R> {
    /// An alias for `EitherOrBoth::map`. For compatibility with `itertools::EitherOrBoth` type.
    pub fn map_any<F, L2, G, R2>(self, f: F, g: G) -> EitherOrBoth<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        self.map2(f, g)
    }

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
