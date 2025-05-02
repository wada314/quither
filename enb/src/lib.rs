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

use ::replace_with::replace_with_or_abort;
use ::std::fmt::Debug;
use ::std::ops::{Deref, DerefMut};
use ::std::pin::Pin;

use ::enb_proc_macros::enb;

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
pub enum EitherOrNeitherOrBoth<L, R> {
    Neither,
    Left(L),
    Right(R),
    Both(L, R),
}

#[enb]
impl<L, R> Enb<L, R> {
    pub fn has_left(&self) -> bool {
        match self {
            #[either]
            Self::Left(_) => true,
            #[both]
            Self::Both(_, _) => true,
            #[allow(unused)]
            _ => false,
        }
    }

    pub fn has_right(&self) -> bool {
        match self {
            #[either]
            Self::Right(_) => true,
            #[both]
            Self::Both(_, _) => true,
            #[allow(unused)]
            _ => false,
        }
    }

    pub fn is_left(&self) -> bool {
        match self {
            #[either]
            Self::Left(_) => true,
            #[allow(unused)]
            _ => false,
        }
    }

    pub fn is_right(&self) -> bool {
        match self {
            #[either]
            Self::Right(_) => true,
            #[allow(unused)]
            _ => false,
        }
    }

    pub fn is_neither(&self) -> bool {
        match self {
            #[neither]
            Self::Neither => true,
            #[allow(unused)]
            _ => false,
        }
    }

    pub fn is_both(&self) -> bool {
        match self {
            #[both]
            Self::Both(_, _) => true,
            #[allow(unused)]
            _ => false,
        }
    }

    /// Convert the left side of the variant into an `Option`.
    /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
    #[enb(has_either || has_both)]
    pub fn left(self) -> Option<L> {
        match self {
            #[either]
            Self::Left(l) => Some(l),
            #[both]
            Self::Both(l, _) => Some(l),
            #[allow(unused)]
            _ => None,
        }
    }

    /// Convert the right side of the variant into an `Option`.
    /// i.e. `Left(_)` -> `None`, `Right(r)` -> `Some(r)`, `Both(_, r)` -> `Some(r)`.
    #[enb(has_either || has_both)]
    pub fn right(self) -> Option<R> {
        match self {
            #[either]
            Self::Right(r) => Some(r),
            #[both]
            Self::Both(_, r) => Some(r),
            #[allow(unused)]
            _ => None,
        }
    }

    #[enb(has_either || has_both)]
    pub fn left_and_right(self) -> (Option<L>, Option<R>) {
        match self {
            #[either]
            Self::Left(l) => (Some(l), None),
            #[either]
            Self::Right(r) => (None, Some(r)),
            #[neither]
            Self::Neither => (None, None),
            #[both]
            Self::Both(l, r) => (Some(l), Some(r)),
        }
    }

    /// If the variant is a `Left` variant, return the left value.
    /// Otherwise (even the variant is a `Both` variant), return `None`.
    #[enb(has_either || has_both)]
    pub fn just_left(self) -> Option<L> {
        match self {
            #[either]
            Self::Left(l) => Some(l),
            #[allow(unused)]
            _ => None,
        }
    }

    /// If the variant is a `Right` variant, return the right value.
    /// Otherwise (even the variant is a `Both` variant), return `None`.
    #[enb(has_either || has_both)]
    pub fn just_right(self) -> Option<R> {
        match self {
            #[either]
            Self::Right(r) => Some(r),
            #[allow(unused)]
            _ => None,
        }
    }

    #[enb(has_either || has_both)]
    pub fn both(self) -> Option<(L, R)> {
        match self {
            #[both]
            Self::Both(l, r) => Some((l, r)),
            #[allow(unused)]
            _ => None,
        }
    }

    pub fn flip(self) -> Enb<R, L> {
        match self {
            #[either]
            Self::Left(l) => Enb::Right(l),
            #[either]
            Self::Right(r) => Enb::Left(r),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(r, l),
        }
    }

    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    #[enb(has_either || has_both)]
    pub fn unwrap_left(self) -> L
    where
        R: Debug,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(r) => panic!("Expected a Left value, but got a right variant:{:?}", r),
            #[neither]
            Self::Neither => panic!("Expected a Left value, but got a Neither variant"),
            #[both]
            Self::Both(l, _) => l,
        }
    }

    /// Unwrap the right value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a right value.
    #[enb(has_either || has_both)]
    pub fn unwrap_right(self) -> R
    where
        L: Debug,
    {
        match self {
            #[either]
            Self::Left(l) => panic!("Expected a Right value, but got a left variant:{:?}", l),
            #[either]
            Self::Right(r) => r,
            #[neither]
            Self::Neither => panic!("Expected a Right value, but got a Neither variant"),
            #[both]
            Self::Both(_, r) => r,
        }
    }

    #[enb(has_either || has_both)]
    pub fn unwrap_both(self) -> (L, R)
    where
        L: Debug,
        R: Debug,
    {
        match self {
            #[either]
            Self::Left(l) => panic!("Expected a Both value, but got a left variant:{:?}", l),
            #[either]
            Self::Right(r) => panic!("Expected a Both value, but got a right variant:{:?}", r),
            #[neither]
            Self::Neither => panic!("Expected a Both value, but got a Neither variant"),
            #[both]
            Self::Both(l, r) => (l, r),
        }
    }

    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    #[enb(has_either || has_both)]
    pub fn expect_left(self, #[allow(unused)] msg: &str) -> L
    where
        R: Debug,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[either]
            Self::Right(r) => panic!("{}: {:?}", msg, r),
            #[neither]
            Self::Neither => panic!("{}", msg),
            #[both]
            Self::Both(l, _) => l,
        }
    }

    /// Unwrap the right value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a right value.
    #[enb(has_either || has_both)]
    pub fn expect_right(self, #[allow(unused)] msg: &str) -> R
    where
        L: Debug,
    {
        match self {
            #[either]
            Self::Left(l) => panic!("{}: {:?}", msg, l),
            #[either]
            Self::Right(r) => r,
            #[neither]
            Self::Neither => panic!("{}", msg),
            #[both]
            Self::Both(_, r) => r,
        }
    }

    #[enb(has_either || has_both)]
    pub fn expect_both(self, #[allow(unused)] msg: &str) -> (L, R)
    where
        L: Debug,
        R: Debug,
    {
        match self {
            #[either]
            Self::Left(l) => panic!("{}: {:?}", msg, l),
            #[either]
            Self::Right(r) => panic!("{}: {:?}", msg, r),
            #[neither]
            Self::Neither => panic!("{}", msg),
            #[both]
            Self::Both(l, r) => (l, r),
        }
    }

    /// Return left value or given value.
    #[enb(has_either || has_both)]
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
    #[enb(has_either || has_both)]
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
    #[enb(has_either || has_both)]
    pub fn both_or(self, #[allow(unused)] other: (L, R)) -> (L, R) {
        match self {
            #[either]
            Self::Left(l) => (l, other.1),
            #[either]
            Self::Right(r) => (other.0, r),
            #[neither]
            Self::Neither => other,
            #[both]
            Self::Both(l, r) => (l, r),
        }
    }

    /// Return left value or default value.
    #[enb(has_either || has_both)]
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
    #[enb(has_either || has_both)]
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
    #[enb(has_either || has_both)]
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
    #[enb(has_either || has_both)]
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
    #[enb(has_either || has_both)]
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

    #[enb(has_either || has_both)]
    pub fn map<F, G, L2, R2>(self, f: F, g: G) -> Enb<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(f(l)),
            #[either]
            Self::Right(r) => Enb::Right(g(r)),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(f(l), g(r)),
        }
    }

    #[enb(has_either || has_both)]
    pub fn map_left<F, L2>(self, f: F) -> Enb<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(f(l)),
            #[either]
            Self::Right(r) => Enb::Right(r),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(f(l), r),
        }
    }

    #[enb(has_either || has_both)]
    pub fn map_right<F, R2>(self, f: F) -> Enb<L, R2>
    where
        F: FnOnce(R) -> R2,
    {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(l),
            #[either]
            Self::Right(r) => Enb::Right(f(r)),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(l, f(r)),
        }
    }

    /// Creates a new variant with references to the contained values.
    #[enb(has_either || has_neither || has_both)]
    pub fn as_ref(&self) -> Enb<&L, &R> {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(l),
            #[either]
            Self::Right(r) => Enb::Right(r),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(l, r),
        }
    }

    /// Creates a new variant with mutable references to the contained values.
    #[enb(has_either || has_neither || has_both)]
    pub fn as_mut(&mut self) -> Enb<&mut L, &mut R> {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(l),
            #[either]
            Self::Right(r) => Enb::Right(r),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(l, r),
        }
    }

    /// Creates a new pinned variant with references to the contained values.
    #[enb(has_either || has_neither || has_both)]
    pub fn as_pin_ref(self: Pin<&Self>) -> Enb<Pin<&L>, Pin<&R>> {
        // SAFETY: This is safe because:
        // 1. We never move the inner values - we only create a new reference to them
        // 2. The original Pin<&Self> guarantees that the original data won't move
        // 3. We're maintaining the pinning invariant by wrapping the references in Pin
        // 4. The lifetime of the output references is tied to the input lifetime
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                #[either]
                Self::Left(l) => Enb::Left(Pin::new_unchecked(l)),
                #[either]
                Self::Right(r) => Enb::Right(Pin::new_unchecked(r)),
                #[neither]
                Self::Neither => Enb::Neither,
                #[both]
                Self::Both(l, r) => Enb::Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }

    /// Creates a new pinned variant with mutable references to the contained values.
    #[enb(has_either || has_neither || has_both)]
    pub fn as_pin_mut(self: Pin<&mut Self>) -> Enb<Pin<&mut L>, Pin<&mut R>> {
        // SAFETY: This is safe because:
        // 1. We never move the inner values out of the pin
        // 2. We're creating new Pin instances from references to pinned data
        // 3. The original Pin<&mut Self> guarantees unique access
        // 4. We maintain the pinning invariant by wrapping the mutable references in Pin
        // 5. get_unchecked_mut is safe here as we have exclusive access via Pin<&mut Self>
        unsafe {
            match self.get_unchecked_mut() {
                #[either]
                Self::Left(l) => Enb::Left(Pin::new_unchecked(l)),
                #[either]
                Self::Right(r) => Enb::Right(Pin::new_unchecked(r)),
                #[neither]
                Self::Neither => Enb::Neither,
                #[both]
                Self::Both(l, r) => Enb::Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }

    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    #[enb(has_either || has_both)]
    pub fn as_deref(&self) -> Enb<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(l.deref()),
            #[either]
            Self::Right(r) => Enb::Right(r.deref()),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(l.deref(), r.deref()),
        }
    }

    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    #[enb(has_either || has_both)]
    pub fn as_deref_mut(&mut self) -> Enb<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(l.deref_mut()),
            #[either]
            Self::Right(r) => Enb::Right(r.deref_mut()),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(l.deref_mut(), r.deref_mut()),
        }
    }

    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    #[enb(has_either || has_both)]
    pub fn left_and_then<F, L2>(self, f: F) -> Enb<L2, R>
    where
        F: FnOnce(L) -> Enb<L2, R>,
    {
        match self {
            #[either]
            Self::Left(l) => f(l),
            #[either]
            Self::Right(r) => Enb::Right(r),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, _) => f(l),
        }
    }

    /// Apply the function `f` on the value in the right position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    #[enb(has_either || has_both)]
    pub fn right_and_then<F, R2>(self, f: F) -> Enb<L, R2>
    where
        F: FnOnce(R) -> Enb<L, R2>,
    {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(l),
            #[either]
            Self::Right(r) => f(r),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(_, r) => f(r),
        }
    }

    #[enb(has_either || has_both)]
    pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
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

    #[enb(has_either || has_both)]
    pub fn or_default(self) -> (L, R)
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

    #[enb(has_either || has_both)]
    pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
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

    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can "promote" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given value and return it.
    #[enb(!has_neither || has_either)]
    // ↑ means: (has_neither => has_either).
    // This is needed to do the variant promotion when inserting the left value into `Neither` variant.
    pub fn ensure_left(&mut self, l: L) -> &mut L {
        self.ensure_left_with(move || l)
    }

    /// Ensure the left value is present. If possible, keep the right value too.
    ///
    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can \"promote\" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given closure's return value and return it.
    #[enb(!has_neither || has_either)]
    pub fn ensure_left_with<F>(&mut self, #[allow(unused)] f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            #[either]
            Self::Left(l) => l,
            #[enb(has_either && has_both)]
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
            #[enb(has_either && !has_both)]
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

    #[enb(!has_neither)]
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

    #[enb(!has_neither)]
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

    #[enb(has_either && !has_both)]
    pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> Enb<L2, R2>
    where
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(f(ctx, l)),
            #[either]
            Self::Right(r) => Enb::Right(g(ctx, r)),
            #[neither]
            Self::Neither => Enb::Neither,
        }
    }

    #[enb(has_either && has_both)]
    pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> Enb<L2, R2>
    where
        Ctx: Clone,
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        match self {
            #[either]
            Self::Left(l) => Enb::Left(f(ctx, l)),
            #[either]
            Self::Right(r) => Enb::Right(g(ctx, r)),
            #[neither]
            Self::Neither => Enb::Neither,
            #[both]
            Self::Both(l, r) => Enb::Both(f(ctx.clone(), l), g(ctx.clone(), r)),
        }
    }
}

#[enb]
impl<L, R> Enb<Option<L>, Option<R>> {
    #[enb(!has_neither && (has_either || has_both))]
    pub fn factor_none(self) -> Option<Enb<L, R, true, false, has_both>> {
        match self {
            #[either]
            Self::Left(Some(l)) => Some(Enb::<L, R, true, false, has_both>::Left(l)),
            #[either]
            Self::Left(None) => None,
            #[either]
            Self::Right(Some(r)) => Some(Enb::<L, R, true, false, has_both>::Right(r)),
            #[either]
            Self::Right(None) => None,
            #[both]
            Self::Both(Some(l), Some(r)) => Some(Enb::<L, R, true, false, has_both>::Both(l, r)),
            #[both]
            Self::Both(Some(l), None) => Some(Enb::<L, R, true, false, has_both>::Left(l)),
            #[both]
            Self::Both(None, Some(r)) => Some(Enb::<L, R, true, false, has_both>::Right(r)),
            #[both]
            Self::Both(None, None) => None,
        }
    }
}

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

    pub fn map_either<F, G, L2, R2>(self, f: F, g: G) -> Either<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        Self::map(self, f, g)
    }

    pub fn map_either_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> Either<L2, R2>
    where
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        Self::map_with(self, ctx, f, g)
    }
}
