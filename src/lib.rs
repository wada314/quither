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

use ::std::fmt::Debug;
use ::std::ops::{Deref, DerefMut};
use ::std::pin::Pin;

#[macro_use]
mod macros;

pub enum Either<A, B> {
    Left(A),
    Right(B),
}

pub enum Both<A, B> {
    Both(A, B),
}

pub enum EitherOrNeither<A, B> {
    Left(A),
    Right(B),
    Neither,
}

pub enum EitherOrBoth<A, B> {
    Left(A),
    Right(B),
    Both(A, B),
}

pub enum NeitherOrBoth<A, B> {
    Neither,
    Both(A, B),
}

pub enum EitherOrNeitherOrBoth<A, B> {
    Left(A),
    Right(B),
    Neither,
    Both(A, B),
}

/// impl left / right getters
macro_rules! impl_left_right_getters {
    ($name:ident, false, false, true) => { /* skip for `Both` type. */};
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        impl<L, R> $name<L, R> {
            /// Return `true` if the variant *contains* a left value.
            /// i.e. `Left(l)` or `Both(l, _)`.
            pub fn is_left(&self) -> bool {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(_) => true,
                    @either => $name::Right(_) => false,
                    @neither => $name::Neither => false,
                    @both => $name::Both(_, _) => true,
                })
            }

            /// Return `true` if the variant *contains* a right value.
            /// i.e. `Right(r)` or `Both(_, r)`.
            pub fn is_right(&self) -> bool {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(_) => false,
                    @either => $name::Right(_) => true,
                    @neither => $name::Neither => false,
                    @both => $name::Both(_, _) => true,
                })
            }

            /// Convert the left side of the variant into an `Option`.
            /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
            pub fn left(self) -> Option<L> {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => Some(l),
                    @either => $name::Right(_) => None,
                    @neither => $name::Neither => None,
                    @both => $name::Both(l, _) => Some(l),
                })
            }

            /// Returns a tuple of the optional left and right values.
            pub fn left_and_right(self) -> (Option<L>, Option<R>) {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => (Some(l), None),
                    @either => $name::Right(r) => (None, Some(r)),
                    @neither => $name::Neither => (None, None),
                    @both => $name::Both(l, r) => (Some(l), Some(r)),
                })
            }

            /// Unwrap the left value from the variant.
            ///
            /// # Panics
            ///
            /// - If the variant is something not containing a left value.
            pub fn unwrap_left(self) -> L where R: Debug {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => l,
                    @either => $name::Right(r) => panic!("Expected a Left variant, but got a right value:{:?}", r),
                    @neither => $name::Neither => panic!("Expected a Left variant, but got a Neither variant"),
                    @both => $name::Both(l, _) => l,
                })
            }

            /// Unwrap the left value from the variant.
            ///
            /// # Panics
            ///
            /// - If the variant is something not containing a left value.
            pub fn expect_left(self, msg: &str) -> L where R: Debug {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => l,
                    @either => $name::Right(r) => panic!("{}: {:?}", msg, r),
                    @neither => $name::Neither => panic!("{}", msg),
                    @both => $name::Both(l, _) => l,
                })
            }
        }
    };
}

// impl for 'or' and 'and' operations.
macro_rules! impl_and_or_methods {
    ($name:ident, false, false, true) => { /* skip for `Both` type. */};
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        impl<L, R> $name<L, R> {
            /// Apply the function `f` on the value in the left position if it is present,
            /// and then rewrap the result in a same variant of the new type.
            pub fn left_and_then<F, L2>(self, f: F) -> $name<L2, R>
            where
                F: FnOnce(L) -> $name<L2, R>,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => f(l),
                    @either => $name::Right(r) => $name::Right(r),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, _) => f(l),
                })
            }

            pub fn or(self, l: L, r: R) -> (L, R) {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l2) => (l2, r),
                    @either => $name::Right(r2) => (l, r2),
                    @neither => $name::Neither => (l, r),
                    @both => $name::Both(l2, r2) => (l2, r2),
                })
            }

            pub fn or_default(self) -> (L, R) where L: Default, R: Default {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => (l, R::default()),
                    @either => $name::Right(r) => (L::default(), r),
                    @neither => $name::Neither => (L::default(), R::default()),
                    @both => $name::Both(l, r) => (l, r),
                })
            }

            pub fn or_else<F, G>(self, f: F, g: G) -> (L, R)
            where
                F: FnOnce() -> L,
                G: FnOnce() -> R,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => (l, g()),
                    @either => $name::Right(r) => (f(), r),
                    @neither => $name::Neither => (f(), g()),
                    @both => $name::Both(l, r) => (l, r),
                })
            }

            /// Return left value or given value.
            pub fn left_or(self, other: L) -> L {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => l,
                    @either => $name::Right(_) => other,
                    @neither => $name::Neither => other,
                    @both => $name::Both(l, _) => l,
                })
            }

            /// Return left value or default value.
            pub fn left_or_default(self) -> L where L: Default {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => l,
                    @either => $name::Right(_) => L::default(),
                    @neither => $name::Neither => L::default(),
                    @both => $name::Both(l, _) => l,
                })
            }

            /// Return left value or computes it from a closure.
            pub fn left_or_else<F>(self, f: F) -> L where F: FnOnce() -> L {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => l,
                    @either => $name::Right(_) => f(),
                    @neither => $name::Neither => f(),
                    @both => $name::Both(l, _) => l,
                })
            }
        }
    };
}

// impl for left / right 'just' getters.
macro_rules! impl_left_right_just_getters {
    ($name:ident, true, $has_n:ident, true) => {
        /* Only available for the types containing both `Either` and `Both` variants. */

        /// If the variant is a `Left` variant, return the left value.
        /// Otherwise (even the variant is a `Both` variant), return `None`.
        impl<L, R> $name<L, R> {
            pub fn just_left(self) -> Option<L> {
                match_possible_variants!(self, true, $has_n, true, {
                    @either => $name::Left(l) => Some(l),
                    @either => $name::Right(_) => None,
                    @neither => $name::Neither => None,
                    @both => $name::Both(_, _) => None,
                })
            }
        }
    };
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        /* empty for other cases. */
    };
}

// impl for as_ref / as_mut.
macro_rules! impl_as_ref_mut {
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        impl<L, R> $name<L, R> {
            /// Creates a new variant with references to the contained values.
            pub fn as_ref(&self) -> $name<&L, &R> {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => $name::Left(l),
                    @either => $name::Right(r) => $name::Right(r),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => $name::Both(l, r),
                })
            }

            /// Creates a new variant with mutable references to the contained values.
            pub fn as_mut(&mut self) -> $name<&mut L, &mut R> {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => $name::Left(l),
                    @either => $name::Right(r) => $name::Right(r),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => $name::Both(l, r),
                })
            }

            /// Creates a new pinned variant with references to the contained values.
            pub fn as_pin_ref(self: Pin<&Self>) -> $name<Pin<&L>, Pin<&R>> {
                // SAFETY: This is safe because:
                // 1. We never move the inner values - we only create a new reference to them
                // 2. The original Pin<&Self> guarantees that the original data won't move
                // 3. We're maintaining the pinning invariant by wrapping the references in Pin
                // 4. The lifetime of the output references is tied to the input lifetime
                unsafe {
                    match_possible_variants!(self.get_ref(), $has_e, $has_n, $has_b, {
                        @either => $name::Left(l) => $name::Left(Pin::new_unchecked(l)),
                        @either => $name::Right(r) => $name::Right(Pin::new_unchecked(r)),
                        @neither => $name::Neither => $name::Neither,
                        @both => $name::Both(l, r) => $name::Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
                    })
                }
            }

            /// Creates a new pinned variant with mutable references to the contained values.
            pub fn as_pin_mut(self: Pin<&mut Self>) -> $name<Pin<&mut L>, Pin<&mut R>> {
                // SAFETY: This is safe because:
                // 1. We never move the inner values out of the pin
                // 2. We're creating new Pin instances from references to pinned data
                // 3. The original Pin<&mut Self> guarantees unique access
                // 4. We maintain the pinning invariant by wrapping the mutable references in Pin
                // 5. get_unchecked_mut is safe here as we have exclusive access via Pin<&mut Self>
                unsafe {
                    match_possible_variants!(self.get_unchecked_mut(), $has_e, $has_n, $has_b, {
                        @either => $name::Left(l) => $name::Left(Pin::new_unchecked(l)),
                        @either => $name::Right(r) => $name::Right(Pin::new_unchecked(r)),
                        @neither => $name::Neither => $name::Neither,
                        @both => $name::Both(l, r) => $name::Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
                    })
                }
            }

            /// Returns a new value using the `Deref` trait for `L` and `R` values.
            pub fn as_deref(&self) -> $name<&L::Target, &R::Target>
            where
                L: Deref,
                R: Deref,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => $name::Left(l.deref()),
                    @either => $name::Right(r) => $name::Right(r.deref()),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => $name::Both(l.deref(), r.deref()),
                })
            }

            /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
            pub fn as_deref_mut(&mut self) -> $name<&mut L::Target, &mut R::Target>
            where
                L: DerefMut,
                R: DerefMut,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => $name::Left(l.deref_mut()),
                    @either => $name::Right(r) => $name::Right(r.deref_mut()),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => $name::Both(l.deref_mut(), r.deref_mut()),
                })
            }
        }
    };
}

// impl for map_left, map_right.
macro_rules! impl_map_left_right {
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        impl<L, R> $name<L, R> {

            /// Apply the function `f` on the value in the left position if it is present,
            /// and then rewrap the result in a same variant of the new type.
            pub fn map_left<F, L2>(self, f: F) -> $name<L2, R>
            where
                F: FnOnce(L) -> L2,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => $name::Left(f(l)),
                    @either => $name::Right(r) => $name::Right(r),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => $name::Both(f(l), r),
                })
            }
        }
    };
}

// impl for into_left, into_right.
macro_rules! impl_into_left_right {
    ($name:ident, $has_e:ident, false, $has_b:ident) => {
        impl<L, R> $name<L, R> {
            pub fn into_left(self) -> L where R: Into<L> {
                match_possible_variants!(self, $has_e, false, $has_b, {
                    @either => $name::Left(l) => l,
                    @either => $name::Right(r) => r.into(),
                    @neither => $name::Neither => unreachable!(),
                    @both => $name::Both(l, _) => l,
                })
            }
        }
    };
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        /* empty for other cases. */
    };
}

macro_rules! impl_both_getters {
    ($name:ident, $has_e:ident, $has_n:ident, true) => {
        impl<L, R> $name<L, R> {
            pub fn both(self) -> Option<(L, R)> {
                match_possible_variants!(self, $has_e, $has_n, true, {
                    @either => $name::Left(_) => None,
                    @either => $name::Right(_) => None,
                    @neither => $name::Neither => None,
                    @both => $name::Both(l, r) => Some((l, r)),
                })
            }
        }
    };
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        /* empty for other cases. */
    };
}

macro_rules! impl_map {
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        impl<L, R> $name<L, R> {
            pub fn map<F, G, L2, R2>(self, f: F, g: G) -> $name<L2, R2>
            where
                F: FnOnce(L) -> L2,
                G: FnOnce(R) -> R2,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => $name::Left(f(l)),
                    @either => $name::Right(r) => $name::Right(g(r)),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => $name::Both(f(l), g(r)),
                })
            }
        }
    };
}

macro_rules! impl_map_with_no_both {
    ($name:ident, $has_e:ident, $has_n:ident, false) => {
        impl<L, R> $name<L, R> {
            pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> $name<L2, R2>
            where
                F: FnOnce(Ctx, L) -> L2,
                G: FnOnce(Ctx, R) -> R2,
            {
                match_possible_variants!(self, $has_e, $has_n, false, {
                    @either => $name::Left(l) => $name::Left(f(ctx, l)),
                    @either => $name::Right(r) => $name::Right(g(ctx, r)),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => unreachable!(),
                })
            }
        }
    };
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        /* empty for other cases. */
    };
}

macro_rules! impl_map_with_both {
    ($name:ident, $has_e:ident, $has_n:ident, true) => {
        impl<L, R> $name<L, R> {
            pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> $name<L2, R2>
            where
                Ctx: Clone,
                F: FnOnce(Ctx, L) -> L2,
                G: FnOnce(Ctx, R) -> R2,
            {
                match_possible_variants!(self, $has_e, $has_n, true, {
                    @either => $name::Left(l) => $name::Left(f(ctx.clone(), l)),
                    @either => $name::Right(r) => $name::Right(g(ctx.clone(), r)),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => $name::Both(f(ctx.clone(), l), g(ctx.clone(), r)),
                })
            }
        }
    };
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        /* empty for other cases. */
    };
}

apply_impl_to_all_variants!(impl_left_right_getters);
apply_impl_to_all_variants!(impl_and_or_methods);
apply_impl_to_all_variants!(impl_left_right_just_getters);
apply_impl_to_all_variants!(impl_as_ref_mut);
apply_impl_to_all_variants!(impl_map_left_right);
apply_impl_to_all_variants!(impl_into_left_right);
apply_impl_to_all_variants!(impl_both_getters);
apply_impl_to_all_variants!(impl_map);
apply_impl_to_all_variants!(impl_map_with_no_both);
apply_impl_to_all_variants!(impl_map_with_both);

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
