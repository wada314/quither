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

pub enum Neither {
    Neither,
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

macro_rules! impl_is_checkers {
    (false, false, false) => { /* Does not allow `!` because we cannot implement `!` types. */ };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        impl_pair_type!($has_e, $has_n, $has_b, L, R, {
            pub fn is_left(&self) -> bool {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(_) => true,
                    @either => Self::Right(_) => false,
                    @neither => Self::Neither => false,
                    @both => Self::Both(_, _) => true,
                })
            }

            pub fn is_neither(&self) -> bool {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(_) => false,
                    @either => Self::Right(_) => false,
                    @neither => Self::Neither => true,
                    @both => Self::Both(_, _) => false,
                })
            }

            pub fn is_both(&self) -> bool {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(_) => false,
                    @either => Self::Right(_) => false,
                    @neither => Self::Neither => false,
                    @both => Self::Both(_, _) => true,
                })
            }
        });
    };
}

macro_rules! impl_flip {
    (false, false, false) => { /* Does not allow `!` because we cannot implement `!` types. */ };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        impl_pair_type!($has_e, $has_n, $has_b, L, R, {
            pub fn flip(self) -> pair_type!($has_e, $has_n, $has_b, R, L) {
                use_pair_variants!($has_e, $has_n, $has_b);
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Right(l),
                    @either => Self::Right(r) => Left(r),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => Both(r, l),
                })
            }
        });
    };
}

/// impl getters
macro_rules! impl_getters {
    (false, $has_n:ident, false) => {
         /* Does not allow `Neither` nor `!` types because they don't have left/right types. */
    };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        impl_pair_type!($has_e, $has_n, $has_b, L, R, {
            /// Convert the left side of the variant into an `Option`.
            /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
            pub fn left(self) -> Option<L> {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Some(l),
                    @either => Self::Right(_) => None,
                    @neither => Self::Neither => None,
                    @both => Self::Both(l, _) => Some(l),
                })
            }

            pub fn both(self) -> Option<(L, R)> {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(_) => None,
                    @either => Self::Right(_) => None,
                    @neither => Self::Neither => None,
                    @both => Self::Both(l, r) => Some((l, r)),
                })
            }

            /// Returns a tuple of the optional left and right values.
            pub fn left_and_right(self) -> (Option<L>, Option<R>) {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => (Some(l), None),
                    @either => Self::Right(r) => (None, Some(r)),
                    @neither => Self::Neither => (None, None),
                    @both => Self::Both(l, r) => (Some(l), Some(r)),
                })
            }

            /// Unwrap the left value from the variant.
            ///
            /// # Panics
            ///
            /// - If the variant is something not containing a left value.
            pub fn unwrap_left(self) -> L where R: Debug {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => l,
                    @either => Self::Right(r) => panic!("Expected a Left variant, but got a right value:{:?}", r),
                    @neither => Self::Neither => panic!("Expected a Left variant, but got a Neither variant"),
                    @both => Self::Both(l, _) => l,
                })
            }

            /// Unwrap the left value from the variant.
            ///
            /// # Panics
            ///
            /// - If the variant is something not containing a left value.
            pub fn expect_left(self, #[allow(unused)] msg: &str) -> L where R: Debug {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => l,
                    @either => Self::Right(r) => panic!("{}: {:?}", msg, r),
                    @neither => Self::Neither => panic!("{}", msg),
                    @both => Self::Both(l, _) => l,
                })
            }

            /// If the variant is a `Left` variant, return the left value.
            /// Otherwise (even the variant is a `Both` variant), return `None`.
            pub fn just_left(self) -> Option<L> {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Some(l),
                    @either => Self::Right(_) => None,
                    @neither => Self::Neither => None,
                    @both => Self::Both(_, _) => None,
                })
            }
        });
    };
}

// impl for 'or' and 'and' operations.
macro_rules! impl_and_or_methods {
    (false, $has_n:ident, false) => {
         /* Does not allow `Neither` nor `!` types because they don't have left/right types. */
    };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        impl_pair_type!($has_e, $has_n, $has_b, L, R, {
            /// Apply the function `f` on the value in the left position if it is present,
            /// and then rewrap the result in a same variant of the new type.
            pub fn left_and_then<F, L2>(self, f: F) -> pair_type!($has_e, $has_n, $has_b, L2, R)
            where
                F: FnOnce(L) -> pair_type!($has_e, $has_n, $has_b, L2, R),
            {
                use_pair_variants!($has_e, $has_n, $has_b);
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => f(l),
                    @either => Self::Right(r) => Right(r),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, _) => f(l),
                })
            }

            pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l2) => (l2, r),
                    @either => Self::Right(r2) => (l, r2),
                    @neither => Self::Neither => (l, r),
                    @both => Self::Both(l2, r2) => (l2, r2),
                })
            }

            pub fn or_default(self) -> (L, R) where L: Default, R: Default {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => (l, R::default()),
                    @either => Self::Right(r) => (L::default(), r),
                    @neither => Self::Neither => (L::default(), R::default()),
                    @both => Self::Both(l, r) => (l, r),
                })
            }

            pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
            where
                F: FnOnce() -> L,
                G: FnOnce() -> R,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => (l, g()),
                    @either => Self::Right(r) => (f(), r),
                    @neither => Self::Neither => (f(), g()),
                    @both => Self::Both(l, r) => (l, r),
                })
            }

            /// Return left value or given value.
            pub fn left_or(self, #[allow(unused)] other: L) -> L {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => l,
                    @either => Self::Right(_) => other,
                    @neither => Self::Neither => other,
                    @both => Self::Both(l, _) => l,
                })
            }

            /// Return left value or default value.
            pub fn left_or_default(self) -> L where L: Default {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => l,
                    @either => Self::Right(_) => L::default(),
                    @neither => Self::Neither => L::default(),
                    @both => Self::Both(l, _) => l,
                })
            }

            /// Return left value or computes it from a closure.
            pub fn left_or_else<F>(self, #[allow(unused)] f: F) -> L where F: FnOnce() -> L {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => l,
                    @either => Self::Right(_) => f(),
                    @neither => Self::Neither => f(),
                    @both => Self::Both(l, _) => l,
                })
            }
        });
    };
}

// impl for as_ref / as_mut.
macro_rules! impl_as_ref {
    (false, false, false) => {
         /* Does not allow `!` type because it is not allowed to implement `!` type. */
    };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        impl_pair_type!($has_e, $has_n, $has_b, L, R, {
            /// Creates a new variant with references to the contained values.
            pub fn as_ref(&self) -> pair_type!($has_e, $has_n, $has_b, &L, &R) {
                use_pair_variants!($has_e, $has_n, $has_b);
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Left(l),
                    @either => Self::Right(r) => Right(r),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => Both(l, r),
                })
            }

            /// Creates a new variant with mutable references to the contained values.
            pub fn as_mut(&mut self) -> pair_type!($has_e, $has_n, $has_b, &mut L, &mut R) {
                use_pair_variants!($has_e, $has_n, $has_b);
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Left(l),
                    @either => Self::Right(r) => Right(r),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => Both(l, r),
                })
            }

            /// Creates a new pinned variant with references to the contained values.
            pub fn as_pin_ref(self: Pin<&Self>) -> pair_type!($has_e, $has_n, $has_b, Pin<&L>, Pin<&R>) {
                use_pair_variants!($has_e, $has_n, $has_b);
                // SAFETY: This is safe because:
                // 1. We never move the inner values - we only create a new reference to them
                // 2. The original Pin<&Self> guarantees that the original data won't move
                // 3. We're maintaining the pinning invariant by wrapping the references in Pin
                // 4. The lifetime of the output references is tied to the input lifetime
                #[allow(unused)]
                unsafe {
                    match_possible_variants!(self.get_ref(), $has_e, $has_n, $has_b, {
                        @either => Self::Left(l) => Left(Pin::new_unchecked(l)),
                        @either => Self::Right(r) => Right(Pin::new_unchecked(r)),
                        @neither => Self::Neither => Neither,
                        @both => Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
                    })
                }
            }

            /// Creates a new pinned variant with mutable references to the contained values.
            pub fn as_pin_mut(self: Pin<&mut Self>) -> pair_type!($has_e, $has_n, $has_b, Pin<&mut L>, Pin<&mut R>) {
                use_pair_variants!($has_e, $has_n, $has_b);
                // SAFETY: This is safe because:
                // 1. We never move the inner values out of the pin
                // 2. We're creating new Pin instances from references to pinned data
                // 3. The original Pin<&mut Self> guarantees unique access
                // 4. We maintain the pinning invariant by wrapping the mutable references in Pin
                // 5. get_unchecked_mut is safe here as we have exclusive access via Pin<&mut Self>
                unsafe {
                    match_possible_variants!(self.get_unchecked_mut(), $has_e, $has_n, $has_b, {
                        @either => Self::Left(l) => Left(Pin::new_unchecked(l)),
                        @either => Self::Right(r) => Right(Pin::new_unchecked(r)),
                        @neither => Self::Neither => Neither,
                        @both => Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
                    })
                }
            }
        });
    }
}

// impl for as_deref / as_deref_mut.
macro_rules! impl_as_deref {
    (false, $has_n:ident, false) => {
         /* Does not allow `Neither` nor `!` types because they don't have left/right types. */
    };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        impl_pair_type!($has_e, $has_n, $has_b, L, R, {
            /// Returns a new value using the `Deref` trait for `L` and `R` values.
            pub fn as_deref(&self) -> pair_type!($has_e, $has_n, $has_b, &L::Target, &R::Target)
            where
                L: Deref,
                R: Deref,
            {
                use_pair_variants!($has_e, $has_n, $has_b);
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Left(l.deref()),
                    @either => Self::Right(r) => Right(r.deref()),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => Both(l.deref(), r.deref()),
                })
            }

            /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
            pub fn as_deref_mut(&mut self) -> pair_type!($has_e, $has_n, $has_b, &mut L::Target, &mut R::Target)
            where
                L: DerefMut,
                R: DerefMut,
            {
                use_pair_variants!($has_e, $has_n, $has_b);
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Left(l.deref_mut()),
                    @either => Self::Right(r) => Right(r.deref_mut()),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => Both(l.deref_mut(), r.deref_mut()),
                })
            }
        });
    };
}

// impl for into_left, into_right.
macro_rules! impl_into_left_right {
    (false, $has_n:ident, false) => {
        /* Does not allow `Neither` nor `!` types because they don't have left/right types. */
    };
    ($has_e:ident, false, $has_b:ident) => {
        /* Only allow the pair type which does not include `Neither` variant. */
        impl_pair_type!($has_e, false, $has_b, L, R, {
            pub fn into_left(self) -> L where R: Into<L> {
                match_possible_variants!(self, $has_e, false, $has_b, {
                    @either => Self::Left(l) => l,
                    @either => Self::Right(r) => r.into(),
                    @neither => Self::Neither => unreachable!(),
                    @both => Self::Both(l, _) => l,
                })
            }
        });
    };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        /* empty for other cases. */
    };
}

macro_rules! impl_map {
    (false, $has_n:ident, false) => {
         /* Does not allow `Neither` nor `!` types because they don't have left/right types. */
    };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        impl_pair_type!($has_e, $has_n, $has_b, L, R, {
            pub fn map<F, G, L2, R2>(self, f: F, g: G)
                -> pair_type!($has_e, $has_n, $has_b, L2, R2)
            where
                F: FnOnce(L) -> L2,
                G: FnOnce(R) -> R2,
            {
                use_pair_variants!($has_e, $has_n, $has_b);
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Left(f(l)),
                    @either => Self::Right(r) => Right(g(r)),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => Both(f(l), g(r)),
                })
            }

            /// Apply the function `f` on the value in the left position if it is present,
            /// and then rewrap the result in a same variant of the new type.
            pub fn map_left<F, L2>(self, f: F) -> pair_type!($has_e, $has_n, $has_b, L2, R)
            where
                F: FnOnce(L) -> L2,
            {
                use_pair_variants!($has_e, $has_n, $has_b);
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => Self::Left(l) => Left(f(l)),
                    @either => Self::Right(r) => Right(r),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => Both(f(l), r),
                })
            }
        });
    };
}

macro_rules! impl_map_with {
    (false, $has_n:ident, false) => {
         /* Does not allow `Neither` nor `!` types because they don't have left/right types. */
    };
    // The case not including `Both` variant. Then the `Ctx` is not required to be `Clone`.
    ($has_e:ident, $has_n:ident, false) => {
        impl_pair_type!($has_e, $has_n, false, L, R, {
            pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G)
                -> pair_type!($has_e, $has_n, false, L2, R2)
            where
                F: FnOnce(Ctx, L) -> L2,
                G: FnOnce(Ctx, R) -> R2,
            {
                use_pair_variants!($has_e, $has_n, false);
                match_possible_variants!(self, $has_e, $has_n, false, {
                    @either => Self::Left(l) => Left(f(ctx, l)),
                    @either => Self::Right(r) => Right(g(ctx, r)),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => unreachable!(),
                })
            }
        });
    };
    // The case including `Both` variant. Then the `Ctx` is required to be `Clone`.
    ($has_e:ident, $has_n:ident, true) => {
        impl_pair_type!($has_e, $has_n, true, L, R, {
            pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G)
                -> pair_type!($has_e, $has_n, true, L2, R2)
            where
                Ctx: Clone,
                F: FnOnce(Ctx, L) -> L2,
                G: FnOnce(Ctx, R) -> R2,
            {
                use_pair_variants!($has_e, $has_n, true);
                match_possible_variants!(self, $has_e, $has_n, true, {
                    @either => Self::Left(l) => Left(f(ctx.clone(), l)),
                    @either => Self::Right(r) => Right(g(ctx.clone(), r)),
                    @neither => Self::Neither => Neither,
                    @both => Self::Both(l, r) => Both(f(ctx.clone(), l), g(ctx.clone(), r)),
                })
            }
        });
    };
    ($has_e:ident, $has_n:ident, $has_b:ident) => {
        /* empty for other cases. */
    };
}

apply_impl_to_all_variants!(impl_is_checkers);
apply_impl_to_all_variants!(impl_flip);
apply_impl_to_all_variants!(impl_getters);
apply_impl_to_all_variants!(impl_and_or_methods);
apply_impl_to_all_variants!(impl_as_ref);
apply_impl_to_all_variants!(impl_as_deref);
apply_impl_to_all_variants!(impl_into_left_right);
apply_impl_to_all_variants!(impl_map);
apply_impl_to_all_variants!(impl_map_with);

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
