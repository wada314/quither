#![feature(prelude_import)]
#[prelude_import]
use std::prelude::rust_2024::*;
#[macro_use]
extern crate std;
use ::replace_with::replace_with_or_abort;
use ::std::fmt::Debug;
use ::std::ops::{Deref, DerefMut};
use ::std::pin::Pin;
use ::enb_proc_macros::enb;
#[macro_use]
mod macros {}
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
impl<L, R> Either<L, R> {
    pub fn hello(&self) {
        {
            ::std::io::_print(format_args!("hello\n"));
        };
    }
    pub fn is_left(&self) -> bool {
        match self {
            Self::Left(_) => true,
            Self::Right(_) => false,
        }
    }
}
impl Neither {
    pub fn hello(&self) {
        {
            ::std::io::_print(format_args!("hello\n"));
        };
    }
    pub fn yeah(&self) {
        {
            ::std::io::_print(format_args!("yeah\n"));
        };
    }
    pub fn is_left(&self) -> bool {
        match self {
            Self::Neither => false,
        }
    }
}
impl<L, R> Both<L, R> {
    pub fn hello(&self) {
        {
            ::std::io::_print(format_args!("hello\n"));
        };
    }
    pub fn is_left(&self) -> bool {
        match self {
            Self::Both(_, _) => true,
        }
    }
}
impl<L, R> EitherOrNeither<L, R> {
    pub fn hello(&self) {
        {
            ::std::io::_print(format_args!("hello\n"));
        };
    }
    pub fn yeah(&self) {
        {
            ::std::io::_print(format_args!("yeah\n"));
        };
    }
    pub fn is_left(&self) -> bool {
        match self {
            Self::Left(_) => true,
            Self::Right(_) => false,
            Self::Neither => false,
        }
    }
}
impl<L, R> EitherOrBoth<L, R> {
    pub fn hello(&self) {
        {
            ::std::io::_print(format_args!("hello\n"));
        };
    }
    pub fn is_left(&self) -> bool {
        match self {
            Self::Left(_) => true,
            Self::Right(_) => false,
            Self::Both(_, _) => true,
        }
    }
}
impl<L, R> NeitherOrBoth<L, R> {
    pub fn hello(&self) {
        {
            ::std::io::_print(format_args!("hello\n"));
        };
    }
    pub fn yeah(&self) {
        {
            ::std::io::_print(format_args!("yeah\n"));
        };
    }
    pub fn is_left(&self) -> bool {
        match self {
            Self::Neither => false,
            Self::Both(_, _) => true,
        }
    }
}
impl<L, R> EitherOrNeitherOrBoth<L, R> {
    pub fn hello(&self) {
        {
            ::std::io::_print(format_args!("hello\n"));
        };
    }
    pub fn yeah(&self) {
        {
            ::std::io::_print(format_args!("yeah\n"));
        };
    }
    pub fn is_left(&self) -> bool {
        match self {
            Self::Left(_) => true,
            Self::Right(_) => false,
            Self::Neither => false,
            Self::Both(_, _) => true,
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    pub fn is_neither(&self) -> bool {
        match self {
            Self::Left(_) => false,
            Self::Right(_) => false,
            Self::Neither => true,
            Self::Both(_, _) => false,
        }
    }
    pub fn is_both(&self) -> bool {
        match self {
            Self::Left(_) => false,
            Self::Right(_) => false,
            Self::Neither => false,
            Self::Both(_, _) => true,
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    pub fn is_neither(&self) -> bool {
        match self {
            Self::Left(_) => false,
            Self::Right(_) => false,
            Self::Neither => true,
        }
    }
    pub fn is_both(&self) -> bool {
        match self {
            Self::Left(_) => false,
            Self::Right(_) => false,
            Self::Neither => false,
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    pub fn is_neither(&self) -> bool {
        match self {
            Self::Left(_) => false,
            Self::Right(_) => false,
            Self::Both(_, _) => false,
        }
    }
    pub fn is_both(&self) -> bool {
        match self {
            Self::Left(_) => false,
            Self::Right(_) => false,
            Self::Both(_, _) => true,
        }
    }
}
impl<L, R> crate::NeitherOrBoth<L, R> {
    pub fn is_neither(&self) -> bool {
        match self {
            Self::Neither => true,
            Self::Both(_, _) => false,
        }
    }
    pub fn is_both(&self) -> bool {
        match self {
            Self::Neither => false,
            Self::Both(_, _) => true,
        }
    }
}
impl<L, R> crate::Either<L, R> {
    pub fn is_neither(&self) -> bool {
        match self {
            Self::Left(_) => false,
            Self::Right(_) => false,
        }
    }
    pub fn is_both(&self) -> bool {
        match self {
            Self::Left(_) => false,
            Self::Right(_) => false,
        }
    }
}
impl<L, R> crate::Both<L, R> {
    pub fn is_neither(&self) -> bool {
        match self {
            Self::Both(_, _) => false,
        }
    }
    pub fn is_both(&self) -> bool {
        match self {
            Self::Both(_, _) => true,
        }
    }
}
impl crate::Neither {
    pub fn is_neither(&self) -> bool {
        match self {
            Self::Neither => true,
        }
    }
    pub fn is_both(&self) -> bool {
        match self {
            Self::Neither => false,
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    pub fn flip(self) -> crate::EitherOrNeitherOrBoth<R, L> {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => Right(l),
            Self::Right(r) => Left(r),
            Self::Neither => Neither,
            Self::Both(l, r) => Both(r, l),
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    pub fn flip(self) -> crate::EitherOrNeither<R, L> {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => Right(l),
            Self::Right(r) => Left(r),
            Self::Neither => Neither,
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    pub fn flip(self) -> crate::EitherOrBoth<R, L> {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => Right(l),
            Self::Right(r) => Left(r),
            Self::Both(l, r) => Both(r, l),
        }
    }
}
impl<L, R> crate::NeitherOrBoth<L, R> {
    pub fn flip(self) -> crate::NeitherOrBoth<R, L> {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, r) => Both(r, l),
        }
    }
}
impl<L, R> crate::Either<L, R> {
    pub fn flip(self) -> crate::Either<R, L> {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => Right(l),
            Self::Right(r) => Left(r),
        }
    }
}
impl<L, R> crate::Both<L, R> {
    pub fn flip(self) -> crate::Both<R, L> {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, r) => Both(r, l),
        }
    }
}
impl crate::Neither {
    pub fn flip(self) -> crate::Neither {
        #[allow(unused)]
        use crate::Neither::*;
        match self {
            Self::Neither => Neither,
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    /// Convert the left side of the variant into an `Option`.
    /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
    pub fn left(self) -> Option<L> {
        match self {
            Self::Left(l) => Some(l),
            Self::Right(_) => None,
            Self::Neither => None,
            Self::Both(l, _) => Some(l),
        }
    }
    pub fn both(self) -> Option<(L, R)> {
        match self {
            Self::Left(_) => None,
            Self::Right(_) => None,
            Self::Neither => None,
            Self::Both(l, r) => Some((l, r)),
        }
    }
    /// Returns a tuple of the optional left and right values.
    pub fn left_and_right(self) -> (Option<L>, Option<R>) {
        match self {
            Self::Left(l) => (Some(l), None),
            Self::Right(r) => (None, Some(r)),
            Self::Neither => (None, None),
            Self::Both(l, r) => (Some(l), Some(r)),
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn unwrap_left(self) -> L
    where
        R: Debug,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => {
                ::core::panicking::panic_fmt(
                    format_args!(
                        "Expected a Left variant, but got a right value:{0:?}",
                        r,
                    ),
                );
            }
            Self::Neither => {
                ::core::panicking::panic_fmt(
                    format_args!("Expected a Left variant, but got a Neither variant"),
                );
            }
            Self::Both(l, _) => l,
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn expect_left(self, #[allow(unused)] msg: &str) -> L
    where
        R: Debug,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => {
                ::core::panicking::panic_fmt(format_args!("{0}: {1:?}", msg, r));
            }
            Self::Neither => {
                #[cold]
                #[track_caller]
                #[inline(never)]
                #[rustc_const_panic_str]
                #[rustc_do_not_const_check]
                const fn panic_cold_display<T: ::core::fmt::Display>(arg: &T) -> ! {
                    ::core::panicking::panic_display(arg)
                }
                panic_cold_display(&msg);
            }
            Self::Both(l, _) => l,
        }
    }
    /// If the variant is a `Left` variant, return the left value.
    /// Otherwise (even the variant is a `Both` variant), return `None`.
    pub fn just_left(self) -> Option<L> {
        match self {
            Self::Left(l) => Some(l),
            Self::Right(_) => None,
            Self::Neither => None,
            Self::Both(_, _) => None,
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    /// Convert the left side of the variant into an `Option`.
    /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
    pub fn left(self) -> Option<L> {
        match self {
            Self::Left(l) => Some(l),
            Self::Right(_) => None,
            Self::Neither => None,
        }
    }
    pub fn both(self) -> Option<(L, R)> {
        match self {
            Self::Left(_) => None,
            Self::Right(_) => None,
            Self::Neither => None,
        }
    }
    /// Returns a tuple of the optional left and right values.
    pub fn left_and_right(self) -> (Option<L>, Option<R>) {
        match self {
            Self::Left(l) => (Some(l), None),
            Self::Right(r) => (None, Some(r)),
            Self::Neither => (None, None),
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn unwrap_left(self) -> L
    where
        R: Debug,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => {
                ::core::panicking::panic_fmt(
                    format_args!(
                        "Expected a Left variant, but got a right value:{0:?}",
                        r,
                    ),
                );
            }
            Self::Neither => {
                ::core::panicking::panic_fmt(
                    format_args!("Expected a Left variant, but got a Neither variant"),
                );
            }
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn expect_left(self, #[allow(unused)] msg: &str) -> L
    where
        R: Debug,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => {
                ::core::panicking::panic_fmt(format_args!("{0}: {1:?}", msg, r));
            }
            Self::Neither => {
                #[cold]
                #[track_caller]
                #[inline(never)]
                #[rustc_const_panic_str]
                #[rustc_do_not_const_check]
                const fn panic_cold_display<T: ::core::fmt::Display>(arg: &T) -> ! {
                    ::core::panicking::panic_display(arg)
                }
                panic_cold_display(&msg);
            }
        }
    }
    /// If the variant is a `Left` variant, return the left value.
    /// Otherwise (even the variant is a `Both` variant), return `None`.
    pub fn just_left(self) -> Option<L> {
        match self {
            Self::Left(l) => Some(l),
            Self::Right(_) => None,
            Self::Neither => None,
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    /// Convert the left side of the variant into an `Option`.
    /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
    pub fn left(self) -> Option<L> {
        match self {
            Self::Left(l) => Some(l),
            Self::Right(_) => None,
            Self::Both(l, _) => Some(l),
        }
    }
    pub fn both(self) -> Option<(L, R)> {
        match self {
            Self::Left(_) => None,
            Self::Right(_) => None,
            Self::Both(l, r) => Some((l, r)),
        }
    }
    /// Returns a tuple of the optional left and right values.
    pub fn left_and_right(self) -> (Option<L>, Option<R>) {
        match self {
            Self::Left(l) => (Some(l), None),
            Self::Right(r) => (None, Some(r)),
            Self::Both(l, r) => (Some(l), Some(r)),
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn unwrap_left(self) -> L
    where
        R: Debug,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => {
                ::core::panicking::panic_fmt(
                    format_args!(
                        "Expected a Left variant, but got a right value:{0:?}",
                        r,
                    ),
                );
            }
            Self::Both(l, _) => l,
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn expect_left(self, #[allow(unused)] msg: &str) -> L
    where
        R: Debug,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => {
                ::core::panicking::panic_fmt(format_args!("{0}: {1:?}", msg, r));
            }
            Self::Both(l, _) => l,
        }
    }
    /// If the variant is a `Left` variant, return the left value.
    /// Otherwise (even the variant is a `Both` variant), return `None`.
    pub fn just_left(self) -> Option<L> {
        match self {
            Self::Left(l) => Some(l),
            Self::Right(_) => None,
            Self::Both(_, _) => None,
        }
    }
}
impl<L, R> crate::NeitherOrBoth<L, R> {
    /// Convert the left side of the variant into an `Option`.
    /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
    pub fn left(self) -> Option<L> {
        match self {
            Self::Neither => None,
            Self::Both(l, _) => Some(l),
        }
    }
    pub fn both(self) -> Option<(L, R)> {
        match self {
            Self::Neither => None,
            Self::Both(l, r) => Some((l, r)),
        }
    }
    /// Returns a tuple of the optional left and right values.
    pub fn left_and_right(self) -> (Option<L>, Option<R>) {
        match self {
            Self::Neither => (None, None),
            Self::Both(l, r) => (Some(l), Some(r)),
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn unwrap_left(self) -> L
    where
        R: Debug,
    {
        match self {
            Self::Neither => {
                ::core::panicking::panic_fmt(
                    format_args!("Expected a Left variant, but got a Neither variant"),
                );
            }
            Self::Both(l, _) => l,
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn expect_left(self, #[allow(unused)] msg: &str) -> L
    where
        R: Debug,
    {
        match self {
            Self::Neither => {
                #[cold]
                #[track_caller]
                #[inline(never)]
                #[rustc_const_panic_str]
                #[rustc_do_not_const_check]
                const fn panic_cold_display<T: ::core::fmt::Display>(arg: &T) -> ! {
                    ::core::panicking::panic_display(arg)
                }
                panic_cold_display(&msg);
            }
            Self::Both(l, _) => l,
        }
    }
    /// If the variant is a `Left` variant, return the left value.
    /// Otherwise (even the variant is a `Both` variant), return `None`.
    pub fn just_left(self) -> Option<L> {
        match self {
            Self::Neither => None,
            Self::Both(_, _) => None,
        }
    }
}
impl<L, R> crate::Either<L, R> {
    /// Convert the left side of the variant into an `Option`.
    /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
    pub fn left(self) -> Option<L> {
        match self {
            Self::Left(l) => Some(l),
            Self::Right(_) => None,
        }
    }
    pub fn both(self) -> Option<(L, R)> {
        match self {
            Self::Left(_) => None,
            Self::Right(_) => None,
        }
    }
    /// Returns a tuple of the optional left and right values.
    pub fn left_and_right(self) -> (Option<L>, Option<R>) {
        match self {
            Self::Left(l) => (Some(l), None),
            Self::Right(r) => (None, Some(r)),
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn unwrap_left(self) -> L
    where
        R: Debug,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => {
                ::core::panicking::panic_fmt(
                    format_args!(
                        "Expected a Left variant, but got a right value:{0:?}",
                        r,
                    ),
                );
            }
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn expect_left(self, #[allow(unused)] msg: &str) -> L
    where
        R: Debug,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => {
                ::core::panicking::panic_fmt(format_args!("{0}: {1:?}", msg, r));
            }
        }
    }
    /// If the variant is a `Left` variant, return the left value.
    /// Otherwise (even the variant is a `Both` variant), return `None`.
    pub fn just_left(self) -> Option<L> {
        match self {
            Self::Left(l) => Some(l),
            Self::Right(_) => None,
        }
    }
}
impl<L, R> crate::Both<L, R> {
    /// Convert the left side of the variant into an `Option`.
    /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
    pub fn left(self) -> Option<L> {
        match self {
            Self::Both(l, _) => Some(l),
        }
    }
    pub fn both(self) -> Option<(L, R)> {
        match self {
            Self::Both(l, r) => Some((l, r)),
        }
    }
    /// Returns a tuple of the optional left and right values.
    pub fn left_and_right(self) -> (Option<L>, Option<R>) {
        match self {
            Self::Both(l, r) => (Some(l), Some(r)),
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn unwrap_left(self) -> L
    where
        R: Debug,
    {
        match self {
            Self::Both(l, _) => l,
        }
    }
    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    pub fn expect_left(self, #[allow(unused)] msg: &str) -> L
    where
        R: Debug,
    {
        match self {
            Self::Both(l, _) => l,
        }
    }
    /// If the variant is a `Left` variant, return the left value.
    /// Otherwise (even the variant is a `Both` variant), return `None`.
    pub fn just_left(self) -> Option<L> {
        match self {
            Self::Both(_, _) => None,
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn left_and_then<F, L2>(self, f: F) -> crate::EitherOrNeitherOrBoth<L2, R>
    where
        F: FnOnce(L) -> crate::EitherOrNeitherOrBoth<L2, R>,
    {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => f(l),
            Self::Right(r) => Right(r),
            Self::Neither => Neither,
            Self::Both(l, _) => f(l),
        }
    }
    pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
        match self {
            Self::Left(l2) => (l2, r),
            Self::Right(r2) => (l, r2),
            Self::Neither => (l, r),
            Self::Both(l2, r2) => (l2, r2),
        }
    }
    pub fn or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            Self::Left(l) => (l, R::default()),
            Self::Right(r) => (L::default(), r),
            Self::Neither => (L::default(), R::default()),
            Self::Both(l, r) => (l, r),
        }
    }
    pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
    where
        F: FnOnce() -> L,
        G: FnOnce() -> R,
    {
        match self {
            Self::Left(l) => (l, g()),
            Self::Right(r) => (f(), r),
            Self::Neither => (f(), g()),
            Self::Both(l, r) => (l, r),
        }
    }
    /// Return left value or given value.
    pub fn left_or(self, #[allow(unused)] other: L) -> L {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => other,
            Self::Neither => other,
            Self::Both(l, _) => l,
        }
    }
    /// Return left value or default value.
    pub fn left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => L::default(),
            Self::Neither => L::default(),
            Self::Both(l, _) => l,
        }
    }
    /// Return left value or computes it from a closure.
    pub fn left_or_else<F>(self, #[allow(unused)] f: F) -> L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => f(),
            Self::Neither => f(),
            Self::Both(l, _) => l,
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn left_and_then<F, L2>(self, f: F) -> crate::EitherOrNeither<L2, R>
    where
        F: FnOnce(L) -> crate::EitherOrNeither<L2, R>,
    {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => f(l),
            Self::Right(r) => Right(r),
            Self::Neither => Neither,
        }
    }
    pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
        match self {
            Self::Left(l2) => (l2, r),
            Self::Right(r2) => (l, r2),
            Self::Neither => (l, r),
        }
    }
    pub fn or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            Self::Left(l) => (l, R::default()),
            Self::Right(r) => (L::default(), r),
            Self::Neither => (L::default(), R::default()),
        }
    }
    pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
    where
        F: FnOnce() -> L,
        G: FnOnce() -> R,
    {
        match self {
            Self::Left(l) => (l, g()),
            Self::Right(r) => (f(), r),
            Self::Neither => (f(), g()),
        }
    }
    /// Return left value or given value.
    pub fn left_or(self, #[allow(unused)] other: L) -> L {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => other,
            Self::Neither => other,
        }
    }
    /// Return left value or default value.
    pub fn left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => L::default(),
            Self::Neither => L::default(),
        }
    }
    /// Return left value or computes it from a closure.
    pub fn left_or_else<F>(self, #[allow(unused)] f: F) -> L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => f(),
            Self::Neither => f(),
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn left_and_then<F, L2>(self, f: F) -> crate::EitherOrBoth<L2, R>
    where
        F: FnOnce(L) -> crate::EitherOrBoth<L2, R>,
    {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => f(l),
            Self::Right(r) => Right(r),
            Self::Both(l, _) => f(l),
        }
    }
    pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
        match self {
            Self::Left(l2) => (l2, r),
            Self::Right(r2) => (l, r2),
            Self::Both(l2, r2) => (l2, r2),
        }
    }
    pub fn or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            Self::Left(l) => (l, R::default()),
            Self::Right(r) => (L::default(), r),
            Self::Both(l, r) => (l, r),
        }
    }
    pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
    where
        F: FnOnce() -> L,
        G: FnOnce() -> R,
    {
        match self {
            Self::Left(l) => (l, g()),
            Self::Right(r) => (f(), r),
            Self::Both(l, r) => (l, r),
        }
    }
    /// Return left value or given value.
    pub fn left_or(self, #[allow(unused)] other: L) -> L {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => other,
            Self::Both(l, _) => l,
        }
    }
    /// Return left value or default value.
    pub fn left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => L::default(),
            Self::Both(l, _) => l,
        }
    }
    /// Return left value or computes it from a closure.
    pub fn left_or_else<F>(self, #[allow(unused)] f: F) -> L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => f(),
            Self::Both(l, _) => l,
        }
    }
}
impl<L, R> crate::NeitherOrBoth<L, R> {
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn left_and_then<F, L2>(self, f: F) -> crate::NeitherOrBoth<L2, R>
    where
        F: FnOnce(L) -> crate::NeitherOrBoth<L2, R>,
    {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, _) => f(l),
        }
    }
    pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
        match self {
            Self::Neither => (l, r),
            Self::Both(l2, r2) => (l2, r2),
        }
    }
    pub fn or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            Self::Neither => (L::default(), R::default()),
            Self::Both(l, r) => (l, r),
        }
    }
    pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
    where
        F: FnOnce() -> L,
        G: FnOnce() -> R,
    {
        match self {
            Self::Neither => (f(), g()),
            Self::Both(l, r) => (l, r),
        }
    }
    /// Return left value or given value.
    pub fn left_or(self, #[allow(unused)] other: L) -> L {
        match self {
            Self::Neither => other,
            Self::Both(l, _) => l,
        }
    }
    /// Return left value or default value.
    pub fn left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Self::Neither => L::default(),
            Self::Both(l, _) => l,
        }
    }
    /// Return left value or computes it from a closure.
    pub fn left_or_else<F>(self, #[allow(unused)] f: F) -> L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Neither => f(),
            Self::Both(l, _) => l,
        }
    }
}
impl<L, R> crate::Either<L, R> {
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn left_and_then<F, L2>(self, f: F) -> crate::Either<L2, R>
    where
        F: FnOnce(L) -> crate::Either<L2, R>,
    {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => f(l),
            Self::Right(r) => Right(r),
        }
    }
    pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
        match self {
            Self::Left(l2) => (l2, r),
            Self::Right(r2) => (l, r2),
        }
    }
    pub fn or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            Self::Left(l) => (l, R::default()),
            Self::Right(r) => (L::default(), r),
        }
    }
    pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
    where
        F: FnOnce() -> L,
        G: FnOnce() -> R,
    {
        match self {
            Self::Left(l) => (l, g()),
            Self::Right(r) => (f(), r),
        }
    }
    /// Return left value or given value.
    pub fn left_or(self, #[allow(unused)] other: L) -> L {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => other,
        }
    }
    /// Return left value or default value.
    pub fn left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => L::default(),
        }
    }
    /// Return left value or computes it from a closure.
    pub fn left_or_else<F>(self, #[allow(unused)] f: F) -> L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => f(),
        }
    }
}
impl<L, R> crate::Both<L, R> {
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn left_and_then<F, L2>(self, f: F) -> crate::Both<L2, R>
    where
        F: FnOnce(L) -> crate::Both<L2, R>,
    {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, _) => f(l),
        }
    }
    pub fn or(self, #[allow(unused)] l: L, #[allow(unused)] r: R) -> (L, R) {
        match self {
            Self::Both(l2, r2) => (l2, r2),
        }
    }
    pub fn or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            Self::Both(l, r) => (l, r),
        }
    }
    pub fn or_else<F, G>(self, #[allow(unused)] f: F, #[allow(unused)] g: G) -> (L, R)
    where
        F: FnOnce() -> L,
        G: FnOnce() -> R,
    {
        match self {
            Self::Both(l, r) => (l, r),
        }
    }
    /// Return left value or given value.
    pub fn left_or(self, #[allow(unused)] other: L) -> L {
        match self {
            Self::Both(l, _) => l,
        }
    }
    /// Return left value or default value.
    pub fn left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Self::Both(l, _) => l,
        }
    }
    /// Return left value or computes it from a closure.
    pub fn left_or_else<F>(self, #[allow(unused)] f: F) -> L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Both(l, _) => l,
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    /// Creates a new variant with references to the contained values.
    pub fn as_ref(&self) -> crate::EitherOrNeitherOrBoth<&L, &R> {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => Left(l),
            Self::Right(r) => Right(r),
            Self::Neither => Neither,
            Self::Both(l, r) => Both(l, r),
        }
    }
    /// Creates a new variant with mutable references to the contained values.
    pub fn as_mut(&mut self) -> crate::EitherOrNeitherOrBoth<&mut L, &mut R> {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => Left(l),
            Self::Right(r) => Right(r),
            Self::Neither => Neither,
            Self::Both(l, r) => Both(l, r),
        }
    }
    /// Creates a new pinned variant with references to the contained values.
    pub fn as_pin_ref(
        self: Pin<&Self>,
    ) -> crate::EitherOrNeitherOrBoth<Pin<&L>, Pin<&R>> {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                Self::Left(l) => Left(Pin::new_unchecked(l)),
                Self::Right(r) => Right(Pin::new_unchecked(r)),
                Self::Neither => Neither,
                Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }
    /// Creates a new pinned variant with mutable references to the contained values.
    pub fn as_pin_mut(
        self: Pin<&mut Self>,
    ) -> crate::EitherOrNeitherOrBoth<Pin<&mut L>, Pin<&mut R>> {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        unsafe {
            match self.get_unchecked_mut() {
                Self::Left(l) => Left(Pin::new_unchecked(l)),
                Self::Right(r) => Right(Pin::new_unchecked(r)),
                Self::Neither => Neither,
                Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    /// Creates a new variant with references to the contained values.
    pub fn as_ref(&self) -> crate::EitherOrNeither<&L, &R> {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => Left(l),
            Self::Right(r) => Right(r),
            Self::Neither => Neither,
        }
    }
    /// Creates a new variant with mutable references to the contained values.
    pub fn as_mut(&mut self) -> crate::EitherOrNeither<&mut L, &mut R> {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => Left(l),
            Self::Right(r) => Right(r),
            Self::Neither => Neither,
        }
    }
    /// Creates a new pinned variant with references to the contained values.
    pub fn as_pin_ref(self: Pin<&Self>) -> crate::EitherOrNeither<Pin<&L>, Pin<&R>> {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                Self::Left(l) => Left(Pin::new_unchecked(l)),
                Self::Right(r) => Right(Pin::new_unchecked(r)),
                Self::Neither => Neither,
            }
        }
    }
    /// Creates a new pinned variant with mutable references to the contained values.
    pub fn as_pin_mut(
        self: Pin<&mut Self>,
    ) -> crate::EitherOrNeither<Pin<&mut L>, Pin<&mut R>> {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        unsafe {
            match self.get_unchecked_mut() {
                Self::Left(l) => Left(Pin::new_unchecked(l)),
                Self::Right(r) => Right(Pin::new_unchecked(r)),
                Self::Neither => Neither,
            }
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    /// Creates a new variant with references to the contained values.
    pub fn as_ref(&self) -> crate::EitherOrBoth<&L, &R> {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => Left(l),
            Self::Right(r) => Right(r),
            Self::Both(l, r) => Both(l, r),
        }
    }
    /// Creates a new variant with mutable references to the contained values.
    pub fn as_mut(&mut self) -> crate::EitherOrBoth<&mut L, &mut R> {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => Left(l),
            Self::Right(r) => Right(r),
            Self::Both(l, r) => Both(l, r),
        }
    }
    /// Creates a new pinned variant with references to the contained values.
    pub fn as_pin_ref(self: Pin<&Self>) -> crate::EitherOrBoth<Pin<&L>, Pin<&R>> {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                Self::Left(l) => Left(Pin::new_unchecked(l)),
                Self::Right(r) => Right(Pin::new_unchecked(r)),
                Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }
    /// Creates a new pinned variant with mutable references to the contained values.
    pub fn as_pin_mut(
        self: Pin<&mut Self>,
    ) -> crate::EitherOrBoth<Pin<&mut L>, Pin<&mut R>> {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        unsafe {
            match self.get_unchecked_mut() {
                Self::Left(l) => Left(Pin::new_unchecked(l)),
                Self::Right(r) => Right(Pin::new_unchecked(r)),
                Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }
}
impl<L, R> crate::NeitherOrBoth<L, R> {
    /// Creates a new variant with references to the contained values.
    pub fn as_ref(&self) -> crate::NeitherOrBoth<&L, &R> {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, r) => Both(l, r),
        }
    }
    /// Creates a new variant with mutable references to the contained values.
    pub fn as_mut(&mut self) -> crate::NeitherOrBoth<&mut L, &mut R> {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, r) => Both(l, r),
        }
    }
    /// Creates a new pinned variant with references to the contained values.
    pub fn as_pin_ref(self: Pin<&Self>) -> crate::NeitherOrBoth<Pin<&L>, Pin<&R>> {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                Self::Neither => Neither,
                Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }
    /// Creates a new pinned variant with mutable references to the contained values.
    pub fn as_pin_mut(
        self: Pin<&mut Self>,
    ) -> crate::NeitherOrBoth<Pin<&mut L>, Pin<&mut R>> {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        unsafe {
            match self.get_unchecked_mut() {
                Self::Neither => Neither,
                Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }
}
impl<L, R> crate::Either<L, R> {
    /// Creates a new variant with references to the contained values.
    pub fn as_ref(&self) -> crate::Either<&L, &R> {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => Left(l),
            Self::Right(r) => Right(r),
        }
    }
    /// Creates a new variant with mutable references to the contained values.
    pub fn as_mut(&mut self) -> crate::Either<&mut L, &mut R> {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => Left(l),
            Self::Right(r) => Right(r),
        }
    }
    /// Creates a new pinned variant with references to the contained values.
    pub fn as_pin_ref(self: Pin<&Self>) -> crate::Either<Pin<&L>, Pin<&R>> {
        #[allow(unused)]
        use crate::Either::*;
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                Self::Left(l) => Left(Pin::new_unchecked(l)),
                Self::Right(r) => Right(Pin::new_unchecked(r)),
            }
        }
    }
    /// Creates a new pinned variant with mutable references to the contained values.
    pub fn as_pin_mut(self: Pin<&mut Self>) -> crate::Either<Pin<&mut L>, Pin<&mut R>> {
        #[allow(unused)]
        use crate::Either::*;
        unsafe {
            match self.get_unchecked_mut() {
                Self::Left(l) => Left(Pin::new_unchecked(l)),
                Self::Right(r) => Right(Pin::new_unchecked(r)),
            }
        }
    }
}
impl<L, R> crate::Both<L, R> {
    /// Creates a new variant with references to the contained values.
    pub fn as_ref(&self) -> crate::Both<&L, &R> {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, r) => Both(l, r),
        }
    }
    /// Creates a new variant with mutable references to the contained values.
    pub fn as_mut(&mut self) -> crate::Both<&mut L, &mut R> {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, r) => Both(l, r),
        }
    }
    /// Creates a new pinned variant with references to the contained values.
    pub fn as_pin_ref(self: Pin<&Self>) -> crate::Both<Pin<&L>, Pin<&R>> {
        #[allow(unused)]
        use crate::Both::*;
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }
    /// Creates a new pinned variant with mutable references to the contained values.
    pub fn as_pin_mut(self: Pin<&mut Self>) -> crate::Both<Pin<&mut L>, Pin<&mut R>> {
        #[allow(unused)]
        use crate::Both::*;
        unsafe {
            match self.get_unchecked_mut() {
                Self::Both(l, r) => Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }
}
impl crate::Neither {
    /// Creates a new variant with references to the contained values.
    pub fn as_ref(&self) -> crate::Neither {
        #[allow(unused)]
        use crate::Neither::*;
        match self {
            Self::Neither => Neither,
        }
    }
    /// Creates a new variant with mutable references to the contained values.
    pub fn as_mut(&mut self) -> crate::Neither {
        #[allow(unused)]
        use crate::Neither::*;
        match self {
            Self::Neither => Neither,
        }
    }
    /// Creates a new pinned variant with references to the contained values.
    pub fn as_pin_ref(self: Pin<&Self>) -> crate::Neither {
        #[allow(unused)]
        use crate::Neither::*;
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                Self::Neither => Neither,
            }
        }
    }
    /// Creates a new pinned variant with mutable references to the contained values.
    pub fn as_pin_mut(self: Pin<&mut Self>) -> crate::Neither {
        #[allow(unused)]
        use crate::Neither::*;
        unsafe {
            match self.get_unchecked_mut() {
                Self::Neither => Neither,
            }
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    pub fn as_deref(&self) -> crate::EitherOrNeitherOrBoth<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => Left(l.deref()),
            Self::Right(r) => Right(r.deref()),
            Self::Neither => Neither,
            Self::Both(l, r) => Both(l.deref(), r.deref()),
        }
    }
    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    pub fn as_deref_mut(
        &mut self,
    ) -> crate::EitherOrNeitherOrBoth<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => Left(l.deref_mut()),
            Self::Right(r) => Right(r.deref_mut()),
            Self::Neither => Neither,
            Self::Both(l, r) => Both(l.deref_mut(), r.deref_mut()),
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    pub fn as_deref(&self) -> crate::EitherOrNeither<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => Left(l.deref()),
            Self::Right(r) => Right(r.deref()),
            Self::Neither => Neither,
        }
    }
    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    pub fn as_deref_mut(
        &mut self,
    ) -> crate::EitherOrNeither<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => Left(l.deref_mut()),
            Self::Right(r) => Right(r.deref_mut()),
            Self::Neither => Neither,
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    pub fn as_deref(&self) -> crate::EitherOrBoth<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => Left(l.deref()),
            Self::Right(r) => Right(r.deref()),
            Self::Both(l, r) => Both(l.deref(), r.deref()),
        }
    }
    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    pub fn as_deref_mut(&mut self) -> crate::EitherOrBoth<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => Left(l.deref_mut()),
            Self::Right(r) => Right(r.deref_mut()),
            Self::Both(l, r) => Both(l.deref_mut(), r.deref_mut()),
        }
    }
}
impl<L, R> crate::NeitherOrBoth<L, R> {
    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    pub fn as_deref(&self) -> crate::NeitherOrBoth<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, r) => Both(l.deref(), r.deref()),
        }
    }
    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    pub fn as_deref_mut(
        &mut self,
    ) -> crate::NeitherOrBoth<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, r) => Both(l.deref_mut(), r.deref_mut()),
        }
    }
}
impl<L, R> crate::Either<L, R> {
    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    pub fn as_deref(&self) -> crate::Either<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => Left(l.deref()),
            Self::Right(r) => Right(r.deref()),
        }
    }
    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    pub fn as_deref_mut(&mut self) -> crate::Either<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => Left(l.deref_mut()),
            Self::Right(r) => Right(r.deref_mut()),
        }
    }
}
impl<L, R> crate::Both<L, R> {
    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    pub fn as_deref(&self) -> crate::Both<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, r) => Both(l.deref(), r.deref()),
        }
    }
    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    pub fn as_deref_mut(&mut self) -> crate::Both<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, r) => Both(l.deref_mut(), r.deref_mut()),
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    pub fn into_left(self) -> L
    where
        R: Into<L>,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => r.into(),
            Self::Both(l, _) => l,
        }
    }
}
impl<L, R> crate::Either<L, R> {
    pub fn into_left(self) -> L
    where
        R: Into<L>,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => r.into(),
        }
    }
}
impl<L, R> crate::Both<L, R> {
    pub fn into_left(self) -> L
    where
        R: Into<L>,
    {
        match self {
            Self::Both(l, _) => l,
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    pub fn map<F, G, L2, R2>(self, f: F, g: G) -> crate::EitherOrNeitherOrBoth<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => Left(f(l)),
            Self::Right(r) => Right(g(r)),
            Self::Neither => Neither,
            Self::Both(l, r) => Both(f(l), g(r)),
        }
    }
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn map_left<F, L2>(self, f: F) -> crate::EitherOrNeitherOrBoth<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => Left(f(l)),
            Self::Right(r) => Right(r),
            Self::Neither => Neither,
            Self::Both(l, r) => Both(f(l), r),
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    pub fn map<F, G, L2, R2>(self, f: F, g: G) -> crate::EitherOrNeither<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => Left(f(l)),
            Self::Right(r) => Right(g(r)),
            Self::Neither => Neither,
        }
    }
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn map_left<F, L2>(self, f: F) -> crate::EitherOrNeither<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => Left(f(l)),
            Self::Right(r) => Right(r),
            Self::Neither => Neither,
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    pub fn map<F, G, L2, R2>(self, f: F, g: G) -> crate::EitherOrBoth<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => Left(f(l)),
            Self::Right(r) => Right(g(r)),
            Self::Both(l, r) => Both(f(l), g(r)),
        }
    }
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn map_left<F, L2>(self, f: F) -> crate::EitherOrBoth<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => Left(f(l)),
            Self::Right(r) => Right(r),
            Self::Both(l, r) => Both(f(l), r),
        }
    }
}
impl<L, R> crate::NeitherOrBoth<L, R> {
    pub fn map<F, G, L2, R2>(self, f: F, g: G) -> crate::NeitherOrBoth<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, r) => Both(f(l), g(r)),
        }
    }
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn map_left<F, L2>(self, f: F) -> crate::NeitherOrBoth<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, r) => Both(f(l), r),
        }
    }
}
impl<L, R> crate::Either<L, R> {
    pub fn map<F, G, L2, R2>(self, f: F, g: G) -> crate::Either<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => Left(f(l)),
            Self::Right(r) => Right(g(r)),
        }
    }
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn map_left<F, L2>(self, f: F) -> crate::Either<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => Left(f(l)),
            Self::Right(r) => Right(r),
        }
    }
}
impl<L, R> crate::Both<L, R> {
    pub fn map<F, G, L2, R2>(self, f: F, g: G) -> crate::Both<L2, R2>
    where
        F: FnOnce(L) -> L2,
        G: FnOnce(R) -> R2,
    {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, r) => Both(f(l), g(r)),
        }
    }
    /// Apply the function `f` on the value in the left position if it is present,
    /// and then rewrap the result in a same variant of the new type.
    pub fn map_left<F, L2>(self, f: F) -> crate::Both<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, r) => Both(f(l), r),
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    pub fn map_with<Ctx, F, G, L2, R2>(
        self,
        ctx: Ctx,
        f: F,
        g: G,
    ) -> crate::EitherOrNeitherOrBoth<L2, R2>
    where
        Ctx: Clone,
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        #[allow(unused)]
        use crate::EitherOrNeitherOrBoth::*;
        match self {
            Self::Left(l) => Left(f(ctx.clone(), l)),
            Self::Right(r) => Right(g(ctx.clone(), r)),
            Self::Neither => Neither,
            Self::Both(l, r) => Both(f(ctx.clone(), l), g(ctx.clone(), r)),
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    pub fn map_with<Ctx, F, G, L2, R2>(
        self,
        ctx: Ctx,
        f: F,
        g: G,
    ) -> crate::EitherOrNeither<L2, R2>
    where
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        #[allow(unused)]
        use crate::EitherOrNeither::*;
        match self {
            Self::Left(l) => Left(f(ctx, l)),
            Self::Right(r) => Right(g(ctx, r)),
            Self::Neither => Neither,
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    pub fn map_with<Ctx, F, G, L2, R2>(
        self,
        ctx: Ctx,
        f: F,
        g: G,
    ) -> crate::EitherOrBoth<L2, R2>
    where
        Ctx: Clone,
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        #[allow(unused)]
        use crate::EitherOrBoth::*;
        match self {
            Self::Left(l) => Left(f(ctx.clone(), l)),
            Self::Right(r) => Right(g(ctx.clone(), r)),
            Self::Both(l, r) => Both(f(ctx.clone(), l), g(ctx.clone(), r)),
        }
    }
}
impl<L, R> crate::NeitherOrBoth<L, R> {
    pub fn map_with<Ctx, F, G, L2, R2>(
        self,
        ctx: Ctx,
        f: F,
        g: G,
    ) -> crate::NeitherOrBoth<L2, R2>
    where
        Ctx: Clone,
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        #[allow(unused)]
        use crate::NeitherOrBoth::*;
        match self {
            Self::Neither => Neither,
            Self::Both(l, r) => Both(f(ctx.clone(), l), g(ctx.clone(), r)),
        }
    }
}
impl<L, R> crate::Either<L, R> {
    pub fn map_with<Ctx, F, G, L2, R2>(
        self,
        ctx: Ctx,
        f: F,
        g: G,
    ) -> crate::Either<L2, R2>
    where
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        #[allow(unused)]
        use crate::Either::*;
        match self {
            Self::Left(l) => Left(f(ctx, l)),
            Self::Right(r) => Right(g(ctx, r)),
        }
    }
}
impl<L, R> crate::Both<L, R> {
    pub fn map_with<Ctx, F, G, L2, R2>(self, ctx: Ctx, f: F, g: G) -> crate::Both<L2, R2>
    where
        Ctx: Clone,
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        #[allow(unused)]
        use crate::Both::*;
        match self {
            Self::Both(l, r) => Both(f(ctx.clone(), l), g(ctx.clone(), r)),
        }
    }
}
impl<L, R> crate::EitherOrNeitherOrBoth<L, R> {
    /// Ensure the left value is present. If possible, keep the right value too.
    ///
    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can "promote" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given value and return it.
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
    pub fn ensure_left_with<F>(&mut self, f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => {
                let new_l = f();
                replace_with_or_abort(
                    self,
                    move |this| {
                        let Self::Right(r) = this else {
                            ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )
                        };
                        Self::Both(new_l, r)
                    },
                );
                let Self::Both(l, _) = self else {
                    ::core::panicking::panic("internal error: entered unreachable code")
                };
                l
            }
            Self::Neither => {
                let new_l = f();
                replace_with_or_abort(
                    self,
                    move |this| {
                        let Self::Neither = this else {
                            ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )
                        };
                        Self::Left(new_l)
                    },
                );
                let Self::Left(l) = self else {
                    ::core::panicking::panic("internal error: entered unreachable code")
                };
                l
            }
            Self::Both(l, _) => l,
        }
    }
}
impl<L, R> crate::EitherOrNeither<L, R> {
    /// Ensure the left value is present. If possible, keep the right value too.
    ///
    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can "promote" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given value and return it.
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
    pub fn ensure_left_with<F>(&mut self, f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => {
                *self = Self::Left(f());
                let Self::Left(l) = self else {
                    ::core::panicking::panic("internal error: entered unreachable code")
                };
                l
            }
            Self::Neither => {
                let new_l = f();
                replace_with_or_abort(
                    self,
                    move |this| {
                        let Self::Neither = this else {
                            ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )
                        };
                        Self::Left(new_l)
                    },
                );
                let Self::Left(l) = self else {
                    ::core::panicking::panic("internal error: entered unreachable code")
                };
                l
            }
        }
    }
}
impl<L, R> crate::EitherOrBoth<L, R> {
    /// Ensure the left value is present. If possible, keep the right value too.
    ///
    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can "promote" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given value and return it.
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
    pub fn ensure_left_with<F>(&mut self, f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => {
                let new_l = f();
                replace_with_or_abort(
                    self,
                    move |this| {
                        let Self::Right(r) = this else {
                            ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )
                        };
                        Self::Both(new_l, r)
                    },
                );
                let Self::Both(l, _) = self else {
                    ::core::panicking::panic("internal error: entered unreachable code")
                };
                l
            }
            Self::Both(l, _) => l,
        }
    }
}
impl<L, R> crate::Either<L, R> {
    /// Ensure the left value is present. If possible, keep the right value too.
    ///
    /// If the left value is already present, do nothing and return the left value.
    /// If the left value is not present, then:
    ///   - If it can "promote" the variant (`Right` => `Both`, `Neither` => `Left`), then do so.
    ///   - Otherwise, set the variant to `Left` (dispose the right value even if it is present).
    /// And set the left value to the given value and return it.
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
    pub fn ensure_left_with<F>(&mut self, f: F) -> &mut L
    where
        F: FnOnce() -> L,
    {
        match self {
            Self::Left(l) => l,
            Self::Right(_) => {
                *self = Self::Left(f());
                let Self::Left(l) = self else {
                    ::core::panicking::panic("internal error: entered unreachable code")
                };
                l
            }
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
    pub fn map_either_with<Ctx, F, G, L2, R2>(
        self,
        ctx: Ctx,
        f: F,
        g: G,
    ) -> Either<L2, R2>
    where
        F: FnOnce(Ctx, L) -> L2,
        G: FnOnce(Ctx, R) -> R2,
    {
        Self::map_with(self, ctx, f, g)
    }
}
