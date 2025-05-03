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
mod factor;
mod get_or_insert;
mod getters;
mod map;

use ::quither_proc_macros::quither;

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
}

#[quither]
impl<T> Quither<T, T> {}

/// `Either` type exclusive methods.
impl<L, R> Either<L, R> {
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
}

impl<T> Either<T, T> {
    pub fn into_inner(self) -> T {
        match self {
            Either::Left(l) => l,
            Either::Right(r) => r,
        }
    }
}
