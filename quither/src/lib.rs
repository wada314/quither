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
mod conv;
mod factor;
mod get_or_insert;
mod getters;
mod into;
pub mod iter;
mod map;
mod std_impls;

// Pair types, essentially comibinations of `Either`, `Neither`, and `Both`.

/// An enum that represents either a left (`Left(L)`) or right (`Right(R)`) value.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// An enum that represents a single `Neither` value.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Neither {
    Neither,
}

/// An enum that represents a pair of values (`Both(L, R)`).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Both<L, R> {
    Both(L, R),
}

/// An enum that represents either a left (`Left(L)`) or right (`Right(R)`) or neither (`Neither`).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum EitherOrNeither<L, R> {
    Neither,
    Left(L),
    Right(R),
}

/// An enum that represents either a left (`Left(L)`) or right (`Right(R)`) or both (`Both(L, R)`).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum EitherOrBoth<L, R> {
    Left(L),
    Right(R),
    Both(L, R),
}

/// An enum that represents a single `Neither` value or a pair of values (`Both(L, R)`).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NeitherOrBoth<L, R> {
    Neither,
    Both(L, R),
}

/// An enum that represents either an empty value, left value, right value, or both values.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Quither<L, R> {
    Neither,
    Left(L),
    Right(R),
    Both(L, R),
}

impl<T> Either<T, T> {
    pub fn into_inner(self) -> T {
        match self {
            Either::Left(l) => l,
            Either::Right(r) => r,
        }
    }
}
