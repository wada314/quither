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
use ::core::fmt::Debug;
use quither_proc_macros::quither;

#[quither]
impl<L, R> Quither<L, R> {
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
    #[quither(has_either || has_both)]
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
    #[quither(has_either || has_both)]
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

    #[quither(has_either || has_both)]
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
    #[quither(has_either || has_both)]
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
    #[quither(has_either || has_both)]
    pub fn just_right(self) -> Option<R> {
        match self {
            #[either]
            Self::Right(r) => Some(r),
            #[allow(unused)]
            _ => None,
        }
    }

    #[quither(has_either || has_both)]
    pub fn both(self) -> Option<(L, R)> {
        match self {
            #[both]
            Self::Both(l, r) => Some((l, r)),
            #[allow(unused)]
            _ => None,
        }
    }

    pub fn flip(self) -> Quither<R, L> {
        match self {
            #[either]
            Self::Left(l) => Quither::Right(l),
            #[either]
            Self::Right(r) => Quither::Left(r),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(r, l),
        }
    }

    /// Unwrap the left value from the variant.
    ///
    /// # Panics
    ///
    /// - If the variant is something not containing a left value.
    #[quither(has_either || has_both)]
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
    #[quither(has_either || has_both)]
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

    #[quither(has_either || has_both)]
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
    #[quither(has_either || has_both)]
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
    #[quither(has_either || has_both)]
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

    #[quither(has_either || has_both)]
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
}
