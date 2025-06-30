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
impl<L, R> Xither<L, R> {
    /// Returns true if the value contains a left value.
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

    /// Returns true if the value contains a right value.
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

    /// Returns true if the value is the left variant.
    pub fn is_left(&self) -> bool {
        match self {
            #[either]
            Self::Left(_) => true,
            #[allow(unused)]
            _ => false,
        }
    }

    /// Returns true if the value is the right variant.
    pub fn is_right(&self) -> bool {
        match self {
            #[either]
            Self::Right(_) => true,
            #[allow(unused)]
            _ => false,
        }
    }

    /// Returns true if the value is the neither variant.
    pub fn is_neither(&self) -> bool {
        match self {
            #[neither]
            Self::Neither => true,
            #[allow(unused)]
            _ => false,
        }
    }

    /// Returns true if the value is the both variant.
    pub fn is_both(&self) -> bool {
        match self {
            #[both]
            Self::Both(_, _) => true,
            #[allow(unused)]
            _ => false,
        }
    }

    /// Returns `Some` if the left value is present, or `None` otherwise.
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

    /// Returns `Some` if the right value is present, or `None` otherwise.
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

    /// Returns both values as a tuple of `Option`s.
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

    /// Returns the left value if the variant is exactly left.
    #[quither(has_either || has_both)]
    pub fn just_left(self) -> Option<L> {
        match self {
            #[either]
            Self::Left(l) => Some(l),
            #[allow(unused)]
            _ => None,
        }
    }

    /// Returns the right value if the variant is exactly right.
    #[quither(has_either || has_both)]
    pub fn just_right(self) -> Option<R> {
        match self {
            #[either]
            Self::Right(r) => Some(r),
            #[allow(unused)]
            _ => None,
        }
    }

    /// Returns both values as a tuple if the variant is both.
    #[quither(has_either || has_both)]
    pub fn both(self) -> Option<(L, R)> {
        match self {
            #[both]
            Self::Both(l, r) => Some((l, r)),
            #[allow(unused)]
            _ => None,
        }
    }

    /// Returns a new value with left and right swapped.
    pub fn flip(self) -> Xither<R, L> {
        match self {
            #[either]
            Self::Left(l) => Xither::Right(l),
            #[either]
            Self::Right(r) => Xither::Left(r),
            #[neither]
            Self::Neither => Xither::Neither,
            #[both]
            Self::Both(l, r) => Xither::Both(r, l),
        }
    }

    /// Unwraps the left value, panicking if not present.
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

    /// Unwraps the right value, panicking if not present.
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

    /// Unwraps both values as a tuple, panicking if not present.
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

    /// Unwraps the left value, panicking with a custom message if not present.
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

    /// Unwraps the right value, panicking with a custom message if not present.
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

    /// Unwraps both values as a tuple, panicking with a custom message if not present.
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
