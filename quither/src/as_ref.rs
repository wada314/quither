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
use ::core::ops::{Deref, DerefMut};
use ::core::pin::Pin;
use ::quither_proc_macros::quither;

#[quither]
impl<L, R> Quither<L, R> {
    /// Creates a new variant with references to the contained values.
    #[quither(has_either || has_neither || has_both)]
    pub fn as_ref(&self) -> Quither<&L, &R> {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l),
            #[either]
            Self::Right(r) => Quither::Right(r),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(l, r),
        }
    }

    /// Creates a new variant with mutable references to the contained values.
    #[quither(has_either || has_neither || has_both)]
    pub fn as_mut(&mut self) -> Quither<&mut L, &mut R> {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l),
            #[either]
            Self::Right(r) => Quither::Right(r),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(l, r),
        }
    }

    /// Creates a new pinned variant with references to the contained values.
    #[quither(has_either || has_neither || has_both)]
    pub fn as_pin_ref(self: Pin<&Self>) -> Quither<Pin<&L>, Pin<&R>> {
        // SAFETY: This is safe because:
        // 1. We never move the inner values - we only create a new reference to them
        // 2. The original Pin<&Self> guarantees that the original data won't move
        // 3. We're maintaining the pinning invariant by wrapping the references in Pin
        // 4. The lifetime of the output references is tied to the input lifetime
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                #[either]
                Self::Left(l) => Quither::Left(Pin::new_unchecked(l)),
                #[either]
                Self::Right(r) => Quither::Right(Pin::new_unchecked(r)),
                #[neither]
                Self::Neither => Quither::Neither,
                #[both]
                Self::Both(l, r) => Quither::Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }

    /// Creates a new pinned variant with mutable references to the contained values.
    #[quither(has_either || has_neither || has_both)]
    pub fn as_pin_mut(self: Pin<&mut Self>) -> Quither<Pin<&mut L>, Pin<&mut R>> {
        // SAFETY: This is safe because:
        // 1. We never move the inner values out of the pin
        // 2. We're creating new Pin instances from references to pinned data
        // 3. The original Pin<&mut Self> guarantees unique access
        // 4. We maintain the pinning invariant by wrapping the mutable references in Pin
        // 5. get_unchecked_mut is safe here as we have exclusive access via Pin<&mut Self>
        unsafe {
            match self.get_unchecked_mut() {
                #[either]
                Self::Left(l) => Quither::Left(Pin::new_unchecked(l)),
                #[either]
                Self::Right(r) => Quither::Right(Pin::new_unchecked(r)),
                #[neither]
                Self::Neither => Quither::Neither,
                #[both]
                Self::Both(l, r) => Quither::Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }

    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    #[quither(has_either || has_both)]
    pub fn as_deref(&self) -> Quither<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l.deref()),
            #[either]
            Self::Right(r) => Quither::Right(r.deref()),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(l.deref(), r.deref()),
        }
    }

    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    #[quither(has_either || has_both)]
    pub fn as_deref_mut(&mut self) -> Quither<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        match self {
            #[either]
            Self::Left(l) => Quither::Left(l.deref_mut()),
            #[either]
            Self::Right(r) => Quither::Right(r.deref_mut()),
            #[neither]
            Self::Neither => Quither::Neither,
            #[both]
            Self::Both(l, r) => Quither::Both(l.deref_mut(), r.deref_mut()),
        }
    }
}
