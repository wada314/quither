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
// CStr is available in core too after rustc version 1.64.0.
#[cfg(feature = "use_std")]
use ::std::ffi::CStr;
#[cfg(feature = "use_std")]
use ::std::ffi::OsStr;
#[cfg(feature = "use_std")]
use ::std::path::Path;

#[quither]
impl<L, R> Xither<L, R> {
    /// Creates a new variant with references to the contained values.
    #[quither(has_either || has_neither || has_both)]
    pub fn as_ref(&self) -> Xither<&L, &R> {
        match self {
            #[either]
            Self::Left(l) => Xither::Left(l),
            #[either]
            Self::Right(r) => Xither::Right(r),
            #[neither]
            Self::Neither => Xither::Neither,
            #[both]
            Self::Both(l, r) => Xither::Both(l, r),
        }
    }

    /// Creates a new variant with mutable references to the contained values.
    #[quither(has_either || has_neither || has_both)]
    pub fn as_mut(&mut self) -> Xither<&mut L, &mut R> {
        match self {
            #[either]
            Self::Left(l) => Xither::Left(l),
            #[either]
            Self::Right(r) => Xither::Right(r),
            #[neither]
            Self::Neither => Xither::Neither,
            #[both]
            Self::Both(l, r) => Xither::Both(l, r),
        }
    }

    /// Creates a new pinned variant with references to the contained values.
    #[quither(has_either || has_neither || has_both)]
    pub fn as_pin_ref(self: Pin<&Self>) -> Xither<Pin<&L>, Pin<&R>> {
        // SAFETY: This is safe because:
        // 1. We never move the inner values - we only create a new reference to them
        // 2. The original Pin<&Self> guarantees that the original data won't move
        // 3. We're maintaining the pinning invariant by wrapping the references in Pin
        // 4. The lifetime of the output references is tied to the input lifetime
        #[allow(unused)]
        unsafe {
            match self.get_ref() {
                #[either]
                Self::Left(l) => Xither::Left(Pin::new_unchecked(l)),
                #[either]
                Self::Right(r) => Xither::Right(Pin::new_unchecked(r)),
                #[neither]
                Self::Neither => Xither::Neither,
                #[both]
                Self::Both(l, r) => Xither::Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }

    /// Creates a new pinned variant with mutable references to the contained values.
    #[quither(has_either || has_neither || has_both)]
    pub fn as_pin_mut(self: Pin<&mut Self>) -> Xither<Pin<&mut L>, Pin<&mut R>> {
        // SAFETY: This is safe because:
        // 1. We never move the inner values out of the pin
        // 2. We're creating new Pin instances from references to pinned data
        // 3. The original Pin<&mut Self> guarantees unique access
        // 4. We maintain the pinning invariant by wrapping the mutable references in Pin
        // 5. get_unchecked_mut is safe here as we have exclusive access via Pin<&mut Self>
        unsafe {
            match self.get_unchecked_mut() {
                #[either]
                Self::Left(l) => Xither::Left(Pin::new_unchecked(l)),
                #[either]
                Self::Right(r) => Xither::Right(Pin::new_unchecked(r)),
                #[neither]
                Self::Neither => Xither::Neither,
                #[both]
                Self::Both(l, r) => Xither::Both(Pin::new_unchecked(l), Pin::new_unchecked(r)),
            }
        }
    }

    /// Returns a new value using the `Deref` trait for `L` and `R` values.
    #[quither(has_either || has_both)]
    pub fn as_deref(&self) -> Xither<&L::Target, &R::Target>
    where
        L: Deref,
        R: Deref,
    {
        match self {
            #[either]
            Self::Left(l) => Xither::Left(l.deref()),
            #[either]
            Self::Right(r) => Xither::Right(r.deref()),
            #[neither]
            Self::Neither => Xither::Neither,
            #[both]
            Self::Both(l, r) => Xither::Both(l.deref(), r.deref()),
        }
    }

    /// Returns a new value using the `DerefMut` trait for `L` and `R` values.
    #[quither(has_either || has_both)]
    pub fn as_deref_mut(&mut self) -> Xither<&mut L::Target, &mut R::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        match self {
            #[either]
            Self::Left(l) => Xither::Left(l.deref_mut()),
            #[either]
            Self::Right(r) => Xither::Right(r.deref_mut()),
            #[neither]
            Self::Neither => Xither::Neither,
            #[both]
            Self::Both(l, r) => Xither::Both(l.deref_mut(), r.deref_mut()),
        }
    }
}

impl<T, L, R> AsRef<T> for Either<L, R>
where
    L: AsRef<T>,
    R: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        match self {
            Self::Left(l) => l.as_ref(),
            Self::Right(r) => r.as_ref(),
        }
    }
}

impl<T, L, R> AsMut<T> for Either<L, R>
where
    L: AsMut<T>,
    R: AsMut<T>,
{
    fn as_mut(&mut self) -> &mut T {
        match self {
            Self::Left(l) => l.as_mut(),
            Self::Right(r) => r.as_mut(),
        }
    }
}

impl<T, L, R> AsRef<[T]> for Either<L, R>
where
    L: AsRef<[T]>,
    R: AsRef<[T]>,
{
    fn as_ref(&self) -> &[T] {
        match self {
            Self::Left(l) => l.as_ref(),
            Self::Right(r) => r.as_ref(),
        }
    }
}

impl<T, L, R> AsMut<[T]> for Either<L, R>
where
    L: AsMut<[T]>,
    R: AsMut<[T]>,
{
    fn as_mut(&mut self) -> &mut [T] {
        match self {
            Self::Left(l) => l.as_mut(),
            Self::Right(r) => r.as_mut(),
        }
    }
}

macro_rules! impl_as_ref_and_mut {
    ($target:ty $(, $attrs:meta)*) => {
        $(#[$attrs])*
        impl<L, R> AsRef<$target> for Either<L, R>
        where
            L: AsRef<$target>,
            R: AsRef<$target>,
        {
            fn as_ref(&self) -> &$target {
                match self {
                    Self::Left(l) => l.as_ref(),
                    Self::Right(r) => r.as_ref(),
                }
            }
        }
        $(#[$attrs])*
        impl<L, R> AsMut<$target> for Either<L, R>
        where
            L: AsMut<$target>,
            R: AsMut<$target>,
        {
            fn as_mut(&mut self) -> &mut $target {
                match self {
                    Self::Left(l) => l.as_mut(),
                    Self::Right(r) => r.as_mut(),
                }
            }
        }
    };
}

impl_as_ref_and_mut!(str);
impl_as_ref_and_mut!(
    Path,
    cfg(feature = "use_std"),
    doc = "Needs crate feature `use_std`"
);
impl_as_ref_and_mut!(
    CStr,
    cfg(feature = "use_std"),
    doc = "Needs crate feature `use_std`"
);
impl_as_ref_and_mut!(
    OsStr,
    cfg(feature = "use_std"),
    doc = "Needs crate feature `use_std`"
);
