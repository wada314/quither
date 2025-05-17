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

//! A file to implement standard traits for `Quither` types.
//!
//! Note some of the `std` traits like `AsRef`, `AsMut` are in other file ([`as_ref.rs`]).

use super::*;
use ::core::error::Error;
use ::core::fmt::Display;
use ::core::ops::{Deref, DerefMut};
use ::core::pin::Pin;
use ::core::task::{Context, Poll};
use ::quither_proc_macros::quither;
#[cfg(feature = "use_std")]
use ::std::io::{BufRead, Read, Result as IoResult, Seek, SeekFrom};

/// Provides Read, chaining Left then Right for Both, otherwise delegating.
///
/// Requires both `L: Read` and `R: Read`. For the `Left`, `Right`, or `Neither` variants, this
/// simply delegates to the inner value or returns `Ok(0)`. For the `Both` variant, it first tries
/// to read from `Left`; if that returns 0, it then reads from `Right`. This behavior differs from
/// `std::io::Read::chain`, which never retries the first reader after it returns 0 bytes.
#[cfg(feature = "use_std")]
#[quither]
impl<L, R> Read for Quither<L, R>
where
    L: Read,
    R: Read,
{
    fn read(&mut self, #[allow(unused)] buf: &mut [u8]) -> IoResult<usize> {
        match self {
            #[either]
            Self::Left(l) => l.read(buf),
            #[either]
            Self::Right(r) => r.read(buf),
            #[neither]
            Self::Neither => Ok(0),
            #[both]
            Self::Both(l, r) => {
                if buf.is_empty() {
                    return Ok(0);
                }
                let left_len = l.read(buf)?;
                if left_len == 0 {
                    r.read(buf)
                } else {
                    Ok(left_len)
                }
            }
        }
    }
}

/// Provides BufRead, but only for types that do not include the Both variant.
///
/// Requires both `L: BufRead` and `R: BufRead`. This implementation is only available for types
/// that do not include the Both variant, because `BufRead::consume` cannot safely choose which
/// reader to consume from if Both is present. If you want to combine two readers, use
/// `std::io::Read::chain` instead.
#[cfg(feature = "use_std")]
#[quither(!has_both)]
impl<L, R> BufRead for Quither<L, R>
where
    L: BufRead,
    R: BufRead,
{
    fn fill_buf(&mut self) -> IoResult<&[u8]> {
        match self {
            #[either]
            Self::Left(l) => l.fill_buf(),
            #[either]
            Self::Right(r) => r.fill_buf(),
            #[neither]
            Self::Neither => Ok(&[]),
        }
    }

    fn consume(&mut self, #[allow(unused)] amt: usize) {
        match self {
            #[either]
            Self::Left(l) => l.consume(amt),
            #[either]
            Self::Right(r) => r.consume(amt),
            #[neither]
            Self::Neither => {}
        }
    }
}

/// Provides Seek, but only for types that do not include the Both variant.
///
/// Requires both `L: Seek` and `R: Seek`. This implementation is only available for types that do
/// not include the Both variant. It delegates to the inner value or returns `Ok(0)` for the Neither
/// variant.
#[cfg(feature = "use_std")]
#[quither(!has_both)]
impl<L, R> Seek for Quither<L, R>
where
    L: Seek,
    R: Seek,
{
    fn seek(&mut self, #[allow(unused)] pos: SeekFrom) -> IoResult<u64> {
        match self {
            #[either]
            Self::Left(l) => l.seek(pos),
            #[either]
            Self::Right(r) => r.seek(pos),
            #[neither]
            Self::Neither => Ok(0),
        }
    }
}

/// Dereferences to the inner value, regardless of variant.
///
/// Requires both `L: Deref` and `R: Deref<Target = L::Target>`. This allows dereferencing to the
/// inner value, regardless of which variant is used.
impl<L, R> Deref for Either<L, R>
where
    L: Deref,
    R: Deref<Target = L::Target>,
{
    type Target = L::Target;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => r,
        }
    }
}

/// Allows mutable dereference to the inner value, for any variant.
///
/// Requires both `L: DerefMut` and `R: DerefMut<Target = L::Target>`. This allows mutable
/// dereferencing to the inner value for any variant.
impl<L, R> DerefMut for Either<L, R>
where
    L: DerefMut,
    R: DerefMut<Target = L::Target>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Left(l) => l,
            Self::Right(r) => r,
        }
    }
}

/// Formats the pair type for display, showing the variant and its contents.
///
/// Requires both `L: Display` and `R: Display`. The output format reflects the variant and its
/// inner value(s).
#[quither]
impl<L, R> Display for Quither<L, R>
where
    L: Display,
    R: Display,
{
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        match self {
            #[either]
            Self::Left(l) => write!(f, "Left({})", l),
            #[either]
            Self::Right(r) => write!(f, "Right({})", r),
            #[neither]
            Self::Neither => write!(f, "Neither"),
            #[both]
            Self::Both(l, r) => write!(f, "Both({}, {})", l, r),
        }
    }
}

/// Delegates Error trait methods to the inner value.
///
/// Requires both `L: Error` and `R: Error`. Error source, description, and cause are delegated to
/// the inner value.
impl<L, R> Error for Either<L, R>
where
    L: Error,
    R: Error,
{
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Left(l) => l.source(),
            Self::Right(r) => r.source(),
        }
    }

    #[allow(deprecated)]
    fn description(&self) -> &str {
        match self {
            Self::Left(l) => l.description(),
            Self::Right(r) => r.description(),
        }
    }

    #[allow(deprecated)]
    fn cause(&self) -> Option<&dyn Error> {
        match self {
            Self::Left(l) => l.cause(),
            Self::Right(r) => r.cause(),
        }
    }

    // TODO: nightly methods?
}

/// Extends with items, only for types that do not include the Neither or Both variants.
///
/// Requires both `L: Extend<T>` and `R: Extend<T>`. This implementation is only available for types
/// that do not include the Neither or Both variants. If the type includes the Both variant, use the
/// implementation that requires `T: Clone`, which extends both inner values with cloned items.
#[quither(!has_neither && !has_both)]
impl<L, R, T> Extend<T> for Quither<L, R>
where
    L: Extend<T>,
    R: Extend<T>,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        match self {
            #[either]
            Self::Left(l) => l.extend(iter),
            #[either]
            Self::Right(r) => r.extend(iter),
        }
    }
}

/// Extends both inner values of Both with cloned items, only for types that include the Both variant.
///
/// Requires `L: Extend<T>`, `R: Extend<T>`, and `T: Clone`. For types that include the Both variant,
/// both inner values are extended with cloned items from the iterator.
#[quither(!has_neither && has_both)]
impl<L, R, T> Extend<T> for Quither<L, R>
where
    L: Extend<T>,
    R: Extend<T>,
    T: Clone,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        match self {
            #[either]
            Self::Left(l) => l.extend(iter),
            #[either]
            Self::Right(r) => r.extend(iter),
            #[both]
            Self::Both(l, r) => {
                let tuple_iter = iter.into_iter().map(|t| (t.clone(), t));

                // Why `Extend` not implemented for `&mut T where T: Extend`?
                struct Wrap<U>(U);
                impl<U, V> Extend<V> for Wrap<&mut U>
                where
                    U: Extend<V>,
                {
                    fn extend<I: IntoIterator<Item = V>>(&mut self, iter: I) {
                        self.0.extend(iter);
                    }
                }
                (Wrap(l), Wrap(r)).extend(tuple_iter);
            }
        }
    }
}

/// Polls the inner future, matching the current variant.
///
/// Requires both `L: Future` and `R: Future<Output = L::Output>`. Polling this type will poll the
/// inner future, matching the current variant.
impl<L, R> Future for Either<L, R>
where
    L: Future,
    R: Future<Output = L::Output>,
{
    type Output = L::Output;
    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.as_pin_mut() {
            Either::Left(l) => l.poll(ctx),
            Either::Right(r) => r.poll(ctx),
        }
    }
}

#[quither]
impl<L, R, OL, OR> PartialEq<Quither<OL, OR>> for Quither<L, R>
where
    L: PartialEq<OL>,
    R: PartialEq<OR>,
{
    fn eq(&self, other: &Quither<OL, OR>) -> bool {
        match (self, other) {
            #[either]
            (Self::Left(l), Quither::Left(ol)) => l == ol,
            #[either]
            (Self::Right(r), Quither::Right(or)) => r == or,
            #[neither]
            (Self::Neither, Quither::Neither) => true,
            #[both]
            (Self::Both(l, r), Quither::Both(ol, or)) => l == ol && r == or,
            #[allow(unreachable_patterns)]
            _ => false,
        }
    }
}

#[quither]
impl<L, R, OL, OR> PartialOrd<Quither<OL, OR>> for Quither<L, R>
where
    L: PartialOrd<OL>,
    R: PartialOrd<OR>,
{
    fn partial_cmp(&self, other: &Quither<OL, OR>) -> Option<std::cmp::Ordering> {
        match (self, other) {
            #[either]
            (Self::Left(l), Quither::Left(ol)) => l.partial_cmp(ol),
            #[either]
            (Self::Right(r), Quither::Right(or)) => r.partial_cmp(or),
            #[neither]
            (Self::Neither, Quither::Neither) => Some(std::cmp::Ordering::Equal),
            #[both]
            (Self::Both(l, r), Quither::Both(ol, or)) => l
                .partial_cmp(ol)
                .and_then(|o| r.partial_cmp(or).map(|o2| o.cmp(&o2))),
            // Non-equal variants patterns
            #[neither]
            #[allow(unreachable_patterns)]
            (Self::Neither, _) => Some(std::cmp::Ordering::Less),
            #[neither]
            #[allow(unreachable_patterns)]
            (_, Quither::Neither) => Some(std::cmp::Ordering::Greater),
            #[either]
            #[allow(unreachable_patterns)]
            (Self::Left(_), _) => Some(std::cmp::Ordering::Less),
            #[either]
            #[allow(unreachable_patterns)]
            (_, Quither::Left(_)) => Some(std::cmp::Ordering::Greater),
            #[either]
            #[allow(unreachable_patterns)]
            (Self::Right(_), _) => Some(std::cmp::Ordering::Less),
            #[either]
            #[allow(unreachable_patterns)]
            (_, Quither::Right(_)) => Some(std::cmp::Ordering::Greater),
        }
    }
}
