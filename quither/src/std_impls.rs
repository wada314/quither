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

/// Implement `Read` for `Quither<L, R>` if `L` and `R` implement `Read`.
///
/// The implementation for `Left`, `Right` or `Neither` case are trivial;
/// it just returns the inner value's result directly, or returns `Ok(0)` if the variant is `Neither`.
///
/// The implementation for `Both` case is little more complex, and is slightly different with
/// the [`std::io::Read::chain`] method. For every call to `read`, it first tries to read data
/// from `Left`, then from `Right` if there is no data read from `Left`.
/// (where the [`std::io::Read::chain`] method will never try again to read from the first
/// reader once it returns `Ok(0)`).
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

/// Implement `BufRead` for `Quither<L, R>` if `L` and `R` implement `BufRead`.
///
/// Surprisingly, this trait impl does not support a type containing `Both` variant,
/// where the plain [`std::io::Read`] trait does.
/// This is because of the `BufRead::consume` method cannot tell which reader to consume from.
/// Instead, you can use [`std::io::Read::chain`] method to chain the readers together,
/// so that you can combine two readers into one.
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

/// Note `Extend` requires the item type `T` to be `Clone` if `Both` variant is present.
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

/// Note `Extend` requires the item type `T` to be `Clone` if `Both` variant is present.
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
