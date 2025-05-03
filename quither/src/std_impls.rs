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
use ::quither_proc_macros::quither;
#[cfg(feature = "use_std")]
use ::std::io::{BufRead, Read, Result as IoResult};

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
