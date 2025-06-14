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

use crate::Either;
use ::std::iter::{Once, once};

/// Extension trait for `Result` that provides methods for working with iterators.
///
/// This trait adds functionality to transpose a `Result` containing an iterator
/// into an iterator of `Result`s. This is particularly useful when you have a
/// `Result<Vec<T>, E>` and want to process each element while preserving any
/// potential errors.
///
/// # Examples
///
/// ```
/// use quither::ResultExt;
///
/// let result: Result<Vec<i32>, &str> = Ok(vec![1, 2, 3]);
/// let mut iter = result.transpose_iter();
///
/// assert_eq!(iter.next(), Some(Ok(1)));
/// assert_eq!(iter.next(), Some(Ok(2)));
/// assert_eq!(iter.next(), Some(Ok(3)));
/// assert_eq!(iter.next(), None);
///
/// let result: Result<Vec<i32>, &str> = Err("error");
/// let mut iter = result.transpose_iter();
///
/// assert_eq!(iter.next(), Some(Err("error")));
/// assert_eq!(iter.next(), None);
/// ```
pub trait ResultExt<T, E> {
    /// Transposes a `Result` containing an iterator into an iterator of `Result`s.
    ///
    /// If the `Result` is `Ok`, it will yield `Ok` values for each element in the iterator.
    /// If the `Result` is `Err`, it will yield a single `Err` value and then stop.
    ///
    /// # Examples
    ///
    /// ```
    /// use quither::ResultExt;
    ///
    /// let result: Result<Vec<i32>, &str> = Ok(vec![1, 2, 3]);
    /// let sum: Result<i32, &str> = result.transpose_iter()
    ///     .collect::<Result<Vec<_>, _>>()
    ///     .map(|v| v.into_iter().sum());
    ///
    /// assert_eq!(sum, Ok(6));
    /// ```
    fn transpose_iter(self) -> Iter<T, E>
    where
        T: IntoIterator;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn transpose_iter(self) -> Iter<T, E>
    where
        T: IntoIterator,
    {
        match self {
            Ok(it) => Iter {
                inner: Either::Left(it.into_iter()),
            },
            Err(e) => Iter {
                inner: Either::Right(once(Err(e))),
            },
        }
    }
}

pub struct Iter<T, E>
where
    T: IntoIterator,
{
    inner: Either<T::IntoIter, Once<Result<T::Item, E>>>,
}

impl<T, E> Iterator for Iter<T, E>
where
    T: IntoIterator,
{
    type Item = Result<T::Item, E>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            Either::Left(it) => it.next().map(Ok),
            Either::Right(it) => it.next(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transpose_iter_ok() {
        let result: Result<Vec<i32>, &str> = Ok(vec![1, 2, 3]);
        let mut iter = result.transpose_iter();

        assert_eq!(iter.next(), Some(Ok(1)));
        assert_eq!(iter.next(), Some(Ok(2)));
        assert_eq!(iter.next(), Some(Ok(3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_transpose_iter_err() {
        let result: Result<Vec<i32>, &str> = Err("error");
        let mut iter = result.transpose_iter();

        assert_eq!(iter.next(), Some(Err("error")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_transpose_iter_empty() {
        let result: Result<Vec<i32>, &str> = Ok(vec![]);
        let mut iter = result.transpose_iter();

        assert_eq!(iter.next(), None);
    }
}
