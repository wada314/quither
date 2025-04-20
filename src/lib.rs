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

pub enum Either<A, B> {
    Left(A),
    Right(B),
}

pub enum Both<A, B> {
    Both(A, B),
}

pub enum EitherOrNeither<A, B> {
    Left(A),
    Right(B),
    Neither,
}

pub enum EitherOrBoth<A, B> {
    Left(A),
    Right(B),
    Both(A, B),
}

pub enum NeitherOrBoth<A, B> {
    Neither,
    Both(A, B),
}

pub enum EitherOrNeitherOrBoth<A, B> {
    Left(A),
    Right(B),
    Neither,
    Both(A, B),
}

impl<A, B> Either<A, B> {
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    fn into_enb(self) -> EitherOrNeitherOrBoth<A, B> {
        match self {
            Either::Left(a) => EitherOrNeitherOrBoth::Left(a),
            Either::Right(b) => EitherOrNeitherOrBoth::Right(b),
        }
    }

    pub fn as_ref(&self) -> Either<&A, &B> {
        match self {
            Either::Left(a) => Either::Left(a),
            Either::Right(b) => Either::Right(b),
        }
    }

    pub fn is_left2(&self) -> bool {
        self.as_ref().into_enb().is_left()
    }
}

impl<A, B> EitherOrNeitherOrBoth<A, B> {
    pub fn is_left(&self) -> bool {
        matches!(self, EitherOrNeitherOrBoth::Left(_))
    }
    pub fn is_right(&self) -> bool {
        matches!(self, EitherOrNeitherOrBoth::Right(_))
    }
    pub fn is_neither(&self) -> bool {
        matches!(self, EitherOrNeitherOrBoth::Neither)
    }
    pub fn is_both(&self) -> bool {
        matches!(self, EitherOrNeitherOrBoth::Both(_, _))
    }
}

#[inline(never)]
pub fn debug_is_left(e: Either<i32, i32>) -> bool {
    e.is_left()
}

#[inline(never)]
pub fn debug_is_left2(e: Either<i32, i32>) -> bool {
    e.is_left2()
}

#[inline(never)]
pub fn debug_is_left3(e: EitherOrNeitherOrBoth<i32, i32>) -> bool {
    e.is_left()
}

#[inline(never)]
pub fn debug_is_right(e: Either<i32, i32>) -> bool {
    e.is_right()
}

#[inline(never)]
pub fn debug_is_neither(e: EitherOrNeitherOrBoth<i32, i32>) -> bool {
    e.is_neither()
}

#[inline(never)]
pub fn debug_is_both(e: EitherOrNeitherOrBoth<i32, i32>) -> bool {
    e.is_both()
}

#[inline(never)]
pub fn is_zero(x: i32) -> bool {
    x == 0
}
