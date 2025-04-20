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
    pub fn right(self) -> Option<B> {
        match self {
            Self::Right(b) | Self::Both(_, b) => Some(b),
            _ => None,
        }
    }

    pub fn left(self) -> Option<A> {
        match self {
            Self::Left(a) | Self::Both(a, _) => Some(a),
            _ => None,
        }
    }
}

#[inline(never)]
fn foo(x: Option<i32>) -> Option<i32> {
    x
}

#[inline(never)]
pub fn right(e: EitherOrNeitherOrBoth<i32, i32>) -> Option<i32> {
    foo(e.right())
}

#[inline(never)]
pub fn left(e: EitherOrNeitherOrBoth<i32, i32>) -> Option<i32> {
    foo(e.left())
}
