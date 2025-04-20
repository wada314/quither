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

pub struct Neither<A, B> {}

pub struct Both<A, B>(A, B);

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

macro_rules! match_arm_group {
    // @either-s
    (@either, yes, { @either => { $($arms:tt)* } $($rest:tt)* }) => {
        $($arms)*
    };
    (@either, no, { @either => { $($arms:tt)* } $($rest:tt)* }) => {};
    (@either, $flag:tt, {}) => {};
    (@either, $flag:tt, { $other:tt => { $($arms:tt)* } $($rest:tt)* }) => {
        match_arm_group!(@neither, $flag, { $other => { $($arms)* } $($rest)* })
    };

    // @neither-s
    (@neither, yes, { @neither => { $($arms:tt)* } $($rest:tt)* }) => {
        $($arms)*
    };
    (@neither, no, { @neither => { $($arms:tt)* } $($rest:tt)* }) => {};
    (@neither, $flag:tt, {}) => {};
    (@neither, $flag:tt, { $other:tt => { $($arms:tt)* } $($rest:tt)* }) => {
        match_arm_group!(@both, $flag, { $other => { $($arms)* } $($rest)* })
    };

    // @both-s
    (@both, yes, { @both => { $($arms:tt)* } $($rest:tt)* }) => {
        $($arms)*
    };
    (@both, no, { @both => { $($arms:tt)* } $($rest:tt)* }) => {};
    (@both, $flag:tt, {}) => {};
    (@both, $flag:tt, { $other:tt => { $($arms:tt)* } $($rest:tt)* }) => {
        match_arm_group!(@either, $flag, { $other => { $($arms)* } $($rest)* })
    };
}

macro_rules! match_possible_variants {
    ($has_e:ident, $has_n:ident, $has_b:ident, match $expr:expr { $($arms:tt)* }) => {
        match $expr {
            $( match_arm_group!(@either, $has_e, { $($arms)* }) )*
            $( match_arm_group!(@neither, $has_n, { $($arms)* }) )*
            $( match_arm_group!(@both, $has_b, { $($arms)* }) )*
        }
    };
}

macro_rules! impl_pair_map {
    ($name:path, $has_e:ident, no, $has_b:ident) => {
        impl<A, B> $name<A, B> {
            pub fn map_either<F, G, C, D>(self, f: F, g: G) -> $name<C, D>
            where
                F: FnOnce(A) -> C,
                G: FnOnce(B) -> D,
            {
                match_possible_variants!($has_e, no, $has_b, match self {
                    @either => {
                        Self::Left(a) => Self::Left(f(a)),
                        Self::Right(b) => Self::Right(g(b)),
                    }
                    @neither => {
                        Self::Neither => Self::Neither,
                    }
                    @both => {
                        Self::Both(a, b) => Self::Both(f(a), g(b)),
                    }
                })
            }
        }
    };
}
