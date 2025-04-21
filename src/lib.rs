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

#[macro_use]
mod macros;

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

/// impl left / right getters
macro_rules! impl_left_right_getters {
    ($name:ident, $has_e:ident, $has_n:ident, $has_b:ident) => {
        impl<L, R> $name<L, R> {
            /// Return `true` if the variant *contains* a left value.
            /// i.e. `Left(l)` or `Both(l, _)`.
            pub fn is_left(&self) -> bool {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(_) => true,
                    @either => $name::Right(_) => false,
                    @neither => $name::Neither => false,
                    @both => $name::Both(_, _) => true,
                })
            }

            /// Return `true` if the variant *contains* a right value.
            /// i.e. `Right(r)` or `Both(_, r)`.
            pub fn is_right(&self) -> bool {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(_) => false,
                    @either => $name::Right(_) => true,
                    @neither => $name::Neither => false,
                    @both => $name::Both(_, _) => true,
                })
            }

            /// Convert the left side of the variant into an `Option`.
            /// i.e. `Left(l)` -> `Some(l)`, `Right(_)` -> `None`, `Both(l, _)` -> `Some(l)`.
            pub fn left(self) -> Option<L> {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => Some(l),
                    @either => $name::Right(_) => None,
                    @neither => $name::Neither => None,
                    @both => $name::Both(l, _) => Some(l),
                })
            }

            /// Apply the function `f` on the value in the left position if it is present,
            /// and then rewrap the result in a same variant of the new type.
            pub fn map_left<F, L2>(self, f: F) -> $name<L2, R>
            where
                F: FnOnce(L) -> L2,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => $name::Left(f(l)),
                    @either => $name::Right(r) => $name::Right(r),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, r) => $name::Both(f(l), r),
                })
            }

            /// Apply the function `f` on the value in the left position if it is present,
            /// and then rewrap the result in a same variant of the new type.
            pub fn left_and_then<F, L2>(self, f: F) -> $name<L2, R>
            where
                F: FnOnce(L) -> $name<L2, R>,
            {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => f(l),
                    @either => $name::Right(r) => $name::Right(r),
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(l, _) => f(l),
                })
            }

            /// Return left value or given value.
            pub fn left_or(self, other: L) -> L {
                match_possible_variants!(self, $has_e, $has_n, $has_b, {
                    @either => $name::Left(l) => l,
                    @either => $name::Right(_) => other,
                    @neither => $name::Neither => other,
                    @both => $name::Both(l, _) => l,
                })
            }

        }
    };
}

/// Implements map_either for pair-like types with conditional variants
macro_rules! impl_pair_map {
    ($name:ident, $has_e:ident, false, $has_b:ident) => {
        impl<A, B> $name<A, B> {
            pub fn map_either<F, G, C, D>(self, f: F, g: G) -> $name<C, D>
            where
                F: FnOnce(A) -> C,
                G: FnOnce(B) -> D,
            {
                match_possible_variants!(self, $has_e, false, $has_b, {
                    @either => $name::Left(a) => $name::Left(f(a)),
                    @either => $name::Right(b) => $name::Right(g(b)),
                    @neither => $name::Neither => unreachable!(),
                    @both => $name::Both(a, b) => $name::Both(f(a), g(b)),
                })
            }
        }
    };
    ($($_:tt),*) => {};
}

apply_impl_to_all_variants!(impl_left_right_getters);
apply_impl_to_all_variants!(impl_pair_map);

pub fn hoge(e: EitherOrBoth<i32, i32>) -> EitherOrBoth<i64, i64> {
    e.map_either(|a| a as i64, |b| b as i64)
}
