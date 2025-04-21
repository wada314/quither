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

apply_impl_to_all_variants!(impl_pair_map);

pub fn hoge(e: EitherOrBoth<i32, i32>) -> EitherOrBoth<i64, i64> {
    e.map_either(|a| a as i64, |b| b as i64)
}
