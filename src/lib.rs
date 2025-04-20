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

/// Helper macro to handle match arms based on variant flags
macro_rules! match_arm_group {
    // Match block-expression for @either variant when enabled
    (@either, true, @either => $pat:pat => $block:block $($rest:tt)*) => {
        $pat => $block
        match_arm_group!(@either, true, $($rest)*)
    };
    // Match comma-separated expression for @either variant when enabled
    (@either, true, @either => $pat:pat => $result:expr $(, $($rest:tt)*)*) => {
        $pat => $result,
        match_arm_group!(@either, true, $($($rest)*)*)
    };
    // Skip @either variant when disabled
    (@either, false, @either => $pat:pat => $block:block $($rest:tt)*) => {
        match_arm_group!(@either, false, $($rest)*)
    };
    (@either, false, @either => $pat:pat => $result:expr $(, $($rest:tt)*)*) => {
        match_arm_group!(@either, false, $($($rest)*)*)
    };
    // Base case: no more patterns to match
    (@either, $flag:expr, ) => {};

    // // Match block-expression for @neither variant when enabled
    // (@neither, true, @neither => $pat:pat => $block:block $($rest:tt)*) => {
    //     $pat => $block
    //     match_arm_group!(@neither, true, $($rest)*)
    // };
    // // Match comma-separated expression for @neither variant when enabled
    // (@neither, true, @neither => $pat:pat => $result:expr, $($rest:tt)*) => {
    //     $pat => $result,
    //     match_arm_group!(@neither, true, $($rest)*)
    // };
    // // Skip @neither variant when disabled
    // (@neither, false, @neither => $pat:pat => $block:block $($rest:tt)*) => {
    //     match_arm_group!(@neither, false, $($rest)*)
    // };
    // (@neither, false, @neither => $pat:pat => $result:expr, $($rest:tt)*) => {
    //     match_arm_group!(@neither, false, $($rest)*)
    // };
    // // Base case: no more patterns to match
    // (@neither, $flag:expr, ) => {};

    // // Match block-expression for @both variant when enabled
    // (@both, true, @both => $pat:pat => $block:block $($rest:tt)*) => {
    //     $pat => $block
    //     match_arm_group!(@both, true, $($rest)*)
    // };
    // // Match comma-separated expression for @both variant when enabled
    // (@both, true, @both => $pat:pat => $result:expr, $($rest:tt)*) => {
    //     $pat => $result,
    //     match_arm_group!(@both, true, $($rest)*)
    // };
    // // Skip @both variant when disabled
    // (@both, false, @both => $pat:pat => $block:block $($rest:tt)*) => {
    //     match_arm_group!(@both, false, $($rest)*)
    // };
    // (@both, false, @both => $pat:pat => $result:expr, $($rest:tt)*) => {};
    // // Base case: no more patterns to match
    // (@both, $flag:expr, ) => {};
}

/// Main macro to generate match expression with conditional variants
macro_rules! match_possible_variants {
    ($expr:expr, $has_e:expr, $has_n:expr, $has_b:expr, {
        $($arms:tt)*
    }) => {
        match $expr {
            match_arm_group!(@either, $has_e, $($arms)*)
            // match_arm_group!(@neither, $has_n, $($arms)*)
            // match_arm_group!(@both, $has_b, $($arms)*)
        }
    };
}

/// Implements map_either for pair-like types with conditional variants
macro_rules! impl_pair_map {
    ($name:ident, $has_e:expr, false, $has_b:expr) => {
        impl<A, B> $name<A, B> {
            pub fn map_either<F, G, C, D>(self, f: F, g: G) -> $name<C, D>
            where
                F: FnOnce(A) -> C,
                G: FnOnce(B) -> D,
            {
                match_possible_variants!(self, $has_e, false, $has_b, {
                    @either => Self::Left(a) => Self::Left(f(a)),
                    // @either => Self::Right(b) => Self::Right(g(b)),
                    // @neither => Self::Neither => Self::Neither,
                    // @both => Self::Both(a, b) => Self::Both(f(a), g(b)),
                })
            }
        }
    };
    ($($_:tt),*) => {};
}

impl_pair_map!(EitherOrBoth, true, false, true);
// impl_pair_map!(EitherOrNeither, true, true, false);
// impl_pair_map!(NeitherOrBoth, false, true, true);
