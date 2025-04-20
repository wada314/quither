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

macro_rules! filter_arms {
    // @either arms
    (@either,
        { 'either => $pat:pat => $expr:expr $(,)? },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@either, { /* empty */ }, { $($generated)* $pat => $expr, })
    };
    (@either,
        { 'either => $pat:pat => $block:block $(,)? $($rest:tt)* },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@either, { $($rest)* }, { $($generated)* $pat => $block })
    };
    (@either,
        { 'either => $pat:pat => $expr:expr, $($rest:tt)* },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@either, { $($($rest)*)* }, { $($generated)* $pat => $expr, })
    };

    // @neither arms
    (@neither,
        { 'neither => $pat:pat => $expr:expr $(,)? },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@neither, { /* empty */ }, { $($generated)* $pat => $expr, })
    };
    (@neither,
        { 'neither => $pat:pat => $block:block $(,)? $($rest:tt)* },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@neither, { $($rest)* }, { $($generated)* $pat => $block })
    };
    (@neither,
        { 'neither => $pat:pat => $expr:expr, $($rest:tt)* },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@neither, { $($rest)* }, { $($generated)* $pat => $expr, })
    };

    // @both arms
    (@both,
        { 'both => $pat:pat => $expr:expr $(,)? },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@both, { /* empty */ }, { $($generated)* $pat => $expr, })
    };
    (@both,
        { 'both => $pat:pat => $block:block $(,)? $($rest:tt)* },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@both, { $($rest)* }, { $($generated)* $pat => $block })
    };
    (@both,
        { 'both => $pat:pat => $expr:expr, $($rest:tt)* },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@both, { $($rest)* }, { $($generated)* $pat => $expr, })
    };

    // Terminal case
    (@$filter:ident, { /* empty */ }, { $($generated:tt)* }) => {
        $($generated)*
    };

    // Skip these arms
    (@$filter:ident,
        { $label:lifetime => $pat:pat => $block:block $(,)? $($rest:tt)* },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@$filter, { $($rest)* }, { $($generated)* })
    };
    (@$filter:ident,
        { $label:lifetime => $pat:pat => $expr:expr, $($rest:tt)* },
        { $($generated:tt)* }
    ) => {
        filter_arms!(@$filter, { $($rest)* }, { $($generated)* })
    };
}

/// Main macro to generate match expression with conditional variants
macro_rules! match_possible_variants {
    ($expr:expr, $has_e:ident, $has_n:ident, $has_b:ident, {
        $($arms:tt)*
    }) => {
        match_possible_variants!(
            @filtered $expr,
            $has_e, $has_n, $has_b,
            { filter_arms!(@either, { $($arms)* }, {}) },
            { filter_arms!(@neither, { $($arms)* }, {}) },
            { filter_arms!(@both, { $($arms)* }, {}) }
        )
    };
    (@filtered $expr:expr, true, true, true, { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }) => {
        match $expr {
            $($e_arms)*
            $($n_arms)*
            $($b_arms)*
        }
    };
    (@filtered $expr:expr, true, true, false, { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }) => {
        match $expr {
            $($e_arms)*
            $($n_arms)*
        }
    };
    (@filtered $expr:expr, true, false, true, { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }) => {
        match $expr {
            $($e_arms)*
            $($b_arms)*
        }
    };
    (@filtered $expr:expr, true, false, false, { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }) => {
        match $expr {
            $($e_arms)*
        }
    };
    (@filtered $expr:expr, false, true, true, { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }) => {
        match $expr {
            $($n_arms)*
            $($b_arms)*
        }
    };
    (@filtered $expr:expr, false, true, false, { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }) => {
        match $expr {
            $($n_arms)*
        }
    };
    (@filtered $expr:expr, false, false, true, { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }) => {
        match $expr {
            $($b_arms)*
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
                    'either => Self::Left(a) => Self::Left(f(a)),
                    'either => Self::Right(b) => Self::Right(g(b)),
                    'neither => Self::Neither => Self::Neither,
                    'both => Self::Both(a, b) => Self::Both(f(a), g(b)),
                })
            }
        }
    };
    ($($_:tt),*) => {};
}

// impl_pair_map!(EitherOrNeitherOrBoth, true, true, true);
// impl_pair_map!(EitherOrBoth, true, false, true);
// impl_pair_map!(EitherOrNeither, true, true, false);
// impl_pair_map!(NeitherOrBoth, false, true, true);
impl_pair_map!(Both, false, false, true);
