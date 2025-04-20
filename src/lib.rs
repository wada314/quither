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

macro_rules! categorize_arms {
    // @either arms
    ($callback:ident, { $($cb_args:tt)* },
        { @either => $pat:pat => $expr:expr $(,)? },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { /* empty */ },
            { $(($e_pat => $e_block),)* ($pat => {$expr}) }, { $(($n_pat => $n_block)),* }, { $(($b_pat => $b_block)),* })
    };
    ($callback:ident, { $($cb_args:tt)* },
        { @either => $pat:pat => $block:block $(,)? $($rest:tt)* },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $(($e_pat => $e_block),)* ($pat => $block) }, { $(($n_pat => $n_block)),* }, { $(($b_pat => $b_block)),* })
    };
    ($callback:ident, { $($cb_args:tt)* },
        { @either => $pat:pat => $expr:expr, $($rest:tt)* },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $(($e_pat => $e_block),)* ($pat => {$expr}) }, { $(($n_pat => $n_block)),* }, { $(($b_pat => $b_block)),* })
    };

    // @neither arms
    ($callback:ident, { $($cb_args:tt)* },
        { @neither => $pat:pat => $expr:expr $(,)? },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { /* empty */ },
            { $(($e_pat => $e_block)),* }, { $(($n_pat => $n_block)),* ($pat => {$expr}) }, { $(($b_pat => $b_block)),* })
    };
    ($callback:ident, { $($cb_args:tt)* },
        { @neither => $pat:pat => $block:block $(,)? $($rest:tt)* },
        { $($e_pat:pat, $e_block:block),* }, { $($n_pat:pat, $n_block:block),* }, { $($b_pat:pat, $b_block:block),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $(($e_pat => $e_block)),* }, { $(($n_pat => $n_block)),* ($pat => $block) }, { $(($b_pat => $b_block)),* })
    };
    ($callback:ident, { $($cb_args:tt)* },
        { @neither => $pat:pat => $expr:expr, $($rest:tt)* },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $(($e_pat => $e_block)),* }, { $(($n_pat => $n_block)),* ($pat => {$expr}) }, { $(($b_pat => $b_block)),* })
    };

    // @both arms
    ($callback:ident, { $($cb_args:tt)* },
        { @both => $pat:pat => $expr:expr $(,)? },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { /* empty */ },
            { $(($e_pat => $e_block)),* }, { $(($n_pat => $n_block)),* }, { $(($b_pat => $b_block)),* ($pat => {$expr}) })
    };
    ($callback:ident, { $($cb_args:tt)* },
        { @both => $pat:pat => $block:block $(,)? $($rest:tt)* },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $(($e_pat => $e_block)),* }, { $(($n_pat => $n_block)),* }, { $(($b_pat => $b_block)),* ($pat => $block) })
    };
    ($callback:ident, { $($cb_args:tt)* },
        { @both => $pat:pat => $expr:expr, $($rest:tt)* },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $(($e_pat => $e_block)),* }, { $(($n_pat => $n_block)),* }, { $(($b_pat => $b_block)),* ($pat => {$expr}) })
    };

    // Terminal case
    ($callback:ident, { $($cb_args:tt)* }, { /* empty */ },
        { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }
    ) => {
        $callback!($($cb_args)*, { $(($e_pat => $e_block)),* }, { $(($n_pat => $n_block)),* }, { $(($b_pat => $b_block)),* })
    };
}

/// Main macro to generate match expression with conditional variants
macro_rules! match_possible_variants {
    ($expr:expr, $has_e:ident, $has_n:ident, $has_b:ident, {
        $($arms:tt)*
    }) => {
        categorize_arms!(
            match_possible_variants, { @filtered $expr, $has_e, $has_n, $has_b },
            { $($arms)* }, {}, {}, {}
        )
    };
    (@filtered $expr:expr, true, true, true, { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }) => {
        match $expr {
            $($e_pat => $e_block)*
            $($n_pat => $n_block)*
            $($b_pat => $b_block)*
        }
    };
    (@filtered $expr:expr, true, true, false, { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }) => {
        match $expr {
            $($e_pat => $e_block)*
            $($n_pat => $n_block)*
        }
    };
    (@filtered $expr:expr, true, false, true, { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }) => {
        match $expr {
            $($e_pat => $e_block)*
            $($b_pat => $b_block)*
        }
    };
    (@filtered $expr:expr, true, false, false, { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }) => {
        match $expr {
            $($e_pat => $e_block)*
            $($n_pat => $n_block)*
        }
    };
    (@filtered $expr:expr, false, true, true, { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }) => {
        match $expr {
            $($n_pat => $n_block)*
            $($b_pat => $b_block)*
        }
    };
    (@filtered $expr:expr, false, true, false, { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }) => {
        match $expr {
            $($n_pat => $n_block)*
        }
    };
    (@filtered $expr:expr, false, false, true, { $(($e_pat:pat => $e_block:block)),* }, { $(($n_pat:pat => $n_block:block)),* }, { $(($b_pat:pat => $b_block:block)),* }) => {
        match $expr {
            $($b_pat => $b_block)*
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
                    @neither => $name::Neither => $name::Neither,
                    @both => $name::Both(a, b) => $name::Both(f(a), g(b)),
                })
            }
        }
    };
    ($($_:tt),*) => {};
}

#[inline(never)]
pub fn right(e: EitherOrNeitherOrBoth<i32, i32>) -> Option<i32> {
    foo(e.right())
}

#[inline(never)]
pub fn left(e: EitherOrNeitherOrBoth<i32, i32>) -> Option<i32> {
    foo(e.left())
}
