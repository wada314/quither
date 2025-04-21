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

/// Takes a list of match arms (with @label => prefix) and returns a list of match arms
/// with the arm's expression part is guaranteed to be a block.
macro_rules! normalize_arms {
    // Terminal case
    ($callback:ident, { $($cb_args:tt)* }, { $($cb_args2:tt)* },
        { /* empty input */}, { $($generated:tt)* }
    ) => {
        $callback!($($cb_args)*, { $($generated)* }, $($cb_args2)*)
    };

    // Normal case: expression is a block
    ($callback:ident, { $($cb_args:tt)* }, { $($cb_args2:tt)* },
        { @$label:ident => $pat:pat => $block:block $(,)? $($rest:tt)* },
        { $($generated:tt)*}
    ) => {
        normalize_arms!($callback, { $($cb_args)* }, { $($cb_args2)* }, { $($rest)* },
            { $($generated)* @$label => $pat => $block }
        )
    };

    // Normal case: expression is an expression
    ($callback:ident, { $($cb_args:tt)* }, { $($cb_args2:tt)* },
        { @$label:ident => $pat:pat => $expr:expr, $($rest:tt)+ },
        { $($generated:tt)*}
    ) => {
        normalize_arms!($callback, { $($cb_args)* }, { $($cb_args2)* }, { $($rest)* },
            { $($generated)* @$label => $pat => {$expr} }
        )
    };

    // Last arm case: expression is an expression
    ($callback:ident, { $($cb_args:tt)* }, { $($cb_args2:tt)* },
        { @$label:ident => $pat:pat => $expr:expr $(,)? },
        { $($generated:tt)*}
    ) => {
        normalize_arms!($callback, { $($cb_args)* }, { $($cb_args2)* }, { /* empty */ },
            { $($generated)* @$label => $pat => {$expr} }
        )
    };
}

macro_rules! categorize_arms {
    // @either arms
    ($callback:ident, { $($cb_args:tt)* },
        { @either => $pat:pat => $block:block $($rest:tt)* },
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $($e_arms)* $pat => $block }, { $($n_arms)* }, { $($b_arms)* }
        )
    };

    // @neither arms
    ($callback:ident, { $($cb_args:tt)* },
        { @neither => $pat:pat => $block:block $($rest:tt)* },
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $($e_arms)* }, { $($n_arms)* $pat => $block }, { $($b_arms)* }
        )
    };

    // @both arms
    ($callback:ident, { $($cb_args:tt)* },
        { @both => $pat:pat => $block:block $($rest:tt)* },
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        categorize_arms!($callback, { $($cb_args)* }, { $($rest)* },
            { $($e_arms)* }, { $($n_arms)* }, { $($b_arms)* $pat => $block }
        )
    };

    // Terminal case
    ($callback:ident, { $($cb_args:tt)* },
        { /* empty */ },
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        $callback!($($cb_args)*, { $($e_arms)* }, { $($n_arms)* }, { $($b_arms)* })
    };
}

/// Main macro to generate match expression with conditional variants
macro_rules! match_possible_variants {
    ($expr:expr, $has_e:ident, $has_n:ident, $has_b:ident, {
        $($arms:tt)*
    }) => {
        normalize_arms!(
            categorize_arms, { match_possible_variants, { @categorized $expr, $has_e, $has_n, $has_b } }, { {}, {}, {} },
            { $($arms)* }, {}
        )
    };
    (@categorized $expr:expr, true, true, true,
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        match $expr {
            $($e_arms)*
            $($n_arms)*
            $($b_arms)*
        }
    };
    (@categorized $expr:expr, true, true, false,
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        match $expr {
            $($e_arms)*
            $($n_arms)*
        }
    };
    (@categorized $expr:expr, true, false, true,
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        match $expr {
            $($e_arms)*
            $($b_arms)*
        }
    };
    (@categorized $expr:expr, true, false, false,
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        match $expr {
            $($e_arms)*
        }
    };
    (@categorized $expr:expr, false, true, true,
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        match $expr {
            $($n_arms)*
            $($b_arms)*
        }
    };
    (@categorized $expr:expr, false, true, false,
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        match $expr {
            $($n_arms)*
        }
    };
    (@categorized $expr:expr, false, false, true,
        { $($e_arms:tt)* }, { $($n_arms:tt)* }, { $($b_arms:tt)* }
    ) => {
        match $expr {
            $($b_arms)*
        }
    };
}

macro_rules! apply_impl_to_all_variants {
    ($name:ident) => {
        $name!(EitherOrNeitherOrBoth, true, true, true);
        $name!(EitherOrNeither, true, true, false);
        $name!(EitherOrBoth, true, false, true);
        $name!(NeitherOrBoth, false, true, true);
        $name!(Either, true, false, false);
        $name!(Both, false, false, true);
    };
}
