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
        $name!(true, true, true);
        $name!(true, true, false);
        $name!(true, false, true);
        $name!(false, true, true);
        $name!(true, false, false);
        $name!(false, false, true);
        $name!(false, true, false);
        $name!(false, false, false);
    };
}

macro_rules! pair_type {
    (true, true, true, $left:ty, $right:ty) => {
        $crate::EitherOrNeitherOrBoth::<$left, $right>
    };
    (true, true, false, $left:ty, $right:ty) => {
        $crate::EitherOrNeither::<$left, $right>
    };
    (true, false, true, $left:ty, $right:ty) => {
        $crate::EitherOrBoth::<$left, $right>
    };
    (false, true, true, $left:ty, $right:ty) => {
        $crate::NeitherOrBoth::<$left, $right>
    };
    (true, false, false, $left:ty, $right:ty) => {
        $crate::Either::<$left, $right>
    };
    (false, false, true, $left:ty, $right:ty) => {
        $crate::Both::<$left, $right>
    };
    (false, true, false, $left:ty, $right:ty) => {
        $crate::Neither
    };
    (false, false, false, $left:ty, $right:ty) => {
        !
    };
}

macro_rules! use_pair_variants {
    (true, true, true) => {
        #[allow(unused)]
        use $crate::EitherOrNeitherOrBoth::*;
    };
    (true, true, false) => {
        #[allow(unused)]
        use $crate::EitherOrNeither::*;
    };
    (true, false, true) => {
        #[allow(unused)]
        use $crate::EitherOrBoth::*;
    };
    (false, true, true) => {
        #[allow(unused)]
        use $crate::NeitherOrBoth::*;
    };
    (true, false, false) => {
        #[allow(unused)]
        use $crate::Either::*;
    };
    (false, false, true) => {
        #[allow(unused)]
        use $crate::Both::*;
    };
    (false, true, false) => {
        #[allow(unused)]
        use $crate::Neither::*;
    };
    (false, false, false) => {};
}

macro_rules! impl_pair_type {
    (false, $has_n:ident, false, $left:ident, $right:ident, { $($body:tt)* }) => {
        impl pair_type!(false, $has_n, false, $left, $right) {
            $($body)*
        }
    };
    ($has_e:ident, $has_n:ident, $has_b:ident, $left:ident, $right:ident, { $($body:tt)* }) => {
        impl<$left, $right> pair_type!($has_e, $has_n, $has_b, $left, $right) {
            $($body)*
        }
    };
}
