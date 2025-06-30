# quither

A flexible enum-based utility for representing values that may be on the left, right, neither, or both sides.

## Highlights
- Provides a generic enum type supporting `Left`, `Right`, `Neither`, and `Both` variants
  - Supports arbitrary combinations of `Either`, `Both`, and `Neither`.
- Iterator and standard trait support
  - More and clearer iterator types than `itertools`'s `Either` and `EitherOrBoth` types.
- (Supposed to) have compatible interfaces with `itertools`'s `Either` and `EitherOrBoth` types.
- Fallible `map` methods, like `try_map()` or `try_map_left()`.
- Convert between each variant types.
  - Expanding conversion like `Either` to `EitherOrBoth` is infallible.
  - Contracting conversion like `EitherOrBoth` to `Either` is fallible, where the error type returns the remaining variant type (`Both` in this case).
- No-std compatible, can be build without `std` features.
- A bonus feature: Supports the transposition of `Result<impl IntoIterator, E>` type into `impl Iterator<Item = Result<T, E>>` type.

## Example
```rust
use quither::{Quither, NeitherOrBoth, EitherOrBoth};

// You can create values with any combination of variants:
let left: Quither<i32, i32> = Quither::Left(1);
let right: Quither<i32, i32> = Quither::Right(2);
let both: Quither<i32, i32> = Quither::Both(1, 2);
let neither = Neither::Neither;
let left2: EitherOrBoth<i32, i32> = EitherOrBoth::Left(1);

// Pattern matching on Quither
match both {
    Quither::Left(l) => println!("Left: {}", l),
    Quither::Right(r) => println!("Right: {}", r),
    Quither::Both(l, r) => println!("Both: {}, {}", l, r),
    Quither::Neither => println!("Neither"),
}

// You can convert the type to a "larger" type
let left2_in_quither: Quither<_, _> = left2.into();

// You can also convert into a "smaller" type with fallible conversion.
// For example, convert a Quither to a type with only Neither and Both variants
let neither_or_both: NeitherOrBoth<_, _> = both.try_into().unwrap();

// Pattern matching works as usual
match neither_or_both {
    NeitherOrBoth::Both(l, r) => println!("Both: {}, {}", l, r),
    NeitherOrBoth::Neither => println!("Neither"),
}
```

## Crate Features
- `use_std` (default: enabled): Enables implementations for std types (e.g., Read, BufRead) 
- `itertools` (default: disabled): Enables `Into` impls from and to `itertools::Either` and `itertools::EitherOrBoth`.
