# quither

A flexible enum-based utility for representing values that may be on the left, right, neither, or both sides.

## Highlights
- Provides a generic enum type supporting `Left`, `Right`, `Neither`, and `Both` variants
  - Supports arbitrary combinations of `Either`, `Both`, and `Neither`.
- Iterator and standard trait support
- Supposed to be compatible with `itertools`'s `Either` and `EitherOrBoth` types.
- No-std compatible (with optional std features)

## Example
```rust
use quither::{Quither, NeitherOrBoth};

// You can create values with any combination of variants:
let left = Quither::Left(1);
let right = Quither::Right(2);
let both = Quither::Both(1, 2);
let neither = Quither::Neither;

// Pattern matching on Quither
match both {
    Quither::Left(l) => println!("Left: {}", l),
    Quither::Right(r) => println!("Right: {}", r),
    Quither::Both(l, r) => println!("Both: {}, {}", l, r),
    Quither::Neither => println!("Neither"),
}

// You can also convert between different variant sets using TryInto:
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