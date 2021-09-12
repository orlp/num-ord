# num-ord

This crate provides a numerically ordered wrapper type, `NumOrd`. This
type implements the `PartialOrd` and `PartialEq` traits for all the
possible combinations of built-in integer types, in a mathematically correct
manner without overflows. Please refer to the
[**the documentation**](https://docs.rs/num-ord) for more information.

To start using `num-ord` add the following to your `Cargo.toml`:

```toml
[dependencies]
num-ord = "0.1"
```

# Example

```rust
use num_ord::NumOrd;

let x = 3_i64;
let y = 3.5_f64;
assert_eq!(x < (y as i64), false); // Incorrect.
assert_eq!(NumOrd(x) < NumOrd(y), true); // Correct.

let x = 9007199254740993_i64;
let y = 9007199254740992_f64;
assert_eq!(format!("{}", y), "9007199254740992"); // No rounded constant trickery!
assert_eq!((x as f64) <= y, true); // Incorrect.
assert_eq!(NumOrd(x) <= NumOrd(y), false); // Correct.
```

# License

`num-ord` is released under the Zlib license, a permissive license. It is
OSI and FSF approved and GPL compatible.
