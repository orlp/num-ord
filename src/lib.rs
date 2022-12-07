#![cfg_attr(not(test), no_std)]
#![warn(
    rustdoc::invalid_html_tags,
    missing_debug_implementations,
    trivial_casts,
    unused_lifetimes,
    unused_import_braces
)]
#![deny(missing_docs, unaligned_references)]

//! # num-ord
//!
//! This crate provides a numerically ordered wrapper type, [`NumOrd`]. This
//! type implements the [`PartialOrd`] and [`PartialEq`] traits for all the
//! possible combinations of built-in integer types, in a mathematically correct
//! manner without overflows.
//!
//! For example, comparing an `x: i64` and a `y: f64` is actually quite
//! difficult.  Neither `(x as f64) < y` nor `x < (y as i64)` is correct. But
//! `NumOrd(x) < NumOrd(y)` is:
//! ```rust
//! use num_ord::NumOrd;
//!
//! let x = 3_i64;
//! let y = 3.5_f64;
//! assert_eq!(x < (y as i64), false); // Incorrect.
//! assert_eq!(NumOrd(x) < NumOrd(y), true); // Correct.
//!
//! let x = 9007199254740993_i64;
//! let y = 9007199254740992_f64;
//! assert_eq!(format!("{}", y), "9007199254740992"); // No rounded constant trickery!
//! assert_eq!((x as f64) <= y, true); // Incorrect.
//! assert_eq!(NumOrd(x) <= NumOrd(y), false); // Correct.
//! ```

use core::cmp::Ordering;

/// A numerically ordered wrapper type.
///
/// See the crate docs for more details.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct NumOrd<T>(pub T);

macro_rules! common_type_impl_body {
    ($Lhs:ty, $Rhs:ty, $CommonT:ty, $lhs:expr, $rhs:expr, $op:ident, $less:expr, $greater:expr, $nan:expr) => {{
        ($lhs as $CommonT).$op(&($rhs as $CommonT))
    }};
}

macro_rules! int_float_impl_body {
    ($IntT:ty, $FloatT:ty, $_UnusedT:ty, $lhs:expr, $rhs:expr, $op:ident, $less:expr, $greater:expr, $nan:expr) => {{
        let lhs = $lhs;
        let rhs = $rhs;

        // Range in which FloatT is dense in the integers.
        const FLOAT_DENSE_INT_MIN: $IntT =
            (0 as $IntT).saturating_sub(1) << <$FloatT>::MANTISSA_DIGITS;
        const FLOAT_DENSE_INT_MAX: $IntT = 1 << <$FloatT>::MANTISSA_DIGITS;

        // One above IntT::MAX as FloatT. May be infinite.
        const INT_MAX_POWER_OF_TWO: $IntT = <$IntT>::MAX ^ (<$IntT>::MAX >> 1);
        const INT_ONE_ABOVE_MAX_AS_FLOAT: $FloatT = 2.0 * (INT_MAX_POWER_OF_TWO as $FloatT);

        if FLOAT_DENSE_INT_MIN <= lhs && lhs <= FLOAT_DENSE_INT_MAX {
            // lhs is exactly representable as an integer valued float.
            (lhs as $FloatT).$op(&rhs)
        } else if INT_ONE_ABOVE_MAX_AS_FLOAT <= rhs {
            $less
        } else if <$IntT>::MIN as $FloatT > rhs {
            $greater
        } else if rhs.is_nan() {
            $nan
        } else {
            // The rounding to integer can't affect the outcome, since we know that
            // `lhs` is sufficiently large such that if `rhs` is close, it must be
            // an integer.
            lhs.$op(&(rhs as $IntT))
        }
    }};
}

// Must have IntT <= UintT in width.
macro_rules! int_uint_impl_body {
    ($IntT:ty, $UintT:ty, $_UnusedT:ty, $lhs:expr, $rhs:expr, $op:ident, $less:expr, $greater:expr, $nan:expr) => {{
        let lhs = $lhs;
        let rhs = $rhs;

        if lhs < 0 {
            $less
        } else {
            (lhs as $UintT).$op(&rhs)
        }
    }};
}

macro_rules! apply_impl_body {
    ($impl_body:ident, $Lhs:ty, $Rhs:ty, $CommonT:ty) => {
        impl PartialEq<NumOrd<$Rhs>> for NumOrd<$Lhs> {
            fn eq(&self, other: &NumOrd<$Rhs>) -> bool {
                $impl_body!($Lhs, $Rhs, $CommonT, self.0, other.0, eq, false, false, false)
            }
        }

        impl PartialOrd<NumOrd<$Rhs>> for NumOrd<$Lhs> {
            fn partial_cmp(&self, other: &NumOrd<$Rhs>) -> Option<Ordering> {
                $impl_body!(
                    $Lhs,
                    $Rhs,
                    $CommonT,
                    self.0,
                    other.0,
                    partial_cmp,
                    Some(Ordering::Less),
                    Some(Ordering::Greater),
                    None
                )
            }

            fn lt(&self, other: &NumOrd<$Rhs>) -> bool {
                $impl_body!($Lhs, $Rhs, $CommonT, self.0, other.0, lt, true, false, false)
            }

            fn le(&self, other: &NumOrd<$Rhs>) -> bool {
                $impl_body!($Lhs, $Rhs, $CommonT, self.0, other.0, le, true, false, false)
            }

            fn gt(&self, other: &NumOrd<$Rhs>) -> bool {
                $impl_body!($Lhs, $Rhs, $CommonT, self.0, other.0, gt, false, true, false)
            }

            fn ge(&self, other: &NumOrd<$Rhs>) -> bool {
                $impl_body!($Lhs, $Rhs, $CommonT, self.0, other.0, ge, false, true, false)
            }
        }

        // Reverse implementation.
        impl PartialEq<NumOrd<$Lhs>> for NumOrd<$Rhs> {
            fn eq(&self, other: &NumOrd<$Lhs>) -> bool {
                other == self
            }
        }

        impl PartialOrd<NumOrd<$Lhs>> for NumOrd<$Rhs> {
            fn partial_cmp(&self, other: &NumOrd<$Lhs>) -> Option<Ordering> {
                other.partial_cmp(self).map(|o| o.reverse())
            }

            fn lt(&self, other: &NumOrd<$Lhs>) -> bool {
                other > self
            }

            fn le(&self, other: &NumOrd<$Lhs>) -> bool {
                other >= self
            }

            fn gt(&self, other: &NumOrd<$Lhs>) -> bool {
                other < self
            }

            fn ge(&self, other: &NumOrd<$Lhs>) -> bool {
                other <= self
            }
        }
    };
}

apply_impl_body!(int_float_impl_body, i64, f32, ());
apply_impl_body!(int_float_impl_body, i128, f32, ());
apply_impl_body!(int_float_impl_body, i64, f64, ());
apply_impl_body!(int_float_impl_body, i128, f64, ());
apply_impl_body!(int_float_impl_body, u64, f32, ());
apply_impl_body!(int_float_impl_body, u128, f32, ());
apply_impl_body!(int_float_impl_body, u64, f64, ());
apply_impl_body!(int_float_impl_body, u128, f64, ());

apply_impl_body!(int_uint_impl_body, i8, u128, ());
apply_impl_body!(int_uint_impl_body, i16, u128, ());
apply_impl_body!(int_uint_impl_body, i32, u128, ());
apply_impl_body!(int_uint_impl_body, i64, u128, ());
apply_impl_body!(int_uint_impl_body, i128, u128, ());

macro_rules! impl_common_type {
    ($($T:ty, $U:ty => $C:ty;)*) => {$(
        apply_impl_body!(common_type_impl_body, $T, $U, $C);
    )*}
}

impl_common_type! {
    // See tools/gen.py.
      u8,   i8 =>  i16;
      u8,  u16 =>  u16;
      u8,  i16 =>  i16;
      u8,  u32 =>  u32;
      u8,  i32 =>  i32;
      u8,  u64 =>  u64;
      u8,  i64 =>  i64;
      u8, u128 => u128;
      u8, i128 => i128;
      u8,  f32 =>  f32;
      u8,  f64 =>  f64;
      i8,  u16 =>  i32;
      i8,  i16 =>  i16;
      i8,  u32 =>  i64;
      i8,  i32 =>  i32;
      i8,  u64 => i128;
      i8,  i64 =>  i64;
      i8, i128 => i128;
      i8,  f32 =>  f32;
      i8,  f64 =>  f64;
     u16,  i16 =>  i32;
     u16,  u32 =>  u32;
     u16,  i32 =>  i32;
     u16,  u64 =>  u64;
     u16,  i64 =>  i64;
     u16, u128 => u128;
     u16, i128 => i128;
     u16,  f32 =>  f32;
     u16,  f64 =>  f64;
     i16,  u32 =>  i64;
     i16,  i32 =>  i32;
     i16,  u64 => i128;
     i16,  i64 =>  i64;
     i16, i128 => i128;
     i16,  f32 =>  f32;
     i16,  f64 =>  f64;
     u32,  i32 =>  i64;
     u32,  u64 =>  u64;
     u32,  i64 =>  i64;
     u32, u128 => u128;
     u32, i128 => i128;
     u32,  f32 =>  f64;
     u32,  f64 =>  f64;
     i32,  u64 => i128;
     i32,  i64 =>  i64;
     i32, i128 => i128;
     i32,  f32 =>  f64;
     i32,  f64 =>  f64;
     u64,  i64 => i128;
     u64, u128 => u128;
     u64, i128 => i128;
     i64, i128 => i128;
     f32,  f64 =>  f64;
}

#[cfg(test)]
mod tests {
    use super::NumOrd;
    use rug::ops::Pow as _;
    use rug::{Integer, Rational};

    struct NumType<T> {
        pub interesting_values: Vec<Rational>,
        pub convert_exactly: fn(&Rational) -> Option<T>,
    }

    fn compare<T1, T2>(t1: &NumType<T1>, t2: &NumType<T2>)
    where
        T1: 'static + std::fmt::Display + Copy,
        T2: 'static + std::fmt::Display + Copy,
        NumOrd<T1>: PartialOrd<NumOrd<T2>>,
    {
        // Ordering between equal types needn't be tested
        if std::any::TypeId::of::<T1>() == std::any::TypeId::of::<T2>() {
            return;
        }

        let mut interesting_values = t1.interesting_values.iter().collect::<Vec<_>>();
        interesting_values.extend(&t2.interesting_values);
        interesting_values.sort_unstable();
        interesting_values.dedup();

        for r1 in &interesting_values {
            for r2 in &interesting_values {
                if let (Some(v1), Some(v2)) = ((t1.convert_exactly)(r1), (t2.convert_exactly)(r2)) {
                    let expected_ordering = r1.partial_cmp(r2).unwrap();
                    let got_ordering = NumOrd(v1).partial_cmp(&NumOrd(v2)).unwrap();

                    if expected_ordering != got_ordering {
                        panic!(
                            "{}_{}.cmp({}_{}) was {:?}, expected {:?}. (Raw values: {}, {})",
                            v1,
                            std::any::type_name::<T1>(),
                            v2,
                            std::any::type_name::<T2>(),
                            got_ordering,
                            expected_ordering,
                            r1,
                            r2,
                        );
                    }
                }
            }
        }
    }

    fn to_integer(x: &Rational) -> Option<&Integer> {
        if *x.denom() == 1 {
            Some(x.numer())
        } else {
            None
        }
    }
    fn interesting_values(bases: &[&Rational]) -> Vec<Rational> {
        let one_half = Rational::from((1, 2));

        let mut vals = Vec::new();
        for &val in bases {
            vals.push(val.clone());
            vals.push((val + &one_half).into());
            vals.push((val - &one_half).into());
            vals.push((val + 1_u32).into());
            vals.push((val - 1_u32).into());
        }
        vals
    }
    fn two_pow(exp: u32) -> Rational {
        Rational::from(2).pow(exp)
    }
    fn make_unsigned<T>(bits: u32, convert_exactly: fn(&Rational) -> Option<T>) -> NumType<T> {
        let min = Rational::from(0);
        let max = two_pow(bits) - 1_u32;
        NumType {
            interesting_values: interesting_values(&[&min, &max]),
            convert_exactly,
        }
    }
    fn make_signed<T>(bits: u32, convert_exactly: fn(&Rational) -> Option<T>) -> NumType<T> {
        let min = -two_pow(bits - 1);
        let max = two_pow(bits - 1) - 1_u32;
        NumType {
            interesting_values: interesting_values(&[&min, &max]),
            convert_exactly,
        }
    }

    #[test]
    fn test_everything() {
        macro_rules! compare_all_combinations {
            ($($type:ty, $type_data:ident;)*) => {
                macro_rules! compare_all_against {
                    ($given_type:ty, $given_type_data:ident) => {
                        // Compare all types against $given_type
                        $( compare::<$type, $given_type>(&$type_data, &$given_type_data); )*
                    };
                }
                // For each type, compare all other types against it
                $( compare_all_against!($type, $type_data); )*
            };
        }

        let u8_data = make_unsigned(8, |x| to_integer(x).and_then(|i| i.to_u8()));
        let u16_data = make_unsigned(16, |x| to_integer(x).and_then(|i| i.to_u16()));
        let u32_data = make_unsigned(32, |x| to_integer(x).and_then(|i| i.to_u32()));
        let u64_data = make_unsigned(64, |x| to_integer(x).and_then(|i| i.to_u64()));
        let u128_data = make_unsigned(128, |x| to_integer(x).and_then(|i| i.to_u128()));
        let i8_data = make_signed(8, |x| to_integer(x).and_then(|i| i.to_i8()));
        let i16_data = make_signed(16, |x| to_integer(x).and_then(|i| i.to_i16()));
        let i32_data = make_signed(32, |x| to_integer(x).and_then(|i| i.to_i32()));
        let i64_data = make_signed(64, |x| to_integer(x).and_then(|i| i.to_i64()));
        let i128_data = make_signed(128, |x| to_integer(x).and_then(|i| i.to_i128()));
        let f32_data = NumType {
            interesting_values: interesting_values(&[
                &-two_pow(24),  // int min
                &two_pow(24),   // int max
                &-two_pow(127), // float min
                &two_pow(127),  // float max
            ]),
            convert_exactly: |r| {
                (Rational::from_f32(r.to_f32()).as_ref() == Some(r)).then(|| r.to_f32())
            },
        };
        let f64_data = NumType {
            interesting_values: interesting_values(&[
                &-two_pow(53),   // int min
                &two_pow(53),    // int max
                &-two_pow(1023), // float min
                &two_pow(1023),  // float max
            ]),
            convert_exactly: |r| (r.to_f64() == *r).then(|| r.to_f64()),
        };

        // Verify correct ordering for all interesting values of all number type combinations
        compare_all_combinations!(
            u8, u8_data;
            u16, u16_data;
            u32, u32_data;
            u64, u64_data;
            u128, u128_data;
            i8, i8_data;
            i16, i16_data;
            i32, i32_data;
            i64, i64_data;
            i128, i128_data;
            f32, f32_data;
            f64, f64_data;
        );
    }
}
