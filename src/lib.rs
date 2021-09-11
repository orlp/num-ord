use core::cmp::Ordering;
use core::convert::TryInto;

#[derive(Copy, Clone, Debug, Hash)]
#[repr(transparent)]
struct RealOrd<T>(T);

macro_rules! signed_float_impl_body {
    ($IntT:ty, $FloatT:ty, $lhs:expr, $rhs:expr, $op:ident, $less:expr, $greater:expr, $nan:expr) => {
        if core::mem::size_of::<$IntT>() < core::mem::size_of::<$FloatT>() {
            // Integer always exactly representable, trivial implementation.
            ($lhs as $FloatT).$op(&$rhs)
        } else {
            // All integers equal or less than FLOAT_DENSE_INT_LIMIT
            // in magnitude are exactly representable in FloatT, the
            // next integer isn't.
            const FLOAT_DENSE_INT_LIMIT: u64 = 1u64 << <$FloatT>::MANTISSA_DIGITS;
            if $lhs.unsigned_abs() <= FLOAT_DENSE_INT_LIMIT.try_into().unwrap() {
                // self is exactly representable as an integer valued float.
                ($lhs as $FloatT).$op(&$rhs)
            } else if -(<$IntT>::MIN as $FloatT) <= $rhs {
                $less
            } else if <$IntT>::MIN as $FloatT > $rhs {
                $greater
            } else {
                // The rounding to integer can't affect the outcome, since we know that
                // `self` is sufficiently large such that if `other` is close, it must be
                // an integer.
                if $rhs.is_nan() {
                    // NaN is incomparable.
                    $nan
                } else {
                    $lhs.$op(&($rhs as $IntT))
                }
            }
        }
    };
}

macro_rules! apply_impl_body {
    ($impl_body:ident, $Lhs:ty, $Rhs:ty) => {
        impl PartialEq<$Rhs> for RealOrd<$Lhs> {
            fn eq(&self, other: &$Rhs) -> bool {
                $impl_body!($Lhs, $Rhs, self.0, *other, eq, false, false, false)
            }
        }

        impl PartialOrd<$Rhs> for RealOrd<$Lhs> {
            fn partial_cmp(&self, other: &$Rhs) -> Option<Ordering> {
                $impl_body!(
                    $Lhs,
                    $Rhs,
                    self.0,
                    *other,
                    partial_cmp,
                    Some(Ordering::Less),
                    Some(Ordering::Greater),
                    None
                )
            }

            fn lt(&self, other: &$Rhs) -> bool {
                $impl_body!($Lhs, $Rhs, self.0, *other, lt, true, false, false)
            }

            fn le(&self, other: &$Rhs) -> bool {
                $impl_body!($Lhs, $Rhs, self.0, *other, le, true, false, false)
            }

            fn gt(&self, other: &$Rhs) -> bool {
                $impl_body!($Lhs, $Rhs, self.0, *other, gt, false, true, false)
            }

            fn ge(&self, other: &$Rhs) -> bool {
                $impl_body!($Lhs, $Rhs, self.0, *other, ge, false, true, false)
            }
        }
    };
}

apply_impl_body!(signed_float_impl_body, i64, f64);

pub trait CommonType<T>
where
    Self: Sized,
{
    type CommonT: From<T> + From<Self>;
}

impl<T> CommonType<T> for T {
    type CommonT = T;
}

macro_rules! impl_common_type {
    ($($T:ty, $U:ty => $C:ty;)*) => {$(
        impl CommonType<$T> for $U {
            type CommonT = $C;
        }
        impl CommonType<$U> for $T {
            type CommonT = $C;
        }
    )*}
}

impl_common_type! {
    u8, i8 => i16;        i8, u16 => i32;     
    u8, u16 => u16;       i8, i16 => i16;     
    u8, i16 => i16;       i8, u32 => i64;     
    u8, u32 => u32;       i8, i32 => i32;     
    u8, i32 => i32;       i8, u64 => i128;    
    u8, u64 => u64;       i8, i64 => i64;     
    u8, i64 => i64;       i8, i128 => i128;   
    u8, u128 => u128;     i8, f32 => f32;     
    u8, i128 => i128;     i8, f64 => f64;     
    u8, f32 => f32;
    u8, f64 => f64;
    
    u16, i16 => i32;      i16, u32 => i64;   
    u16, u32 => u32;      i16, i32 => i32;   
    u16, i32 => i32;      i16, u64 => i128;  
    u16, u64 => u64;      i16, i64 => i64;   
    u16, i64 => i64;      i16, i128 => i128; 
    u16, u128 => u128;    i16, f32 => f32;   
    u16, i128 => i128;    i16, f64 => f64;   
    u16, f32 => f32;
    u16, f64 => f64;
    
    u32, i32 => i64;      i32, u64 => i128;  
    u32, u64 => u64;      i32, i64 => i64;   
    u32, i64 => i64;      i32, i128 => i128; 
    u32, u128 => u128;    i32, f32 => f64;   
    u32, i128 => i128;    i32, f64 => f64;   
    u32, f32 => f64;
    u32, f64 => f64;
    
    u64, i64 => i128;     i64, i128 => i128;
    u64, u128 => u128;
    u64, i128 => i128;
    
    f32, f64 => f64;
}




// impl PartialOrd<$Rhs> for RealOrd<$Lhs> {
//     fn partial_cmp(&self, other: &$Rhs) -> Option<Ordering> {
//         $impl_body!(
//             $Lhs,
//             $Rhs,
//             self.0,
//             *other,
//             partial_cmp,
//             Some(Ordering::Less),
//             Some(Ordering::Greater),
//             None
//         )
//     }

//     fn lt(&self, other: &$Rhs) -> bool {
//         $impl_body!($Lhs, $Rhs, self.0, *other, lt, true, false, false)
//     }

//     fn le(&self, other: &$Rhs) -> bool {
//         $impl_body!($Lhs, $Rhs, self.0, *other, le, true, false, false)
//     }

//     fn gt(&self, other: &$Rhs) -> bool {
//         $impl_body!($Lhs, $Rhs, self.0, *other, gt, false, true, false)
//     }

//     fn ge(&self, other: &$Rhs) -> bool {
//         $impl_body!($Lhs, $Rhs, self.0, *other, ge, false, true, false)
//     }
// }









// NO COMMON TYPE i8 u128
// NO COMMON TYPE i16 u128
// NO COMMON TYPE i32 u128
// NO COMMON TYPE i64 u128
// NO COMMON TYPE i128 u128

// NO COMMON TYPE i64 f32
// NO COMMON TYPE i64 f64
// NO COMMON TYPE i128 f32
// NO COMMON TYPE i128 f64
// NO COMMON TYPE u64 f32
// NO COMMON TYPE u64 f64
// NO COMMON TYPE u128 f32
// NO COMMON TYPE u128 f64

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
