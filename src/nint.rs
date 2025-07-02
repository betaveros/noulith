use num::bigint::{BigInt, Sign};
use num::pow::Pow;
use num::BigUint;
use num::Integer;
use num::{Signed, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};
use std::ops::{AddAssign, DivAssign, MulAssign};

use std::borrow::Cow;

#[derive(Debug, Clone)]
pub enum NInt {
    Small(i64),
    Big(BigInt),
}

macro_rules! forward {
    ($method:ident, $ty:ty) => {
        pub fn $method(&self) -> $ty {
            match self {
                NInt::Small(n) => n.$method(),
                NInt::Big(n) => n.$method(),
            }
        }
    };
}
impl From<BigInt> for NInt {
    fn from(x: BigInt) -> Self {
        match x.to_i64() {
            Some(x) => NInt::Small(x),
            None => NInt::Big(x),
        }
    }
}
impl NInt {
    pub fn usize(x: usize) -> Self {
        match x.to_i64() {
            Some(x) => NInt::Small(x),
            None => NInt::Big(BigInt::from(x)),
        }
    }
    pub fn u64(x: u64) -> Self {
        match x.to_i64() {
            Some(x) => NInt::Small(x),
            None => NInt::Big(BigInt::from(x)),
        }
    }
}
impl<'a> NInt {
    pub fn to_bigint(&'a self) -> Cow<'a, BigInt> {
        match self {
            NInt::Small(n) => Cow::Owned(BigInt::from(*n)),
            NInt::Big(n) => Cow::Borrowed(n),
        }
    }
    forward!(to_f64, Option<f64>);
    forward!(to_i32, Option<i32>);
    forward!(to_i64, Option<i64>);
    forward!(to_isize, Option<isize>);
    forward!(to_u32, Option<u32>);
    forward!(to_u8, Option<u8>);
    forward!(to_usize, Option<usize>);
    forward!(to_u64, Option<u64>);
    forward!(is_zero, bool);
    forward!(is_positive, bool);
    forward!(is_negative, bool);
}
impl NInt {
    pub fn into_bigint(self) -> BigInt {
        match self {
            NInt::Small(n) => BigInt::from(n),
            NInt::Big(n) => n,
        }
    }
}

macro_rules! forward_display {
    ($impl:ident) => {
        impl fmt::$impl for NInt {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                match self {
                    NInt::Small(n) => fmt::$impl::fmt(n, formatter),
                    NInt::Big(n) => fmt::$impl::fmt(n, formatter),
                }
            }
        }
    };
}
forward_display!(Display);
forward_display!(LowerHex);
forward_display!(UpperHex);
forward_display!(Binary);
forward_display!(Octal);

macro_rules! impl_binary {
    ($imp:ident, $method:ident, $func:expr) => {
        impl $imp<NInt> for NInt {
            type Output = NInt;
            fn $method(self, other: NInt) -> NInt {
                match (&self, &other) {
                    (NInt::Small(a), NInt::Small(b)) => NInt::Small($func(*a, *b)),
                    _ => NInt::Big($func(self.into_bigint(), other.into_bigint())),
                }
            }
        }
        impl $imp<&NInt> for NInt {
            type Output = NInt;
            fn $method(self, other: &NInt) -> NInt {
                match (&self, other) {
                    (NInt::Small(a), NInt::Small(b)) => NInt::Small($func(*a, *b)),
                    _ => NInt::Big(match other {
                        NInt::Big(b) => $func(self.into_bigint(), b),
                        NInt::Small(b) => $func(self.into_bigint(), BigInt::from(*b)),
                    }),
                }
            }
        }
        impl $imp<NInt> for &NInt {
            type Output = NInt;
            fn $method(self, other: NInt) -> NInt {
                match (self, &other) {
                    (NInt::Small(a), NInt::Small(b)) => NInt::Small($func(*a, *b)),
                    _ => NInt::Big(match self {
                        NInt::Big(a) => $func(a, other.into_bigint()),
                        NInt::Small(a) => $func(BigInt::from(*a), other.into_bigint()),
                    }),
                }
            }
        }
        impl $imp<&NInt> for &NInt {
            type Output = NInt;
            fn $method(self, other: &NInt) -> NInt {
                match (self, other) {
                    (NInt::Small(a), NInt::Small(b)) => NInt::Small($func(*a, *b)),
                    (NInt::Big(a), NInt::Small(b)) => NInt::Big($func(a, BigInt::from(*b))),
                    (NInt::Small(a), NInt::Big(b)) => NInt::Big($func(BigInt::from(*a), b)),
                    (NInt::Big(a), NInt::Big(b)) => NInt::Big($func(a, b)),
                }
            }
        }
    };
}

impl_binary!(BitAnd, bitand, BitAnd::bitand);
impl_binary!(BitOr, bitor, BitOr::bitor);
impl_binary!(BitXor, bitxor, BitXor::bitxor);

macro_rules! impl_binary_checked {
    ($imp:ident, $method:ident, $func:expr, $checked:ident) => {
        impl $imp<NInt> for NInt {
            type Output = NInt;
            fn $method(self, other: NInt) -> NInt {
                match (&self, &other) {
                    (NInt::Small(a), NInt::Small(b)) => {
                        if let Some(r) = i64::$checked(*a, *b) {
                            return NInt::Small(r);
                        }
                    }
                    _ => (),
                }
                NInt::Big($func(self.into_bigint(), other.into_bigint()))
            }
        }
        impl $imp<&NInt> for NInt {
            type Output = NInt;
            fn $method(self, other: &NInt) -> NInt {
                match (&self, other) {
                    (NInt::Small(a), NInt::Small(b)) => {
                        if let Some(r) = i64::$checked(*a, *b) {
                            return NInt::Small(r);
                        }
                    }
                    _ => (),
                }
                NInt::Big(match other {
                    NInt::Big(b) => $func(self.into_bigint(), b),
                    NInt::Small(b) => $func(self.into_bigint(), BigInt::from(*b)),
                })
            }
        }
        impl $imp<NInt> for &NInt {
            type Output = NInt;
            fn $method(self, other: NInt) -> NInt {
                match (self, &other) {
                    (NInt::Small(a), NInt::Small(b)) => {
                        if let Some(r) = i64::$checked(*a, *b) {
                            return NInt::Small(r);
                        }
                    }
                    _ => (),
                }
                NInt::Big(match self {
                    NInt::Big(a) => $func(a, other.into_bigint()),
                    NInt::Small(a) => $func(BigInt::from(*a), other.into_bigint()),
                })
            }
        }
        impl $imp<&NInt> for &NInt {
            type Output = NInt;
            fn $method(self, other: &NInt) -> NInt {
                match (self, other) {
                    (NInt::Small(a), NInt::Small(b)) => {
                        if let Some(r) = i64::$checked(*a, *b) {
                            return NInt::Small(r);
                        }
                    }
                    _ => (),
                }
                NInt::Big(match (self, other) {
                    (NInt::Small(a), NInt::Small(b)) => $func(BigInt::from(*a), BigInt::from(*b)),
                    (NInt::Big(a), NInt::Small(b)) => $func(a, BigInt::from(*b)),
                    (NInt::Small(a), NInt::Big(b)) => $func(BigInt::from(*a), b),
                    (NInt::Big(a), NInt::Big(b)) => $func(a, b),
                })
            }
        }
    };
}

impl_binary_checked!(Add, add, Add::add, checked_add);
impl_binary_checked!(Sub, sub, Sub::sub, checked_sub);
impl_binary_checked!(Mul, mul, Mul::mul, checked_mul);
impl_binary_checked!(Div, div, Div::div, checked_div);
impl_binary_checked!(Rem, rem, Rem::rem, checked_rem);

impl Neg for NInt {
    type Output = NInt;

    fn neg(self) -> NInt {
        NInt::from(-self.into_bigint())
    }
}
impl Neg for &NInt {
    type Output = NInt;

    fn neg(self) -> NInt {
        NInt::from(-self.to_bigint().into_owned())
    }
}
impl Not for NInt {
    type Output = NInt;

    fn not(self) -> NInt {
        match self {
            NInt::Small(a) => NInt::Small(!a),
            NInt::Big(a) => NInt::Big(!a),
        }
    }
}
impl Not for &NInt {
    type Output = NInt;

    fn not(self) -> NInt {
        match self {
            NInt::Small(a) => NInt::Small(!a),
            NInt::Big(a) => NInt::Big(!a),
        }
    }
}
impl PartialEq for NInt {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (NInt::Small(a), NInt::Small(b)) => a == b,
            (NInt::Small(a), NInt::Big(b)) => b.to_i64().map_or(false, |n| *a == n),
            (NInt::Big(a), NInt::Small(b)) => a.to_i64().map_or(false, |n| n == *b),
            (NInt::Big(a), NInt::Big(b)) => a == b,
        }
    }
}
impl Eq for NInt {}
impl PartialOrd for NInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (NInt::Small(a), NInt::Small(b)) => a.partial_cmp(b),
            _ => (&*self.to_bigint()).partial_cmp(&*other.to_bigint()),
        }
    }
}
impl Ord for NInt {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (NInt::Small(a), NInt::Small(b)) => a.cmp(b),
            _ => (&*self.to_bigint()).cmp(&*other.to_bigint()),
        }
    }
}
impl Hash for NInt {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            NInt::Small(a) => state.write_i64(*a),
            NInt::Big(a) => match a.to_i64() {
                Some(a) => state.write_i64(a),
                None => a.hash(state),
            },
        }
    }
}

impl<'a> NInt {
    pub fn magnitude(&'a self) -> Cow<'a, BigUint> {
        match self.to_bigint() {
            Cow::Owned(a) => Cow::Owned(a.into_parts().1),
            Cow::Borrowed(a) => Cow::Borrowed(a.magnitude()),
        }
    }
}
impl NInt {
    pub fn div_floor(&self, other: &NInt) -> NInt {
        NInt::Big(self.to_bigint().div_floor(&*other.to_bigint()))
    }
    pub fn mod_floor(&self, other: &NInt) -> NInt {
        NInt::Big(self.to_bigint().mod_floor(&*other.to_bigint()))
    }
    pub fn abs(&self) -> NInt {
        match self {
            NInt::Small(x) => match x.checked_abs() {
                Some(x) => return NInt::Small(x),
                None => (),
            },
            NInt::Big(_) => (),
        }
        NInt::Big(self.to_bigint().abs())
    }
    pub fn sign(&self) -> Sign {
        match self {
            NInt::Small(a) => {
                if *a == 0 {
                    Sign::NoSign
                } else if *a > 0 {
                    Sign::Plus
                } else {
                    Sign::Minus
                }
            }
            NInt::Big(a) => a.sign(),
        }
    }
    pub fn pow(&self, other: u32) -> Self {
        NInt::Big((&*self.to_bigint()).pow(other))
    }
    pub fn pow_maybe_recip(&self, other: &Self) -> (bool, Self) {
        match other.sign() {
            Sign::NoSign => (false, NInt::Small(1)),
            Sign::Plus => (
                false,
                NInt::Big(Pow::pow(&*self.to_bigint(), &*other.magnitude())),
            ),
            Sign::Minus => (
                true,
                NInt::Big(Pow::pow(&*self.to_bigint(), &*other.magnitude())),
            ),
        }
    }
    pub fn signum(&self) -> NInt {
        match self {
            NInt::Small(a) => NInt::Small(a.signum()),
            NInt::Big(a) => match a.sign() {
                Sign::Minus => NInt::Small(1),
                Sign::NoSign => NInt::Small(0),
                Sign::Plus => NInt::Small(-1),
            },
        }
    }
    pub fn gcd(&self, other: &Self) -> NInt {
        NInt::Big(Integer::gcd(&*self.to_bigint(), &*other.to_bigint()))
    }
    pub fn lcm(&self, other: &Self) -> NInt {
        NInt::Big(Integer::lcm(&*self.to_bigint(), &*other.to_bigint()))
    }
    pub fn sqrt(&self) -> NInt {
        NInt::Big(self.to_bigint().sqrt())
    }
    pub fn lte(&self, other: i64) -> bool {
        match self {
            NInt::Small(a) => *a <= other,
            NInt::Big(a) => a <= &BigInt::from(other),
        }
    }
    pub fn lazy_is_prime(self: &Self) -> bool {
        if self.lte(1) {
            false
        } else if self.lte(3) {
            true
        } else if (self % NInt::Small(2)).is_zero() || (self % NInt::Small(3)).is_zero() {
            false
        } else {
            let s = self.sqrt(); // truncates
            let mut f = NInt::Small(5);
            loop {
                if f > s {
                    return true;
                }
                if (self % &f).is_zero() {
                    return false;
                }

                f += 2;
                if f > s {
                    return true;
                }
                if (self % &f).is_zero() {
                    return false;
                }

                f += 4;
            }
        }
    }
    pub fn factorial(&self) -> NInt {
        let mut ret = NInt::Small(1);
        let mut i = NInt::Small(1);
        while &i < self {
            ret = ret * &i;
            i += 1;
        }
        ret
    }
}

impl Shl<usize> for NInt {
    type Output = Self;
    fn shl(self, other: usize) -> Self {
        NInt::Big(self.into_bigint() << other)
    }
}
impl Shr<usize> for NInt {
    type Output = Self;
    fn shr(self, other: usize) -> Self {
        NInt::Big(self.into_bigint() >> other)
    }
}

impl AddAssign<&NInt> for NInt {
    fn add_assign(&mut self, other: &NInt) {
        *self = mem::replace(self, NInt::Small(0)) + &*other;
    }
}

impl MulAssign<&NInt> for NInt {
    fn mul_assign(&mut self, other: &NInt) {
        *self = mem::replace(self, NInt::Small(0)) * &*other;
    }
}

impl AddAssign<i64> for NInt {
    fn add_assign(&mut self, other: i64) {
        *self += &NInt::Small(other)
    }
}

impl DivAssign<u32> for NInt {
    fn div_assign(&mut self, other: u32) {
        match self {
            NInt::Small(a) => *a /= other as i64,
            NInt::Big(a) => *a /= other,
        }
    }
}
