// a lot ripped from paradoc-rust, but we can be a sensible language that doesn't worry about chars
// and doesn't just randomly coerce floats like ints...

use std::cmp::Ordering;
use std::ops::{Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Neg, Not, Shl, Shr, Deref};
use std::ops::{AddAssign, SubAssign};
use std::iter::{Sum, Product};
use std::hash::{Hash, Hasher};
use std::mem;
use std::fmt;
use num::Integer;
use num::bigint::BigInt;
use num::bigint::ToBigInt;
use num::complex::Complex64;
use num::{Zero, One, Signed, ToPrimitive};
use num::pow::Pow;

use crate::gamma;

#[derive(Debug, Clone)]
pub enum NNum {
    Int(BigInt),
    Float(f64),
    Complex(Complex64),
}

// Simple utility to collapse two Option layers into one
pub fn char_from_bigint(n: &BigInt) -> Option<char> {
    std::char::from_u32(n.to_u32()?)
}

impl fmt::Display for NNum {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NNum::Int(n) => write!(formatter, "{}", n),
            NNum::Float(f) => write!(formatter, "{}", f),
            NNum::Complex(z) => write!(formatter, "{}", z),
        }
    }
}

impl From<BigInt> for NNum {
    fn from(x: BigInt) -> Self { NNum::Int(x) }
}
impl From<i32> for NNum {
    fn from(x: i32) -> Self { NNum::Int(BigInt::from(x)) }
}
impl From<f64> for NNum {
    fn from(x: f64) -> Self { NNum::Float(x) }
}
impl From<usize> for NNum {
    fn from(x: usize) -> Self { NNum::Int(BigInt::from(x)) }
}
impl From<Complex64> for NNum {
    fn from(z: Complex64) -> Self { NNum::Complex(z) }
}

trait PowIF: Sized {
    fn powi(self, n: i32) -> Self;
    fn powf(self, f: f64) -> Self;
    fn powif(self, b: &BigInt) -> Self {
        match b.to_i32() {
            Some(ib) => self.powi(ib),
            None => self.powf(bigint_to_f64_or_inf(b)),
        }
    }
}
impl PowIF for f64 {
    fn powi(self, n: i32) -> f64 { f64::powi(self, n) }
    fn powf(self, f: f64) -> f64 { f64::powf(self, f) }
}
impl PowIF for Complex64 {
    fn powi(self, n: i32) -> Complex64 { Complex64::powi(&self, n) }
    fn powf(self, f: f64) -> Complex64 { Complex64::powf(self, f) }
}

fn powf_pdnum(a: f64, b: f64) -> NNum {
    let fx = a.powf(b);
    if fx.is_nan() {
        let zx = Complex64::from(a).powf(b);
        if !zx.re.is_nan() && !zx.im.is_nan() {
            return NNum::from(zx)
        }
    }
    NNum::from(fx)
}

fn powif_pdnum(a: f64, b: &BigInt) -> NNum {
    let fx = a.powif(b);
    if fx.is_nan() {
        let zx = Complex64::from(a).powif(b);
        if !zx.re.is_nan() && !zx.im.is_nan() {
            return NNum::from(zx)
        }
    }
    NNum::from(fx)
}


fn pow_big_ints(a: &BigInt, b: &BigInt) -> NNum {
    match b.sign() {
        num::bigint::Sign::NoSign => NNum::from(0),
        num::bigint::Sign::Plus => NNum::from(Pow::pow(a, b.magnitude())),
        num::bigint::Sign::Minus => NNum::from(powif_pdnum(bigint_to_f64_or_inf(a), b)),
    }
}

fn factorial_big_int(a: &BigInt) -> BigInt {
    let mut ret = BigInt::one();
    for i in num::range_inclusive(BigInt::one(), BigInt::clone(a)) {
        ret *= i;
    }
    ret
}

fn bigint_to_f64_or_inf(i: &BigInt) -> f64 {
    i.to_f64().unwrap_or_else(|| {
        if i.is_positive() { f64::INFINITY } else { f64::NEG_INFINITY }
    })
}

macro_rules! forward_int_coercion {
    ($method:ident) => {
        pub fn $method(&self) -> NNum {
            match self {
                NNum::Int(_) => self.clone(),
                NNum::Float(f) => f.$method().to_bigint().map_or(self.clone(), NNum::Int),
                NNum::Complex(z) => z.re.$method().to_bigint().map_or(self.clone(), NNum::Int),
            }
        }
    };
}

impl NNum {
    pub fn one_j() -> Self {
        Self::from(Complex64::new(0.0, 1.0))
    }

    pub fn to_string(&self) -> String {
        match self {
            NNum::Int(n) => n.to_string(),
            NNum::Float(f) => f.to_string(),
            NNum::Complex(z) => z.to_string(),
        }
    }

    pub fn repr(&self) -> String {
        match self {
            NNum::Int(n)     => n.to_string(),
            NNum::Float(f)   => f.to_string(),
            NNum::Complex(z) => format!("{}+{}j", z.re, z.im),
        }
    }

    forward_int_coercion!(ceil);
    forward_int_coercion!(floor);
    forward_int_coercion!(trunc);
    forward_int_coercion!(round);

    pub fn abs(&self) -> NNum {
        match self {
            NNum::Int(k) => NNum::Int(k.abs()),
            NNum::Float(f) => NNum::Float(f.abs()),
            NNum::Complex(z) => NNum::Float(z.norm()),
        }
    }

    pub fn signum(&self) -> NNum {
        match self {
            NNum::Int(k) => NNum::Int(k.signum()),
            NNum::Float(f) => {
                // This is NOT Rust's f64's signum. We want +/-0 to give 0 (for consistency with
                // integers)
                if f.is_nan() {
                    self.clone()
                } else if *f == 0.0 {
                    NNum::from(0)
                } else if *f > 0.0 {
                    NNum::from(1)
                } else {
                    NNum::from(-1)
                }
            }
            NNum::Complex(z) => {
                if z.is_zero() {
                    self.clone()
                } else {
                    NNum::Complex(z / z.norm())
                }
            }
        }
    }

    pub fn is_nonzero(&self) -> bool {
        match self {
            NNum::Int(i) => !i.is_zero(),
            NNum::Float(f) => *f != 0.0,
            NNum::Complex(z) => !z.is_zero(),
        }
    }

    pub fn to_f64(&self) -> Option<f64> {
        match self {
            NNum::Int(i) => i.to_f64(),
            NNum::Float(f) => Some(*f),
            NNum::Complex(_) => None,
        }
    }

    pub fn to_f64_or_inf_or_complex(&self) -> Result<f64, Complex64> {
        match self {
            NNum::Int(i) => Ok(bigint_to_f64_or_inf(i)),
            NNum::Float(f) => Ok(*f),
            NNum::Complex(z) => Err(*z),
        }
    }

    pub fn to_f64_re_or_inf(&self) -> f64 {
        match self.to_f64_or_inf_or_complex() {
            Err(z) => z.re,
            Ok(x) => x,
        }
    }

    pub fn to_complex_or_inf(&self) -> Complex64 {
        match self.to_f64_or_inf_or_complex() {
            Err(z) => z,
            Ok(x) => Complex64::from(x),
        }
    }

    pub fn real_part(&self) -> NNum {
        match self {
            NNum::Int(_) => self.clone(),
            NNum::Float(_) => self.clone(),
            NNum::Complex(z) => NNum::Float(z.re),
        }
    }

    pub fn imaginary_part(&self) -> NNum {
        match self {
            NNum::Int(_) => NNum::Int(BigInt::from(0)),
            NNum::Float(_) => NNum::Float(0.0),
            NNum::Complex(z) => NNum::Float(z.im),
        }
    }

    pub fn sqrt(&self) -> Option<NNum> {
        self.to_f64().map(|x| NNum::Float(x.sqrt()))
    }

    pub fn pow(&self, e: u32) -> NNum {
        match self {
            NNum::Int(i) => NNum::Int(i.pow(e)),
            NNum::Float(f) => NNum::Float(f.powi(e as i32)),
            NNum::Complex(z) => NNum::Complex(z.powi(e as i32)),
        }
    }

    pub fn pow_num(&self, other: &NNum) -> NNum {
        match (self, other) {
            (NNum::Int   (a), NNum::Int   (b)) => pow_big_ints(a, b),
            (NNum::Int   (a), NNum::Float (b)) => powf_pdnum(bigint_to_f64_or_inf(a), *b),

            (NNum::Float (a),  NNum::Float(b)) => powf_pdnum(*a, *b),
            (NNum::Complex(a), NNum::Float(b)) => NNum::from(a.powf(*b)),

            (NNum::Float  (a), NNum::Int (b)) => powif_pdnum(*a, b),
            (NNum::Complex(a), NNum::Int (b)) => NNum::from(a.powif(b)),

            (a, NNum::Complex(zb)) => NNum::Complex(a.to_complex_or_inf().pow(zb)),
        }
    }

    pub fn factorial(&self) -> NNum {
        match self {
            NNum::Int(a) => NNum::Int(factorial_big_int(a)),
            NNum::Float(f) => NNum::Float(gamma::gamma(f + 1.0)),
            NNum::Complex(_) => {
                panic!("OK you should be able to compute the factorial of a complex number but it's hard");
            }
        }
    }

    pub fn is_nan(&self) -> bool {
        match self {
            NNum::Int(_) => false,
            NNum::Float(f) => f.is_nan(),
            NNum::Complex(z) => z.re.is_nan() || z.im.is_nan(),
        }
    }

    pub fn to_bigint(&self) -> Option<&BigInt> {
        match self {
            NNum::Int(n) => Some(n),
            _ => None,
        }
    }

    pub fn into_bigint(self) -> Option<BigInt> {
        match self {
            NNum::Int(n) => Some(n),
            _ => None,
        }
    }

    pub fn to_isize(&self) -> Option<isize> {
        match self {
            NNum::Int(n) => n.to_isize(),
            _ => None,
        }
    }

    pub fn to_usize(&self) -> Option<usize> {
        match self {
            NNum::Int(n) => n.to_usize(),
            _ => None,
        }
    }

    pub fn iverson(b: bool) -> Self { NNum::from(if b { 1 } else { 0 }) }
}

// this seems... nontrivial??
fn cmp_bigint_f64(a: &BigInt, b: &f64) -> Option<Ordering> {
    if let Some(bi) = b.to_bigint() {
        Some(a.cmp(&bi))
    } else if b.is_infinite() {
        if b.is_sign_positive() {
            Some(Ordering::Less)
        } else {
            Some(Ordering::Greater)
        }
    } else {
        b.floor().to_bigint().map(|bi| {
            match a.cmp(&bi) {
                Ordering::Less    => Ordering::Less,
                Ordering::Equal   => Ordering::Less,
                Ordering::Greater => Ordering::Greater,
            }
        })
    }
}

// useful to project down to this for ease of doing stuff
enum NNumReal<'a> {
    Int(&'a BigInt),
    Float(f64),
}

impl<'a> PartialEq for NNumReal<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (NNumReal::Int  (a), NNumReal::Int  (b)) => a == b,
            (NNumReal::Int  (a), NNumReal::Float(b)) => b.to_bigint().map_or(false, |x| &x == *a),
            (NNumReal::Float(a), NNumReal::Int  (b)) => a.to_bigint().map_or(false, |x| &x == *b),
            (NNumReal::Float(a), NNumReal::Float(b)) => a == b,
        }
    }
}

impl<'a> PartialOrd for NNumReal<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (NNumReal::Int  (a), NNumReal::Int  (b)) => Some(a.cmp(b)),
            (NNumReal::Int  (a), NNumReal::Float(b)) => cmp_bigint_f64(a, b),
            (NNumReal::Float(a), NNumReal::Int  (b)) => cmp_bigint_f64(b, a).map(|ord| ord.reverse()),
            (NNumReal::Float(a), NNumReal::Float(b)) => a.partial_cmp(b),
        }
    }
}

impl<'a> NNumReal<'a> {
    fn total_cmp_small_nan(&self, other: &Self) -> Ordering {
        match (self, other) {
            (NNumReal::Int  (a), NNumReal::Int  (b)) => a.cmp(b),
            (NNumReal::Int  (a), NNumReal::Float(b)) => cmp_bigint_f64(a, b).unwrap_or(Ordering::Greater),
            (NNumReal::Float(a), NNumReal::Int  (b)) => cmp_bigint_f64(b, a).map_or(Ordering::Less, |ord| ord.reverse()),
            (NNumReal::Float(a), NNumReal::Float(b)) => a.partial_cmp(b).unwrap_or(b.is_nan().cmp(&a.is_nan())), // note swap
        }
    }

    fn total_cmp_big_nan(&self, other: &Self) -> Ordering {
        match (self, other) {
            (NNumReal::Int  (a), NNumReal::Int  (b)) => a.cmp(b),
            (NNumReal::Int  (a), NNumReal::Float(b)) => cmp_bigint_f64(a, b).unwrap_or(Ordering::Less),
            (NNumReal::Float(a), NNumReal::Int  (b)) => cmp_bigint_f64(b, a).map_or(Ordering::Greater, |ord| ord.reverse()),
            (NNumReal::Float(a), NNumReal::Float(b)) => a.partial_cmp(b).unwrap_or(a.is_nan().cmp(&b.is_nan())),
        }
    }
}

impl<'a> NNum {
    fn project_to_reals(&'a self) -> (NNumReal<'a>, NNumReal<'a>) {
        match self {
            NNum::Int(a) => (NNumReal::Int(a), NNumReal::Float(0.0)),
            NNum::Float(a) => (NNumReal::Float(*a), NNumReal::Float(0.0)),
            NNum::Complex(z) => (NNumReal::Float(z.re), NNumReal::Float(z.im)),
        }
    }
}

impl PartialEq for NNum {
    fn eq(&self, other: &Self) -> bool {
        self.project_to_reals() == other.project_to_reals()
    }
}

// TODO: Watch https://github.com/rust-lang/rust/issues/72599, we will probably want total
// orderings in some cases.

impl PartialOrd for NNum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.project_to_reals().partial_cmp(&other.project_to_reals())
    }
}

impl NNum {
    // (considers NaNs equal)
    fn total_cmp_small_nan(&self, other: &Self) -> Ordering {
        let (ra, ia) = self.project_to_reals();
        let (rb, ib) = other.project_to_reals();
        ra.total_cmp_small_nan(&rb).then(ia.total_cmp_small_nan(&ib))
    }

    fn total_cmp_big_nan(&self, other: &Self) -> Ordering {
        let (ra, ia) = self.project_to_reals();
        let (rb, ib) = other.project_to_reals();
        ra.total_cmp_big_nan(&rb).then(ia.total_cmp_big_nan(&ib))
    }
}


// Tries to follow the laws
#[derive(Debug, Clone)]
pub struct NTotalNum(pub NNum);

impl fmt::Display for NTotalNum {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "{}t", self.0)
    }
}


impl Deref for NTotalNum {
    type Target = NNum;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// Considers NaNs equal
impl PartialEq for NTotalNum {
    fn eq(&self, other: &Self) -> bool {
        NNum::eq(&**self, &**other) || self.is_nan() && other.is_nan()
    }
}

impl Eq for NTotalNum {}

impl Ord for NTotalNum {
    fn cmp(&self, other: &Self) -> Ordering {
        self.total_cmp_small_nan(&**other)
    }
}
impl PartialOrd for NTotalNum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

fn consistent_hash_f64<H: Hasher>(f: f64, state: &mut H) {
    match f.to_bigint() {
        Some(s) => BigInt::hash(&s, state),
        None => if f.is_nan() {
            // some nan from wikipedia (not that this matters)
            state.write_u64(0x7FF0000000000001u64)
        } else {
            // I *think* this actually obeys the laws...?
            // (+/- 0 are handled by the bigint branch)
            f.to_bits().hash(state)
        }
    }
}

impl Hash for NTotalNum {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &**self {
            NNum::Int(a) => BigInt::hash(&a, state),
            NNum::Float(f) => consistent_hash_f64(*f, state),
            NNum::Complex(z) => {
                consistent_hash_f64(z.re, state);
                consistent_hash_f64(z.im, state);
            }
        }
    }
}

// https://github.com/rust-lang/rust/pull/64047 will give us these for free
// note that we follow the Rust implementations and in particular the f64 implementations of min
// and max: when equal, pretend the left is smaller than the right; if one of its inputs is NaN,
// return the other

impl NNum {
    pub fn min<'a>(&'a self, other: &'a Self) -> &'a NNum {
        match self.total_cmp_big_nan(other) {
            Ordering::Greater => other,
            _ => self,
        }
    }

    pub fn max<'a>(&'a self, other: &'a Self) -> &'a NNum {
        match self.total_cmp_small_nan(other) {
            Ordering::Greater => self,
            _ => other,
        }
    }

    pub fn min_consuming(self, other: Self) -> NNum {
        match self.total_cmp_big_nan(&other) {
            Ordering::Greater => other,
            _ => self,
        }
    }

    pub fn max_consuming(self, other: Self) -> NNum {
        match self.total_cmp_small_nan(&other) {
            Ordering::Greater => self,
            _ => other,
        }
    }
}

// ????????????????????
trait SoftDeref {
    type Output;
    fn soft_deref(self) -> Self::Output;
}
impl SoftDeref for Complex64 {
    type Output = Complex64;
    fn soft_deref(self) -> Complex64 { self }
}
impl SoftDeref for &Complex64 {
    type Output = Complex64;
    fn soft_deref(self) -> Complex64 { *self }
}
impl SoftDeref for f64 {
    type Output = f64;
    fn soft_deref(self) -> f64 { self }
}
impl SoftDeref for &f64 {
    type Output = f64;
    fn soft_deref(self) -> f64 { *self }
}

// ????????
macro_rules! binary_match {
    ($a:expr, $b:expr, $intmethod:expr, $floatmethod:expr, $complexmethod:expr) => {
        match ($a, $b) {
            (NNum::Complex(za), b) => NNum::Complex($complexmethod(za.soft_deref(), b.to_complex_or_inf())),
            (a, NNum::Complex(zb)) => NNum::Complex($complexmethod(a.to_complex_or_inf(), zb.soft_deref())),

            (NNum::Float(fa), b) => NNum::Float($floatmethod(fa.soft_deref(), b.to_f64_or_inf_or_complex().expect("complex not elim"))),
            (a, NNum::Float(fb)) => NNum::Float($floatmethod(a.to_f64_or_inf_or_complex().expect("complex not elim"), fb.soft_deref())),

            (NNum::Int  (a), NNum::Int  (b)) => NNum::Int($intmethod(a, b)),
        }
    };
}

macro_rules! forward_impl_binary_method {
    ($imp:ident, $method:ident) => {
        impl $imp<NNum> for NNum {
            type Output = NNum;

            fn $method(self, other: NNum) -> NNum { (&self).$method(&other) }
        }
    };
}

macro_rules! impl_binary_method_1 {
    ($self:ty, $other:ty, $imp:ident, $method:ident, $intmethod:expr, $floatmethod:expr, $complexmethod:expr) => {
        impl $imp<$other> for $self {
            type Output = NNum;

            fn $method(self, other: $other) -> NNum {
                binary_match!(self, other, $intmethod, $floatmethod, $complexmethod)
            }
        }
    };
}

macro_rules! impl_binary_method_4 {
    ($imp:ident, $method:ident, $intmethod:expr, $floatmethod:expr, $complexmethod:expr) => {
        impl_binary_method_1!(&NNum, &NNum, $imp, $method, $intmethod, $floatmethod, $complexmethod);
        impl_binary_method_1!(&NNum, NNum, $imp, $method, $intmethod, $floatmethod, $complexmethod);
        impl_binary_method_1!(NNum, &NNum, $imp, $method, $intmethod, $floatmethod, $complexmethod);
        impl_binary_method_1!(NNum, NNum, $imp, $method, $intmethod, $floatmethod, $complexmethod);
    };
}

fn dumb_complex_div_floor(a: Complex64, b: Complex64) -> Complex64 {
    let c = a / b;
    Complex64::new(c.re.floor(), c.im.floor())
}

// hmmm... https://github.com/rust-num/num-bigint/issues/146
impl NNum {
    pub fn div_floor(&self, other: &NNum) -> NNum {
        binary_match!(self, other, Integer::div_floor, f64::div_euclid, dumb_complex_div_floor)
    }
    pub fn mod_floor(&self, other: &NNum) -> NNum {
        binary_match!(self, other, Integer::mod_floor, f64::rem_euclid, Rem::rem)
    }
}

impl_binary_method_4!(Add, add, Add::add, Add::add, Add::add);
impl_binary_method_4!(Sub, sub, Sub::sub, Sub::sub, Sub::sub);
impl_binary_method_4!(Mul, mul, Mul::mul, Mul::mul, Mul::mul);
impl_binary_method_4!(Rem, rem, Rem::rem, Rem::rem, Rem::rem);

// Integer::mod_floor takes references only
// impl_binary_method!(Rem, rem, Integer::mod_floor, f64::rem_euclid, Rem::rem);

impl Div<&NNum> for &NNum {
    type Output = NNum;
    fn div(self, other: &NNum) -> NNum {
        let a = self.to_f64_or_inf_or_complex();
        let b = other.to_f64_or_inf_or_complex();
        match (a, b) {
            (Ok (fa), Ok (fb)) => NNum::Float(fa / fb),
            (Err(za), Ok (fb)) => NNum::Complex(Complex64::from(za / fb)),
            (Ok (fa), Err(zb)) => NNum::Complex(Complex64::from(fa / zb)),
            (Err(za), Err(zb)) => NNum::Complex(Complex64::from(za / zb)),
        }
    }
}

forward_impl_binary_method!(Div, div);

impl Neg for NNum {
    type Output = NNum;

    fn neg(self) -> NNum {
        match self {
            NNum::Int(n) => NNum::Int(-n),
            NNum::Float(f) => NNum::Float(-f),
            NNum::Complex(z) => NNum::Complex(-z),
        }
    }
}
impl Neg for &NNum {
    type Output = NNum;

    fn neg(self) -> NNum {
        match self {
            NNum::Int(n) => NNum::Int(-n),
            NNum::Float(f) => NNum::Float(-f),
            NNum::Complex(z) => NNum::Complex(-z),
        }
    }
}
impl Not for NNum {
    type Output = NNum;

    fn not(self) -> NNum { !&self }
}
impl Not for &NNum {
    type Output = NNum;

    fn not(self) -> NNum {
        match self.to_bigint() {
            Some(n) => NNum::Int(!n),
            None => NNum::Float(f64::NAN),
        }
    }
}

impl AddAssign<&NNum> for NNum {
    fn add_assign(&mut self, other: &NNum) {
        let n = mem::replace(self, NNum::from(0));
        *self = &n + other;
    }
}

impl SubAssign<&NNum> for NNum {
    fn sub_assign(&mut self, other: &NNum) {
        let n = mem::replace(self, NNum::from(0));
        *self = &n - other;
    }
}

impl Sum for NNum {
    fn sum<I: Iterator<Item=Self>>(iter: I) -> Self {
        iter.fold(NNum::from(0), Add::add)
    }
}

impl Product for NNum {
    fn product<I: Iterator<Item=Self>>(iter: I) -> Self {
        iter.fold(NNum::from(1), Mul::mul)
    }
}

macro_rules! force_bi_binary_match {
    ($a:expr, $b:expr, $method:ident, $intmethod:expr) => {
        match ($a.to_bigint(), $b.to_bigint()) {
            (Some(ia), Some(ib)) => NNum::Int($intmethod(ia, ib)),
            _ => NNum::Float(f64::NAN),
        }
    };
}

macro_rules! def_force_bi_binary_method {
    ($method:ident, $intmethod:expr) => {
        fn $method(self, other: &NNum) -> NNum {
            force_bi_binary_match!(self, other, $method, $intmethod)
        }
    };
}

macro_rules! impl_force_bi_binary_method {
    ($imp:ident, $method:ident, $intmethod:expr) => {
        impl $imp<&NNum> for &NNum {
            type Output = NNum;

            def_force_bi_binary_method!($method, $intmethod);
        }

        forward_impl_binary_method!($imp, $method);
    };
}

impl_force_bi_binary_method!(BitAnd, bitand, BitAnd::bitand);
impl_force_bi_binary_method!(BitOr, bitor, BitOr::bitor);
impl_force_bi_binary_method!(BitXor, bitxor, BitXor::bitxor);

impl Shl<NNum> for NNum {
    type Output = Self;
    fn shl(self, other: NNum) -> Self {
        match (self, other.to_usize()) {
            (NNum::Int(a), Some(s)) => NNum::Int(a << s),
            _ => NNum::Float(f64::NAN),
        }
    }
}
impl Shr<NNum> for NNum {
    type Output = Self;
    fn shr(self, other: NNum) -> Self {
        match (self, other.to_usize()) {
            (NNum::Int(a), Some(s)) => NNum::Int(a >> s),
            _ => NNum::Float(f64::NAN),
        }
    }
}

fn lazy_is_prime(n: &BigInt) -> bool {
    if n <= &BigInt::from(1) {
        false
    } else if n <= &BigInt::from(3) {
        true
    } else if (n % BigInt::from(2)).is_zero() || (n % BigInt::from(3)).is_zero() {
        false
    } else {
        let s = n.sqrt(); // truncates
        let mut f = BigInt::from(5);
        loop {
            if f > s {
                return true;
            }
            if (n % &f).is_zero() {
                return false;
            }

            let g = &f + BigInt::from(2);
            if g > s {
                return true;
            }
            if (n % &g).is_zero() {
                return false;
            }

            f += 6;
        }
    }
}

impl NNum {
    pub fn gcd(&self, other: &NNum) -> NNum {
        force_bi_binary_match!(self, other, gcd, Integer::gcd)
    }

    pub fn is_prime(&self) -> bool {
        match self {
            NNum::Int(a) => lazy_is_prime(a),
            NNum::Float(a) => match a.to_bigint() {
                Some(n) => lazy_is_prime(&n),
                None => false,
            }
            NNum::Complex(a) => a.im == 0.0 && match a.re.to_bigint() {
                Some(n) => lazy_is_prime(&n),
                None => false,
            }
        }
    }
}

