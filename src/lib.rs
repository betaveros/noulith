#[macro_use] extern crate lazy_static;

// TODO: isolate
use std::fs;
use std::io;
use std::io::{Read, BufRead, Write};

use std::cmp::Ordering;
use std::fmt;
use std::fmt::Display;
use std::fmt::Debug;
use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use std::cell::RefCell;

use regex::Regex;

use num::complex::Complex64;
use num::bigint::BigInt;
use num::ToPrimitive;

#[cfg(target_arch="wasm32")]
use wasm_bindgen::prelude::*;

mod nnum;
mod gamma;

use crate::nnum::NNum;
use crate::nnum::NTotalNum;

#[derive(Debug, Clone, Copy)]
pub enum Assoc { Left, Right }
#[derive(Debug, Clone, Copy)]
pub struct Precedence(f64, Assoc);
impl Precedence {
    fn zero() -> Self { Precedence(0.0, Assoc::Left) }
}

#[derive(Debug)]
enum Few<T> { Zero, One(T), Many(Vec<T>), }
fn few<T>(mut xs: Vec<T>) -> Few<T> {
    match xs.len() {
        0 => Few::Zero,
        1 => Few::One(xs.remove(0)),
        _ => Few::Many(xs),
    }
}
impl<T> Few<T> {
    fn len(&self) -> usize {
        match self {
            Few::Zero => 0,
            Few::One(..) => 1,
            Few::Many(x) => x.len(),
        }
    }
}
#[derive(Debug)]
enum Few2<T> { Zero, One(T), Two(T, T), Many(Vec<T>), }
fn few2<T>(mut xs: Vec<T>) -> Few2<T> {
    match xs.len() {
        0 => Few2::Zero,
        1 => Few2::One(xs.remove(0)),
        2 => Few2::Two(xs.remove(0), xs.pop().unwrap()),
        _ => Few2::Many(xs),
    }
}
impl<T> Few2<T> {
    fn len(&self) -> usize {
        match self {
            Few2::Zero => 0,
            Few2::One(..) => 1,
            Few2::Two(..) => 2,
            Few2::Many(x) => x.len(),
        }
    }
}

#[derive(Debug)]
enum Few3<T> { Zero, One(T), Two(T, T), Three(T, T, T), Many(Vec<T>), }
fn few3<T>(mut xs: Vec<T>) -> Few3<T> {
    match xs.len() {
        0 => Few3::Zero,
        1 => Few3::One(xs.remove(0)),
        2 => Few3::Two(xs.remove(0), xs.pop().unwrap()),
        3 => Few3::Three(xs.remove(0), xs.remove(0), xs.pop().unwrap()),
        _ => Few3::Many(xs),
    }
}
/*
impl<T> Few3<T> {
    fn len(&self) -> usize {
        match self {
            Few3::Zero => 0,
            Few3::One(..) => 1,
            Few3::Two(..) => 2,
            Few3::Three(..) => 3,
            Few3::Many(x) => x.len(),
        }
    }
}
*/

#[derive(Debug, Clone)]
pub enum Obj {
    Null,
    Num(NNum),
    Seq(Seq),
    Func(Func, Precedence),
}

#[derive(Debug, Clone)]
pub enum Seq {
    String(Rc<String>),
    List(Rc<Vec<Obj>>),
    Dict(Rc<HashMap<ObjKey, Obj>>, Option<Box<Obj>>), // default value
    Vector(Rc<Vec<NNum>>),
    Bytes(Rc<Vec<u8>>),
}

// more like an arbitrary predicate. want to add subscripted types to this later
#[derive(Debug, Clone)]
pub enum ObjType { Null, Int, Float, Complex, Number, String, List, Dict, Vector, Bytes, Func, Type, Any }

impl ObjType {
    fn name(&self) -> String {
        match self {
            ObjType::Null => "nulltype",
            ObjType::Int => "int",
            ObjType::Float => "float",
            ObjType::Complex => "complex",
            ObjType::Number => "number",
            ObjType::List => "list",
            ObjType::String => "str",
            ObjType::Dict => "dict",
            ObjType::Vector => "vector",
            ObjType::Bytes => "bytes",
            ObjType::Type => "type",
            ObjType::Func => "func",
            ObjType::Any => "anything",
        }.to_string()
    }
}

fn type_of(obj: &Obj) -> ObjType {
    match obj {
        Obj::Null => ObjType::Null,
        Obj::Num(NNum::Int(_)) => ObjType::Int,
        Obj::Num(NNum::Float(_)) => ObjType::Float,
        Obj::Num(NNum::Complex(_)) => ObjType::Complex,
        Obj::Seq(Seq::List(_)) => ObjType::List,
        Obj::Seq(Seq::String(_)) => ObjType::String,
        Obj::Seq(Seq::Dict(..)) => ObjType::Dict,
        Obj::Seq(Seq::Vector(_)) => ObjType::Vector,
        Obj::Seq(Seq::Bytes(..)) => ObjType::Bytes,
        Obj::Func(Func::Type(_), _) => ObjType::Type,
        Obj::Func(..) => ObjType::Func,
    }
}

fn is_type(ty: &ObjType, arg: &Obj) -> bool {
    match (ty, arg) {
        (ObjType::Null, Obj::Null) => true,
        (ObjType::Int, Obj::Num(NNum::Int(_))) => true,
        (ObjType::Float, Obj::Num(NNum::Float(_))) => true,
        (ObjType::Complex, Obj::Num(NNum::Complex(_))) => true,
        (ObjType::Number, Obj::Num(_)) => true,
        (ObjType::List, Obj::Seq(Seq::List(_))) => true,
        (ObjType::String, Obj::Seq(Seq::String(_))) => true,
        (ObjType::Dict, Obj::Seq(Seq::Dict(..))) => true,
        (ObjType::Func, Obj::Func(..)) => true,
        (ObjType::Type, Obj::Func(Func::Type(_), _)) => true,
        (ObjType::Any, _) => true,
        _ => false,
    }
}

fn call_type(ty: &ObjType, arg: Obj) -> NRes<Obj> {
    match ty {
        ObjType::Int => match arg {
            Obj::Num(n) => Ok(Obj::Num(n.trunc())), // FIXME wat
            Obj::Seq(Seq::String(s)) => match s.parse::<BigInt>() {
                Ok(x) => Ok(Obj::from(x)),
                Err(s) => Err(NErr::value_error(format!("can't parse: {}", s))),
            },
            _ => Err(NErr::type_error("int: expected number or string".to_string())),
        }
        ObjType::Float => match arg {
            Obj::Num(n) => Ok(Obj::from(to_f64_ok(&n)?)),
            Obj::Seq(Seq::String(s)) => match s.parse::<f64>() {
                Ok(x) => Ok(Obj::from(x)),
                Err(s) => Err(NErr::value_error(format!("can't parse: {}", s))),
            },
            _ => Err(NErr::type_error("float: expected number or string".to_string())),
        }
        ObjType::List => match arg {
            Obj::Seq(Seq::List(xs)) => Ok(Obj::Seq(Seq::List(xs))),
            mut arg => Ok(Obj::list(mut_obj_into_iter(&mut arg, "list conversion")?.collect())),
        }
        ObjType::String => Ok(Obj::from(format!("{}", arg))),
        ObjType::Bytes => match arg {
            Obj::Seq(Seq::Bytes(xs)) => Ok(Obj::Seq(Seq::Bytes(xs))),
            Obj::Seq(Seq::String(s)) => Ok(Obj::Seq(Seq::Bytes(Rc::new(s.as_bytes().to_vec())))),
            mut arg => Ok(Obj::Seq(Seq::Bytes(Rc::new(
                mut_obj_into_iter(&mut arg, "bytes conversion")?
                .map(|e| match e {
                    Obj::Num(n) => n.to_u8().ok_or(NErr::value_error(format!("can't to byte: {}", n))),
                    x => Err(NErr::value_error(format!("can't to byte: {}", x))),
                })
                .collect::<NRes<Vec<u8>>>()?
            )))),
        }
        ObjType::Vector => match arg {
            Obj::Seq(Seq::Vector(s)) => Ok(Obj::Seq(Seq::Vector(s))),
            mut arg => to_obj_vector(mut_obj_into_iter(&mut arg, "vector conversion")?.map(Ok)),
        }
        ObjType::Dict => match arg {
            Obj::Seq(Seq::Dict(x, d)) => Ok(Obj::Seq(Seq::Dict(x, d))),
            // nonsensical but maybe this is something some day
            /*
            mut arg => Ok(Obj::Dict(
                    Rc::new(mut_obj_into_iter_pairs(&mut arg, "dict conversion")?.collect::<HashMap<ObjKey, Obj>>()), None)),
                    */
            mut arg => Ok(Obj::dict(
                        mut_obj_into_iter(&mut arg, "dict conversion")?
                        .map(|p| match p {
                            // TODO not taking but blech
                            Obj::Seq(Seq::List(xs)) => match xs.as_slice() {
                                [k, v] => Ok((to_key(k.clone())?, v.clone())),
                                _ => Err(NErr::type_error("dict conversion: not pair".to_string())),
                            }
                            _ => Err(NErr::type_error("dict conversion: not list".to_string())),
                        }).collect::<NRes<HashMap<ObjKey, Obj>>>()?, None)),
        }
        ObjType::Type => Ok(Obj::Func(Func::Type(type_of(&arg)), Precedence::zero())),
        // TODO: complex, number, vector, bytes
        _ => Err(NErr::type_error("that type can't be called (maybe not implemented)".to_string())),
    }
}

// TODO can we take?
fn to_type(arg: &Obj, msg: &str) -> NRes<ObjType> {
    match arg {
        Obj::Null => Ok(ObjType::Null),
        Obj::Func(Func::Type(t), _) => Ok(t.clone()),
        // TODO: possibly intelligently convert some objects to types?
        // e.g. "heterogenous tuples"
        a => Err(NErr::type_error(format!("can't convert {} to type for {}", a, msg))),
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum ObjKey {
    Null,
    Num(NTotalNum),
    String(Rc<String>),
    List(Rc<Vec<ObjKey>>),
    Dict(Rc<Vec<(ObjKey, ObjKey)>>),
    Vector(Rc<Vec<NTotalNum>>),
    Bytes(Rc<Vec<u8>>),
}

impl Obj {
    fn truthy(&self) -> bool {
        match self {
            Obj::Null => false,
            Obj::Num(x) => x.is_nonzero(),
            Obj::Seq(Seq::String(x)) => !x.is_empty(),
            Obj::Seq(Seq::List(x)) => !x.is_empty(),
            Obj::Seq(Seq::Dict(x, _)) => !x.is_empty(),
            Obj::Seq(Seq::Vector(x)) => !x.is_empty(),
            Obj::Seq(Seq::Bytes(x)) => !x.is_empty(),
            Obj::Func(..) => true,
        }
    }

    fn list(n: Vec<Obj>) -> Self { Obj::Seq(Seq::List(Rc::new(n))) }
    fn dict(m: HashMap<ObjKey, Obj>, def: Option<Obj>) -> Self {
        Obj::Seq(Seq::Dict(Rc::new(m), def.map(Box::new)))
    }
}

impl From<bool> for Obj {
    fn from(n: bool) -> Self { Obj::Num(NNum::iverson(n)) }
}
impl From<char> for Obj {
    fn from(n: char) -> Self { Obj::Seq(Seq::String(Rc::new(n.to_string()))) }
}
impl From<&str> for Obj {
    fn from(n: &str) -> Self { Obj::Seq(Seq::String(Rc::new(n.to_string()))) }
}
impl From<String> for Obj {
    fn from(n: String) -> Self { Obj::Seq(Seq::String(Rc::new(n))) }
}
impl From<Vec<Obj>> for Obj {
    fn from(n: Vec<Obj>) -> Self { Obj::Seq(Seq::List(Rc::new(n))) }
}

macro_rules! forward_from {
    ($ty:ident) => {
        impl From<$ty> for Obj {
            fn from(n: $ty) -> Self { Obj::Num(NNum::from(n)) }
        }
    }
}
forward_from!(BigInt);
// forward_from!(i32);
forward_from!(f64);
forward_from!(usize);
forward_from!(Complex64);

impl From<usize> for ObjKey {
    fn from(n: usize) -> Self { ObjKey::Num(NTotalNum(NNum::from(n))) }
}

impl PartialEq for Obj {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Obj::Null     , Obj::Null     ) => true,
            (Obj::Num   (a), Obj::Num   (b)) => a == b,
            (Obj::Seq   (a), Obj::Seq   (b)) => a == b,
            _ => false,
        }
    }
}

impl PartialEq for Seq {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Seq::List  (a), Seq::List  (b)) => a == b,
            (Seq::Dict(a,_), Seq::Dict(b,_)) => a == b,
            (Seq::String(a), Seq::String(b)) => a == b,
            _ => false,
        }
    }
}

impl PartialOrd for Obj {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Obj::Null     , Obj::Null     ) => Some(Ordering::Equal),
            (Obj::Num   (a), Obj::Num   (b)) => a.partial_cmp(b),
            (Obj::Seq   (a), Obj::Seq   (b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

impl PartialOrd for Seq {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Seq::List  (a), Seq::List  (b)) => a.partial_cmp(b),
            (Seq::String(a), Seq::String(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

/*
fn to_bigint_ok(n: &NNum) -> NRes<BigInt> {
    Ok(n.to_bigint().ok_or(NErr::value_error("bad number to int".to_string()))?.clone())
}
*/
fn clamp_to_usize_ok(n: &NNum) -> NRes<usize> {
    n.clamp_to_usize().ok_or(NErr::value_error("bad number to usize".to_string()))
}
fn obj_clamp_to_usize_ok(n: &Obj) -> NRes<usize> {
    match n {
        Obj::Num(n) => clamp_to_usize_ok(n),
        _ => Err(NErr::type_error("bad scalar".to_string())),
    }
}
fn into_bigint_ok(n: NNum) -> NRes<BigInt> {
    n.into_bigint().ok_or(NErr::value_error("bad number to int".to_string()))
}
fn to_f64_ok(n: &NNum) -> NRes<f64> {
    n.to_f64().ok_or(NErr::value_error("bad number to float".to_string()))
}

fn to_key(obj: Obj) -> NRes<ObjKey> {
    match obj {
        Obj::Null => Ok(ObjKey::Null),
        Obj::Num(x) => Ok(ObjKey::Num(NTotalNum(x))),
        Obj::Seq(Seq::String(x)) => Ok(ObjKey::String(x)),
        Obj::Seq(Seq::List(mut xs)) => Ok(ObjKey::List(Rc::new(
                    mut_rc_vec_into_iter(&mut xs).map(|e| to_key(e)).collect::<NRes<Vec<ObjKey>>>()?))),
        Obj::Seq(Seq::Dict(mut d, _)) => {
            let mut pairs = mut_rc_hash_map_into_iter(&mut d).map(
                |(k,v)| Ok((k,to_key(v)?))).collect::<NRes<Vec<(ObjKey,ObjKey)>>>()?;
            pairs.sort();
            Ok(ObjKey::Dict(Rc::new(pairs)))
        }
        Obj::Seq(Seq::Vector(x)) => Ok(ObjKey::Vector(Rc::new(x.iter().map(|e| NTotalNum(e.clone())).collect()))),
        Obj::Seq(Seq::Bytes(x)) => Ok(ObjKey::Bytes(x)),
        Obj::Func(..) => Err(NErr::type_error("Using a function as a dictionary key isn't supported".to_string())),
    }
}

fn key_to_obj(key: ObjKey) -> Obj {
    match key {
        ObjKey::Null => Obj::Null,
        ObjKey::Num(NTotalNum(x)) => Obj::Num(x),
        ObjKey::String(x) => Obj::Seq(Seq::String(x)),
        ObjKey::List(mut xs) => Obj::list(
                mut_rc_vec_into_iter(&mut xs).map(
                    |e| key_to_obj(e.clone())).collect::<Vec<Obj>>()),
        ObjKey::Dict(mut d) => Obj::dict(
                mut_rc_vec_into_iter(&mut d).map(
                    |(k, v)| (k, key_to_obj(v))).collect::<HashMap<ObjKey,Obj>>(), None),
        ObjKey::Vector(v) => Obj::Seq(Seq::Vector(Rc::new(v.iter().map(|x| x.0.clone()).collect()))),
        ObjKey::Bytes(v) => Obj::Seq(Seq::Bytes(v)),
    }
}

#[derive(Clone)]
pub enum FmtBase { Decimal, Binary, Octal, LowerHex, UpperHex }

#[derive(Clone)]
pub struct MyFmtFlags {
    base: FmtBase,
    repr: bool,
    budget: usize,
}

impl MyFmtFlags {
    pub fn new() -> MyFmtFlags {
        MyFmtFlags { base: FmtBase::Decimal, repr: false, budget: usize::MAX }
    }
    pub fn budgeted_repr(budget: usize) -> MyFmtFlags {
        MyFmtFlags { base: FmtBase::Decimal, repr: true, budget }
    }
    fn deduct(&mut self, amt: usize) {
        if self.budget >= amt {
            self.budget -= amt
        } else {
            self.budget = 0
        }
    }
}

impl MyDisplay for NNum {
    fn is_null(&self) -> bool { false }
    fn fmt_with_mut(&self, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
        match flags.base {
            FmtBase::Decimal => write!(formatter, "{}", self),
            FmtBase::Binary => write!(formatter, "{:b}", self),
            FmtBase::Octal => write!(formatter, "{:o}", self),
            FmtBase::LowerHex => write!(formatter, "{:x}", self),
            FmtBase::UpperHex => write!(formatter, "{:X}", self),
        }
    }
}
impl MyDisplay for NTotalNum {
    fn is_null(&self) -> bool { false }
    fn fmt_with_mut(&self, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
        self.0.fmt_with_mut(formatter, flags)
    }
}

fn write_string(s: &str, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
    flags.deduct(s.len() / 2);
    if flags.repr {
        // FIXME??
        write!(formatter, "{:?}", s)
    } else {
        write!(formatter, "{}", s)
    }
}
fn write_slice(v: &[impl MyDisplay], formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
    let old_repr = flags.repr;
    flags.repr = true;
    // Regardless of budget, always fmt first and last
    match v {
        [] => {},
        [only] => only.fmt_with_mut(formatter, flags)?,
        [first, rest @ .., last] => {
            first.fmt_with_mut(formatter, flags)?;
            write!(formatter, ", ")?;
            for x in rest {
                if flags.budget == 0 {
                    // TODO this has the "sometimes longer than what's omitted"
                    // property
                    write!(formatter, "..., ")?;
                    break
                }
                x.fmt_with_mut(formatter, flags)?;
                write!(formatter, ", ")?;
            }
            last.fmt_with_mut(formatter, flags)?;
        }
    }
    flags.repr = old_repr;
    Ok(())
}

fn write_pairs<'a,'b>(it: impl Iterator<Item=(&'a (impl MyDisplay + 'a), &'b (impl MyDisplay + 'b))>, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
    let old_repr = flags.repr;
    flags.repr = true;
    let mut started = false;
    for (k, v) in it {
        if started {
            write!(formatter, ", ")?;
            if flags.budget == 0 {
                write!(formatter, "...")?;
                break
            }
        }
        started = true;
        k.fmt_with_mut(formatter, flags)?;
        if !v.is_null() {
            write!(formatter, ": ")?;
            v.fmt_with_mut(formatter, flags)?;
        }
    }
    flags.repr = old_repr;
    Ok(())
}

fn write_bytes(s: &[u8], formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
    flags.deduct(s.len());
    write!(formatter, "B[")?;
    match s {
        [] => {},
        [only] => { write!(formatter, "{}", only)?; }
        [first, rest @ .., last] => {
            write!(formatter, "{},", first)?;
            for x in rest {
                if flags.budget == 0 {
                    // TODO this has the "sometimes longer than what's omitted"
                    // property
                    write!(formatter, "..., ")?;
                    break
                }
                write!(formatter, "{},", x)?;
            }
            write!(formatter, "{}", last)?;
        }
    }
    write!(formatter, "]")
}

trait MyDisplay {
    fn is_null(&self) -> bool;
    fn fmt_with_mut(&self, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result;
}

impl MyDisplay for Obj {
    fn is_null(&self) -> bool { self == &Obj::Null } // thonk
    fn fmt_with_mut(&self, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
        flags.deduct(1);
        match self {
            Obj::Null => write!(formatter, "null"),
            Obj::Num(n) => n.fmt_with_mut(formatter, flags),
            Obj::Seq(Seq::String(s)) => write_string(s, formatter, flags),
            Obj::Seq(Seq::List(xs)) => {
                write!(formatter, "[")?;
                write_slice(xs.as_slice(), formatter, flags)?;
                write!(formatter, "]")
            }
            Obj::Seq(Seq::Dict(xs, def)) => {
                write!(formatter, "{{")?;
                match def {
                    Some(v) => {
                        write!(formatter, "(default: ")?;
                        let old_repr = flags.repr;
                        flags.repr = true;
                        v.fmt_with_mut(formatter, flags)?;
                        flags.repr = old_repr;
                        write!(formatter, ")")?;
                        // TODO: spacing considerations, pain
                    }
                    None => {}
                }
                write_pairs(xs.iter(), formatter, flags)?;
                write!(formatter, "}}")
            }
            Obj::Seq(Seq::Vector(xs)) => {
                write!(formatter, "V(")?;
                write_slice(xs.as_slice(), formatter, flags)?;
                write!(formatter, ")")
            }
            Obj::Seq(Seq::Bytes(xs)) => {
                write_bytes(xs.as_slice(), formatter, flags)
            }
            Obj::Func(f, p) => write!(formatter, "<{} p:{}>", f, p.0),
        }
    }
}

impl Obj {
    pub fn fmt_with(&self, formatter: &mut dyn fmt::Write, mut flags: MyFmtFlags) -> fmt::Result {
        self.fmt_with_mut(formatter, &mut flags)
    }
}

// ????
pub struct FlaggedObj(pub Obj, pub MyFmtFlags);
impl Display for FlaggedObj {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt_with(formatter, self.1.clone())
    }
}

impl Display for Obj {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_with(formatter, MyFmtFlags::new())
    }
}

impl Display for ObjKey {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_with_mut(formatter, &mut MyFmtFlags::new())
    }
}

// FIXME massive copypasta
impl MyDisplay for ObjKey {
    fn is_null(&self) -> bool { self == &ObjKey::Null } // thonk
    fn fmt_with_mut(&self, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
        flags.deduct(1);
        match self {
            ObjKey::Null => write!(formatter, "null"),
            ObjKey::Num(n) => n.fmt_with_mut(formatter, flags),
            ObjKey::String(s) => write_string(s, formatter, flags),
            ObjKey::List(xs) => {
                write!(formatter, "[")?;
                write_slice(xs.as_slice(), formatter, flags)?;
                write!(formatter, "]")
            }
            ObjKey::Dict(xs) => {
                write!(formatter, "{{")?;
                write_pairs(xs.iter().map(|x| (&x.0, &x.1)), formatter, flags)?;
                write!(formatter, "}}")
            }
            ObjKey::Vector(xs) => {
                write!(formatter, "V[")?;
                write_slice(xs.as_slice(), formatter, flags)?;
                write!(formatter, "]")
            }
            ObjKey::Bytes(xs) => {
                write_bytes(xs.as_slice(), formatter, flags)
            }
        }
    }

}

impl ObjKey {
    pub fn fmt_with(&self, formatter: &mut dyn fmt::Write, mut flags: MyFmtFlags) -> fmt::Result {
        self.fmt_with_mut(formatter, &mut flags)
    }
}

pub enum RcVecIter<'a, T> {
    Draining(std::vec::Drain<'a, T>),
    Cloning(std::slice::Iter<'a, T>),
}

// Say we have an Rc<Vec>. If it has refcount 1, we can drain it, so we can lazily move out each
// element; but if it has has refcount >1, we lazily clone each element. At least, that's the
// theory.
//
// Alternatively, consuming the object and either going IntoIter or handrolling a (Rc<Vec>, usize)
// would also work fine for lists, but dictionaries don't have an easy handrollable self-owning
// iterator, I think?
fn mut_rc_vec_into_iter<T>(v: &mut Rc<Vec<T>>) -> RcVecIter<'_, T> {
    // Some non-lexical lifetime stuff going on here, matching Rc::get_mut(v) doesn't drop it in
    // the None branch and we can't access v again even though we should be able to. If I switch to
    // nightly I can probably use #![feature(nll)]
    if Rc::get_mut(v).is_some() {
        match Rc::get_mut(v) {
            Some(v) => RcVecIter::Draining(v.drain(..)),
            None => panic!("non-lexical lifetime issue"),
        }
    } else {
        RcVecIter::Cloning(v.iter())
    }
}

impl<T: Clone> Iterator for RcVecIter<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        match self {
            RcVecIter::Draining(it) => it.next(),
            RcVecIter::Cloning(it) => it.next().cloned(),
        }
    }
}

pub enum RcHashMapIter<'a, K, V> {
    Draining(std::collections::hash_map::Drain<'a, K, V>),
    Cloning(std::collections::hash_map::Iter<'a, K, V>),
}

fn mut_rc_hash_map_into_iter<K, V>(v: &mut Rc<HashMap<K, V>>) -> RcHashMapIter<'_, K, V> {
    // Same non-lexical lifetime stuff
    if Rc::get_mut(v).is_some() {
        match Rc::get_mut(v) {
            Some(v) => RcHashMapIter::Draining(v.drain()),
            None => panic!("non-lexical lifetime issue"),
        }
    } else {
        RcHashMapIter::Cloning(v.iter())
    }
}

impl<K: Clone, V: Clone> Iterator for RcHashMapIter<'_, K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        match self {
            RcHashMapIter::Draining(it) => it.next(),
            RcHashMapIter::Cloning(it) => it.next().map(|(k, v)| (k.clone(), v.clone())),
        }
    }
}

pub enum ObjToCloningIter<'a> {
    List(std::slice::Iter<'a, Obj>),
    Dict(std::collections::hash_map::Iter<'a, ObjKey, Obj>),
    String(std::str::Chars<'a>),
    Vector(std::slice::Iter<'a, NNum>),
    Bytes(std::slice::Iter<'a, u8>),
}

fn seq_to_cloning_iter(seq: &Seq) -> ObjToCloningIter<'_> {
    match seq {
        Seq::List(v) => ObjToCloningIter::List(v.iter()),
        Seq::Dict(v, _) => ObjToCloningIter::Dict(v.iter()),
        Seq::String(s) => ObjToCloningIter::String(s.chars()),
        Seq::Vector(v) => ObjToCloningIter::Vector(v.iter()),
        Seq::Bytes(v) => ObjToCloningIter::Bytes(v.iter()),
    }
}

fn obj_to_cloning_iter<'a,'b>(obj: &'a Obj, purpose: &'b str) -> NRes<ObjToCloningIter<'a>> {
    match obj {
        Obj::Seq(s) => Ok(seq_to_cloning_iter(s)),
        _ => Err(NErr::type_error(format!("{}; not iterable", purpose))),
    }
}

impl Iterator for ObjToCloningIter<'_> {
    type Item = Obj;

    fn next(&mut self) -> Option<Obj> {
        match self {
            ObjToCloningIter::List(it) => it.next().cloned(),
            ObjToCloningIter::Dict(it) => Some(key_to_obj(it.next()?.0.clone())),
            ObjToCloningIter::String(it) => Some(Obj::from(it.next()?)),
            ObjToCloningIter::Vector(it) => Some(Obj::Num(it.next()?.clone())),
            ObjToCloningIter::Bytes(it) => Some(Obj::from(*it.next()? as usize)),
        }
    }
}

// iterates over elements of lists, or just keys of dictionaries (as if they were sets)
pub enum MutObjIntoIter<'a> {
    List(RcVecIter<'a, Obj>),
    Dict(RcHashMapIter<'a, ObjKey, Obj>),
    String(std::str::Chars<'a>),
    Vector(RcVecIter<'a, NNum>),
    Bytes(RcVecIter<'a, u8>),
}

// iterates over (index, value) or (key, value)
pub enum MutObjIntoIterPairs<'a> {
    List(usize, RcVecIter<'a, Obj>),
    Dict(RcHashMapIter<'a, ObjKey, Obj>),
    String(usize, std::str::Chars<'a>),
    Vector(usize, RcVecIter<'a, NNum>),
    Bytes(usize, RcVecIter<'a, u8>),
}

fn mut_seq_into_iter(seq: &mut Seq) -> MutObjIntoIter<'_> {
    match seq {
        Seq::List(v) => MutObjIntoIter::List(mut_rc_vec_into_iter(v)),
        Seq::Dict(v, _) => MutObjIntoIter::Dict(mut_rc_hash_map_into_iter(v)),
        Seq::String(s) => MutObjIntoIter::String(s.chars()),
        Seq::Vector(v) => MutObjIntoIter::Vector(mut_rc_vec_into_iter(v)),
        Seq::Bytes(v) => MutObjIntoIter::Bytes(mut_rc_vec_into_iter(v)),
    }
}

fn mut_obj_into_iter<'a,'b>(obj: &'a mut Obj, purpose: &'b str) -> NRes<MutObjIntoIter<'a>> {
    match obj {
        Obj::Seq(s) => Ok(mut_seq_into_iter(s)),
        _ => Err(NErr::type_error(format!("{}: not iterable", purpose)))
    }
}

impl Iterator for MutObjIntoIter<'_> {
    type Item = Obj;

    fn next(&mut self) -> Option<Obj> {
        match self {
            MutObjIntoIter::List(it) => it.next(),
            MutObjIntoIter::Dict(it) => Some(key_to_obj(it.next()?.0)),
            MutObjIntoIter::String(it) => Some(Obj::from(it.next()?)),
            MutObjIntoIter::Vector(it) => Some(Obj::Num(it.next()?.clone())),
            MutObjIntoIter::Bytes(it) => Some(Obj::from(it.next()? as usize)),
        }
    }
}

fn mut_seq_into_iter_pairs(seq: &mut Seq) -> MutObjIntoIterPairs<'_> {
    match seq {
        Seq::List(v) => MutObjIntoIterPairs::List(0, mut_rc_vec_into_iter(v)),
        Seq::Dict(v, _) => MutObjIntoIterPairs::Dict(mut_rc_hash_map_into_iter(v)),
        Seq::String(s) => MutObjIntoIterPairs::String(0, s.chars()),
        Seq::Vector(v) => MutObjIntoIterPairs::Vector(0, mut_rc_vec_into_iter(v)),
        Seq::Bytes(v) => MutObjIntoIterPairs::Bytes(0, mut_rc_vec_into_iter(v)),
    }
}

fn mut_obj_into_iter_pairs<'a, 'b>(obj: &'a mut Obj, purpose: &'b str) -> NRes<MutObjIntoIterPairs<'a>> {
    match obj {
        Obj::Seq(s) => Ok(mut_seq_into_iter_pairs(s)),
        _ => Err(NErr::type_error(format!("{}: not iterable", purpose))),
    }
}

impl Iterator for MutObjIntoIterPairs<'_> {
    type Item = (ObjKey, Obj);

    fn next(&mut self) -> Option<(ObjKey, Obj)> {
        match self {
            MutObjIntoIterPairs::List(i, it) => { let o = it.next()?; let j = *i; *i += 1; Some((ObjKey::from(j), o)) }
            MutObjIntoIterPairs::Dict(it) => it.next(),
            MutObjIntoIterPairs::String(i, it) => { let o = it.next()?; let j = *i; *i += 1; Some((ObjKey::from(j), Obj::from(o))) }
            MutObjIntoIterPairs::Vector(i, it) => { let o = it.next()?; let j = *i; *i += 1; Some((ObjKey::from(j), Obj::Num(o))) }
            MutObjIntoIterPairs::Bytes(i, it) => { let o = it.next()?; let j = *i; *i += 1; Some((ObjKey::from(j), Obj::from(o as usize))) }
        }
    }
}

impl Seq {
    fn len(self) -> usize {
        match self {
            Seq::List(d) => d.len(),
            Seq::String(d) => d.len(),
            Seq::Dict(d, _) => d.len(),
            Seq::Vector(v) => v.len(),
            Seq::Bytes(v) => v.len(),
        }
    }

    fn reversed(self) -> NRes<Seq> {
        match self {
            Seq::List(mut v) => {
                Rc::make_mut(&mut v).reverse();
                Ok(Seq::List(v))
            }
            Seq::String(v) => {
                // TODO take??
                let mut r = v.chars().collect::<Vec<char>>();
                r.reverse();
                Ok(Seq::String(Rc::new(r.into_iter().collect())))
            }
            Seq::Dict(..) => Err(NErr::type_error("can't reverse dict".to_string())),
            Seq::Vector(mut v) => {
                Rc::make_mut(&mut v).reverse();
                Ok(Seq::Vector(v))
            }
            Seq::Bytes(mut v) => {
                Rc::make_mut(&mut v).reverse();
                Ok(Seq::Bytes(v))
            }
        }
    }
}

fn to_mutated_list(seq: Seq, mutator: impl FnOnce(&mut Vec<Obj>) -> NRes<()>) -> NRes<Seq> {
    match seq {
        Seq::List(mut v) => {
            mutator(Rc::make_mut(&mut v))?;
            Ok(Seq::List(v))
        }
        mut seq => {
            let mut v = mut_seq_into_iter(&mut seq).collect();
            mutator(&mut v)?;
            Ok(Seq::List(Rc::new(v)))
        }
    }
}

#[derive(Debug)]
pub struct NErr(String);

impl NErr {
    fn argument_error(s: String) -> NErr { NErr(format!("argument error: {}", s)) }
    fn index_error   (s: String) -> NErr { NErr(format!("index error: {}"   , s)) }
    fn key_error     (s: String) -> NErr { NErr(format!("key error: {}"     , s)) }
    fn empty_error   (s: String) -> NErr { NErr(format!("empty error: {}"   , s)) }
    fn name_error    (s: String) -> NErr { NErr(format!("name error: {}"    , s)) }
    fn syntax_error  (s: String) -> NErr { NErr(format!("syntax error: {}"  , s)) }
    fn type_error    (s: String) -> NErr { NErr(format!("type error: {}"    , s)) }
    fn value_error   (s: String) -> NErr { NErr(format!("value error: {}"   , s)) }
    fn io_error      (s: String) -> NErr { NErr(format!("io error: {}"      , s)) }
    fn assert_error  (s: String) -> NErr { NErr(format!("assert error: {}"  , s)) }

    fn generic_argument_error() -> NErr { NErr("unrecognized argument types".to_string()) }
}

fn err_add_name<T>(res: NRes<T>, s: &str) -> NRes<T> {
    match res {
        Ok(x) => Ok(x),
        Err(msg) => Err(NErr(format!("{}: {}", s, msg)))
    }
}

impl fmt::Display for NErr {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "{}", self.0)
    }
}

pub type NRes<T> = Result<T, NErr>;

#[derive(Debug, Clone)]
pub enum Func {
    Builtin(Rc<dyn Builtin>),
    Closure(Closure),
    // partially applied first argument (lower priority)
    PartialApp1(Box<Func>, Box<Obj>),
    // partially applied second argument (more of the default in our weird world)
    PartialApp2(Box<Func>, Box<Obj>),
    // mathematical notation, first of second
    Composition(Box<Func>, Box<Func>),
    // \x, y: f(y, x) (...I feel like we shouldn't special-case so many but shrug...)
    Flip(Box<Func>),
    Type(ObjType),
}

type REnv = Rc<RefCell<Env>>;

impl Func {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match self {
            Func::Builtin(b) => b.run(env, args),
            Func::Closure(c) => c.run(args),
            Func::PartialApp1(f, x) => match few(args) {
                Few::One(arg) => f.run(env, vec![(**x).clone(), arg]),
                _ => Err(NErr::argument_error("For now, partially applied functions can only be called with one more argument".to_string()))
            }
            Func::PartialApp2(f, x) => match few(args) {
                Few::One(arg) => f.run(env, vec![arg, (**x).clone()]),
                _ => Err(NErr::argument_error("For now, partially applied functions can only be called with one more argument".to_string()))
            }
            Func::Composition(f, g) => f.run(env, vec![g.run(env, args)?]),
            Func::Flip(f) => match few2(args) {
                // weird lol
                Few2::One(a) => Ok(Obj::Func(Func::PartialApp1(f.clone(), Box::new(a)), Precedence::zero())),
                Few2::Two(a, b) => f.run(env, vec![b, a]),
                _ => Err(NErr::argument_error("Flipped function can only be called on two arguments".to_string()))
            }
            Func::Type(t) => match few(args) {
                Few::One(arg) => call_type(t, arg),
                _ => Err(NErr::argument_error("Types can only take one argument".to_string()))
            }
        }
    }

    // Whether this might possibly look up a name in an environment
    fn can_refer(&self) -> bool {
        match self {
            Func::Builtin(b) => b.can_refer(),
            Func::Closure(_) => true,
            Func::PartialApp1(f, _) => f.can_refer(),
            Func::PartialApp2(f, _) => f.can_refer(),
            Func::Composition(f, g) => f.can_refer() || g.can_refer(),
            Func::Flip(f) => f.can_refer(),
            Func::Type(_) => false,
        }
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match self {
            Func::Builtin(b) => b.try_chain(other),
            Func::Closure(_) => None,
            Func::PartialApp1(..) => None,
            Func::PartialApp2(..) => None,
            Func::Composition(..) => None,
            Func::Flip(..) => None,
            Func::Type(_) => None,
        }
    }
}

impl Display for Func {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Func::Builtin(b) => write!(formatter, "Builtin({})", b.builtin_name()),
            Func::Closure(_) => write!(formatter, "Closure"),
            Func::PartialApp1(f, x) => write!(formatter, "Partial({}({}, ?))", f, x),
            Func::PartialApp2(f, x) => write!(formatter, "Partial({}(?, {}))", f, x),
            Func::Composition(f, g) => write!(formatter, "Comp({} . {})", f, g),
            Func::Flip(f) => write!(formatter, "Flip({})", f),
            Func::Type(t) => write!(formatter, "{}", t.name()),
        }
    }
}

pub trait Builtin : Debug {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj>;

    // Used for builtins to identify each other, since comparing pointers is bad (?)
    // https://rust-lang.github.io/rust-clippy/master/#vtable_address_comparisons
    fn builtin_name(&self) -> &str;

    fn try_chain(&self, _other: &Func) -> Option<Func> {
        None
    }

    fn can_refer(&self) -> bool { false }
}

#[derive(Debug, Clone)]
struct ComparisonOperator {
    name: String, // will be "illegal" for chained operators
    chained: Vec<Func>,
    accept: fn(Ordering) -> bool,
}

impl ComparisonOperator {
    fn of(name: &str, accept: fn(Ordering) -> bool) -> ComparisonOperator {
        ComparisonOperator {
            name: name.to_string(),
            chained: Vec::new(),
            accept,
        }
    }
}

fn ncmp(aa: &Obj, bb: &Obj) -> NRes<Ordering> {
    match (aa, bb) {
        (Obj::Num(a), Obj::Num(b)) => a.partial_cmp(b).ok_or(NErr::type_error(format!("Can't compare nums {:?} and {:?}", a, b))),
        (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => Ok(a.cmp(b)),
        (Obj::Seq(Seq::List(a)), Obj::Seq(Seq::List(b))) => a.partial_cmp(b).ok_or(NErr::type_error(format!("Can't compare lists {:?} and {:?}", a, b))),
        _ => Err(NErr::type_error(format!("Can't compare {:?} and {:?}", aa, bb))),
    }
}

fn clone_and_part_app_2(f: &(impl Builtin + Clone + 'static), arg: Obj) -> Obj{
    Obj::Func(Func::PartialApp2(
        Box::new(Func::Builtin(Rc::new(f.clone()))),
        Box::new(arg)
    ), Precedence::zero())
}

impl Builtin for ComparisonOperator {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        if self.chained.is_empty() {
            match few(args) {
                Few::Zero => Err(NErr::argument_error(format!("Comparison operator {:?} needs 2+ args", self.name))),
                Few::One(arg) => Ok(clone_and_part_app_2(self, arg)),
                Few::Many(args) => {
                    for i in 0 .. args.len() - 1 {
                        if !(self.accept)(ncmp(&args[i], &args[i+1])?) {
                            return Ok(Obj::from(false))
                        }
                    }
                    Ok(Obj::from(true))
                }
            }
        } else {
            if self.chained.len() + 2 == args.len() {
                if !(self.accept)(ncmp(&args[0], &args[1])?) {
                    return Ok(Obj::from(false))
                }
                for i in 0 .. self.chained.len() {
                    let res = self.chained[i].run(env, vec![args[i+1].clone(), args[i+2].clone()])?;
                    if !res.truthy() {
                        return Ok(res)
                    }
                }
                Ok(Obj::from(true))
            } else {
                Err(NErr::argument_error(format!("Chained comparison operator got the wrong number of args")))
            }
        }
    }

    fn builtin_name(&self) -> &str { &self.name }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                other_name @ ("==" | "!=" | "<" | ">" | "<=" | ">=") => Some(Func::Builtin(Rc::new(ComparisonOperator {
                    name: format!("{},{}", self.name, other_name),
                    chained: {
                        let mut k = self.chained.clone();
                        k.push(Func::clone(other));
                        k
                    },
                    accept: self.accept,
                }))),
                _ => None,
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
struct TilBuiltin {}

impl Builtin for TilBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few3::Two(Obj::Num(a), Obj::Num(b)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                // TODO: should be lazy
                Ok(Obj::list(num::range(n1, n2).map(|x| Obj::Num(NNum::from(x))).collect()))
            }
            Few3::Three(Obj::Num(a), Obj::Num(b), Obj::Num(c)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                let n3 = into_bigint_ok(c)?;
                // TODO: should be lazy
                Ok(Obj::list(num::range_step(n1, n2, n3).map(|x| Obj::Num(NNum::from(x))).collect()))
            }
            _ => Err(NErr::argument_error(format!("Bad args for til")))
        }
    }

    fn builtin_name(&self) -> &str { "til" }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "by" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            }
            _ => None,
        }
    }
}


#[derive(Debug, Clone)]
struct ToBuiltin {}

impl Builtin for ToBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few3::Two(Obj::Num(a), Obj::Num(b)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                // TODO: should be lazy
                Ok(Obj::list(num::range_inclusive(n1, n2).map(|x| Obj::Num(NNum::from(x))).collect()))
            }
            Few3::Two(a, Obj::Func(Func::Type(t), _)) => call_type(&t, a), // sugar lmao
            Few3::Three(Obj::Num(a), Obj::Num(b), Obj::Num(c)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                let n3 = into_bigint_ok(c)?;
                // TODO: should be lazy
                Ok(Obj::list(num::range_step_inclusive(n1, n2, n3).map(|x| Obj::Num(NNum::from(x))).collect()))
            }
            _ => Err(NErr::argument_error(format!("Bad args for to")))
        }
    }

    fn builtin_name(&self) -> &str { "to" }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "by" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            }
            _ => None,
        }
    }
}

// self-chainable
#[derive(Debug, Clone)]
struct Zip {}

impl Builtin for Zip {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::Zero => Err(NErr::argument_error("zip: no args".to_string())),
            Few::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few::Many(mut args) => {
                let mut func = None;
                // I can't believe this works (type annotation for me not the compiler)
                let mut iterators: Vec<MutObjIntoIter<'_>> = Vec::new();
                for arg in args.iter_mut() {
                    match (arg, &mut func) {
                        (Obj::Func(f, _), None) => {
                            func = Some(f.clone());
                        }
                        (Obj::Func(..), Some(_)) => Err(NErr::argument_error("zip: more than one function".to_string()))?,
                        (arg, _) => iterators.push(mut_obj_into_iter(arg, "zip")?),
                    }
                }
                if iterators.is_empty() {
                    Err(NErr::argument_error("zip: zero iterables".to_string()))?
                }
                let mut ret = Vec::new();
                while let Some(batch) = iterators.iter_mut().map(|a| a.next()).collect() {
                    ret.push(match &func {
                        Some(f) => f.run(env, batch)?,
                        None => Obj::list(batch),
                    })
                }
                Ok(Obj::list(ret))
            }
        }
    }

    fn builtin_name(&self) -> &str { "zip" }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "zip" | "with" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            }
            _ => None,
        }
    }
}

// self-chainable
#[derive(Debug, Clone)]
struct CartesianProduct {}

// surprisingly rare function where we really can't consume the iterators
fn cartesian_foreach(acc: &mut Vec<Obj>, seqs: &[Seq], f: &mut impl FnMut(&Vec<Obj>) -> NRes<()>) -> NRes<()> {
    match seqs {
        [] => f(acc)?,
        [a, rest @ ..] => {
            for e in seq_to_cloning_iter(a) {
                acc.push(e);
                cartesian_foreach(acc, rest, f)?;
                acc.pop();
            }
        }
    }
    Ok(())
}

impl Builtin for CartesianProduct {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::Zero => Err(NErr::argument_error("**: no args".to_string())),
            Few::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few::Many(args) => {
                // Bit overgeneral, also are we interested in accepting a function?
                let mut seqs = Vec::new();
                let mut scalar = None;
                for arg in args {
                    match arg {
                        Obj::Seq(s) => seqs.push(s),
                        Obj::Num(n) => match scalar {
                            None => scalar = Some(into_bigint_ok(n)?),
                            Some(_) => Err(NErr::argument_error("cartesian product: more than one integer".to_string()))?,
                        }
                        _ => Err(NErr::argument_error("cartesian product: non-sequence non-integer".to_string()))?,
                    }
                }

                match (scalar, few(seqs)) {
                    (Some(s), Few::One(seq)) => {
                        let mut acc = Vec::new();
                        for _ in num::range(BigInt::from(0), s) {
                            for e in seq_to_cloning_iter(&seq) {
                                acc.push(e);
                            }
                        }
                        Ok(Obj::list(acc))
                    }
                    (None, Few::Many(seqs)) => {
                        let mut acc = Vec::new();
                        let mut ret = Vec::new();
                        let mut f = |k: &Vec<Obj>| {
                            ret.push(Obj::list(k.clone()));
                            Ok(())
                        };
                        cartesian_foreach(&mut acc, seqs.as_slice(), &mut f)?;
                        Ok(Obj::list(ret))
                    }
                    _ => Err(NErr::argument_error("cartesian product: bad combo of scalars and sequences".to_string()))?,
                }
            }
        }
    }

    fn builtin_name(&self) -> &str { "**" }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "**" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            }
            _ => None,
        }
    }
}

// takes an optional starting value
#[derive(Debug, Clone)]
struct Fold {}

impl Builtin for Fold {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        // TODO partial app
        match few3(args) {
            Few3::Zero => Err(NErr::argument_error("fold: no args".to_string())),
            Few3::One(arg) => Ok(clone_and_part_app_2(self, arg)),
            Few3::Two(mut s, f) => {
                let mut it = mut_obj_into_iter(&mut s, "fold")?;
                match f {
                    Obj::Func(f, _) => match it.next() {
                        Some(mut cur) => {
                            // not sure if any standard fallible rust methods work...
                            for e in it {
                                cur = f.run(env, vec![cur, e])?;
                            }
                            Ok(cur)
                        }
                        None => Err(NErr::empty_error("fold: empty seq".to_string())),
                    }
                    _ => Err(NErr::type_error("fold: not callable".to_string()))
                }
            }
            Few3::Three(mut s, f, mut cur) => {
                let it = mut_obj_into_iter(&mut s, "fold")?;
                match f {
                    Obj::Func(f, _) => {
                        // not sure if any standard fallible rust methods work...
                        for e in it {
                            cur = f.run(env, vec![cur, e])?;
                        }
                        Ok(cur)
                    }
                    _ => Err(NErr::type_error("fold: not callable".to_string()))
                }
            }
            Few3::Many(_) => Err(NErr::argument_error("fold: too many args".to_string())),
        }
    }

    fn builtin_name(&self) -> &str { "fold" }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "from" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            }
            _ => None,
        }
    }
}

// it's just "with" lmao
#[derive(Debug, Clone)]
struct Replace {}

impl Builtin for Replace {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::Three(Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b)), Obj::Seq(Seq::String(c))) => {
                // rust's replacement syntax is $n or ${n} for nth group
                let r = Regex::new(&b).map_err(|e| NErr::value_error(format!("replace: invalid regex: {}", e)))?;
                Ok(Obj::from(r.replace(&a, &*c).into_owned()))
            }
            _ => Err(NErr::type_error("replace: must get three strings".to_string()))
        }
    }

    fn builtin_name(&self) -> &str { "replace" }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "with" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Preposition(String);

impl Builtin for Preposition {
    fn run(&self, _env: &REnv, _: Vec<Obj>) -> NRes<Obj> {
        Err(NErr::type_error(format!("{}: cannot call", self.0)))
    }

    fn builtin_name(&self) -> &str { &self.0 }
    fn can_refer(&self) -> bool { false }
}

#[derive(Clone)]
pub struct BasicBuiltin {
    name: String,
    can_refer: bool,
    body: fn(env: &REnv, args: Vec<Obj>) -> NRes<Obj>,
}

// https://github.com/rust-lang/rust/issues/45048
impl Debug for BasicBuiltin {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "BasicBuiltin {{ name: {:?}, can_refer: {:?}, body: {:?} }}", self.name, self.can_refer, self.body as usize)
    }
}

impl Builtin for BasicBuiltin {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        err_add_name((self.body)(env, args), &self.name)
    }

    fn builtin_name(&self) -> &str { &self.name }
    fn can_refer(&self) -> bool { self.can_refer }
}

#[derive(Debug, Clone)]
pub struct OneArgBuiltin {
    name: String,
    can_refer: bool,
    body: fn(a: Obj) -> NRes<Obj>,
}

impl Builtin for OneArgBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(arg) => (self.body)(arg),
            f => Err(NErr::argument_error(format!("{} only accepts one argument, got {}", self.name, f.len()))),
        }
    }

    fn builtin_name(&self) -> &str { &self.name }
    fn can_refer(&self) -> bool { self.can_refer }
}

#[derive(Debug, Clone)]
pub struct TwoArgBuiltin {
    name: String,
    can_refer: bool,
    body: fn(a: Obj, b: Obj) -> NRes<Obj>,
}

impl Builtin for TwoArgBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg) => Ok(clone_and_part_app_2(self, arg)),
            Few2::Two(a, b) => err_add_name((self.body)(a, b), &self.name),
            f => Err(NErr::argument_error(format!("{} only accepts two arguments (or one for partial application), got {}", self.name, f.len())))
        }
    }

    fn builtin_name(&self) -> &str { &self.name }
    fn can_refer(&self) -> bool { self.can_refer }
}

#[derive(Debug, Clone)]
pub struct OneNumBuiltin {
    name: String,
    body: fn(a: NNum) -> NRes<Obj>,
}

#[derive(Clone)]
pub struct EnvTwoArgBuiltin {
    name: String,
    can_refer: bool,
    body: fn(env: &REnv, a: Obj, b: Obj) -> NRes<Obj>,
}

impl Debug for EnvTwoArgBuiltin {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "EnvTwoArgBuiltin {{ name: {:?}, can_refer: {:?}, body: {:?} }}", self.name, self.can_refer, self.body as usize)
    }
}

impl Builtin for EnvTwoArgBuiltin {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg) => Ok(clone_and_part_app_2(self, arg)),
            Few2::Two(a, b) => err_add_name((self.body)(env, a, b), &self.name),
            f => Err(NErr::argument_error(format!("{} only accepts two arguments (or one for partial application), got {}", self.name, f.len())))
        }
    }

    fn builtin_name(&self) -> &str { &self.name }
    fn can_refer(&self) -> bool { self.can_refer }
}


fn to_obj_vector(iter: impl Iterator<Item=NRes<Obj>>) -> NRes<Obj> {
    Ok(Obj::Seq(Seq::Vector(Rc::new(iter.map(|e| match e? {
        Obj::Num(n) => Ok(n),
        x => Err(NErr::type_error(format!("can't convert to vector, non-number: {}", x))),
    }).collect::<NRes<Vec<NNum>>>()?))))
}

fn expect_nums_and_vectorize_1(body: fn(NNum) -> NRes<Obj>, a: Obj) -> NRes<Obj> {
    match a {
        Obj::Num(a) => body(a),
        Obj::Seq(Seq::Vector(mut a)) => to_obj_vector(mut_rc_vec_into_iter(&mut a).map(body)),
        x => Err(NErr::argument_error(format!("only accepts numbers, got {:?}", x))),
    }
}

impl Builtin for OneNumBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(x) => err_add_name(expect_nums_and_vectorize_1(self.body, x), &self.name),
            f => Err(NErr::argument_error(format!("{} only accepts one argument, got {}", self.name, f.len())))
        }
    }

    fn builtin_name(&self) -> &str { &self.name }
    fn can_refer(&self) -> bool { false }
}

#[derive(Debug, Clone)]
pub struct NumsBuiltin {
    name: String,
    body: fn(args: Vec<NNum>) -> NRes<Obj>,
}

impl Builtin for NumsBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        err_add_name((self.body)(args.into_iter().map(|x| match x {
            Obj::Num(n) => Ok(n),
            _ => Err(NErr::argument_error(format!("only accepts numbers, got {:?}", x))),
        }).collect::<NRes<Vec<NNum>>>()?), &self.name)
    }

    fn builtin_name(&self) -> &str { &self.name }

    fn can_refer(&self) -> bool { false }
}

#[derive(Debug, Clone)]
pub struct TwoNumsBuiltin {
    name: String,
    body: fn(a: NNum, b: NNum) -> NRes<Obj>,
}

fn expect_nums_and_vectorize_2(body: fn(NNum, NNum) -> NRes<Obj>, a: Obj, b: Obj) -> NRes<Obj> {
    match (a, b) {
        (Obj::Num(a), Obj::Num(b)) => body(a, b),
        (Obj::Num(a), Obj::Seq(Seq::Vector(mut b))) => to_obj_vector(mut_rc_vec_into_iter(&mut b).map(|e| body(a.clone(), e))),
        (Obj::Seq(Seq::Vector(mut a)), Obj::Num(b)) => to_obj_vector(mut_rc_vec_into_iter(&mut a).map(|e| body(e, b.clone()))),
        (Obj::Seq(Seq::Vector(mut a)), Obj::Seq(Seq::Vector(mut b))) => if a.len() == b.len() {
            to_obj_vector(
                mut_rc_vec_into_iter(&mut a)
                .zip(mut_rc_vec_into_iter(&mut b))
                .map(|(a, b)| body(a, b)))
        } else {
            Err(NErr::value_error(format!("vectorized op: different lengths: {} {}", a.len(), b.len())))
        },
        (a, b) => Err(NErr::argument_error(format!("only accepts numbers (or vectors), got {:?} {:?}", a, b))),
    }
}

impl Builtin for TwoNumsBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg @ (Obj::Num(_) | Obj::Seq(Seq::Vector(_)))) => Ok(clone_and_part_app_2(self, arg)),
            Few2::One(a) => Err(NErr::argument_error(format!("{} only accepts numbers (or vectors), got {:?}", self.name, a))),
            Few2::Two(a, b) => err_add_name(expect_nums_and_vectorize_2(self.body, a, b), &self.name),
            f => Err(NErr::argument_error(format!("{} only accepts two numbers, got {}", self.name, f.len()))),
        }
    }

    fn builtin_name(&self) -> &str { &self.name }

    fn can_refer(&self) -> bool { false }
}

#[derive(Clone)]
pub struct Closure {
    params: Rc<Vec<Box<Lvalue>>>,
    body: Rc<Expr>,
    env: Rc<RefCell<Env>>,
}

// directly debug-printing env can easily recurse infinitely
impl Debug for Closure {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "Closure {{ params: {:?}, body: {:?}, env: ... }}", self.params, self.body)
    }
}

impl Closure {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        let ee = Env::with_parent(&self.env);
        let p = self.params.iter().map(|e| Ok(Box::new(eval_lvalue(&ee, e)?))).collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?;
        assign_all(&mut ee.borrow_mut(), &p, Some(&ObjType::Any), &args)?;
        evaluate(&ee, &self.body)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    IntLit(BigInt),
    FloatLit(f64),
    ImaginaryFloatLit(f64),
    StringLit(Rc<String>),
    FormatString(Rc<String>),
    Ident(String),
    LeftParen,
    VLeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    And,
    Or,
    For,
    Yield,
    If,
    Else,
    Bang,
    Colon,
    DoubleColon,
    Semicolon,
    Ellipsis,
    Lambda,
    Comma,
    Assign,
    Pop,
    Remove,
    Swap,
    Every,
    // Newline,
}

#[derive(Debug)]
pub enum ForIterationType { Normal, Item, Declare }

#[derive(Debug)]
pub enum ForIteration {
    Iteration(ForIterationType, Box<Lvalue>, Box<Expr>),
    Guard(Box<Expr>),
}

#[derive(Debug)]
pub enum IndexOrSlice {
    Index(Box<Expr>),
    Slice(Option<Box<Expr>>, Option<Box<Expr>>),
}

#[derive(Debug)]
pub enum Expr {
    IntLit(BigInt),
    FloatLit(f64),
    ImaginaryFloatLit(f64),
    StringLit(Rc<String>),
    FormatString(Rc<String>),
    Ident(String),
    Backref(usize),
    Call(Box<Expr>, Vec<Box<Expr>>),
    List(Vec<Box<Expr>>),
    Dict(Option<Box<Expr>>, Vec<(Box<Expr>, Option<Box<Expr>>)>),
    Vector(Vec<Box<Expr>>),
    Index(Box<Expr>, IndexOrSlice),
    Chain(Box<Expr>, Vec<(String, Box<Expr>)>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Annotation(Box<Expr>, Option<Box<Expr>>),
    Pop(Box<Lvalue>),
    Remove(Box<Lvalue>),
    Swap(Box<Lvalue>, Box<Lvalue>),
    // bool: Every
    Assign(bool, Box<Lvalue>, Box<Expr>),
    OpAssign(bool, Box<Lvalue>, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    For(Vec<ForIteration>, bool /* yield */, Box<Expr>),
    Sequence(Vec<Box<Expr>>),
    // these get cloned in particular
    Lambda(Rc<Vec<Box<Lvalue>>>, Rc<Expr>),
    // meaningful in lvalues
    Paren(Box<Expr>),

    // shouldn't stay in the tree:
    CommaSeq(Vec<Box<Expr>>),
    Splat(Box<Expr>),
}

#[derive(Debug)]
pub enum Lvalue {
    IndexedIdent(String, Vec<IndexOrSlice>),
    Annotation(Box<Lvalue>, Option<Box<Expr>>),
    Unannotation(Box<Lvalue>),
    CommaSeq(Vec<Box<Lvalue>>),
    Splat(Box<Lvalue>),
}

#[derive(Debug)]
enum EvaluatedIndexOrSlice {
    Index(Obj),
    Slice(Option<Obj>, Option<Obj>),
}

#[derive(Debug)]
enum EvaluatedLvalue {
    IndexedIdent(String, Vec<EvaluatedIndexOrSlice>),
    Annotation(Box<EvaluatedLvalue>, Option<Obj>),
    Unannotation(Box<EvaluatedLvalue>),
    CommaSeq(Vec<Box<EvaluatedLvalue>>),
    Splat(Box<EvaluatedLvalue>),
}

fn to_lvalue(expr: Expr) -> Result<Lvalue, String> {
    match expr {
        Expr::Ident(s) => Ok(Lvalue::IndexedIdent(s, Vec::new())),
        Expr::Index(e, i) => {
            match to_lvalue(*e)? {
                Lvalue::IndexedIdent(idn, mut ixs) => {
                    ixs.push(i);
                    Ok(Lvalue::IndexedIdent(idn, ixs))
                }
                ee => Err(format!("can't to_lvalue index of nonident {:?}", ee)),
            }
        }
        Expr::Annotation(e, t) => Ok(Lvalue::Annotation(Box::new(to_lvalue(*e)?), t)),
        Expr::CommaSeq(es) => Ok(Lvalue::CommaSeq(
            es.into_iter().map(|e| Ok(Box::new(to_lvalue(*e)?))).collect::<Result<Vec<Box<Lvalue>>, String>>()?
        )),
        Expr::Splat(x) => Ok(Lvalue::Splat(Box::new(to_lvalue(*x)?))),
        Expr::Paren(p) => Ok(Lvalue::Unannotation(Box::new(to_lvalue(*p)?))),
        _ => Err(format!("can't to_lvalue {:?}", expr)),
    }
}

#[derive(Clone, Copy)]
struct CodeLoc {
    line: usize,
    col: usize,
}

pub struct LocToken {
    token: Token,
    start: CodeLoc,
    end: CodeLoc,
}

struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    start: CodeLoc,

    // maintained at what chars.next() would give
    cur: CodeLoc,
    tokens: Vec<LocToken>,

    // the lightest hole I could punch in the abstractions to support format strings...
    last_comment: Option<String>,
}

impl<'a> Lexer<'a> {
    fn new(code: &'a str) -> Self {
        Lexer {
            chars: code.chars().peekable(),
            start: CodeLoc { line: 1, col: 1 },
            cur: CodeLoc { line: 1, col: 1 },
            tokens: Vec::new(),
            last_comment: None,
        }
    }

    fn peek(&mut self) -> Option<&char> {
        self.chars.peek()
    }

    fn next(&mut self) -> Option<char> {
        let c = self.chars.next();
        match c {
            Some('\n') => { self.cur.line += 1; self.cur.col = 1; }
            Some(_) => { self.cur.col += 1; }
            None => {}
        }
        c
    }

    fn emit(&mut self, token: Token) {
        self.tokens.push(LocToken { token, start: self.start, end: self.cur });
        self.start = self.cur;
    }

    fn lex_simple_string_after_start(&mut self, end: char) -> String {
        let mut acc = String::new();
        while self.peek() != Some(&end) {
            match self.next() {
                Some('\\') => match self.next() {
                    Some('n') => acc.push('\n'),
                    Some('r') => acc.push('\r'),
                    Some('t') => acc.push('\t'),
                    Some('0') => acc.push('\0'),
                    Some(c @ ('\\' | '\'' | '\"')) => acc.push(c),
                    Some('x') => {
                        let e = "lexing: string literal: bad hex escape";
                        let d1 = self.next().expect(e).to_digit(16).expect(e);
                        let d2 = self.next().expect(e).to_digit(16).expect(e);
                        acc.push(char::from_u32(d1 * 16 + d2).unwrap())
                    }
                    Some(c) => panic!("lexing: string literal: unknown escape {}", c),
                    None => panic!("lexing: string literal: escape eof"),
                }
                Some(c) => acc.push(c),
                None => panic!("lexing: string literal hit eof")
            }
        }
        self.next();
        acc
    }

    fn lex_base_and_emit(&mut self, base: u32) {
        let mut x = BigInt::from(0);
        while let Some(cc) = self.peek().and_then(|d| d.to_digit(base)) {
            self.next();
            x = base * x + cc;
        }
        self.emit(Token::IntLit(x))
    }

    fn lex_base_64_and_emit(&mut self) {
        let mut x = BigInt::from(0);
        while let Some(cc) = self.peek().and_then(|d| match d {
            'A'..='Z' => Some((*d as u32) - ('A' as u32)),
            'a'..='z' => Some((*d as u32) - ('a' as u32) + 26),
            '0'..='9' => Some((*d as u32) - ('0' as u32) + 52),
            '+' | '-' => Some(62),
            '/' | '_' => Some(63),
            _ => None,
        }) {
            self.next();
            x = 64 * x + cc;
        }
        self.emit(Token::IntLit(x))
    }

    fn lex(&mut self) {
        lazy_static! {
            static ref OPERATOR_SYMBOLS: HashSet<char> = "!$%&*+-./<=>?@^|~".chars().collect::<HashSet<char>>();
        }

        // let mut chars = code.chars().peekable();
        while let Some(c) = self.next() {
            match c {
                '(' => self.emit(Token::LeftParen),
                ')' => self.emit(Token::RightParen),
                '[' => self.emit(Token::LeftBracket),
                ']' => self.emit(Token::RightBracket),
                '{' => self.emit(Token::LeftBrace),
                '}' => self.emit(Token::RightBrace),
                '\\' => self.emit(Token::Lambda),
                ',' => self.emit(Token::Comma),
                ';' => self.emit(Token::Semicolon),
                ':' => {
                    if self.peek() == Some(&':') {
                        self.next();
                        self.emit(Token::DoubleColon);
                    } else {
                        self.emit(Token::Colon);
                    }
                }
                ' ' => (),
                '\n' => (),
                '#' => {
                    let mut comment = String::new();
                    loop {
                        match self.next() {
                            None | Some('\n') => break,
                            Some(c) => comment.push(c),
                        }
                    }
                    self.last_comment = Some(comment);
                }
                '\'' | '"' => {
                    let s = self.lex_simple_string_after_start(c);
                    self.emit(Token::StringLit(Rc::new(s)))
                }
                c => {
                    if c.is_digit(10) {
                        let mut acc = c.to_string();

                        while let Some(cc) = self.peek().filter(|d| d.is_digit(10)) {
                            acc.push(*cc);
                            self.next();
                        }
                        if self.peek() == Some(&'.') {
                            acc.push('.');
                            self.next();
                            while let Some(cc) = self.peek().filter(|d| d.is_digit(10)) {
                                acc.push(*cc);
                                self.next();
                            }
                            match self.peek() {
                                Some('i' | 'I' | 'j' | 'J') => {
                                    self.next();
                                    self.emit(Token::ImaginaryFloatLit(acc.parse::<f64>().unwrap()))
                                }
                                Some('e' | 'E') => {
                                    acc.push('e'); self.next();
                                    if self.peek() == Some(&'-') {
                                        acc.push('-'); self.next();
                                    }
                                    while let Some(cc) = self.peek().filter(|d| d.is_digit(10)) {
                                        acc.push(*cc);
                                        self.next();
                                    }
                                    self.emit(Token::FloatLit(acc.parse::<f64>().unwrap()))
                                }
                                _ => self.emit(Token::FloatLit(acc.parse::<f64>().unwrap()))
                            }
                        } else {
                            match (acc.as_str(), self.peek()) {
                                ("0", Some('x' | 'X')) => { self.next(); self.lex_base_and_emit(16) }
                                ("0", Some('b' | 'B')) => { self.next(); self.lex_base_and_emit(2) }
                                ("0", Some('o' | 'O')) => { self.next(); self.lex_base_and_emit(8) }
                                ( _ , Some('r' | 'R')) => {
                                    // radix. not sure who does this actually? common lisp?
                                    match acc.parse::<u32>() {
                                        Ok(radix) if 2 <= radix && radix <= 36 => {
                                            self.next();
                                            self.lex_base_and_emit(radix)
                                        }
                                        Ok(64) => {
                                            self.next();
                                            self.lex_base_64_and_emit()
                                        }
                                        _ => self.emit(Token::IntLit(acc.parse::<BigInt>().unwrap())),
                                    }

                                }
                                ( _ , Some('i' | 'I' | 'j' | 'J')) => {
                                    self.next();
                                    self.emit(Token::ImaginaryFloatLit(acc.parse::<f64>().unwrap()))
                                }
                                ( _ , Some('e' | 'E')) => {
                                    acc.push('e'); self.next();
                                    if self.peek() == Some(&'-') {
                                        acc.push('-'); self.next();
                                    }
                                    while let Some(cc) = self.peek().filter(|d| d.is_digit(10)) {
                                        acc.push(*cc);
                                        self.next();
                                    }
                                    self.emit(Token::FloatLit(acc.parse::<f64>().unwrap()))
                                }
                                _ => self.emit(Token::IntLit(acc.parse::<BigInt>().unwrap())),
                            }
                        }
                    } else if c.is_alphabetic() {
                        let mut acc = c.to_string();

                        while let Some(cc) = self.peek().filter(|c| c.is_alphanumeric() || **c == '_') {
                            acc.push(*cc);
                            self.next();
                        }
                        if acc == "F" {
                            // wow
                            // i guess we lex and parse at evaluation?? idk
                            match self.next() {
                                Some(delim @ ('\'' | '"')) => {
                                    let s = self.lex_simple_string_after_start(delim);
                                    self.emit(Token::FormatString(Rc::new(s)))
                                }
                                _ => panic!("lexing: format string: no quote")
                            }
                        } else if acc == "R" {
                            // wow
                            match self.next() {
                                Some(delim @ ('\'' | '"')) => {
                                    let mut acc = String::new();
                                    while self.peek() != Some(&delim) {
                                        match self.next() {
                                            Some(c) => acc.push(c),
                                            None => panic!("lexing: string literal hit eof")
                                        }
                                    }
                                    self.next();
                                    self.emit(Token::StringLit(Rc::new(acc)))
                                }
                                _ => panic!("lexing: raw string literal: no quote")
                            }
                        } else if acc == "V" {
                            match self.next() {
                                Some('(') => {
                                    self.emit(Token::VLeftParen)
                                }
                                _ => panic!("lexing: V: what")
                            }
                        } else {
                            self.emit(match acc.as_str() {
                                "if" => Token::If,
                                "else" => Token::Else,
                                "for" => Token::For,
                                "yield" => Token::Yield,
                                "and" => Token::And,
                                "or" => Token::Or,
                                "pop" => Token::Pop,
                                "remove" => Token::Remove,
                                "swap" => Token::Swap,
                                "every" => Token::Every,
                                _ => Token::Ident(acc),
                            })
                        }
                    } else if OPERATOR_SYMBOLS.contains(&c) {
                        // Most operators ending in = parse weird. It's hard to pop the last character
                        // off a String because of UTF-8 stuff so keep them separate until the last
                        // possible moment.
                        let mut last = c;
                        let mut acc = String::new();

                        while let Some(cc) = self.peek().filter(|c| OPERATOR_SYMBOLS.contains(c)) {
                            acc.push(last);
                            last = *cc;
                            self.next();
                        }
                        match (acc.as_str(), last) {
                            ("!" | "<" | ">" | "=", '=') => {
                                acc.push(last); self.emit(Token::Ident(acc))
                            }
                            ("", '=') => self.emit(Token::Assign),
                            (_, '=') => {
                                self.emit(Token::Ident(acc));
                                self.emit(Token::Assign)
                            }
                            (_, _) => {
                                acc.push(last);
                                self.emit(match acc.as_str() {
                                    "!" => Token::Bang,
                                    "..." => Token::Ellipsis,
                                    _ => Token::Ident(acc)
                                })
                            }
                        }
                    }
                }
            }
        }
    }
}

pub fn lex(code: &str) -> Vec<LocToken> {
    let mut lexer = Lexer::new(code);
    lexer.lex();
    lexer.tokens
}

struct Parser {
    tokens: Vec<LocToken>,
    i: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.i).map(|lt| &lt.token)
    }

    fn advance(&mut self) {
        self.i += 1;
    }

    fn try_consume(&mut self, desired: &Token) -> bool {
        if self.peek() == Some(desired) {
            self.advance(); true
        } else {
            false
        }
    }

    fn peek_err(&self) -> String {
        match self.tokens.get(self.i) {
            Some(LocToken { token, start, end }) => format!("{:?} (at {}:{}-{})", token, start.line, start.col, end.col),
            None => "EOF".to_string()
        }
    }

    fn require(&mut self, expected: Token, message: String) -> Result<(), String> {
        if self.try_consume(&expected) { // wat
            Ok(())
        } else {
            Err(format!("{}; required {:?}, got {:?}", message, expected, self.peek_err()))
        }
    }

    fn atom(&mut self) -> Result<Expr, String> {
        if let Some(token) = self.peek() {
            match token {
                Token::IntLit(n) => {
                    let n = n.clone();
                    self.advance();
                    Ok(Expr::IntLit(n))
                }
                Token::FloatLit(n) => {
                    let n = *n;
                    self.advance();
                    Ok(Expr::FloatLit(n))
                }
                Token::ImaginaryFloatLit(n) => {
                    let n = *n;
                    self.advance();
                    Ok(Expr::ImaginaryFloatLit(n))
                }
                Token::StringLit(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(Expr::StringLit(s))
                }
                Token::FormatString(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(Expr::FormatString(s))
                }
                Token::Ident(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(Expr::Ident(s))
                }
                Token::Ellipsis => {
                    self.advance();
                    Ok(Expr::Splat(Box::new(self.single()?)))
                }
                Token::Pop => {
                    self.advance();
                    Ok(Expr::Pop(Box::new(to_lvalue(self.single()?)?)))
                }
                Token::Remove => {
                    self.advance();
                    Ok(Expr::Remove(Box::new(to_lvalue(self.single()?)?)))
                }
                Token::LeftParen => {
                    self.advance();
                    let e = self.expression()?;
                    self.require(Token::RightParen, "normal parenthesized expr".to_string())?;
                    // Only add the paren if it looks important in lvalues.
                    match &e {
                        Expr::Ident(_) | Expr::Index(..) => Ok(Expr::Paren(Box::new(e))),
                        _ => Ok(e),
                    }
                }
                Token::VLeftParen => {
                    self.advance();
                    if self.try_consume(&Token::RightParen) {
                        Ok(Expr::Vector(Vec::new()))
                    } else {
                        let (exs, _) = self.comma_separated()?;
                        self.require(Token::RightParen, "vector expr".to_string())?;
                        Ok(Expr::Vector(exs))
                    }
                }
                Token::LeftBracket => {
                    self.advance();
                    if self.try_consume(&Token::RightBracket) {
                        Ok(Expr::List(Vec::new()))
                    } else {
                        let (exs, _) = self.comma_separated()?;
                        self.require(Token::RightBracket, "list expr".to_string())?;
                        Ok(Expr::List(exs))
                    }
                }
                Token::LeftBrace => {
                    self.advance();
                    // Dict(Vec<(Box<Expr>, Option<Box<Expr>>)>),
                    let mut xs = Vec::new();
                    let mut def = None;
                    if self.try_consume(&Token::Colon) {
                        def = Some(Box::new(self.single()?));
                        if !self.peek_csc_stopper() {
                            self.require(Token::Comma, "dict expr".to_string())?;
                        }
                    }

                    while !self.peek_csc_stopper() {
                        let c1 = Box::new(self.single()?);
                        let c2 = if self.try_consume(&Token::Colon) {
                            Some(Box::new(self.single()?))
                        } else {
                            None
                        };
                        xs.push((c1, c2));

                        if !self.peek_csc_stopper() {
                            self.require(Token::Comma, "dict expr".to_string())?;
                        }
                    }
                    self.require(Token::RightBrace, "dict expr end".to_string())?;
                    Ok(Expr::Dict(def, xs))
                }
                Token::RightParen => Err(format!("Unexpected {}", self.peek_err())),
                Token::Lambda => {
                    self.advance();
                    if let Some(Token::IntLit(x)) = self.peek().cloned() {
                        self.advance();
                        Ok(Expr::Backref(x.to_usize().ok_or(format!("backref: not usize: {}", x))?))
                    } else {
                        let params = if self.try_consume(&Token::Colon) {
                            Vec::new()
                        } else {
                            let (params0, _) = self.comma_separated()?;
                            let ps = params0.into_iter().map(|p| Ok(Box::new(to_lvalue(*p)?))).collect::<Result<Vec<Box<Lvalue>>, String>>()?;
                            self.require(Token::Colon, "lambda start".to_string())?;
                            ps
                        };
                        let body = self.single()?;
                        Ok(Expr::Lambda(Rc::new(params), Rc::new(body)))
                    }
                }
                Token::If => {
                    self.advance();
                    self.require(Token::LeftParen, "if start".to_string())?;
                    let cond = self.expression()?;
                    self.require(Token::RightParen, "if cond end".to_string())?;
                    let body = self.assignment()?;
                    let else_body = if self.try_consume(&Token::Else) {
                        Some(Box::new(self.assignment()?))
                    } else {
                        None
                    };
                    Ok(Expr::If(Box::new(cond), Box::new(body), else_body))
                }
                Token::For => {
                    self.advance();
                    self.require(Token::LeftParen, "for start".to_string())?;
                    let mut its = Vec::new();
                    loop {
                        its.push(self.for_iteration()?);
                        match self.peek() {
                            Some(Token::RightParen) => { self.advance(); break }
                            Some(Token::Semicolon) => { self.advance(); }
                            _ => Err(format!("for: expected right paren or semicolon after iteration, got {}", self.peek_err()))?,
                        }
                    }
                    let do_yield = self.try_consume(&Token::Yield);
                    let body = self.assignment()?;
                    Ok(Expr::For(its, do_yield, Box::new(body)))
                }
                _ => Err(format!("Unexpected {}", self.peek_err())),
            }
        } else {
            Err("atom: ran out of stuff to parse".to_string())
        }
    }

    fn for_iteration(&mut self) -> Result<ForIteration, String> {
        if self.try_consume(&Token::If) {
            Ok(ForIteration::Guard(Box::new(self.single()?)))
        } else {
            let pat0 = self.pattern()?;
            let pat = to_lvalue(pat0)?;
            let ty = match self.peek() {
                Some(Token::Colon) => {
                    self.advance();
                    if self.try_consume(&Token::Assign) {
                        ForIterationType::Declare
                    } else {
                        ForIterationType::Normal
                    }
                }
                Some(Token::DoubleColon) => {
                    self.advance();
                    ForIterationType::Item
                }
                _ => return Err(format!("for: require : or :: or :=, got {}", self.peek_err())),
            };
            let iteratee = self.pattern()?;
            Ok(ForIteration::Iteration(ty, Box::new(pat), Box::new(iteratee)))
        }
    }

    fn operand(&mut self) -> Result<Expr, String> {
        let mut cur = self.atom()?;

        loop {
            match self.peek() {
                Some(Token::LeftParen) => {
                    self.advance();
                    if self.try_consume(&Token::RightParen) {
                        cur = Expr::Call(Box::new(cur), Vec::new());
                    } else {
                        let (cs, _) = self.comma_separated()?;
                        self.require(Token::RightParen, "call expr".to_string())?;
                        cur = Expr::Call(Box::new(cur), cs);
                    }
                }
                Some(Token::LeftBracket) => {
                    self.advance();
                    if self.try_consume(&Token::Colon) {
                        if self.try_consume(&Token::RightBracket) {
                            cur = Expr::Index(Box::new(cur), IndexOrSlice::Slice(None, None));
                        } else {
                            let c = self.single()?;
                            self.require(Token::RightBracket, "index expr".to_string())?;
                            cur = Expr::Index(Box::new(cur), IndexOrSlice::Slice(None, Some(Box::new(c))));
                        }
                    } else {
                        let c = self.single()?;
                        if self.try_consume(&Token::Colon) {
                            if self.try_consume(&Token::RightBracket) {
                                cur = Expr::Index(Box::new(cur), IndexOrSlice::Slice(Some(Box::new(c)), None));
                            } else {
                                let cc = self.single()?;
                                self.require(Token::RightBracket, "index expr".to_string())?;
                                cur = Expr::Index(Box::new(cur), IndexOrSlice::Slice(Some(Box::new(c)), Some(Box::new(cc))));
                            }
                        } else {
                            self.require(Token::RightBracket, "index expr".to_string())?;
                            cur = Expr::Index(Box::new(cur), IndexOrSlice::Index(Box::new(c)));
                        }
                    }
                }
                Some(Token::Bang) => {
                    self.advance();
                    if self.peek_csc_stopper() {
                        cur = Expr::Call(Box::new(cur), Vec::new());
                    } else {
                        let (cs, _) = self.comma_separated()?;
                        cur = Expr::Call(Box::new(cur), cs);
                    }
                }
                _ => break Ok(cur)
            }
        }
    }

    fn peek_csc_stopper(&self) -> bool {
        match self.peek() {
            Some(Token::RightParen) => true,
            Some(Token::RightBracket) => true,
            Some(Token::RightBrace) => true,
            Some(Token::Assign) => true,
            Some(Token::Colon) => true,
            Some(Token::DoubleColon) => true,
            Some(Token::Semicolon) => true,
            Some(Token::Else) => true,
            None => true,
            _ => false,
        }
    }

    fn peek_chain_stopper(&self) -> bool {
        self.peek_csc_stopper() || match self.peek() {
            Some(Token::Comma) => true,
            Some(Token::And) => true,
            Some(Token::Or) => true,
            _ => false,
        }
    }

    fn chain(&mut self) -> Result<Expr, String> {
        let op1 = self.operand()?;
        if self.peek_chain_stopper() {
            Ok(op1)
        } else {
            // We'll specially allow some two-chains, (a b), as calls, so that negative number
            // literals and just writing an expression like "-x" works. But we will be
            // aggressive-ish about checking that the chain ends afterwards so we don't get runaway
            // syntax errors.
            let second = self.atom()?;
            match second {
                Expr::Ident(op) => {
                    if self.peek_chain_stopper() {
                        Ok(Expr::Call(Box::new(op1), vec![Box::new(Expr::Ident(op))]))
                    } else {
                        let mut ops = vec![(op.to_string(), Box::new(self.operand()?))];

                        while let Some(Token::Ident(op)) = self.peek() {
                            let op = op.to_string();
                            self.advance();
                            ops.push((op, Box::new(self.operand()?)));
                        }
                        Ok(Expr::Chain(Box::new(op1), ops))
                    }
                }
                _ => {
                    let ret = Expr::Call(Box::new(op1), vec![Box::new(second)]);
                    if !self.peek_chain_stopper() {
                        Err(format!("saw non-identifier in operator position: these chains must be short, got {} after", self.peek_err()))
                    } else {
                        Ok(ret)
                    }
                }
            }
        }
    }

    fn logic_and(&mut self) -> Result<Expr, String> {
        let mut op1 = self.chain()?;
        while self.try_consume(&Token::And) {
            op1 = Expr::And(Box::new(op1), Box::new(self.chain()?));
        }
        Ok(op1)
    }

    fn single(&mut self) -> Result<Expr, String> {
        let mut op1 = self.logic_and()?;
        while self.try_consume(&Token::Or) {
            op1 = Expr::Or(Box::new(op1), Box::new(self.logic_and()?));
        }
        Ok(op1)
    }

    // Nonempty (caller should check empty condition); no semicolons allowed. List literals;
    // function declarations; LHSes of assignments. Not for function calls, I think? f(x; y) might
    // actually be ok...  bool is whether a comma was found, to distinguish (x) from (x,)
    fn comma_separated(&mut self) -> Result<(Vec<Box<Expr>>, bool), String> {
        let mut xs = vec![Box::new(self.single()?)];
        let mut comma = false;
        while self.try_consume(&Token::Comma) {
            comma = true;
            if self.peek_csc_stopper() {
                return Ok((xs, comma))
            }
            xs.push(Box::new(self.single()?));
        }
        return Ok((xs, comma))
    }

    // Comma-separated things. No semicolons or assigns allowed. Should be nonempty I think.
    fn pattern(&mut self) -> Result<Expr, String> {
        let (exs, comma) = self.comma_separated()?;
        match (few(exs), comma) {
            (Few::Zero, _) => Err(format!("Expected pattern, got nothing, next is {}", self.peek_err())),
            (Few::One(ex), false) => Ok(*ex),
            (Few::One(ex), true) => Ok(Expr::CommaSeq(vec![ex])),
            (Few::Many(exs), _) => Ok(Expr::CommaSeq(exs))
        }
    }

    // Comma-separated things. No semicolons or assigns allowed. Should be nonempty I think.
    fn annotated_pattern(&mut self) -> Result<Expr, String> {
        let pat = self.pattern()?;
        if self.try_consume(&Token::Colon) {
            if self.peek_csc_stopper() {
                Ok(Expr::Annotation(Box::new(pat), None))
            } else {
                Ok(Expr::Annotation(Box::new(pat), Some(Box::new(self.single()?))))
            }
        } else {
            Ok(pat)
        }
    }

    fn assignment(&mut self) -> Result<Expr, String> {
        let ag_start_err = self.peek_err();
        if self.try_consume(&Token::Swap) {
            let a = to_lvalue(self.single()?)?;
            self.require(Token::Comma, format!("swap between lvalues at {}", ag_start_err))?;
            let b = to_lvalue(self.single()?)?;
            Ok(Expr::Swap(Box::new(a), Box::new(b)))
        } else {
            let every = self.try_consume(&Token::Every);
            // TODO: parsing can be different after Every
            let pat = self.annotated_pattern()?;

            match self.peek() {
                Some(Token::Assign) => {
                    self.advance();
                    match pat {
                        Expr::Call(lhs, op) => match few(op) {
                            Few::One(op) => Ok(Expr::OpAssign(
                                every,
                                Box::new(to_lvalue(*lhs)?),
                                Box::new(*op),
                                Box::new(self.pattern()?),
                            )),
                            _ => Err(format!("call w not 1 arg is not assignop, at {}", ag_start_err)),
                        }
                        _ => {
                            Ok(Expr::Assign(every, Box::new(to_lvalue(pat)?), Box::new(self.pattern()?)))
                        }
                    }
                }
                /*
                Some(Token::Declare) => {
                    self.advance();
                    Ok(Expr::Declare(Box::new(to_lvalue(pat)?), Box::new(self.pattern()?)))
                }
                */
                _ => if every {
                    Err(format!("`every` as not assignment at {} now {}", ag_start_err, self.peek_err()))
                } else {
                    Ok(pat)
                }
            }
        }
    }

    fn expression(&mut self) -> Result<Expr, String> {
        let mut ags = vec![Box::new(self.assignment()?)];
        let mut semicolon = false;

        while self.try_consume(&Token::Semicolon) {
            semicolon = true;
            if self.peek() != None {
                ags.push(Box::new(self.assignment()?));
            }
        }

        Ok(if ags.len() == 1 && !semicolon {
            *ags.remove(0)
        } else {
            Expr::Sequence(ags)
        })
    }

    fn is_at_end(&self) -> bool {
        self.i == self.tokens.len()
    }
}

// allow the empty expression
pub fn parse(code: &str) -> Result<Option<Expr>, String> {
    let tokens = lex(code);
    if tokens.is_empty() {
        Ok(None)
    } else {
        let mut p = Parser { tokens, i: 0 };
        match p.expression() {
            Ok(ret) => if p.is_at_end() {
                Ok(Some(ret))
            } else {
                Err(format!("Didn't finish parsing: got {}", p.peek_err()))
            }
            Err(err) => Err(err),
        }
    }
}

pub trait WriteMaybeExtractable: Write {
    fn extract(&self) -> Option<&[u8]>;
}

impl WriteMaybeExtractable for io::Sink {
    fn extract(&self) -> Option<&[u8]> { None }
}
impl WriteMaybeExtractable for io::Stdout {
    fn extract(&self) -> Option<&[u8]> { None }
}
impl WriteMaybeExtractable for Vec<u8> {
    fn extract(&self) -> Option<&[u8]> { Some(self) }
}

pub struct TopEnv {
    pub backrefs: Vec<Obj>,
    pub input: Box<dyn BufRead>,
    pub output: Box<dyn WriteMaybeExtractable>,
}

impl Debug for TopEnv {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "TopEnv {{ backrefs: {:?}, input: {:p}, output: {:p} }}", self.backrefs, self.input, self.output)
    }
}

#[derive(Debug)]
pub struct Env {
    vars: HashMap<String, (ObjType, Obj)>,
    parent: Result<Rc<RefCell<Env>>, TopEnv>,
}
impl Env {
    pub fn new(top: TopEnv) -> Env {
        Env { vars: HashMap::new(), parent: Err(top) }
    }
    fn with_parent(env: &Rc<RefCell<Env>>) -> Rc<RefCell<Env>> {
        Rc::new(RefCell::new(
            Env { vars: HashMap::new(), parent: Ok(Rc::clone(&env)) }
        ))
    }
    pub fn mut_top_env<T>(&mut self, f: impl FnOnce(&mut TopEnv) -> T) -> T {
        match &mut self.parent {
            Ok(v) => v.borrow_mut().mut_top_env(f),
            Err(t) => f(t),
        }
    }

    fn get_var(&self, s: &str) -> NRes<Obj> {
        match self.vars.get(s) {
            Some(v) => Ok(v.1.clone()),
            None => match &self.parent {
                Ok(p) => p.borrow().get_var(s),
                Err(_) => Err(NErr::name_error(format!("No such variable: {}", s))),
            }
        }
    }

    fn modify_existing_var<T>(&mut self, key: &str, f: impl FnOnce(&mut (ObjType, Obj)) -> T) -> Option<T> {
        match self.vars.get_mut(key) {
            Some(target) => Some(f(target)),
            None => match &self.parent {
                Ok(p) => p.borrow_mut().modify_existing_var(key, f),
                Err(_) => None,
            }
        }
    }
    fn insert(&mut self, key: String, ty: ObjType, val: Obj) -> Option<Obj> {
        self.vars.insert(key, (ty, val)).map(|x| x.1)
    }
    fn insert_type(&mut self, b: ObjType) {
        self.insert(b.name(), ObjType::Any, Obj::Func(Func::Type(b), Precedence::zero()));
    }
    fn insert_builtin_with_precedence(&mut self, b: impl Builtin + 'static, p: Precedence) {
        self.insert(b.builtin_name().to_string(), ObjType::Any, Obj::Func(Func::Builtin(Rc::new(b)), p));
    }
    fn insert_builtin(&mut self, b: impl Builtin + 'static) {
        let p = Precedence(default_precedence(b.builtin_name()), Assoc::Left);
        self.insert_builtin_with_precedence(b, p);
    }
}

// the ObjType is provided iff it's a declaration

fn assign_all_basic(env: &mut Env, lhs: &[Box<EvaluatedLvalue>], rt: Option<&ObjType>, rhs: &[Obj]) -> NRes<()> {
    if lhs.len() == rhs.len() {
        for (lhs1, rhs1) in lhs.iter().zip(rhs.iter()) {
            assign(env, lhs1, rt, rhs1)?;
        }
        Ok(())
    } else {
        Err(NErr::value_error(format!("Can't unpack into mismatched length {:?} {} != {:?} {}", lhs, lhs.len(), rhs, rhs.len())))
    }
}

fn assign_all(env: &mut Env, lhs: &[Box<EvaluatedLvalue>], rt: Option<&ObjType>, rhs: &[Obj]) -> NRes<()> {
    let mut splat = None;
    for (i, lhs1) in lhs.iter().enumerate() {
        match &**lhs1 {
            EvaluatedLvalue::Splat(inner) => match splat {
                Some(_) => return Err(NErr::syntax_error(format!("Can't have two splats in same sequence on left-hand side of assignment"))),
                None => {
                    splat = Some((i, inner));
                }
            }
            _ => {}
        }
    }
    match splat {
        Some((si, inner)) => {
            assign_all_basic(env, &lhs[..si], rt, &rhs[..si])?;
            assign(env, inner, rt, &Obj::from(rhs[si..rhs.len() - lhs.len() + si + 1].to_vec()))?;
            assign_all_basic(env, &lhs[si + 1..], rt, &rhs[rhs.len() - lhs.len() + si + 1..])
        }
        None => assign_all_basic(env, lhs, rt, rhs),
    }
}

// Modifying parts of a &mut Obj
// =============================

fn set_index(lhs: &mut Obj, indexes: &[EvaluatedIndexOrSlice], value: Obj, every: bool) -> NRes<()> {
    match (lhs, indexes) {
        (lhs, []) => { *lhs = value; Ok(()) }
        (Obj::Seq(s), [fi, rest @ ..]) => match (s, fi) {
            (Seq::List(v), EvaluatedIndexOrSlice::Index(i)) => {
                set_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, value, every)
            }
            (Seq::List(v), EvaluatedIndexOrSlice::Slice(i, j)) => {
                if every {
                    let v = Rc::make_mut(v);
                    let (lo, hi) = pythonic_slice(v, i.as_ref(), j.as_ref())?;
                    for i in lo..hi {
                        set_index(&mut v[i], rest, value.clone(), true)?;
                    }
                    Ok(())
                } else {
                    todo!("assgn to slice")
                    // set_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, value)
                }
            }
            (Seq::String(s), EvaluatedIndexOrSlice::Index(i)) if rest.is_empty() => match value {
                Obj::Seq(Seq::String(v)) => {
                    let mut_s = Rc::make_mut(s);
                    if v.as_bytes().len() == 1 {
                        // FIXME lmao
                        let mut owned = std::mem::take(mut_s).into_bytes();
                        let i = match pythonic_index(&owned, i) {
                            Ok(i) => i,
                            Err(e) => {
                                // put it baaaack!!
                                *mut_s = String::from_utf8(owned).unwrap();
                                return Err(e)
                            }
                        };
                        owned[i..i+1].copy_from_slice(v.as_bytes());
                        match String::from_utf8(owned) {
                            Ok(r) => { *mut_s = r; Ok(()) }
                            Err(err) => {
                                *mut_s = String::from_utf8_lossy(err.as_bytes()).into_owned();
                                Err(NErr::value_error(format!("assigning to string result not utf-8 (string corrupted)")))
                            }
                        }
                    } else {
                        Err(NErr::value_error(format!("assigning to string index, not a byte")))
                    }
                }
                _ => Err(NErr::value_error(format!("assigning to string index, not a string")))
            }
            (Seq::String(_), _) => Err(NErr::type_error(format!("string bad slice"))),
            (Seq::Dict(v, _), EvaluatedIndexOrSlice::Index(kk)) => {
                let k = to_key(kk.clone())?;
                let mut_d = Rc::make_mut(v);
                // We might create a new map entry, but only at the end, which is a bit of a
                // mismatch for Rust's map API if we want to recurse all the way
                if rest.is_empty() {
                    mut_d.insert(k, value); Ok(())
                } else {
                    set_index(match mut_d.get_mut(&k) {
                        Some(vvv) => vvv,
                        None => Err(NErr::type_error(format!("setting dictionary: nothing at key {:?} {:?}", mut_d, k)))?,
                    }, rest, value, every)
                }
            }
            (Seq::Dict(v, _), EvaluatedIndexOrSlice::Slice(None, None)) if rest.is_empty() => {
                let mut_d = Rc::make_mut(v);
                if every {
                    for (_, vv) in mut_d.iter_mut() {
                        set_index(vv, rest, value.clone(), true)?;
                    }
                    Ok(())
                } else {
                    Err(NErr::type_error(format!("can't slice dictionaries except with every")))
                }
            }
            (Seq::Dict(..), _) => Err(NErr::type_error(format!("dict bad slice"))),
            (Seq::Vector(v), EvaluatedIndexOrSlice::Index(i)) if rest.is_empty() => {
                match value {
                    Obj::Num(n) => {
                        let i = pythonic_index(v, i)?;
                        Rc::make_mut(v)[i] = n;
                        Ok(())
                    }
                    _ => Err(NErr::type_error(format!("vec bad value assgn")))
                }
            }
            (Seq::Vector(_), _) => Err(NErr::type_error(format!("vec bad slice / not impl"))),
            (Seq::Bytes(v), EvaluatedIndexOrSlice::Index(i)) if rest.is_empty() => {
                match value {
                    Obj::Num(n) => {
                        let i = pythonic_index(v, i)?;
                        Rc::make_mut(v)[i] = n.to_u8().ok_or(NErr::value_error(format!("can't to byte: {}", n)))?;
                        Ok(())
                    }
                    _ => Err(NErr::type_error(format!("bytes bad value assgn")))
                }
            }
            (Seq::Bytes(_), _) => Err(NErr::type_error(format!("vec bad slice / not impl"))),
        }
        (Obj::Func(_, Precedence(p, _)), [EvaluatedIndexOrSlice::Index(Obj::Seq(Seq::String(r)))]) => match &***r {
            "precedence" => match value {
                Obj::Num(f) => match f.to_f64() {
                    Some(f) => { *p = f; Ok(()) }
                    None => Err(NErr::value_error(format!("precedence must be convertible to float: {}", f))),
                }
                f => Err(NErr::type_error(format!("precedence must be number, got {}", f))),
            }
            k => Err(NErr::key_error(format!("function key must be 'precedence', got {}", k))),
        }
        (lhs, ii) => Err(NErr::index_error(format!("can't set index {:?} {:?}", lhs, ii))),
    }
}

// be careful not to call this with both lhs holding a mutable reference into a RefCell and rhs
// trying to take such a reference!
fn modify_existing_index(lhs: &mut Obj, indexes: &[EvaluatedIndexOrSlice], f: impl FnOnce(&mut Obj) -> NRes<Obj>) -> NRes<Obj> {
    match indexes.split_first() {
        None => f(lhs),
        Some((i, rest)) => {
            match (lhs, i) {
                (Obj::Seq(Seq::List(v)), EvaluatedIndexOrSlice::Index(i)) => {
                    modify_existing_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, f)
                }
                (Obj::Seq(Seq::Dict(v, def)), EvaluatedIndexOrSlice::Index(kk)) => {
                    let k = to_key(kk.clone())?;
                    let mut_d = Rc::make_mut(v);
                    // FIXME improve
                    if !mut_d.contains_key(&k) {
                        match def {
                            Some(d) => { mut_d.insert(k.clone(), (&**d).clone()); }
                            None => return Err(NErr::key_error(format!("nothing at key {:?} {:?}", mut_d, k))),
                        }
                    }
                    modify_existing_index(match mut_d.get_mut(&k) {
                        Some(vvv) => vvv,
                        // shouldn't happen:
                        None => Err(NErr::key_error(format!("nothing at key {:?} {:?}", mut_d, k)))?,
                    }, rest, f)
                }
                // TODO everything
                (lhs2, ii) => Err(NErr::type_error(format!("can't modify index {:?} {:?}", lhs2, ii))),
            }
        }
    }
}

// same here...
fn modify_every_existing_index(lhs: &mut Obj, indexes: &[EvaluatedIndexOrSlice], f: &mut impl FnMut(&mut Obj) -> NRes<()>) -> NRes<()> {
    match indexes.split_first() {
        None => f(lhs),
        Some((i, rest)) => {
            match (lhs, i) {
                (Obj::Seq(Seq::List(v)), EvaluatedIndexOrSlice::Index(i)) => {
                    modify_every_existing_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, f)
                }
                (Obj::Seq(Seq::List(v)), EvaluatedIndexOrSlice::Slice(lo, hi)) => {
                    let (lo, hi) = pythonic_slice(v, lo.as_ref(), hi.as_ref())?;
                    for m in &mut Rc::make_mut(v)[lo..hi] {
                        modify_every_existing_index(m, rest, f)?
                    }
                    Ok(())
                }
                (Obj::Seq(Seq::Dict(v, def)), EvaluatedIndexOrSlice::Index(kk)) => {
                    let k = to_key(kk.clone())?;
                    let mut_d = Rc::make_mut(v);
                    // FIXME improve
                    if !mut_d.contains_key(&k) {
                        match def {
                            Some(d) => { mut_d.insert(k.clone(), (&**d).clone()); }
                            None => return Err(NErr::key_error(format!("nothing at key {:?} {:?}", mut_d, k))),
                        }
                    }
                    modify_every_existing_index(match mut_d.get_mut(&k) {
                        Some(vvv) => vvv,
                        // shouldn't happen:
                        None => Err(NErr::key_error(format!("nothing at key {:?} {:?}", mut_d, k)))?,
                    }, rest, f)
                }
                // TODO everything
                (lhs2, ii) => Err(NErr::type_error(format!("can't modify every index {:?} {:?}", lhs2, ii))),
            }
        }
    }
}

fn insert_declare(env: &mut Env, s: &str, ty: ObjType, rhs: Obj) -> NRes<()> {
    if env.insert(s.to_string(), ty, rhs).is_some() {
        Err(NErr::name_error(format!("Declaring/assigning variable that already exists: {:?}. If in pattern with other declarations, parenthesize existent variables", s)))
    } else {
        Ok(())
    }
}

fn assign_respecting_type(env: &mut Env, s: &str, ixs: &[EvaluatedIndexOrSlice], rhs: &Obj, every: bool) -> NRes<()> {
    env.modify_existing_var(s, |(ty, v)| {
        // Eagerly check type only if ixs is empty, otherwise we can't really do
        // that (at least not in full generality)
        if ixs.is_empty() && !is_type(ty, rhs) {
            Err(NErr::type_error(format!("Assignment to {} type check failed: {} not {}", s, rhs, ty.name())))?
        }
        set_index(v, ixs, rhs.clone(), every)?;
        // Check type after the fact. TODO if we ever do subscripted types: this
        // will be super inefficient lmao, we can be smart tho
        if !ixs.is_empty() && !is_type(ty, &v) {
            Err(NErr::type_error(format!("Assignment to {} LATE type check failed (the assignment still happened): {} not {}", s, rhs, ty.name())))
        } else {
            Ok(())
        }
    }).ok_or(NErr::name_error(if ixs.is_empty() {
         format!("Variable {:?} not found (use := to declare)", s)
    } else {
         format!("Variable {:?} not found, couldn't set into index {:?}", s, ixs)
    }))?
}

fn assign(env: &mut Env, lhs: &EvaluatedLvalue, rt: Option<&ObjType>, rhs: &Obj) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::IndexedIdent(s, ixs) => match rt {
            Some(ty) => {
                // declaration
                if ixs.is_empty() {
                    insert_declare(env, s, ty.clone(), rhs.clone())
                } else {
                    return Err(NErr::name_error(format!("Can't declare new value into index expression: {:?} {:?}", s, ixs)))
                }
            }
            None => assign_respecting_type(env, s, ixs, rhs, false),
        }
        EvaluatedLvalue::CommaSeq(ss) => {
            match rhs {
                Obj::Seq(Seq::List(ls)) => assign_all(env, ss, rt, ls),
                rhs => assign_all(env, ss, rt, obj_to_cloning_iter(&rhs, "unpacking")?.collect::<Vec<Obj>>().as_slice()),
            }
        }
        EvaluatedLvalue::Annotation(s, ann) => match ann {
            None => assign(env, s, Some(&ObjType::Any), rhs),
            Some(t) => assign(env, s, Some(&to_type(t, "annotation")?), rhs),
        }
        EvaluatedLvalue::Unannotation(s) => {
            assign(env, s, None, rhs)
        }
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!("Can't assign to raw splat {:?}", lhs))),
    }
}

fn assign_every(env: &mut Env, lhs: &EvaluatedLvalue, rt: Option<&ObjType>, rhs: &Obj) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::IndexedIdent(s, ixs) => match rt {
            Some(ty) => {
                // declaration
                if ixs.is_empty() {
                    insert_declare(env, s, ty.clone(), rhs.clone())
                } else {
                    return Err(NErr::name_error(format!("Can't declare new value into index expression: {:?} {:?}", s, ixs)))
                }
            }
            None => assign_respecting_type(env, s, ixs, rhs, true),
        }
        EvaluatedLvalue::CommaSeq(ss) => {
            for v in ss {
                assign_every(env, v, rt, rhs)?;
            }
            Ok(())
        }
        EvaluatedLvalue::Annotation(s, ann) => match ann {
            None => assign_every(env, s, Some(&ObjType::Any), rhs),
            Some(t) => assign_every(env, s, Some(&to_type(t, "annotation")?), rhs),
        }
        EvaluatedLvalue::Unannotation(s) => {
            assign_every(env, s, None, rhs)
        }
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!("Can't assign to raw splat {:?}", lhs))),
    }
}

// different: doesn't hold a mutable borrow to the environment when calling rhs; doesn't accept
// declarations
fn modify_every(env: &Rc<RefCell<Env>>, lhs: &EvaluatedLvalue, rhs: &mut impl FnMut(Obj) -> NRes<Obj>) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::IndexedIdent(s, ixs) => {
            // drop borrow immediately
            let mut old: Obj = env.borrow_mut().get_var(s)?;

            if ixs.is_empty() {
                let new = rhs(old)?;
                env.borrow_mut().modify_existing_var(s, |(ty, old)| {
                    if is_type(ty, &new) {
                        *old = new.clone(); Ok(())
                    } else {
                        Err(NErr::name_error(format!("Modify every: assignment to {} type check failed: {} not {}", s, new, ty.name())))
                    }
                }).ok_or(NErr::name_error(format!("Variable {:?} not found in modify every", s)))?
            } else {
                modify_every_existing_index(&mut old, ixs, &mut |x: &mut Obj| {
                    // TODO take??
                    *x = rhs(x.clone())?; Ok(())
                })
            }
        }
        EvaluatedLvalue::CommaSeq(ss) => {
            for v in ss {
                modify_every(env, v, rhs)?;
            }
            Ok(())
        }
        EvaluatedLvalue::Annotation(..) => Err(NErr::type_error(format!("No annotations in modify every: {:?}", lhs))),
        EvaluatedLvalue::Unannotation(s) => modify_every(env, s, rhs),
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!("Can't assign to raw splat {:?}", lhs))),
    }
}


const DEFAULT_PRECEDENCE: f64 = 0.0;
const COMPARISON_PRECEDENCE: f64 = 1.0;
const STRING_PRECEDENCE: f64 = 2.0;
const OR_PRECEDENCE: f64 = 3.0;
const PLUS_PRECEDENCE: f64 = 4.0;
const MULTIPLY_PRECEDENCE: f64 = 5.0;
const EXPONENT_PRECEDENCE: f64 = 6.0;
const INDEX_PRECEDENCE: f64 = 7.0;
const DOT_PRECEDENCE: f64 = 8.0;

fn default_precedence(name: &str) -> f64 {
    name.chars().map(|c| if c.is_alphanumeric() || c == '_' {
        DEFAULT_PRECEDENCE
    } else {
        match c {
            '=' | '<' | '>' | '~' => COMPARISON_PRECEDENCE,
            '$' => STRING_PRECEDENCE,
            '|' => OR_PRECEDENCE,
            '+' | '-' | '@' => PLUS_PRECEDENCE,
            '*' | '/' | '%' | '&' => MULTIPLY_PRECEDENCE,
            '^' => EXPONENT_PRECEDENCE,
            '!' | '?' => INDEX_PRECEDENCE,
            _ => DOT_PRECEDENCE, // particularly .
        }
    }).reduce(f64::min).unwrap_or(0.0)
}

struct ChainEvaluator {
    operands: Vec<Vec<Obj>>,
    operators: Vec<(Func, Precedence)>,
}

impl ChainEvaluator {
    fn new(operand: Obj) -> ChainEvaluator {
        ChainEvaluator { operands: vec![vec![operand]], operators: Vec::new() }
    }

    fn run_top_popped(&mut self, env: &REnv, op: Func) -> NRes<()> {
        let mut rhs = self.operands.pop().expect("sync");
        let mut lhs = self.operands.pop().expect("sync");
        lhs.append(&mut rhs); // concats and drains rhs of elements
        self.operands.push(vec![op.run(env, lhs)?]);
        Ok(())
    }

    fn run_top(&mut self, env: &REnv) -> NRes<()> {
        let (op, _) = self.operators.pop().expect("sync");
        self.run_top_popped(env, op)
    }

    fn give(&mut self, env: &REnv, operator: Func, precedence: Precedence, operand: Obj) -> NRes<()> {
        while self.operators.last().map_or(false, |t| t.1.0 >= precedence.0) {
            let (top, prec) = self.operators.pop().expect("sync");
            match top.try_chain(&operator) {
                Some(new_op) => {
                    self.operators.push((new_op, prec));
                    self.operands.last_mut().expect("sync").push(operand);
                    return Ok(())
                }
                None => { self.run_top_popped(env, top)?; }
            }
        }

        self.operators.push((operator, precedence));
        self.operands.push(vec![operand]);
        Ok(())
    }

    fn finish(&mut self, env: &REnv) -> NRes<Obj> {
        while !self.operators.is_empty() {
            self.run_top(env)?;
        }
        if self.operands.len() == 1 {
            Ok(self.operands.remove(0).remove(0))
        } else {
            panic!("chain eval out of sync")
        }
    }
}

// allow splats
fn eval_seq(env: &Rc<RefCell<Env>>, exprs: &Vec<Box<Expr>>) -> NRes<Vec<Obj>> {
    let mut acc = Vec::new();
    for x in exprs {
        match &**x {
            Expr::Splat(inner) => {
                let res = evaluate(env, inner)?;
                match res {
                    // FIXME
                    Obj::Seq(Seq::List(mut xx)) => acc.append(Rc::make_mut(&mut xx)),
                    _ => Err(NErr::type_error(format!("Can't splat non-list {:?}", res)))?
                }
            }
            _ => acc.push(evaluate(env, x)?)
        }
    }
    Ok(acc)
}

fn eval_index_or_slice(env: &Rc<RefCell<Env>>, expr: &IndexOrSlice) -> NRes<EvaluatedIndexOrSlice> {
    match expr {
        IndexOrSlice::Index(v) => Ok(EvaluatedIndexOrSlice::Index(evaluate(env, v)?)),
        IndexOrSlice::Slice(a, b) => Ok(EvaluatedIndexOrSlice::Slice(
                match a { Some(a) => Some(evaluate(env, a)?), None => None },
                match b { Some(b) => Some(evaluate(env, b)?), None => None })),
    }
}

fn eval_lvalue(env: &Rc<RefCell<Env>>, expr: &Lvalue) -> NRes<EvaluatedLvalue> {
    match expr {
        Lvalue::IndexedIdent(s, v) => Ok(EvaluatedLvalue::IndexedIdent(
            s.to_string(),
            v.iter().map(|e| Ok(eval_index_or_slice(env, e)?)).collect::<NRes<Vec<EvaluatedIndexOrSlice>>>()?
        )),
        Lvalue::Annotation(s, t) => Ok(EvaluatedLvalue::Annotation(
            Box::new(eval_lvalue(env, s)?),
            match t { Some(e) => Some(evaluate(env, e)?), None => None }
        )),
        Lvalue::Unannotation(s) => Ok(EvaluatedLvalue::Unannotation(
            Box::new(eval_lvalue(env, s)?),
        )),
        Lvalue::CommaSeq(v) => Ok(EvaluatedLvalue::CommaSeq(
            v.iter().map(|e| Ok(Box::new(eval_lvalue(env, e)?))).collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?
        )),
        Lvalue::Splat(v) => Ok(EvaluatedLvalue::Splat(Box::new(eval_lvalue(env, v)?))),
    }
}

fn pythonic_index_isize<T>(xs: &[T], n: isize) -> NRes<usize> {
    if n >= 0 && n < (xs.len() as isize) { return Ok(n as usize) }

    let i2 = (n + (xs.len() as isize)) as usize;
    if i2 < xs.len() { return Ok(i2) }

    Err(NErr::index_error(format!("Index out of bounds: {:?}", n)))
}

fn pythonic_index<T>(xs: &[T], i: &Obj) -> NRes<usize> {
    match i {
        Obj::Num(ii) => match ii.to_isize() {
            Some(n) => pythonic_index_isize(xs, n),
            _ => Err(NErr::index_error(format!("Index out of bounds of isize or non-integer: {:?}", ii)))
        }
        _ => Err(NErr::index_error(format!("Invalid (non-numeric) index: {:?}", i))),
    }
}

fn pythonic_mut<'a, 'b>(xs: &'a mut Vec<Obj>, i: &'b Obj) -> NRes<&'a mut Obj> {
    let ii = pythonic_index(xs, i)?; Ok(&mut xs[ii])
}

// for slicing
fn clamped_pythonic_index<T>(xs: &[T], i: &Obj) -> NRes<usize> {
    match i {
        Obj::Num(ii) => match ii.to_isize() {
            Some(n) => {
                if n >= 0 { return Ok((n as usize).min(xs.len())) }

                let i2 = n + (xs.len() as isize);
                if i2 < 0 { Ok(0) } else { Ok(i2 as usize) }
            }
            _ => Err(NErr::index_error(format!("Slice index out of bounds of isize or non-integer: {:?}", ii)))
        }
        _ => Err(NErr::index_error(format!("Invalid (non-numeric) slice index: {:?}", i))),
    }
}

fn pythonic_slice<T>(xs: &[T], lo: Option<&Obj>, hi: Option<&Obj>) -> NRes<(usize, usize)> {
    Ok((
        match lo { Some(lo) => clamped_pythonic_index(xs, &lo)?, None => 0 },
        match hi { Some(hi) => clamped_pythonic_index(xs, &hi)?, None => xs.len() },
    ))
}

fn cyclic_index<T>(xs: &[T], i: &Obj) -> NRes<usize> {
    match i {
        Obj::Num(ii) => match ii.to_isize() {
            Some(n) => if xs.len() == 0 {
                Err(NErr::index_error("Empty, can't cyclic index".to_string()))
            } else {
                Ok(n.rem_euclid(xs.len() as isize) as usize)
            }
            _ => Err(NErr::index_error(format!("Index out of bounds of isize or non-integer: {:?}", ii)))
        }
        _ => Err(NErr::index_error(format!("Invalid (non-numeric) index: {:?}", i))),
    }
}

fn linear_index_isize(xr: Seq, i: isize) -> NRes<Obj> {
    match xr {
        Seq::List(xx) => Ok(xx[pythonic_index_isize(&xx, i)?].clone()),
        Seq::Vector(x) => Ok(Obj::Num(x[pythonic_index_isize(&x, i)?].clone())),
        Seq::Bytes(x) => Ok(Obj::from(x[pythonic_index_isize(&x, i)?] as usize)),
        Seq::String(s) => {
            let bs = s.as_bytes();
            let i = pythonic_index_isize(bs, i)?;
            // TODO this was the path of least resistance; idk what good semantics actually are
            // TODO copypasta
            Ok(Obj::from(String::from_utf8_lossy(&bs[i..i+1]).into_owned()))
        }
        Seq::Dict(..) => Err(NErr::type_error("dict is not a linear sequence".to_string())),
    }
}

fn index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, ir) {
        (Obj::Seq(s), ii) => match s {
            Seq::List(xx) => Ok(xx[pythonic_index(xx, &ii)?].clone()),
            Seq::String(s) => {
                let bs = s.as_bytes();
                let i = pythonic_index(bs, &ii)?;
                // TODO this was the path of least resistance; idk what good semantics actually are
                Ok(Obj::from(String::from_utf8_lossy(&bs[i..i+1]).into_owned()))
            }
            Seq::Dict(xx, def) => {
                let k = to_key(ii)?;
                match xx.get(&k) {
                    Some(e) => Ok(e.clone()),
                    None => match def {
                        Some(d) => Ok((&**d).clone()),
                        None => Err(NErr::key_error(format!("Dictionary lookup: nothing at key {:?} {:?}", xx, k))),
                    }
                }
            }
            Seq::Vector(v) => Ok(Obj::Num(v[pythonic_index(v, &ii)?].clone())),
            Seq::Bytes(v) => Ok(Obj::from(v[pythonic_index(v, &ii)?] as usize)),
        }
        (Obj::Func(_, Precedence(p, _)), Obj::Seq(Seq::String(k))) => match &**k {
            "precedence" => Ok(Obj::from(*p)),
            _ => Err(NErr::type_error(format!("can't index into func {:?}", k))),
        }
        (xr, ir) => Err(NErr::type_error(format!("can't index {:?} {:?}", xr, ir))),
    }
}

fn obj_cyclic_index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, ir) {
        (Obj::Seq(s), ii) => match s {
            Seq::List(xx) => Ok(xx[cyclic_index(xx, &ii)?].clone()),
            Seq::String(s) => {
                let bs = s.as_bytes();
                let i = cyclic_index(bs, &ii)?;
                // TODO this was the path of least resistance; idk what good semantics actually are
                Ok(Obj::from(String::from_utf8_lossy(&bs[i..i+1]).into_owned()))
            }
            Seq::Dict(..) => Err(NErr::type_error(format!("can't cyclically index {:?} {:?}", xr, ii))),
            Seq::Vector(xx) => Ok(Obj::Num(xx[cyclic_index(xx, &ii)?].clone())),
            Seq::Bytes(xx) => Ok(Obj::from(xx[cyclic_index(xx, &ii)?] as usize)),
        }
        // TODO other sequences
        (xr, ir) => Err(NErr::type_error(format!("can't cyclically index {:?} {:?}", xr, ir))),
    }
}

fn slice(xr: Obj, lo: Option<Obj>, hi: Option<Obj>) -> NRes<Obj> {
    match (&xr, lo, hi) {
        (Obj::Seq(Seq::List(xx)), lo, hi) => {
            let (lo, hi) = pythonic_slice(xx, lo.as_ref(), hi.as_ref())?;
            Ok(Obj::from(xx[lo..hi].to_vec()))
        }
        (Obj::Seq(Seq::String(s)), lo, hi) => {
            let bs = s.as_bytes();
            let (lo, hi) = pythonic_slice(bs, lo.as_ref(), hi.as_ref())?;
            // TODO this was the path of least resistance; idk what good semantics actually are
            Ok(Obj::from(String::from_utf8_lossy(&bs[lo..hi]).into_owned()))
        }
        (xr, lo, hi) => Err(NErr::type_error(format!("can't slice {:?} {:?} {:?}", xr, lo, hi))),
    }
}

fn index_or_slice(xr: Obj, ir: EvaluatedIndexOrSlice) -> NRes<Obj> {
    match ir {
        EvaluatedIndexOrSlice::Index(i) => index(xr, i),
        EvaluatedIndexOrSlice::Slice(i, j) => slice(xr, i, j),
    }
}


fn safe_index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, &ir) {
        (Obj::Null, _) => Ok(Obj::Null),
        (Obj::Seq(s), ii) => match s {
            Seq::String(s) => {
                let bs = s.as_bytes();
                // TODO above
                match pythonic_index(bs, ii) {
                    Ok(i) => Ok(Obj::from(String::from_utf8_lossy(&bs[i..i+1]).into_owned())),
                    Err(_) => Ok(Obj::Null),
                }
            }
            Seq::List(xx) => {
                // Not sure about catching *every* err from pythonic_index here...
                match pythonic_index(xx, ii) {
                    Ok(i) => Ok(xx[i].clone()),
                    Err(_) => Ok(Obj::Null),
                }
            }
            Seq::Dict(xx, def) => {
                let k = to_key(ir)?;
                match xx.get(&k) {
                    Some(e) => Ok(e.clone()),
                    None => match def {
                        Some(d) => Ok((&**d).clone()),
                        None => Ok(Obj::Null),
                    }
                }
            }
            Seq::Vector(v) => {
                // ^
                match pythonic_index(v, ii) {
                    Ok(i) => Ok(Obj::Num(v[i].clone())),
                    Err(_) => Ok(Obj::Null),
                }
            }
            Seq::Bytes(v) => {
                // ^
                match pythonic_index(v, ii) {
                    Ok(i) => Ok(Obj::from(v[i] as usize)),
                    Err(_) => Ok(Obj::Null),
                }
            }
        }
        _ => Err(NErr::type_error(format!("Can't safe index {:?} {:?}", xr, ir))),
    }
}

fn call(env: &REnv, f: Obj, args: Vec<Obj>) -> NRes<Obj> {
    match f {
        Obj::Func(ff, _) => ff.run(env, args),
        _ => Err(NErr::type_error(format!("Can't call non-function {:?}", f))),
    }
}

fn call_or_part_apply(env: &REnv, f: Obj, args: Vec<Obj>) -> NRes<Obj> {
    match f {
        Obj::Func(ff, _) => ff.run(env, args),
        f => match few(args) {
            Few::One(Obj::Func(f2, _)) => Ok(Obj::Func(Func::PartialApp1(Box::new(f2), Box::new(f)), Precedence::zero())),
            Few::One(f2) => Err(NErr::type_error(format!("Can't call non-function {:?} (and argument {:?} not callable)", f, f2))),
            _ => Err(NErr::type_error(format!("Can't call non-function {:?} (and more than one argument)", f))),
        }
    }
}

fn eval_lvalue_as_obj(env: &Rc<RefCell<Env>>, expr: &Lvalue) -> NRes<Obj> {
    match expr {
        Lvalue::IndexedIdent(s, v) => {
            let mut sr = env.borrow_mut().get_var(s)?;
            for ix in v {
                sr = index_or_slice(sr, eval_index_or_slice(env, ix)?)?.clone();
            }
            Ok(sr)
        },
        Lvalue::Annotation(s, _) => eval_lvalue_as_obj(env, s),
        Lvalue::Unannotation(s) => eval_lvalue_as_obj(env, s),
        Lvalue::CommaSeq(v) => Ok(Obj::from(
            v.iter().map(|e| Ok(eval_lvalue_as_obj(env, e)?)).collect::<NRes<Vec<Obj>>>()?
        )),
        // maybe if commaseq eagerly looks for splats...
        Lvalue::Splat(_) => Err(NErr::syntax_error("Can't evaluate splat on LHS of assignment??".to_string())),
    }
}

/*
// note we must (?) not hold a mutable borrow of env while calling f since f might (will probably?)
// also get one
fn modify_every_lvalue(env: &Rc<RefCell<Env>>, expr: &Lvalue, f: &Func) -> NRes<()> {
    match expr {
        Lvalue::IndexedIdent(s, v) => {
            let mut sr = env.borrow_mut().get_var(s)?;
            for ix in v {
                sr = index_or_slice(sr, eval_index_or_slice(env, ix)?)?.clone();
            }
            Ok(sr)
        },
        Lvalue::Annotation(s, _) => eval_lvalue_as_obj(env, s),
        Lvalue::Unannotation(s) => eval_lvalue_as_obj(env, s),
        Lvalue::CommaSeq(v) => Ok(Obj::List(Rc::new(
            v.iter().map(|e| Ok(eval_lvalue_as_obj(env, e)?)).collect::<NRes<Vec<Obj>>>()?
        ))),
        // maybe if commaseq eagerly looks for splats...
        Lvalue::Splat(_) => Err(NErr::syntax_error("Can't evaluate splat on LHS of assignment??".to_string())),
    }
}
*/

fn obj_in(a: Obj, b: Obj) -> NRes<bool> {
    match (a, b) {
        (a, Obj::Seq(Seq::Dict(v, _))) => Ok(v.contains_key(&to_key(a)?)),
        (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(v))) => Ok((*v).contains(&*s)),
        (a, Obj::Seq(mut s)) => Ok(mut_seq_into_iter(&mut s).any(|x| x == a)),
        _ => Err(NErr::type_error("in: not compatible".to_string())),
    }
}

fn evaluate_for(env: &Rc<RefCell<Env>>, its: &[ForIteration], body: &Expr, callback: &mut impl FnMut(Obj) -> ()) -> NRes<()> {
    match its {
        [] => Ok(callback(evaluate(env, body)?)),
        [ForIteration::Iteration(ty, lvalue, expr), rest @ ..] => {
            let mut itr = evaluate(env, expr)?;
            match ty {
                ForIterationType::Normal => {
                    for x in mut_obj_into_iter(&mut itr, "for iteration")? {
                        let ee = Env::with_parent(env);
                        let p = eval_lvalue(&ee, lvalue)?;

                        // should assign take x
                        assign(&mut ee.borrow_mut(), &p, Some(&ObjType::Any), &x)?;
                        evaluate_for(&ee, rest, body, callback)?;
                    }
                }
                ForIterationType::Item => {
                    for (k, v) in mut_obj_into_iter_pairs(&mut itr, "for (item) iteration")? {
                        let ee = Env::with_parent(env);
                        let p = eval_lvalue(&ee, lvalue)?;

                        // should assign take x
                        assign(&mut ee.borrow_mut(), &p, Some(&ObjType::Any), &Obj::from(vec![key_to_obj(k), v]))?;
                        evaluate_for(&ee, rest, body, callback)?;
                    }
                }
                ForIterationType::Declare => {
                    let ee = Env::with_parent(env);
                    let p = eval_lvalue(&ee, lvalue)?;
                    assign(&mut ee.borrow_mut(), &p, Some(&ObjType::Any), &itr)?;

                    evaluate_for(&ee, rest, body, callback)?;
                }
            }
            Ok(())
        }
        [ForIteration::Guard(guard), rest @ ..] => {
            let r = evaluate(env, guard)?;
            if r.truthy() {
                evaluate_for(env, rest, body, callback)
            } else {
                Ok(())
            }
        }
    }
}

pub fn evaluate(env: &Rc<RefCell<Env>>, expr: &Expr) -> NRes<Obj> {
    match expr {
        Expr::IntLit(n) => Ok(Obj::from(n.clone())),
        Expr::FloatLit(n) => Ok(Obj::from(*n)),
        Expr::ImaginaryFloatLit(n) => Ok(Obj::Num(NNum::Complex(Complex64::new(0.0, *n)))),
        Expr::StringLit(s) => Ok(Obj::Seq(Seq::String(Rc::clone(s)))),
        Expr::FormatString(s) => {
            // TODO: split this up? honestly idk
            let mut nesting_level = 0;
            let mut ret = String::new();
            let mut expr_acc = String::new(); // accumulate
            let mut p = s.chars().peekable();
            while let Some(c) = p.next() {
                match (nesting_level, c) {
                    (0, '{') => {
                        if p.peek() == Some(&'{') {
                            p.next();
                            ret.push('{');
                        } else {
                            nesting_level += 1;
                        }
                    }
                    (0, '}') => {
                        if p.peek() == Some(&'}') {
                            p.next();
                            ret.push('}');
                        } else {
                            return Err(NErr::syntax_error("format string: unmatched right brace".to_string()))
                        }
                    }
                    (0, c) => { ret.push(c); }
                    (_, '{') => { nesting_level += 1; expr_acc.push('{'); }
                    (1, '}') => {
                        nesting_level -= 1;

                        let mut lexer = Lexer::new(&expr_acc);
                        lexer.lex();
                        let mut flags = MyFmtFlags::new();
                        if lexer.tokens.is_empty() {
                            return Err(NErr::syntax_error("format string: empty format expr".to_string()))
                        } else {
                            for com in lexer.last_comment {
                                for c in com.chars() {
                                    match c {
                                        'x' => { flags.base = FmtBase::LowerHex; }
                                        'X' => { flags.base = FmtBase::UpperHex; }
                                        'b' | 'B' => { flags.base = FmtBase::Binary; }
                                        'o' | 'O' => { flags.base = FmtBase::Octal; }
                                        // 'e' => { flags.base = FmtBase::LowerExp; }
                                        // 'E' => { flags.base = FmtBase::UpperExp; }
                                        'd' | 'D' => { flags.base = FmtBase::Decimal; }
                                        _ => {}
                                    }
                                }
                            }
                            let mut p = Parser { tokens: lexer.tokens, i: 0 };
                            let fex = p.expression().map_err(|e| NErr::syntax_error(format!("format string: failed to parse expr: {}", e)))?;
                            if p.is_at_end() {
                                // FIXME err?
                                evaluate(env, &fex)?.fmt_with(&mut ret, flags).unwrap();
                            } else {
                                return Err(NErr::syntax_error("format string: couldn't finish parsing format expr".to_string()))
                            }
                        }
                        expr_acc.clear();
                    }
                    (_, '}') => { nesting_level -= 1; expr_acc.push('}'); }
                    (_, c) => { expr_acc.push(c) }
                }
            }
            if nesting_level != 0 {
                return Err(NErr::syntax_error("format string: unmatched left brace".to_string()))
            }
            Ok(Obj::from(ret))
        }
        Expr::Ident(s) => env.borrow_mut().get_var(s),
        Expr::Index(x, i) => {
            let xr = evaluate(env, x)?;
            let ir = eval_index_or_slice(env, i)?;
            index_or_slice(xr, ir)
        }
        Expr::Chain(op1, ops) => {
            let mut ev = ChainEvaluator::new(evaluate(env, op1)?);
            for (oper, opd) in ops {
                // make sure this borrow_mut goes out of scope
                let oprr = env.borrow_mut().get_var(oper)?;
                if let Obj::Func(b, prec) = oprr {
                    let oprd = evaluate(env, opd)?;
                    ev.give(env, b, prec, oprd)?;
                } else {
                    return Err(NErr::type_error(format!("Chain cannot use nonblock in operand position: {:?}", oprr)))
                }
            }
            ev.finish(env)
        }
        Expr::And(lhs, rhs) => {
            let lr = evaluate(env, lhs)?;
            if lr.truthy() {
                evaluate(env, rhs)
            } else {
                Ok(lr)
            }
        }
        Expr::Or(lhs, rhs) => {
            let lr = evaluate(env, lhs)?;
            if lr.truthy() {
                Ok(lr)
            } else {
                evaluate(env, rhs)
            }
        }
        Expr::Assign(every, pat, rhs) => {
            let p = eval_lvalue(env, pat)?;
            let res = match &**rhs {
                Expr::CommaSeq(xs) => Ok(Obj::from(eval_seq(env, xs)?)),
                _ => evaluate(env, rhs),
            }?;
            if *every {
                assign_every(&mut env.borrow_mut(), &p, None, &res)?;
            } else {
                assign(&mut env.borrow_mut(), &p, None, &res)?;
            }
            Ok(Obj::Null)
        }
        Expr::Annotation(s, _) => evaluate(env, s),
        Expr::Pop(pat) => {
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => {
                    env.borrow_mut().modify_existing_var(&s, |(_type, vv)| {
                        modify_existing_index(vv, &ixs, |x| match x {
                            Obj::Seq(Seq::List(xs)) => {
                                Rc::make_mut(xs).pop().ok_or(NErr::name_error("can't pop empty".to_string()))
                            }
                            _ => Err(NErr::type_error("can't pop".to_string())),
                        })
                    }).ok_or(NErr::type_error("failed to pop??".to_string()))?
                }
                _ => Err(NErr::type_error("can't pop, weird pattern".to_string())),
            }
        }
        Expr::Remove(pat) => {
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => match ixs.as_slice() {
                    [] => Err(NErr::value_error("can't remove flat identifier".to_string())),
                    [rest @ .., last_i] => {
                        env.borrow_mut().modify_existing_var(&s, |(_type, vv)| {
                            modify_existing_index(vv, &rest, |x| match (x, last_i) {
                                (Obj::Seq(Seq::List(xs)), EvaluatedIndexOrSlice::Index(i)) => {
                                    let ii = pythonic_index(xs, i)?;
                                    Ok(Rc::make_mut(xs).remove(ii))
                                }
                                (Obj::Seq(Seq::List(xs)), EvaluatedIndexOrSlice::Slice(i, j)) => {
                                    let (lo, hi) = pythonic_slice(xs, i.as_ref(), j.as_ref())?;
                                    Ok(Obj::list(Rc::make_mut(xs).drain(lo..hi).collect()))
                                }
                                (Obj::Seq(Seq::Dict(xs, _)), EvaluatedIndexOrSlice::Index(i)) => {
                                    Rc::make_mut(xs).remove(&to_key(i.clone())?).ok_or(NErr::key_error("key not found in dict".to_string()))
                                }
                                // TODO: remove parts of strings...
                                // TODO: vecs, bytes...
                                _ => Err(NErr::type_error("can't remove".to_string())),
                            })
                        }).ok_or(NErr::name_error("var not found to remove".to_string()))?
                    }
                }
                _ => Err(NErr::type_error("can't pop, weird pattern".to_string())),
            }
        }
        Expr::Swap(a, b) => {
            let al = eval_lvalue(env, a)?;
            let bl = eval_lvalue(env, b)?;
            let ao = eval_lvalue_as_obj(env, a)?;
            let bo = eval_lvalue_as_obj(env, b)?;
            assign(&mut env.borrow_mut(), &al, None, &bo)?;
            assign(&mut env.borrow_mut(), &bl, None, &ao)?;
            Ok(Obj::Null)
        }
        Expr::OpAssign(every, pat, op, rhs) => {
            if *every {
                let p = eval_lvalue(env, pat)?;
                match evaluate(env, rhs)? {
                    Obj::Func(ff, _) => {
                        let res = match &**rhs {
                            Expr::CommaSeq(xs) => Ok(Obj::from(eval_seq(env, xs)?)),
                            _ => evaluate(env, rhs),
                        }?;
                        modify_every(env, &p, &mut |x| { ff.run(env, vec![x, res.clone()]) })?;
                        Ok(Obj::Null)
                    }
                    opv => Err(NErr::type_error(format!("Operator assignment: operator is not function {:?}", opv))),
                }
            } else {
                let pv = eval_lvalue_as_obj(env, pat)?;
                let p = eval_lvalue(env, pat)?;
                match evaluate(env, op)? {
                    Obj::Func(ff, _) => {
                        let res = match &**rhs {
                            Expr::CommaSeq(xs) => Ok(Obj::from(eval_seq(env, xs)?)),
                            _ => evaluate(env, rhs),
                        }?;
                        if !ff.can_refer() {
                            // Drop the Rc from the lvalue so that pure functions can try to consume it
                            assign(&mut env.borrow_mut(), &p, None, &Obj::Null)?;
                        }
                        let fres = ff.run(env, vec![pv, res])?;
                        assign(&mut env.borrow_mut(), &p, None, &fres)?;
                        Ok(Obj::Null)
                    }
                    opv => Err(NErr::type_error(format!("Operator assignment: operator is not function {:?}", opv))),
                }
            }
        }
        Expr::Call(f, args) => {
            let fr = evaluate(env, f)?;
            let a = eval_seq(env, args)?;
            call_or_part_apply(env, fr, a)
        }
        Expr::CommaSeq(_) => Err(NErr::syntax_error("Comma seqs only allowed directly on a side of an assignment (for now)".to_string())),
        Expr::Splat(_) => Err(NErr::syntax_error("Splats only allowed on an assignment-related place or in call or list (?)".to_string())),
        Expr::List(xs) => {
            Ok(Obj::from(eval_seq(env, xs)?))
        }
        Expr::Vector(xs) => {
            to_obj_vector(eval_seq(env, xs)?.into_iter().map(Ok))
        }
        Expr::Dict(def, xs) => {
            let dv = match def {
                Some(de) => Some(evaluate(env, de)?),
                None => None,
            };
            let mut acc = HashMap::new();
            for (ke, ve) in xs {
                match (&**ke, ve) {
                    (Expr::Splat(inner), None) => {
                        let mut res = evaluate(env, inner)?;
                        let it = mut_obj_into_iter_pairs(&mut res, "dictionary splat")?;
                        for (k, v) in it {
                            acc.insert(k, v);
                        }
                    }
                    (Expr::Splat(_), Some(_)) => {
                        Err(NErr::type_error(format!("Dictionary: Can only splat other dictionary without value; instead got {:?} {:?}", ke, ve)))?
                    }
                    _ => {
                        let k = evaluate(env, ke)?;
                        let kk = to_key(k)?;
                        let v = match ve {
                            Some(vve) => evaluate(env, vve)?,
                            None => Obj::Null,
                        };
                        acc.insert(kk, v);
                    }
                }
            }
            Ok(Obj::dict(acc, dv))
        }
        Expr::Sequence(xs) => {
            for x in &xs[..xs.len() - 1] {
                evaluate(env, x)?;
            }
            evaluate(env, xs.last().unwrap())
        }
        Expr::If(cond, if_body, else_body) => {
            let cr = evaluate(env, cond)?;
            if cr.truthy() {
                evaluate(env, if_body)
            } else {
                match else_body {
                    Some(b) => evaluate(env, b),
                    None => Ok(Obj::Null),
                }
            }
        }
        Expr::For(iteratees, do_yield, body) => {
            if *do_yield {
                let mut acc = Vec::new();
                let mut f = |e| acc.push(e);
                evaluate_for(env, iteratees.as_slice(), body, &mut f)?;
                Ok(Obj::from(acc))
            } else {
                evaluate_for(env, iteratees.as_slice(), body, &mut |_| ())?;
                Ok(Obj::Null)
            }
        }
        Expr::Lambda(params, body) => {
            Ok(Obj::Func(Func::Closure(Closure {
                params: Rc::clone(params),
                body: Rc::clone(body),
                env: Rc::clone(env),
            }), Precedence::zero()))
        }
        Expr::Backref(i) => env.borrow_mut().mut_top_env(|top| {
            match if *i == 0 { top.backrefs.last() } else { top.backrefs.get(i - 1) } {
                Some(x) => Ok(x.clone()),
                None => Err(NErr::index_error("no such backref".to_string())),
            }
        }),
        Expr::Paren(p) => evaluate(env, &*p),
    }
}

pub fn simple_eval(code: &str) -> Obj {
    let mut env = Env::new(TopEnv { backrefs: Vec::new(), input: Box::new(io::empty()), output: Box::new(io::sink()) });
    initialize(&mut env);

    let e = Rc::new(RefCell::new(env));
    evaluate(&e, &parse(code).unwrap().unwrap()).unwrap()
}

fn simple_join(mut obj: Obj, joiner: &str) -> NRes<String> {
    // this might coerce too hard but idk
    let mut acc = String::new();
    let mut started = false;
    for arg in mut_obj_into_iter(&mut obj, "join")? {
        if started {
            acc += joiner;
        }
        acc += format!("{}", arg).as_str();
        started = true;
    }
    Ok(acc)
}

pub fn initialize(env: &mut Env) {
    env.insert("null".to_string(), ObjType::Null, Obj::Null);

    env.insert_builtin(TwoNumsBuiltin {
        name: "+".to_string(),
        body: |a, b| { Ok(Obj::Num(a + b)) }
    });
    env.insert_builtin(BasicBuiltin {
        name: "-".to_string(),
        can_refer: false,
        body: |_env, args| match few2(args) {
            Few2::Zero => Err(NErr::argument_error("received 0 args".to_string())),
            Few2::One(s) => expect_nums_and_vectorize_1(|x| Ok(Obj::Num(-x)), s),
            Few2::Two(a, b) => expect_nums_and_vectorize_2(|a, b| Ok(Obj::Num(a-b)), a, b),
            Few2::Many(_) => Err(NErr::argument_error("received >2 args".to_string())),
        }
    });
    // for partial application
    env.insert_builtin(TwoNumsBuiltin {
        name: "subtract".to_string(),
        body: |a, b| { Ok(Obj::Num(a - b)) }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "*".to_string(),
        body: |a, b| { Ok(Obj::Num(a * b)) }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "sum".to_string(),
        can_refer: false,
        body: |mut arg| {
            let mut acc = NNum::from(0);
            for x in mut_obj_into_iter(&mut arg, "sum")? {
                match x {
                    Obj::Num(n) => { acc += &n }
                    _ => Err(NErr::argument_error("non-number".to_string()))?,
                }
            }
            Ok(Obj::Num(acc))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "product".to_string(),
        can_refer: false,
        body: |mut arg| {
            let mut acc = NNum::from(1);
            for x in mut_obj_into_iter(&mut arg, "product")? {
                match x {
                    Obj::Num(n) => { acc = acc * &n }
                    _ => Err(NErr::argument_error("non-number".to_string()))?,
                }
            }
            Ok(Obj::Num(acc))
        }
    });
    env.insert_builtin(ComparisonOperator::of("==", |ord| ord == Ordering::Equal));
    env.insert_builtin(ComparisonOperator::of("!=", |ord| ord != Ordering::Equal));
    env.insert_builtin(ComparisonOperator::of("<",  |ord| ord == Ordering::Less));
    env.insert_builtin(ComparisonOperator::of(">",  |ord| ord == Ordering::Greater));
    env.insert_builtin(ComparisonOperator::of("<=", |ord| ord != Ordering::Greater));
    env.insert_builtin(ComparisonOperator::of(">=", |ord| ord != Ordering::Less));
    env.insert_builtin(TwoNumsBuiltin {
        name: "/".to_string(),
        body: |a, b| { Ok(Obj::Num(a / b)) }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "%".to_string(),
        body: |a, b| { Ok(Obj::Num(a % b)) }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "//".to_string(),
        body: |a, b| { Ok(Obj::Num(a.div_floor(&b))) }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "%%".to_string(),
        body: |a, b| { Ok(Obj::Num(a.mod_floor(&b))) }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "^".to_string(),
        body: |a, b| { Ok(Obj::Num(a.pow_num(&b))) }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "&".to_string(),
        body: |a, b| { Ok(Obj::Num(a & b)) }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "|".to_string(),
        body: |a, b| { Ok(Obj::Num(a | b)) }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "@".to_string(),
        body: |a, b| { Ok(Obj::Num(a ^ b)) }
    });
    env.insert_builtin_with_precedence(TwoNumsBuiltin {
        name: "<<".to_string(),
        body: |a, b| { Ok(Obj::Num(a << b)) }
    }, Precedence(EXPONENT_PRECEDENCE, Assoc::Left));
    env.insert_builtin_with_precedence(TwoNumsBuiltin {
        name: ">>".to_string(),
        body: |a, b| { Ok(Obj::Num(a >> b)) }
    }, Precedence(EXPONENT_PRECEDENCE, Assoc::Left));
    env.insert_builtin(OneNumBuiltin {
        name: "abs".to_string(),
        body: |a| { Ok(Obj::Num(a.abs())) }
    });
    env.insert_builtin(OneNumBuiltin {
        name: "floor".to_string(),
        body: |a| { Ok(Obj::Num(a.floor())) }
    });
    env.insert_builtin(OneNumBuiltin {
        name: "ceil".to_string(),
        body: |a| { Ok(Obj::Num(a.ceil())) }
    });
    env.insert_builtin(OneNumBuiltin {
        name: "signum".to_string(),
        body: |a| { Ok(Obj::Num(a.signum())) }
    });
    env.insert_builtin(OneNumBuiltin {
        name: "even".to_string(),
        body: |a| { Ok(Obj::Num(NNum::iverson(!a.mod_floor(&NNum::from(2)).is_nonzero()))) }
    });
    env.insert_builtin(OneNumBuiltin {
        name: "odd".to_string(),
        body: |a| { Ok(Obj::Num(NNum::iverson(a.mod_floor(&NNum::from(2)) == NNum::from(1)))) }
    });
    env.insert_builtin(OneNumBuiltin {
        name: "real_part".to_string(),
        body: |a| match a.to_f64_or_inf_or_complex() {
            Ok(f) => Ok(Obj::from(f)),
            Err(c) => Ok(Obj::from(c.re)),
        }
    });
    env.insert_builtin(OneNumBuiltin {
        name: "imag_part".to_string(),
        body: |a| match a.to_f64_or_inf_or_complex() {
            Ok(_) => Ok(Obj::from(0.0)),
            Err(c) => Ok(Obj::from(c.im)),
        }
    });
    env.insert_builtin(OneNumBuiltin {
        name: "complex_parts".to_string(),
        body: |a| match a.to_f64_or_inf_or_complex() {
            Ok(f) => Ok(Obj::list(vec![Obj::from(f), Obj::from(0.0)])),
            Err(c) => Ok(Obj::list(vec![Obj::from(c.re), Obj::from(c.im)])),
        }
    });

    macro_rules! forward_f64 {
        ($name:ident) => {
            env.insert_builtin(OneNumBuiltin {
                name: stringify!($name).to_string(),
                body: |a| match a.to_f64_or_inf_or_complex() {
                    Ok(f) => Ok(Obj::from(f.$name())),
                    Err(c) => Ok(Obj::from(c.$name())),
                }
            });
        }
    }
    forward_f64!(sin);
    forward_f64!(sinh);
    forward_f64!(cos);
    forward_f64!(cosh);
    forward_f64!(tan);
    forward_f64!(tanh);
    forward_f64!(asin);
    forward_f64!(asinh);
    forward_f64!(acos);
    forward_f64!(acosh);
    forward_f64!(atan);
    forward_f64!(atanh);
    // TODO: atan2
    forward_f64!(sqrt);
    forward_f64!(cbrt);
    forward_f64!(exp);
    forward_f64!(ln);
    forward_f64!(log10);
    forward_f64!(log2);
    // forward_f64!(fract);
    // forward_f64!(exp_m1);
    // forward_f64!(ln_1p);

    env.insert_builtin(OneNumBuiltin {
        name: "factorize".to_string(),
        body: |a| { Ok(Obj::list(
                                nnum::lazy_factorize(into_bigint_ok(a)?).into_iter().map(
                                    |(a, e)| Obj::list(vec![Obj::from(a), Obj::from(e)]))
                                .collect())) }
    });
    env.insert_builtin(TilBuiltin {});
    env.insert_builtin(ToBuiltin {});
    env.insert_builtin(OneArgBuiltin {
        name: "ord".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => {
                if s.len() != 1 {
                    Err(NErr::value_error("arg string length != 1".to_string()))
                } else {
                    Ok(Obj::from(s.chars().next().unwrap() as usize))
                }
            }
            _ => Err(NErr::type_error("arg non-string".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "chr".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::Num(n) => Ok(Obj::from(nnum::char_from_bigint(&into_bigint_ok(n)?).ok_or(NErr::value_error("chr of int oob".to_string()))?.to_string())),
            _ => Err(NErr::type_error("not number".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "len".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::Seq(s) => Ok(Obj::Num(NNum::from(s.len()))),
            _ => Err(NErr::type_error("sequence only".to_string()))
        }
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "then".to_string(),
        can_refer: true,
        body: |env, a, b| call(env, b, vec![a]),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "apply".to_string(),
        can_refer: true,
        body: |env, mut a, b| call(env, b, mut_obj_into_iter(&mut a, "apply")?.collect()),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "of".to_string(),
        can_refer: true,
        body: |env, a, mut b| call(env, a, mut_obj_into_iter(&mut b, "of")?.collect()),
    });
    env.insert_builtin(Preposition("by".to_string()));
    env.insert_builtin(Preposition("with".to_string()));
    env.insert_builtin(Preposition("from".to_string()));
    env.insert_builtin(Preposition("default".to_string()));
    env.insert_builtin(TwoArgBuiltin {
        name: "in".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::from(obj_in(a, b)?)),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "not_in".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::from(!obj_in(a, b)?)),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "contains".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::from(obj_in(b, a)?)),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: ".".to_string(),
        can_refer: true,
        body: |env, a, b| call(env, b, vec![a]),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: ".>".to_string(),
        can_refer: true,
        body: |env, a, b| call(env, b, vec![a]),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "<.".to_string(),
        can_refer: true,
        body: |env, a, b| call(env, a, vec![b]),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ">>>".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::Func(f, _), Obj::Func(g, _)) => Ok(Obj::Func(Func::Composition(Box::new(g), Box::new(f)), Precedence::zero())),
            _ => Err(NErr::type_error("not function".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "<<<".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::Func(f, _), Obj::Func(g, _)) => Ok(Obj::Func(Func::Composition(Box::new(f), Box::new(g)), Precedence::zero())),
            _ => Err(NErr::type_error("not function".to_string()))
        }
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "each".to_string(),
        can_refer: true,
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "each")?;
            match b {
                Obj::Func(b, _) => {
                    for e in it {
                        b.run(env, vec![e])?;
                    }
                    Ok(Obj::Null)
                }
                _ => Err(NErr::type_error("not callable".to_string()))
            }
        }
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "map".to_string(),
        can_refer: true,
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "map")?;
            match b {
                Obj::Func(b, _) => Ok(Obj::from(
                    it.map(|e| b.run(env, vec![e])).collect::<NRes<Vec<Obj>>>()?
                )),
                _ => Err(NErr::type_error("not callable".to_string()))
            }
        }
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "map_keys".to_string(),
        can_refer: true,
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut d, def)), Obj::Func(b, _)) => {
                Ok(Obj::dict(
                    Rc::make_mut(&mut d).drain().map(|(k, v)| Ok((to_key(b.run(env, vec![key_to_obj(k)])?)?, v))).collect::<NRes<HashMap<ObjKey, Obj>>>()?, def.map(|x| *x)))
            }
            _ => Err(NErr::type_error("not dict or callable".to_string()))
        }
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "map_values".to_string(),
        can_refer: true,
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut d, def)), Obj::Func(b, _)) => {
                Ok(Obj::dict(
                    Rc::make_mut(&mut d).drain().map(|(k, v)| Ok((k, b.run(env, vec![v])?))).collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                    match def {
                        Some(def) => Some(b.run(env, vec![*def])?),
                        None => None
                    }
                ))
            }
            _ => Err(NErr::type_error("not dict or callable".to_string()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "flatten".to_string(),
        can_refer: false,
        body: |mut a| {
            let mut acc = Vec::new();
            for mut e in mut_obj_into_iter(&mut a, "flatten (outer)")? {
                for k in mut_obj_into_iter(&mut e, "flatten (inner)")? {
                    acc.push(k);
                }
            }
            Ok(Obj::from(acc))
        }
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "flat_map".to_string(),
        can_refer: true,
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "flat_map (outer)")?;
            match b {
                Obj::Func(b, _) => {
                    let mut acc = Vec::new();
                    for e in it {
                        let mut r = b.run(env, vec![e])?;
                        for k in mut_obj_into_iter(&mut r, "flat_map (inner)")? {
                            acc.push(k);
                        }
                    }
                    Ok(Obj::from(acc))
                }
                _ => Err(NErr::type_error("not callable".to_string()))
            }
        }
    });
    env.insert_builtin(Zip {});
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "filter".to_string(),
        can_refer: true,
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "filter")?;
            match b {
                Obj::Func(b, _) => {
                    let mut acc = Vec::new();
                    for e in it {
                        if b.run(env, vec![e.clone()])?.truthy() {
                            acc.push(e)
                        }
                    }
                    Ok(Obj::from(acc))
                }
                _ => Err(NErr::type_error("list and func only".to_string()))
            }
        }
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "reject".to_string(),
        can_refer: true,
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "reject")?;
            match b {
                Obj::Func(b, _) => {
                    let mut acc = Vec::new();
                    for e in it {
                        if !b.run(env, vec![e.clone()])?.truthy() {
                            acc.push(e)
                        }
                    }
                    Ok(Obj::from(acc))
                }
                _ => Err(NErr::type_error("seq and func only".to_string()))
            }
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "any".to_string(),
        can_refer: true,
        body: |env, args| match few2(args) {
            Few2::Zero => Err(NErr::argument_error("zero args".to_string())),
            Few2::One(mut a) => Ok(Obj::from(mut_obj_into_iter(&mut a, "any")?.any(|x| x.truthy()))),
            Few2::Two(mut a, Obj::Func(b, _)) => {
                for e in mut_obj_into_iter(&mut a, "any")? {
                    if b.run(env, vec![e.clone()])?.truthy() {
                        return Ok(Obj::from(true))
                    }
                }
                Ok(Obj::from(false))
            }
            _ => Err(NErr::argument_error("too many args".to_string())),
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "all".to_string(),
        can_refer: true,
        body: |env, args| match few2(args) {
            Few2::Zero => Err(NErr::argument_error("zero args".to_string())),
            Few2::One(mut a) => Ok(Obj::from(mut_obj_into_iter(&mut a, "all")?.all(|x| x.truthy()))),
            Few2::Two(mut a, Obj::Func(b, _)) => {
                for e in mut_obj_into_iter(&mut a, "all")? {
                    if !b.run(env, vec![e.clone()])?.truthy() {
                        return Ok(Obj::from(false))
                    }
                }
                Ok(Obj::from(true))
            }
            Few2::Two(_, b) => Err(NErr::type_error(format!("second arg not func: {}", b))),
            ff => Err(NErr::argument_error(format!("too many args: {:?}", ff))),
        }
    });
    env.insert_builtin(Fold {});
    env.insert_builtin(TwoArgBuiltin {
        name: "append".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::List(mut a)), b) => {
                Rc::make_mut(&mut a).push(b.clone());
                Ok(Obj::Seq(Seq::List(a)))
            }
            _ => Err(NErr::argument_error("2 args only".to_string()))
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "max".to_string(),
        can_refer: false,
        body: |_env, args| match few(args) {
            Few::Zero => Err(NErr::argument_error("max: at least 1 arg".to_string())),
            Few::One(mut s) => {
                let mut ret: Option<Obj> = None;
                for b in mut_obj_into_iter(&mut s, "max")? {
                    if match &ret {
                        None => true,
                        Some(r) => ncmp(&b, r)? == Ordering::Greater,
                    } { ret = Some(b) }
                }
                Ok(ret.ok_or(NErr::empty_error("empty".to_string()))?.clone())
            }
            Few::Many(t) => {
                let mut ret: Option<Obj> = None;
                for b in t {
                    if match &ret {
                        None => true,
                        Some(r) => ncmp(&b, r)? == Ordering::Greater,
                    } { ret = Some(b) }
                }
                Ok(ret.ok_or(NErr::empty_error("empty".to_string()))?.clone())
            }
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "min".to_string(),
        can_refer: false,
        body: |_env, args| match few(args) {
            Few::Zero => Err(NErr::type_error("min: at least 1 arg".to_string())),
            Few::One(mut s) => {
                let mut ret: Option<Obj> = None;
                for b in mut_obj_into_iter(&mut s, "min")? {
                    if match &ret {
                        None => true,
                        Some(r) => ncmp(&b, r)? == Ordering::Less,
                    } { ret = Some(b) }
                }
                Ok(ret.ok_or(NErr::empty_error("min: empty".to_string()))?.clone())
            }
            Few::Many(t) => {
                let mut ret: Option<Obj> = None;
                for b in t {
                    if match &ret {
                        None => true,
                        Some(r) => ncmp(&b, r)? == Ordering::Less,
                    } { ret = Some(b) }
                }
                Ok(ret.ok_or(NErr::empty_error("min: empty".to_string()))?.clone())
            }
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "print".to_string(),
        can_refer: false,
        body: |env, args| {
            env.borrow_mut().mut_top_env(|t| {
                let mut started = false;
                for arg in args.iter() {
                    if started { write!(t.output, " ")?; }
                    started = true;
                    write!(t.output, "{}", arg)?;
                }
                writeln!(t.output, "")
            }).unwrap(); // TODO: propagate error
            Ok(Obj::Null)
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "echo".to_string(),
        can_refer: false,
        body: |env, args| {
            env.borrow_mut().mut_top_env(|t| {
                let mut started = false;
                for arg in args.iter() {
                    if started { write!(t.output, " ")?; }
                    started = true;
                    write!(t.output, "{}", arg)?;
                }
                writeln!(t.output, "")
            }).unwrap(); // TODO: propagate error
            Ok(Obj::Null)
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "debug".to_string(),
        can_refer: false,
        body: |env, args| {
            env.borrow_mut().mut_top_env(|t| {
                let mut started = false;
                for arg in args.iter() {
                    if started { write!(t.output, " ")?; }
                    started = true;
                    write!(t.output, "{:?}", arg)?;
                }
                writeln!(t.output, "")
            }).unwrap(); // TODO: propagate error
            Ok(Obj::Null)
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "is".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::from(is_type(&to_type(&b, "builtin 'is'")?, &a))),
    });
    env.insert_type(ObjType::Null);
    env.insert_type(ObjType::Int);
    env.insert_type(ObjType::Float);
    env.insert_type(ObjType::Complex);
    env.insert_type(ObjType::Number);
    env.insert_type(ObjType::String);
    env.insert_type(ObjType::List);
    env.insert_type(ObjType::Dict);
    env.insert_type(ObjType::Vector);
    env.insert_type(ObjType::Bytes);
    env.insert_type(ObjType::Func);
    env.insert_type(ObjType::Type);
    env.insert_builtin(BasicBuiltin {
        name: "$".to_string(),
        can_refer: false,
        body: |_env, args| {
            let mut acc = String::new();
            for arg in args {
                acc += format!("{}", arg).as_str();
            }
            Ok(Obj::from(acc))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "*$".to_string(),
        can_refer: false,
        body: |a, b| {
            Ok(Obj::from(format!("{}", b).repeat(obj_clamp_to_usize_ok(&a)?)))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "$*".to_string(),
        can_refer: false,
        body: |a, b| {
            Ok(Obj::from(format!("{}", a).repeat(obj_clamp_to_usize_ok(&b)?)))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "upper".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.to_uppercase())),
            _ => Err(NErr::type_error("expected string".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "lower".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.to_lowercase())),
            _ => Err(NErr::type_error("expected string".to_string())),
        }
    });
    // unlike python these are true on empty string. hmm...
    env.insert_builtin(OneArgBuiltin {
        name: "is_upper".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.chars().all(char::is_uppercase))),
            _ => Err(NErr::type_error("expected string".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "is_lower".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.chars().all(char::is_lowercase))),
            _ => Err(NErr::type_error("expected string".to_string())),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "join".to_string(),
        can_refer: false,
        body: |a, b| {
            Ok(Obj::from(simple_join(a, format!("{}", b).as_str())?))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "split".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => Ok(Obj::list(s.split(&*t).map(|w| Obj::from(w.to_string())).collect())),
            _ => Err(NErr::argument_error(":(".to_string())),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "starts_with".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => Ok(Obj::from(s.starts_with(&*t))),
            _ => Err(NErr::argument_error(":(".to_string())),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "ends_with".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => Ok(Obj::from(s.ends_with(&*t))),
            _ => Err(NErr::argument_error(":(".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "strip".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.trim())),
            _ => Err(NErr::argument_error(":(".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "trim".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.trim())),
            _ => Err(NErr::argument_error(":(".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "words".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::list(s.split_whitespace().map(|w| Obj::from(w)).collect())),
            _ => Err(NErr::argument_error(":(".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "lines".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::list(s.split_terminator('\n').map(|w| Obj::from(w.to_string())).collect())),
            _ => Err(NErr::argument_error(":(".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "unwords".to_string(),
        can_refer: false,
        body: |a| Ok(Obj::from(simple_join(a, " ")?)),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "unlines".to_string(),
        can_refer: false,
        body: |a| {
            let mut s = simple_join(a, "\n")?;
            s.push('\n');
            Ok(Obj::from(s))
        }
    });

    env.insert_builtin(TwoArgBuiltin {
        name: "search".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                let r = Regex::new(&b).map_err(|e| NErr::value_error(format!("invalid regex: {}", e)))?;
                if r.capture_locations().len() == 1 {
                    match r.find(&a) {
                        None => Ok(Obj::Null),
                        Some(c) => Ok(Obj::from(c.as_str())),
                    }
                } else {
                    match r.captures(&a) {
                        None => Ok(Obj::Null),
                        Some(c) => Ok(Obj::list(c.iter().map(|cap| match cap {
                            None => Obj::Null, // didn't participate
                            Some(s) => Obj::from(s.as_str()),
                        }).collect())),
                    }
                }
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "search_all".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                let r = Regex::new(&b).map_err(|e| NErr::value_error(format!("invalid regex: {}", e)))?;
                if r.capture_locations().len() == 1 {
                    Ok(Obj::list(r.find_iter(&a).map(|c| Obj::from(c.as_str())).collect()))
                } else {
                    Ok(Obj::list(r.captures_iter(&a).map(|c|
                        Obj::list(c.iter().map(|cap| match cap {
                            None => Obj::Null, // didn't participate
                            Some(s) => Obj::from(s.as_str()),
                        }).collect())
                    ).collect()))
                }
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });

    // Haskell-ism for partial application (when that works)
    env.insert_builtin(TwoArgBuiltin {
        name: "!!".to_string(),
        can_refer: false,
        body: index,
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "!?".to_string(),
        can_refer: false,
        body: safe_index,
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "!%".to_string(),
        can_refer: false,
        body: obj_cyclic_index,
    });

    // Lists
    env.insert_builtin(TwoArgBuiltin {
        name: "++".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::List(mut a)), Obj::Seq(Seq::List(mut b))) => {
                Rc::make_mut(&mut a).append(Rc::make_mut(&mut b));
                Ok(Obj::Seq(Seq::List(a)))
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ".+".to_string(),
        can_refer: false,
        body: |a, b| match b {
            Obj::Seq(Seq::List(mut b)) => {
                Rc::make_mut(&mut b).insert(0, a);
                Ok(Obj::Seq(Seq::List(b)))
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "+.".to_string(),
        can_refer: false,
        body: |a, b| match a {
            Obj::Seq(Seq::List(mut a)) => {
                Rc::make_mut(&mut a).push(b);
                Ok(Obj::Seq(Seq::List(a)))
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "..".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::from(vec![a, b]))
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "=>".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::from(vec![a, b]))
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "*.".to_string(),
        can_refer: false,
        body: |a, b| {
            Ok(Obj::list(vec![b; obj_clamp_to_usize_ok(&a)?]))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ".*".to_string(),
        can_refer: false,
        body: |a, b| {
            Ok(Obj::list(vec![a; obj_clamp_to_usize_ok(&b)?]))
        }
    });
    env.insert_builtin(CartesianProduct {});
    env.insert_builtin(OneArgBuiltin {
        name: "id".to_string(),
        can_refer: false,
        body: |a| Ok(a),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "const".to_string(),
        can_refer: false,
        body: |_, b| Ok(b),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "flip".to_string(),
        can_refer: true,
        body: |a| match a {
            Obj::Func(f, _) => Ok(Obj::Func(Func::Flip(Box::new(f)), Precedence::zero())),
            _ => Err(NErr::type_error("not function".to_string()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "first".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(s) => linear_index_isize(s, 0),
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "second".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(s) => linear_index_isize(s, 1),
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "third".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(s) => linear_index_isize(s, 2),
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "last".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(s) => linear_index_isize(s, -1),
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "sort".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(s) => Ok(Obj::Seq(to_mutated_list(s, |v| {
                // ????
                v.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
                Ok(())
            })?)),
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "reverse".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(s) => Ok(Obj::Seq(s.reversed()?)),
            _ => Err(NErr::generic_argument_error()),
        }
    });

    // Dicts
    env.insert_builtin(TwoArgBuiltin {
        name: "||".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::Dict(mut b, _))) => {
                Rc::make_mut(&mut a).extend(Rc::make_mut(&mut b).drain());
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "|.".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), b) => {
                Rc::make_mut(&mut a).insert(to_key(b)?, Obj::Null);
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "discard".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), b) => {
                Rc::make_mut(&mut a).remove(&to_key(b)?);
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "-.".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), b) => {
                Rc::make_mut(&mut a).remove(&to_key(b)?);
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            _ => Err(NErr::generic_argument_error()),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "insert".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::List(b))) => match b.as_slice() {
                [k, v] => {
                    // TODO could take b theoretically, but, pain
                    // TODO maybe fail if key exists? have |.. = "upsert"?
                    Rc::make_mut(&mut a).insert(to_key(k.clone())?, v.clone());
                    Ok(Obj::Seq(Seq::Dict(a, d)))
                }
                _ => Err(NErr::argument_error("RHS must be pair".to_string()))
            }
            _ => Err(NErr::generic_argument_error())
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "|..".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::List(b))) => match b.as_slice() {
                [k, v] => {
                    // TODO could take b theoretically, but, pain
                    Rc::make_mut(&mut a).insert(to_key(k.clone())?, v.clone());
                    Ok(Obj::Seq(Seq::Dict(a, d)))
                }
                _ => Err(NErr::argument_error("RHS must be pair".to_string()))
            }
            _ => Err(NErr::generic_argument_error())
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "&&".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::Dict(b, _))) => {
                Rc::make_mut(&mut a).retain(|k, _| b.contains_key(k));
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            _ => Err(NErr::generic_argument_error())
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "set".to_string(),
        can_refer: false,
        body: |mut a| {
            Ok(Obj::dict(mut_obj_into_iter(&mut a, "set conversion")?.map(|k| Ok((to_key(k)?, Obj::Null))).collect::<NRes<HashMap<ObjKey,Obj>>>()?, None))
        }
    });
    // TODO
    env.insert_builtin(OneArgBuiltin {
        name: "items".to_string(),
        can_refer: false,
        body: |mut a| {
            Ok(Obj::list(mut_obj_into_iter_pairs(&mut a, "items conversion")?.map(|(k, v)| Obj::from(vec![key_to_obj(k), v])).collect()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "enumerate".to_string(),
        can_refer: false,
        body: |mut a| {
            Ok(Obj::list(mut_obj_into_iter_pairs(&mut a, "enumerate conversion")?.map(|(k, v)| Obj::from(vec![key_to_obj(k), v])).collect()))
        }
    });

    env.insert_builtin(BasicBuiltin {
        name: "eval".to_string(),
        can_refer: false,
        body: |env, a| match few(a) {
            Few::One(Obj::Seq(Seq::String(r))) => match parse(&r) {
                Ok(Some(code)) => evaluate(env, &code),
                Ok(None) => Err(NErr::value_error("eval: empty expression".to_string())),
                Err(s) => Err(NErr::value_error(s)),
            }
            Few::One(s) => Err(NErr::value_error(format!("can't eval {:?}", s))),
            _ => Err(NErr::generic_argument_error()),
        }
    });

    // TODO safety, wasm version
    env.insert_builtin(BasicBuiltin {
        name: "input".to_string(),
        can_refer: false,
        body: |env, args| if args.is_empty() {
            let mut input = String::new();
            match env.borrow_mut().mut_top_env(|t| t.input.read_line(&mut input)) {
                Ok(_) => Ok(Obj::from(input)),
                Err(msg) => Err(NErr::value_error(format!("input failed: {}", msg))),
            }
        } else {
            Err(NErr::generic_argument_error())
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "read".to_string(),
        can_refer: false,
        body: |env, args| if args.is_empty() {
            let mut input = String::new();
            // to EOF
            match env.borrow_mut().mut_top_env(|t| t.input.read_to_string(&mut input)) {
                Ok(_) => Ok(Obj::from(input)),
                Err(msg) => Err(NErr::value_error(format!("input failed: {}", msg))),
            }
        } else {
            Err(NErr::generic_argument_error())
        }
    });

    // TODO safety, wasm version
    env.insert_builtin(OneArgBuiltin {
        name: "read_file".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => match fs::read_to_string(&*s) {
                Ok(c) => Ok(Obj::from(c)),
                Err(e) => Err(NErr::io_error(format!("{}", e))),
            }
            _ => Err(NErr::generic_argument_error())
        }
    });

    // this isn't a very good assert
    env.insert_builtin(OneArgBuiltin {
        name: "assert".to_string(),
        can_refer: false,
        body: |a| if a.truthy() {
            Ok(Obj::Null)
        } else {
            Err(NErr::assert_error(format!("{}", a)))
        }
    });

    // l m a o
    env.insert_builtin(BasicBuiltin {
        name: "import".to_string(),
        can_refer: false,
        body: |env, args| {
            let mut ret = Obj::Null;
            for arg in args {
                ret = match arg {
                    Obj::Seq(Seq::String(f)) => match fs::read_to_string(&*f) {
                        Ok(c) => match parse(&c) {
                            Ok(Some(code)) => evaluate(env, &code),
                            Ok(None) => Err(NErr::value_error("empty file".to_string())),
                            Err(s) => Err(NErr::value_error(format!("lex failed: {}", s))),
                        }
                        Err(e) => Err(NErr::io_error(format!("failed: {}", e))),
                    }
                    a => Err(NErr::type_error(format!("can't import: {}", a))),
                }?
            }
            Ok(ret)
        }
    });
}

// copypasta
#[cfg_attr(target_arch="wasm32", wasm_bindgen)]
pub struct WasmOutputs {
    output: String,
    error: String,
}

#[cfg_attr(target_arch="wasm32", wasm_bindgen)]
impl WasmOutputs {
    pub fn get_output(&self) -> String { self.output.to_string() }
    pub fn get_error(&self) -> String { self.error.to_string() }
}

// stdout and error
#[cfg_attr(target_arch="wasm32", wasm_bindgen)]
pub fn encapsulated_eval(code: &str, input: &str) -> WasmOutputs {
    let mut env = Env::new(TopEnv { backrefs: Vec::new(), input: Box::new(io::Cursor::new(input.as_bytes().to_vec())), output: Box::new(Vec::new()) });
    initialize(&mut env);

    let e = Rc::new(RefCell::new(env));

    match parse(code) {
        Err(p) => WasmOutputs {
            output: String::new(),
            error: p,
        },
        Ok(None) => WasmOutputs {
            output: String::new(),
            error: String::new(),
        },
        Ok(Some(code)) => match evaluate(&e, &code) {
            Err(err) => WasmOutputs {
                output: e.borrow_mut().mut_top_env(|e|
                   String::from_utf8_lossy(e.output.extract().unwrap()).into_owned()),
                error: err.0,
            },
            Ok(res) => WasmOutputs {
                output: e.borrow_mut().mut_top_env(|e|
                   String::from_utf8_lossy(e.output.extract().unwrap()).into_owned())
                + &format!("{}", res),
                error: String::new(),
            },
        },
    }
}
