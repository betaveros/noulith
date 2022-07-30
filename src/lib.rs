#[macro_use] extern crate lazy_static;

// TODO: isolate
use std::fs;
use std::io;

use std::cmp::Ordering;
use std::fmt;
use std::fmt::Display;
use std::fmt::Debug;
use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use std::cell::RefCell;

use num::complex::Complex64;
use num::bigint::BigInt;
use num::ToPrimitive;

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
    // Float(f64),
    String(Rc<String>),
    List(Rc<Vec<Obj>>),
    Dict(Rc<HashMap<ObjKey, Obj>>, Option<Box<Obj>>), // default value
    Func(Func, Precedence),
}

// more like an arbitrary predicate. want to add subscripted types to this later
#[derive(Debug, Clone)]
pub enum ObjType { Null, Int, Float, Complex, Number, String, List, Dict, Func, Type, Any }

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
        Obj::List(_) => ObjType::List,
        Obj::String(_) => ObjType::String,
        Obj::Dict(..) => ObjType::Dict,
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
        (ObjType::List, Obj::List(_)) => true,
        (ObjType::String, Obj::String(_)) => true,
        (ObjType::Dict, Obj::Dict(..)) => true,
        (ObjType::Func, Obj::Func(..)) => true,
        (ObjType::Type, Obj::Func(Func::Type(_), _)) => true,
        (ObjType::Any, _) => true,
        _ => false,
    }
}

fn call_type(ty: &ObjType, arg: Obj) -> NRes<Obj> {
    match ty {
        ObjType::Int => match arg {
            Obj::Num(n) => Ok(Obj::Num(n.trunc())),
            Obj::String(s) => match s.parse::<BigInt>() {
                Ok(x) => Ok(Obj::from(x)),
                Err(s) => Err(NErr::ValueError(format!("int: can't parse: {}", s))),
            },
            _ => Err(NErr::TypeError("int: expected number or string".to_string())),
        }
        ObjType::Float => match arg {
            Obj::Num(n) => Ok(Obj::Num(n.trunc())),
            Obj::String(s) => match s.parse::<f64>() {
                Ok(x) => Ok(Obj::from(x)),
                Err(s) => Err(NErr::ValueError(format!("float: can't parse: {}", s))),
            },
            _ => Err(NErr::TypeError("float: expected number or string".to_string())),
        }
        ObjType::List => match arg {
            Obj::List(xs) => Ok(Obj::List(xs)),
            mut arg => Ok(Obj::List(Rc::new(mut_obj_into_iter(&mut arg, "list conversion")?.collect()))),
        }
        ObjType::Dict => match arg {
            Obj::Dict(x, d) => Ok(Obj::Dict(x, d)),
            // nonsensical but maybe this is something some day
            /*
            mut arg => Ok(Obj::Dict(
                    Rc::new(mut_obj_into_iter_pairs(&mut arg, "dict conversion")?.collect::<HashMap<ObjKey, Obj>>()), None)),
                    */
            mut arg => Ok(Obj::Dict(
                    Rc::new(
                        mut_obj_into_iter(&mut arg, "dict conversion")?
                        .map(|p| match p {
                            // TODO not taking but blech
                            Obj::List(xs) => match xs.as_slice() {
                                [k, v] => Ok((to_key(k.clone())?, v.clone())),
                                _ => Err(NErr::TypeError("dict conversion: not pair".to_string())),
                            }
                            _ => Err(NErr::TypeError("dict conversion: not list".to_string())),
                        }).collect::<NRes<HashMap<ObjKey, Obj>>>()?
                    ), None)),
        }
        ObjType::Type => Ok(Obj::Func(Func::Type(type_of(&arg)), Precedence::zero())),
        // TODO: complex, number, list, dict
        _ => Err(NErr::TypeError("that type can't be called (maybe not implemented)".to_string())),
    }
}

// TODO can we take?
fn to_type(arg: &Obj, msg: &str) -> NRes<ObjType> {
    match arg {
        Obj::Null => Ok(ObjType::Null),
        Obj::Func(Func::Type(t), _) => Ok(t.clone()),
        // TODO: possibly intelligently convert some objects to types?
        // e.g. "heterogenous tuples"
        a => Err(NErr::TypeError(format!("can't convert {} to type for {}", a, msg))),
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum ObjKey {
    Null,
    Num(NTotalNum),
    String(Rc<String>),
    List(Rc<Vec<ObjKey>>),
    Dict(Rc<Vec<(ObjKey, ObjKey)>>),
}

impl Obj {
    fn truthy(&self) -> bool {
        match self {
            Obj::Null => false,
            Obj::Num(x) => x.is_nonzero(),
            Obj::String(x) => !x.is_empty(),
            Obj::List(x) => !x.is_empty(),
            Obj::Dict(x, _) => !x.is_empty(),
            Obj::Func(..) => true,
        }
    }
}

impl From<bool> for Obj {
    fn from(n: bool) -> Self { Obj::Num(NNum::iverson(n)) }
}
impl From<char> for Obj {
    fn from(n: char) -> Self { Obj::String(Rc::new(n.to_string())) }
}
impl From<&str> for Obj {
    fn from(n: &str) -> Self { Obj::String(Rc::new(n.to_string())) }
}
impl From<String> for Obj {
    fn from(n: String) -> Self { Obj::String(Rc::new(n)) }
}

macro_rules! forward_from {
    ($ty:ident) => {
        impl From<$ty> for Obj {
            fn from(n: $ty) -> Self { Obj::Num(NNum::from(n)) }
        }
    }
}
forward_from!(BigInt);
forward_from!(i32);
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
            (Obj::String(a), Obj::String(b)) => a == b,
            (Obj::List  (a), Obj::List  (b)) => a == b,
            (Obj::Dict(a,_), Obj::Dict(b,_)) => a == b,
            _ => false,
        }
    }
}

impl PartialOrd for Obj {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Obj::Null     , Obj::Null     ) => Some(Ordering::Equal),
            (Obj::Num   (a), Obj::Num   (b)) => a.partial_cmp(b),
            (Obj::String(a), Obj::String(b)) => Some(a.cmp(b)),
            (Obj::List  (a), Obj::List  (b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

fn to_bigint_ok(n: &NNum) -> NRes<BigInt> {
    Ok(n.to_bigint().ok_or(NErr::ValueError("bad number to int".to_string()))?.clone())
}
fn into_bigint_ok(n: NNum) -> NRes<BigInt> {
    n.into_bigint().ok_or(NErr::ValueError("bad number to int".to_string()))
}

fn to_key(obj: Obj) -> NRes<ObjKey> {
    match obj {
        Obj::Null => Ok(ObjKey::Null),
        Obj::Num(x) => Ok(ObjKey::Num(NTotalNum(x))),
        Obj::String(x) => Ok(ObjKey::String(x)),
        Obj::List(mut xs) => Ok(ObjKey::List(Rc::new(
                    mut_rc_vec_into_iter(&mut xs).map(|e| to_key(e)).collect::<NRes<Vec<ObjKey>>>()?))),
        Obj::Dict(mut d, _) => {
            let mut pairs = mut_rc_hash_map_into_iter(&mut d).map(
                |(k,v)| Ok((k,to_key(v)?))).collect::<NRes<Vec<(ObjKey,ObjKey)>>>()?;
            pairs.sort();
            Ok(ObjKey::Dict(Rc::new(pairs)))
        }
        Obj::Func(..) => Err(NErr::TypeError("Using a function as a dictionary key isn't supported".to_string())),
    }
}

fn key_to_obj(key: ObjKey) -> Obj {
    match key {
        ObjKey::Null => Obj::Null,
        ObjKey::Num(NTotalNum(x)) => Obj::Num(x),
        ObjKey::String(x) => Obj::String(x),
        ObjKey::List(mut xs) => Obj::List(Rc::new(
                mut_rc_vec_into_iter(&mut xs).map(
                    |e| key_to_obj(e.clone())).collect::<Vec<Obj>>())),
        ObjKey::Dict(mut d) => Obj::Dict(Rc::new(
                mut_rc_vec_into_iter(&mut d).map(
                    |(k, v)| (k, key_to_obj(v))).collect::<HashMap<ObjKey,Obj>>()), None),
    }
}

impl Display for Obj {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Obj::Null => write!(formatter, "null"),
            Obj::Num(n) => write!(formatter, "{}", n),
            Obj::String(s) => write!(formatter, "{}", s),
            Obj::List(xs) => {
                write!(formatter, "[")?;
                let mut started = false;
                for x in xs.iter() {
                    if started { write!(formatter, ", ")?; }
                    started = true;
                    write!(formatter, "{}", x)?;
                }
                write!(formatter, "]")
            }
            Obj::Dict(xs, def) => {
                write!(formatter, "{{")?;
                let mut started = false;
                match def {
                    Some(v) => {
                        started = true;
                        write!(formatter, "(default: {})", v)?;
                    }
                    None => {}
                }
                for (k, v) in xs.iter() {
                    if started { write!(formatter, ", ")?; }
                    started = true;
                    write!(formatter, "{}", k)?;
                    match v {
                        Obj::Null => {}
                        v => write!(formatter, ": {}", v)?
                    }
                }
                write!(formatter, "}}")
            }
            Obj::Func(f, p) => write!(formatter, "<{} p:{}>", f, p.0),
        }
    }
}

impl Display for ObjKey {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ObjKey::Null => write!(formatter, "null"),
            ObjKey::Num(n) => write!(formatter, "{}", n),
            ObjKey::String(s) => write!(formatter, "{}", s),
            ObjKey::List(xs) => {
                write!(formatter, "[")?;
                let mut started = false;
                for x in xs.iter() {
                    if started { write!(formatter, ", ")?; }
                    started = true;
                    write!(formatter, "{}", x)?;
                }
                write!(formatter, "]")
            }
            ObjKey::Dict(xs) => {
                write!(formatter, "{{")?;
                let mut started = false;
                for (k, v) in xs.iter() {
                    if started { write!(formatter, ", ")?; }
                    started = true;
                    write!(formatter, "{}: {}", k, v)?;
                }
                write!(formatter, "}}")
            }
        }
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
}

fn obj_to_cloning_iter(obj: &Obj) -> NRes<ObjToCloningIter<'_>> {
    match obj {
        Obj::List(v) => Ok(ObjToCloningIter::List(v.iter())),
        Obj::Dict(v, _) => Ok(ObjToCloningIter::Dict(v.iter())),
        Obj::String(s) => Ok(ObjToCloningIter::String(s.chars())),
        _ => Err(NErr::TypeError("cannot convert to cloning iter".to_string())),
    }
}

impl Iterator for ObjToCloningIter<'_> {
    type Item = Obj;

    fn next(&mut self) -> Option<Obj> {
        match self {
            ObjToCloningIter::List(it) => it.next().cloned(),
            ObjToCloningIter::Dict(it) => Some(key_to_obj(it.next()?.0.clone())),
            ObjToCloningIter::String(it) => Some(Obj::from(it.next()?)),
        }
    }
}

// iterates over elements of lists, or just keys of dictionaries (as if they were sets)
pub enum MutObjIntoIter<'a> {
    List(RcVecIter<'a, Obj>),
    Dict(RcHashMapIter<'a, ObjKey, Obj>),
    String(std::str::Chars<'a>),
}

// iterates over (index, value) or (key, value)
pub enum MutObjIntoIterPairs<'a> {
    List(usize, RcVecIter<'a, Obj>),
    Dict(RcHashMapIter<'a, ObjKey, Obj>),
    String(usize, std::str::Chars<'a>),
}

// TODO: change these to go through some new enum like MutSeq<'_> or something so we have a uniform
// place to make objects sequences, in case we add, e.g., bytes or pointers
fn mut_obj_into_iter<'a,'b>(obj: &'a mut Obj, purpose: &'b str) -> NRes<MutObjIntoIter<'a>> {
    match obj {
        Obj::List(v) => Ok(MutObjIntoIter::List(mut_rc_vec_into_iter(v))),
        Obj::Dict(v, _) => Ok(MutObjIntoIter::Dict(mut_rc_hash_map_into_iter(v))),
        Obj::String(s) => Ok(MutObjIntoIter::String(s.chars())),
        _ => Err(NErr::TypeError(format!("{}: not iterable", purpose)))
    }
}

impl Iterator for MutObjIntoIter<'_> {
    type Item = Obj;

    fn next(&mut self) -> Option<Obj> {
        match self {
            MutObjIntoIter::List(it) => it.next(),
            MutObjIntoIter::Dict(it) => Some(key_to_obj(it.next()?.0)),
            MutObjIntoIter::String(it) => Some(Obj::from(it.next()?)),
        }
    }
}

fn mut_obj_into_iter_pairs<'a, 'b>(obj: &'a mut Obj, purpose: &'b str) -> NRes<MutObjIntoIterPairs<'a>> {
    match obj {
        Obj::List(v) => Ok(MutObjIntoIterPairs::List(0, mut_rc_vec_into_iter(v))),
        Obj::Dict(v, _) => Ok(MutObjIntoIterPairs::Dict(mut_rc_hash_map_into_iter(v))),
        Obj::String(s) => Ok(MutObjIntoIterPairs::String(0, s.chars())),
        _ => Err(NErr::TypeError(format!("{}: not iterable", purpose))),
    }
}

impl Iterator for MutObjIntoIterPairs<'_> {
    type Item = (ObjKey, Obj);

    fn next(&mut self) -> Option<(ObjKey, Obj)> {
        match self {
            MutObjIntoIterPairs::List(i, it) => { let o = it.next()?; let j = *i; *i += 1; Some((ObjKey::from(j), o)) }
            MutObjIntoIterPairs::Dict(it) => it.next(),
            MutObjIntoIterPairs::String(i, it) => { let o = it.next()?; let j = *i; *i += 1; Some((ObjKey::from(j), Obj::from(o))) }
        }
    }
}

#[derive(Debug)]
pub enum NErr {
    ArgumentError(String),
    IndexError(String),
    KeyError(String),
    NameError(String),
    SyntaxError(String),
    TypeError(String),
    ValueError(String),
}

impl fmt::Display for NErr {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NErr::ArgumentError(s) => write!(formatter, "ArgumentError: {}", s),
            NErr::IndexError(s) => write!(formatter, "IndexError: {}", s),
            NErr::KeyError(s) => write!(formatter, "KeyError: {}", s),
            NErr::NameError(s) => write!(formatter, "NameError: {}", s),
            NErr::SyntaxError(s) => write!(formatter, "SyntaxError: {}", s),
            NErr::TypeError(s) => write!(formatter, "TypeError: {}", s),
            NErr::ValueError(s) => write!(formatter, "ValueError: {}", s),
        }
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
    Type(ObjType),
}

impl Func {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        match self {
            Func::Builtin(b) => b.run(args),
            Func::Closure(c) => c.run(args),
            Func::PartialApp1(f, x) => match few(args) {
                Few::One(arg) => f.run(vec![(**x).clone(), arg]),
                _ => Err(NErr::ArgumentError("For now, partially applied functions can only be called with one more argument".to_string()))
            }
            Func::PartialApp2(f, x) => match few(args) {
                Few::One(arg) => f.run(vec![arg, (**x).clone()]),
                _ => Err(NErr::ArgumentError("For now, partially applied functions can only be called with one more argument".to_string()))
            }
            Func::Composition(f, g) => f.run(vec![g.run(args)?]),
            Func::Type(t) => match few(args) {
                Few::One(arg) => call_type(t, arg),
                _ => Err(NErr::ArgumentError("Types can only take one argument".to_string()))
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
            Func::Type(t) => write!(formatter, "{}", t.name()),
        }
    }
}

pub trait Builtin : Debug {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj>;

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
        (Obj::Num(a), Obj::Num(b)) => a.partial_cmp(b).ok_or(NErr::TypeError(format!("Can't compare nums {:?} and {:?}", a, b))),
        (Obj::String(a), Obj::String(b)) => Ok(a.cmp(b)),
        (Obj::List(a), Obj::List(b)) => a.partial_cmp(b).ok_or(NErr::TypeError(format!("Can't compare lists {:?} and {:?}", a, b))),
        _ => Err(NErr::TypeError(format!("Can't compare {:?} and {:?}", aa, bb))),
    }
}

impl Builtin for ComparisonOperator {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        if self.chained.is_empty() {
            match few(args) {
                Few::Zero => Err(NErr::ArgumentError(format!("Comparison operator {:?} needs 2+ args", self.name))),
                Few::One(arg) => Ok(Obj::Func(Func::PartialApp2(
                    Box::new(Func::Builtin(Rc::new(self.clone()))),
                    Box::new(arg)
                ), Precedence::zero())),
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
                    let res = self.chained[i].run(vec![args[i+1].clone(), args[i+2].clone()])?;
                    if !res.truthy() {
                        return Ok(res)
                    }
                }
                Ok(Obj::from(true))
            } else {
                Err(NErr::ArgumentError(format!("Chained comparison operator got the wrong number of args")))
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
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::Two(Obj::Num(a), Obj::Num(b)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                // TODO: should be lazy
                Ok(Obj::List(Rc::new(num::range(n1, n2).map(|x| Obj::Num(NNum::from(x))).collect())))
            }
            Few3::Three(Obj::Num(a), Obj::Num(b), Obj::Num(c)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                let n3 = into_bigint_ok(c)?;
                // TODO: should be lazy
                Ok(Obj::List(Rc::new(num::range_step(n1, n2, n3).map(|x| Obj::Num(NNum::from(x))).collect())))
            }
            _ => Err(NErr::ArgumentError(format!("Bad args for til")))
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
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::Two(Obj::Num(a), Obj::Num(b)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                // TODO: should be lazy
                Ok(Obj::List(Rc::new(num::range_inclusive(n1, n2).map(|x| Obj::Num(NNum::from(x))).collect())))
            }
            Few3::Two(a, Obj::Func(Func::Type(t), _)) => call_type(&t, a), // sugar lmao
            Few3::Three(Obj::Num(a), Obj::Num(b), Obj::Num(c)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                let n3 = into_bigint_ok(c)?;
                // TODO: should be lazy
                Ok(Obj::List(Rc::new(num::range_step_inclusive(n1, n2, n3).map(|x| Obj::Num(NNum::from(x))).collect())))
            }
            _ => Err(NErr::ArgumentError(format!("Bad args for to")))
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
    fn run(&self, mut args: Vec<Obj>) -> NRes<Obj> {
        let mut func = None;
        // I can't believe this works (type annotation for me not the compiler)
        let mut iterators: Vec<MutObjIntoIter<'_>> = Vec::new();
        for arg in args.iter_mut() {
            match (arg, &mut func) {
                (Obj::Func(f, _), None) => {
                    func = Some(f.clone());
                }
                (Obj::Func(..), Some(_)) => Err(NErr::ArgumentError("zip: more than one function".to_string()))?,
                (arg, _) => iterators.push(mut_obj_into_iter(arg, "zip")?),
            }
        }
        if iterators.is_empty() {
            Err(NErr::ArgumentError("zip: zero iterables".to_string()))?
        }
        let mut ret = Vec::new();
        while let Some(batch) = iterators.iter_mut().map(|a| a.next()).collect() {
            ret.push(match &func {
                Some(f) => f.run(batch)?,
                None => Obj::List(Rc::new(batch)),
            })
        }
        Ok(Obj::List(Rc::new(ret)))
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
fn cartesian_foreach(acc: &mut Vec<Obj>, objs: &[Obj], f: &mut impl FnMut(&Vec<Obj>) -> NRes<()>) -> NRes<()> {
    match objs {
        [] => f(acc)?,
        [a, rest @ ..] => {
            for e in obj_to_cloning_iter(a)? {
                acc.push(e);
                cartesian_foreach(acc, rest, f)?;
                acc.pop();
            }
        }
    }
    Ok(())
}

impl Builtin for CartesianProduct {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        // Bit overgeneral, also are we interested in accepting a function?
        let mut seqs = Vec::new();
        let mut scalar = None;
        for arg in args {
            match &arg {
                Obj::List(_) | Obj::Dict(..) | Obj::String(_) => seqs.push(arg),
                Obj::Num(n) => match scalar {
                    None => scalar = Some(to_bigint_ok(n)?),
                    Some(_) => Err(NErr::ArgumentError("cartesian product: more than one integer".to_string()))?,
                }
                _ => Err(NErr::ArgumentError("cartesian product: non-sequence non-integer".to_string()))?,
            }
        }

        match (scalar, few(seqs)) {
            (Some(s), Few::One(seq)) => {
                let mut acc = Vec::new();
                for _ in num::range(BigInt::from(0), s) {
                    for e in obj_to_cloning_iter(&seq)? {
                        acc.push(e);
                    }
                }
                Ok(Obj::List(Rc::new(acc)))
            }
            (None, Few::Many(seqs)) => {
                let mut acc = Vec::new();
                let mut ret = Vec::new();
                let mut f = |k: &Vec<Obj>| {
                    ret.push(Obj::List(Rc::new(k.clone())));
                    Ok(())
                };
                cartesian_foreach(&mut acc, seqs.as_slice(), &mut f)?;
                Ok(Obj::List(Rc::new(ret)))
            }
            _ => Err(NErr::ArgumentError("cartesian product: bad combo of scalars and sequences".to_string()))?,
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

#[derive(Debug, Clone)]
pub struct BasicBuiltin {
    name: String,
    can_refer: bool,
    body: fn(args: Vec<Obj>) -> NRes<Obj>,
}

impl Builtin for BasicBuiltin {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        (self.body)(args)
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
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(arg) => (self.body)(arg),
            f => Err(NErr::ArgumentError(format!("{} only accepts one argument, got {}", self.name, f.len()))),
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
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(arg) => {
                // partial application, spicy
                Ok(Obj::Func(Func::PartialApp2(
                    Box::new(Func::Builtin(Rc::new(self.clone()))),
                    Box::new(arg)
                ), Precedence::zero()))
            }
            Few2::Two(a, b) => (self.body)(a, b),
            f => Err(NErr::ArgumentError(format!("{} only accepts two arguments (or one for partial application), got {}", self.name, f.len())))
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

impl Builtin for OneNumBuiltin {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(Obj::Num(n)) => (self.body)(n),
            Few::One(x) => Err(NErr::ArgumentError(format!("{} only accepts numbers, got {:?}", self.name, x))),
            f => Err(NErr::ArgumentError(format!("{} only accepts one argument, got {}", self.name, f.len())))
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
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        (self.body)(args.into_iter().map(|x| match x {
            Obj::Num(n) => Ok(n),
            _ => Err(NErr::ArgumentError(format!("{} only accepts numbers, got {:?}", self.name, x))),
        }).collect::<NRes<Vec<NNum>>>()?)
    }

    fn builtin_name(&self) -> &str { &self.name }

    fn can_refer(&self) -> bool { false }
}

#[derive(Debug, Clone)]
pub struct TwoNumsBuiltin {
    name: String,
    body: fn(a: NNum, b: NNum) -> NRes<Obj>,
}

impl Builtin for TwoNumsBuiltin {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(a @ Obj::Num(_)) => {
                // partial application, spicy
                Ok(Obj::Func(Func::PartialApp2(
                    Box::new(Func::Builtin(Rc::new(self.clone()))),
                    Box::new(a)
                ), Precedence::zero()))
            }
            Few2::One(a) => Err(NErr::ArgumentError(format!("{} only accepts numbers, got {:?}", self.name, a))),
            Few2::Two(Obj::Num(a), Obj::Num(b)) => (self.body)(a, b),
            Few2::Two(a, b) => Err(NErr::ArgumentError(format!("{} only accepts numbers, got {:?} {:?}", self.name, a, b))),
            f => Err(NErr::ArgumentError(format!("{} only accepts two numbers, got {}", self.name, f.len()))),
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
    // FloatLit(f64),
    StringLit(Rc<String>),
    Ident(String),
    LeftParen,
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
    Eval,
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
    StringLit(Rc<String>),
    Ident(String),
    Backref(usize),
    Call(Box<Expr>, Vec<Box<Expr>>),
    List(Vec<Box<Expr>>),
    Dict(Option<Box<Expr>>, Vec<(Box<Expr>, Option<Box<Expr>>)>),
    Index(Box<Expr>, IndexOrSlice),
    Chain(Box<Expr>, Vec<(String, Box<Expr>)>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Annotation(Box<Expr>, Option<Box<Expr>>),
    Pop(Box<Lvalue>),
    Remove(Box<Lvalue>),
    Swap(Box<Lvalue>, Box<Lvalue>),
    // Weird hack to support punching a hole in side effects while minimally affecting other stuff.
    // Eval is a node that there's no syntax for; it evaluates its contents in the current
    // environment. The token `eval` becomes Expr::EvalToken, which, when evaluated, turns into a
    // closure that captures its environment and invokes the Eval node. IMO this is marginally
    // better than specialized `eval` syntax in that you can use it like any other identifier, e.g.
    // mapping over it, and a lot better than requiring us to pass the environment to every
    // function call everywhere.
    Eval(Box<Expr>),
    EvalToken,
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
}

impl Lexer<'_> {
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
                    loop {
                        if let None | Some('\n') = self.next() { break; }
                    }
                }
                '\'' | '"' => {
                    let mut acc = String::new();
                    while self.peek() != Some(&c) {
                        match self.next() {
                            Some('\\') => match self.next() {
                                Some('n') => acc.push('\n'),
                                Some('r') => acc.push('\r'),
                                Some('t') => acc.push('\t'),
                                Some(c @ ('\\' | '\'' | '\"')) => acc.push(c),
                                Some(c) => panic!("lexing: string literal: unknown escape {}", c),
                                None => panic!("lexing: string literal: escape eof"),
                            }
                            Some(c) => acc.push(c),
                            None => panic!("lexing: string literal hit eof")
                        }
                    }
                    self.next();
                    self.emit(Token::StringLit(Rc::new(acc)))
                }
                c => {
                    if c.is_digit(10) {
                        let mut acc = c.to_string();

                        while let Some(cc) = self.peek().filter(|d| d.is_digit(10)) {
                            acc.push(*cc);
                            self.next();
                        }
                        self.emit(Token::IntLit(acc.parse::<BigInt>().unwrap()))
                    } else if c.is_alphabetic() {
                        let mut acc = c.to_string();

                        while let Some(cc) = self.peek().filter(|c| c.is_alphanumeric() || **c == '_') {
                            acc.push(*cc);
                            self.next();
                        }
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
                            "eval" => Token::Eval,
                            _ => Token::Ident(acc),
                        })
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
    let mut lexer = Lexer {
        chars: code.chars().peekable(),
        start: CodeLoc { line: 1, col: 1 },
        cur: CodeLoc { line: 1, col: 1 },
        tokens: Vec::new(),
    };
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
                Token::StringLit(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(Expr::StringLit(s))
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
                Token::Eval => {
                    self.advance();
                    Ok(Expr::EvalToken)
                }
                Token::LeftParen => {
                    self.advance();
                    let e = self.expression()?;
                    self.require(Token::RightParen, "normal parenthesized expr".to_string())?;
                    // Only add the paren if it looks important in lvalues.
                    match &e {
                        // TODO: slice would go here ig
                        Expr::Ident(_) | Expr::Index(..) => Ok(Expr::Paren(Box::new(e))),
                        _ => Ok(e),
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
                    let (cs, _) = self.comma_separated()?;
                    self.require(Token::RightParen, "call expr".to_string())?;
                    cur = Expr::Call(Box::new(cur), cs);
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
        let ret = p.expression().map(Some);
        if p.is_at_end() {
            ret
        } else {
            Err(format!("Didn't finish parsing: got {}", p.peek_err()))
        }
    }
}

#[derive(Debug)]
pub struct TopEnv {
    pub backrefs: Vec<Obj>,
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
                Err(_) => Err(NErr::NameError(format!("No such variable: {}", s))),
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
        Err(NErr::ValueError(format!("Can't unpack into mismatched length {:?} {} != {:?} {}", lhs, lhs.len(), rhs, rhs.len())))
    }
}

fn assign_all(env: &mut Env, lhs: &[Box<EvaluatedLvalue>], rt: Option<&ObjType>, rhs: &[Obj]) -> NRes<()> {
    let mut splat = None;
    for (i, lhs1) in lhs.iter().enumerate() {
        match &**lhs1 {
            EvaluatedLvalue::Splat(inner) => match splat {
                Some(_) => return Err(NErr::SyntaxError(format!("Can't have two splats in assign lhs"))),
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
            assign(env, inner, rt, &Obj::List(Rc::new(rhs[si..rhs.len() - lhs.len() + si + 1].to_vec())))?;
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
        (Obj::List(v), [EvaluatedIndexOrSlice::Index(i), rest @ ..]) => {
            set_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, value, every)
        }
        (Obj::List(v), [EvaluatedIndexOrSlice::Slice(i, j), rest @ ..]) => {
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
        (Obj::String(s), [EvaluatedIndexOrSlice::Index(i)]) => match value {
            Obj::String(v) => {
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
                            Err(NErr::ValueError(format!("assigning to string result not utf-8 (string corrupted)")))
                        }
                    }
                } else {
                    Err(NErr::ValueError(format!("assigning to string index, not a byte")))
                }
            }
            _ => Err(NErr::ValueError(format!("assigning to string index, not a string")))
        }
        (Obj::Dict(v, _), [EvaluatedIndexOrSlice::Index(kk), rest @ ..]) => {
            let k = to_key(kk.clone())?;
            let mut_d = Rc::make_mut(v);
            // We might create a new map entry, but only at the end, which is a bit of a
            // mismatch for Rust's map API if we want to recurse all the way
            if rest.is_empty() {
                mut_d.insert(k, value); Ok(())
            } else {
                set_index(match mut_d.get_mut(&k) {
                    Some(vvv) => vvv,
                    None => Err(NErr::TypeError(format!("nothing at key {:?} {:?}", mut_d, k)))?,
                }, rest, value, every)
            }
        }
        (Obj::Dict(v, _), [EvaluatedIndexOrSlice::Slice(None, None), rest @ ..]) => {
            let mut_d = Rc::make_mut(v);
            if every {
                for (_, vv) in mut_d.iter_mut() {
                    set_index(vv, rest, value.clone(), true)?;
                }
                Ok(())
            } else {
                Err(NErr::TypeError(format!("can't slice dictionaries except with every")))
            }
        }
        (Obj::Func(_, Precedence(p, _)), [EvaluatedIndexOrSlice::Index(Obj::String(r))]) => match &***r {
            "precedence" => match value {
                Obj::Num(f) => match f.to_f64() {
                    Some(f) => { *p = f; Ok(()) }
                    None => Err(NErr::TypeError(format!("precedence must be convertible to float: {}", f))),
                }
                f => Err(NErr::TypeError(format!("precedence must be number, got {}", f))),
            }
            k => Err(NErr::TypeError(format!("function key must be 'precedence', got {}", k))),
        }
        (lhs, ii) => Err(NErr::TypeError(format!("can't index {:?} {:?}", lhs, ii))),
    }
}

// be careful not to call this with both lhs holding a mutable reference into a RefCell and rhs
// trying to take such a reference!
fn modify_existing_index(lhs: &mut Obj, indexes: &[EvaluatedIndexOrSlice], f: impl FnOnce(&mut Obj) -> NRes<Obj>) -> NRes<Obj> {
    match indexes.split_first() {
        None => f(lhs),
        Some((i, rest)) => {
            match (lhs, i) {
                (Obj::List(v), EvaluatedIndexOrSlice::Index(i)) => {
                    modify_existing_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, f)
                }
                (Obj::Dict(v, def), EvaluatedIndexOrSlice::Index(kk)) => {
                    let k = to_key(kk.clone())?;
                    let mut_d = Rc::make_mut(v);
                    // FIXME improve
                    if !mut_d.contains_key(&k) {
                        match def {
                            Some(d) => { mut_d.insert(k.clone(), (&**d).clone()); }
                            None => return Err(NErr::TypeError(format!("nothing at key {:?} {:?}", mut_d, k))),
                        }
                    }
                    modify_existing_index(match mut_d.get_mut(&k) {
                        Some(vvv) => vvv,
                        // shouldn't happen:
                        None => Err(NErr::TypeError(format!("nothing at key {:?} {:?}", mut_d, k)))?,
                    }, rest, f)
                }
                (lhs2, ii) => Err(NErr::TypeError(format!("can't index {:?} {:?}", lhs2, ii))),
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
                (Obj::List(v), EvaluatedIndexOrSlice::Index(i)) => {
                    modify_every_existing_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, f)
                }
                (Obj::List(v), EvaluatedIndexOrSlice::Slice(lo, hi)) => {
                    let (lo, hi) = pythonic_slice(v, lo.as_ref(), hi.as_ref())?;
                    for m in &mut Rc::make_mut(v)[lo..hi] {
                        modify_every_existing_index(m, rest, f)?
                    }
                    Ok(())
                }
                (Obj::Dict(v, def), EvaluatedIndexOrSlice::Index(kk)) => {
                    let k = to_key(kk.clone())?;
                    let mut_d = Rc::make_mut(v);
                    // FIXME improve
                    if !mut_d.contains_key(&k) {
                        match def {
                            Some(d) => { mut_d.insert(k.clone(), (&**d).clone()); }
                            None => return Err(NErr::TypeError(format!("nothing at key {:?} {:?}", mut_d, k))),
                        }
                    }
                    modify_every_existing_index(match mut_d.get_mut(&k) {
                        Some(vvv) => vvv,
                        // shouldn't happen:
                        None => Err(NErr::TypeError(format!("nothing at key {:?} {:?}", mut_d, k)))?,
                    }, rest, f)
                }
                (lhs2, ii) => Err(NErr::TypeError(format!("can't index {:?} {:?}", lhs2, ii))),
            }
        }
    }
}

fn insert_declare(env: &mut Env, s: &str, ty: ObjType, rhs: Obj) -> NRes<()> {
    if env.insert(s.to_string(), ty, rhs).is_some() {
        Err(NErr::NameError(format!("Declaring/assigning variable that already exists: {:?}. If in pattern with other declarations, parenthesize existent variables", s)))
    } else {
        Ok(())
    }
}

fn assign_respecting_type(env: &mut Env, s: &str, ixs: &[EvaluatedIndexOrSlice], rhs: &Obj, every: bool) -> NRes<()> {
    env.modify_existing_var(s, |(ty, v)| {
        // Eagerly check type only if ixs is empty, otherwise we can't really do
        // that (at least not in full generality)
        if ixs.is_empty() && !is_type(ty, rhs) {
            Err(NErr::NameError(format!("Assignment to {} type check failed: {} not {}", s, rhs, ty.name())))?
        }
        set_index(v, ixs, rhs.clone(), every)?;
        // Check type after the fact. TODO if we ever do subscripted types: this
        // will be super inefficient lmao, we can be smart tho
        if !ixs.is_empty() && !is_type(ty, &v) {
            Err(NErr::NameError(format!("Assignment to {} LATE type check failed (the assignment still happened): {} not {}", s, rhs, ty.name())))
        } else {
            Ok(())
        }
    }).ok_or(NErr::NameError(if ixs.is_empty() {
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
                    return Err(NErr::NameError(format!("Can't declare new value into index expression: {:?} {:?}", s, ixs)))
                }
            }
            None => assign_respecting_type(env, s, ixs, rhs, false),
        }
        EvaluatedLvalue::CommaSeq(ss) => {
            match rhs {
                Obj::List(ls) => assign_all(env, ss, rt, ls),
                _ => Err(NErr::TypeError(format!("Can't unpack non-list {:?}", rhs))),
            }
        }
        EvaluatedLvalue::Annotation(s, ann) => match ann {
            None => assign(env, s, Some(&ObjType::Any), rhs),
            Some(t) => assign(env, s, Some(&to_type(t, "annotation")?), rhs),
        }
        EvaluatedLvalue::Unannotation(s) => {
            assign(env, s, None, rhs)
        }
        EvaluatedLvalue::Splat(_) => Err(NErr::TypeError(format!("Can't assign to raw splat {:?}", lhs))),
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
                    return Err(NErr::NameError(format!("Can't declare new value into index expression: {:?} {:?}", s, ixs)))
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
        EvaluatedLvalue::Splat(_) => Err(NErr::TypeError(format!("Can't assign to raw splat {:?}", lhs))),
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
                        Err(NErr::NameError(format!("Modify every: assignment to {} type check failed: {} not {}", s, new, ty.name())))
                    }
                }).ok_or(NErr::NameError(format!("Variable {:?} not found in modify every", s)))?
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
        EvaluatedLvalue::Annotation(..) => Err(NErr::TypeError(format!("No annotations in modify every: {:?}", lhs))),
        EvaluatedLvalue::Unannotation(s) => modify_every(env, s, rhs),
        EvaluatedLvalue::Splat(_) => Err(NErr::TypeError(format!("Can't assign to raw splat {:?}", lhs))),
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

    fn run_top_popped(&mut self, op: Func) -> NRes<()> {
        let mut rhs = self.operands.pop().expect("sync");
        let mut lhs = self.operands.pop().expect("sync");
        lhs.append(&mut rhs); // concats and drains rhs of elements
        self.operands.push(vec![op.run(lhs)?]);
        Ok(())
    }

    fn run_top(&mut self) -> NRes<()> {
        let (op, _) = self.operators.pop().expect("sync");
        self.run_top_popped(op)
    }

    fn give(&mut self, operator: Func, precedence: Precedence, operand: Obj) -> NRes<()> {
        while self.operators.last().map_or(false, |t| t.1.0 >= precedence.0) {
            let (top, prec) = self.operators.pop().expect("sync");
            match top.try_chain(&operator) {
                Some(new_op) => {
                    self.operators.push((new_op, prec));
                    self.operands.last_mut().expect("sync").push(operand);
                    return Ok(())
                }
                None => { self.run_top_popped(top)?; }
            }
        }

        self.operators.push((operator, precedence));
        self.operands.push(vec![operand]);
        Ok(())
    }

    fn finish(&mut self) -> NRes<Obj> {
        while !self.operators.is_empty() {
            self.run_top()?;
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
                    Obj::List(mut xx) => acc.append(Rc::make_mut(&mut xx)),
                    _ => Err(NErr::TypeError(format!("Can't splat non-list {:?}", res)))?
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

fn pythonic_index<T>(xs: &[T], i: &Obj) -> NRes<usize> {
    match i {
        Obj::Num(ii) => match ii.to_isize() {
            Some(n) => {
                if n >= 0 && n < (xs.len() as isize) { return Ok(n as usize) }

                let i2 = (n + (xs.len() as isize)) as usize;
                if i2 < xs.len() { return Ok(i2) }

                Err(NErr::IndexError(format!("Index out of bounds: {:?}", ii)))
            }
            _ => Err(NErr::IndexError(format!("Index out of bounds of isize or non-integer: {:?}", ii)))
        }
        _ => Err(NErr::IndexError(format!("Invalid (non-numeric) index: {:?}", i))),
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
            _ => Err(NErr::IndexError(format!("Slice index out of bounds of isize or non-integer: {:?}", ii)))
        }
        _ => Err(NErr::IndexError(format!("Invalid (non-numeric) slice index: {:?}", i))),
    }
}

fn pythonic_slice<T>(xs: &[T], lo: Option<&Obj>, hi: Option<&Obj>) -> NRes<(usize, usize)> {
    Ok((
        match lo { Some(lo) => clamped_pythonic_index(xs, &lo)?, None => 0 },
        match hi { Some(hi) => clamped_pythonic_index(xs, &hi)?, None => xs.len() },
    ))
}

fn index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, ir) {
        (Obj::List(xx), ii) => Ok(xx[pythonic_index(xx, &ii)?].clone()),
        (Obj::String(s), ii) => {
            let bs = s.as_bytes();
            let i = pythonic_index(bs, &ii)?;
            // TODO this was the path of least resistance; idk what good semantics actually are
            Ok(Obj::from(String::from_utf8_lossy(&bs[i..i+1]).into_owned()))
        }
        (Obj::Dict(xx, def), ir) => {
            let k = to_key(ir)?;
            match xx.get(&k) {
                Some(e) => Ok(e.clone()),
                None => match def {
                    Some(d) => Ok((&**d).clone()),
                    None => Err(NErr::KeyError(format!("Dictionary lookup: nothing at key {:?} {:?}", xx, k))),
                }
            }
        }
        (Obj::Func(_, Precedence(p, _)), Obj::String(k)) => match &**k {
            "precedence" => Ok(Obj::from(*p)),
            _ => Err(NErr::TypeError(format!("can't index into func {:?}", k))),
        }
        (xr, ir) => Err(NErr::TypeError(format!("can't index {:?} {:?}", xr, ir))),
    }
}

fn slice(xr: Obj, lo: Option<Obj>, hi: Option<Obj>) -> NRes<Obj> {
    match (&xr, lo, hi) {
        (Obj::List(xx), lo, hi) => {
            let (lo, hi) = pythonic_slice(xx, lo.as_ref(), hi.as_ref())?;
            Ok(Obj::List(Rc::new(xx[lo..hi].to_vec())))
        }
        (Obj::String(s), lo, hi) => {
            let bs = s.as_bytes();
            let (lo, hi) = pythonic_slice(bs, lo.as_ref(), hi.as_ref())?;
            // TODO this was the path of least resistance; idk what good semantics actually are
            Ok(Obj::from(String::from_utf8_lossy(&bs[lo..hi]).into_owned()))
        }
        (xr, lo, hi) => Err(NErr::TypeError(format!("can't slice {:?} {:?} {:?}", xr, lo, hi))),
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
        (Obj::String(s), ii) => {
            let bs = s.as_bytes();
            // TODO above
            match pythonic_index(bs, ii) {
                Ok(i) => Ok(Obj::from(String::from_utf8_lossy(&bs[i..i+1]).into_owned())),
                Err(_) => Ok(Obj::Null),
            }
        }
        (Obj::List(xx), ii) => {
            // Not sure about catching *every* err from pythonic_index here...
            match pythonic_index(xx, ii) {
                Ok(i) => Ok(xx[i].clone()),
                Err(_) => Ok(Obj::Null),
            }
        }
        (Obj::Dict(xx, def), _) => {
            let k = to_key(ir)?;
            match xx.get(&k) {
                Some(e) => Ok(e.clone()),
                None => match def {
                    Some(d) => Ok((&**d).clone()),
                    None => Ok(Obj::Null),
                }
            }
        }
        _ => Err(NErr::TypeError(format!("Can't safe index {:?} {:?}", xr, ir))),
    }
}

fn call(f: Obj, args: Vec<Obj>) -> NRes<Obj> {
    match f {
        Obj::Func(ff, _) => ff.run(args),
        f => match few(args) {
            Few::One(Obj::Func(f2, _)) => Ok(Obj::Func(Func::PartialApp1(Box::new(f2), Box::new(f)), Precedence::zero())),
            Few::One(f2) => Err(NErr::TypeError(format!("Can't call non-function {:?} (and argument {:?} not callable)", f, f2))),
            _ => Err(NErr::TypeError(format!("Can't call non-function {:?} (and more than one argument)", f))),
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
        Lvalue::CommaSeq(v) => Ok(Obj::List(Rc::new(
            v.iter().map(|e| Ok(eval_lvalue_as_obj(env, e)?)).collect::<NRes<Vec<Obj>>>()?
        ))),
        // maybe if commaseq eagerly looks for splats...
        Lvalue::Splat(_) => Err(NErr::SyntaxError("Can't evaluate splat on LHS of assignment??".to_string())),
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
        Lvalue::Splat(_) => Err(NErr::SyntaxError("Can't evaluate splat on LHS of assignment??".to_string())),
    }
}
*/

fn obj_in(a: Obj, b: Obj) -> NRes<bool> {
    match (a, b) {
        (a, Obj::List(mut v)) => Ok(mut_rc_vec_into_iter(&mut v).any(|x| x == a)),
        (a, Obj::Dict(v, _)) => Ok(v.contains_key(&to_key(a)?)),
        (Obj::String(s), Obj::String(v)) => Ok((*v).contains(&*s)),
        _ => Err(NErr::TypeError("in: not compatible".to_string())),
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
                        assign(&mut ee.borrow_mut(), &p, Some(&ObjType::Any), &Obj::List(Rc::new(vec![key_to_obj(k), v])))?;
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
        Expr::StringLit(s) => Ok(Obj::String(Rc::clone(s))),
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
                    ev.give(b, prec, oprd)?;
                } else {
                    return Err(NErr::TypeError(format!("Chain cannot use nonblock in operand position: {:?}", oprr)))
                }
            }
            ev.finish()
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
                Expr::CommaSeq(xs) => Ok(Obj::List(Rc::new(eval_seq(env, xs)?))),
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
        /*
            let p = eval_lvalue(env, pat)?;
            let res = match &**rhs {
                Expr::CommaSeq(xs) => Ok(Obj::List(Rc::new(eval_seq(env, xs)?))),
                _ => evaluate(env, rhs),
            }?;
            assign(&mut env.borrow_mut(), &p, AssignRHS::Assign(true, &res))?;
            Ok(Obj::Null)
        */
        Expr::Pop(pat) => {
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => {
                    env.borrow_mut().modify_existing_var(&s, |(_type, vv)| {
                        modify_existing_index(vv, &ixs, |x| match x {
                            Obj::List(xs) => {
                                Rc::make_mut(xs).pop().ok_or(NErr::NameError("can't pop empty".to_string()))
                            }
                            _ => Err(NErr::TypeError("can't pop".to_string())),
                        })
                    }).ok_or(NErr::TypeError("failed to pop??".to_string()))?
                }
                _ => Err(NErr::TypeError("can't pop, weird pattern".to_string())),
            }
        }
        Expr::Remove(pat) => {
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => match ixs.as_slice() {
                    [] => Err(NErr::ValueError("can't remove flat identifier".to_string())),
                    [rest @ .., last_i] => {
                        env.borrow_mut().modify_existing_var(&s, |(_type, vv)| {
                            modify_existing_index(vv, &rest, |x| match (x, last_i) {
                                (Obj::List(xs), EvaluatedIndexOrSlice::Index(i)) => {
                                    let ii = pythonic_index(xs, i)?;
                                    Ok(Rc::make_mut(xs).remove(ii))
                                }
                                (Obj::List(xs), EvaluatedIndexOrSlice::Slice(i, j)) => {
                                    let (lo, hi) = pythonic_slice(xs, i.as_ref(), j.as_ref())?;
                                    Ok(Obj::List(Rc::new(Rc::make_mut(xs).drain(lo..hi).collect())))
                                }
                                (Obj::Dict(xs, _), EvaluatedIndexOrSlice::Index(i)) => {
                                    Rc::make_mut(xs).remove(&to_key(i.clone())?).ok_or(NErr::KeyError("key not found in dict".to_string()))
                                }
                                // TODO: remove parts of strings...
                                _ => Err(NErr::TypeError("can't remove".to_string())),
                            })
                        }).ok_or(NErr::NameError("var not found to remove".to_string()))?
                    }
                }
                _ => Err(NErr::TypeError("can't pop, weird pattern".to_string())),
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
                            Expr::CommaSeq(xs) => Ok(Obj::List(Rc::new(eval_seq(env, xs)?))),
                            _ => evaluate(env, rhs),
                        }?;
                        modify_every(env, &p, &mut |x| { ff.run(vec![x, res.clone()]) })?;
                        Ok(Obj::Null)
                    }
                    opv => Err(NErr::TypeError(format!("Operator assignment: operator is not function {:?}", opv))),
                }
            } else {
                let pv = eval_lvalue_as_obj(env, pat)?;
                let p = eval_lvalue(env, pat)?;
                match evaluate(env, op)? {
                    Obj::Func(ff, _) => {
                        let res = match &**rhs {
                            Expr::CommaSeq(xs) => Ok(Obj::List(Rc::new(eval_seq(env, xs)?))),
                            _ => evaluate(env, rhs),
                        }?;
                        if !ff.can_refer() {
                            // Drop the Rc from the lvalue so that pure functions can try to consume it
                            assign(&mut env.borrow_mut(), &p, None, &Obj::Null)?;
                        }
                        let fres = ff.run(vec![pv, res])?;
                        assign(&mut env.borrow_mut(), &p, None, &fres)?;
                        Ok(Obj::Null)
                    }
                    opv => Err(NErr::TypeError(format!("Operator assignment: operator is not function {:?}", opv))),
                }
            }
        }
        Expr::Call(f, args) => {
            let fr = evaluate(env, f)?;
            let a = eval_seq(env, args)?;
            call(fr, a)
        }
        Expr::CommaSeq(_) => Err(NErr::SyntaxError("Comma seqs only allowed directly on a side of an assignment (for now)".to_string())),
        Expr::Splat(_) => Err(NErr::SyntaxError("Splats only allowed on an assignment-related place or in call or list (?)".to_string())),
        Expr::List(xs) => {
            Ok(Obj::List(Rc::new(eval_seq(env, xs)?)))
        }
        Expr::Dict(def, xs) => {
            let dv = match def {
                Some(de) => Some(Box::new(evaluate(env, de)?)),
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
                        Err(NErr::TypeError(format!("Dictionary: Can only splat other dictionary without value; instead got {:?} {:?}", ke, ve)))?
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
            Ok(Obj::Dict(Rc::new(acc), dv))
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
                Ok(Obj::List(Rc::new(acc)))
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
        Expr::Eval(expr) => {
            match evaluate(env, expr)? {
                Obj::String(r) => match parse(&r) {
                    Ok(Some(code)) => evaluate(env, &code),
                    Ok(None) => Err(NErr::ValueError("eval: empty expression".to_string())),
                    Err(s) => Err(NErr::ValueError(s)),
                }
                s => Err(NErr::ValueError(format!("can't eval {}", s))),
            }
        }
        Expr::EvalToken => Ok(Obj::Func(Func::Closure(Closure {
            params: Rc::new(vec![Box::new(Lvalue::IndexedIdent("arg".to_string(), Vec::new()))]),
            body: Rc::new(Expr::Eval(Box::new(Expr::Ident("arg".to_string())))),
            env: Env::with_parent(env),
        }), Precedence::zero())),
        Expr::Backref(i) => env.borrow_mut().mut_top_env(|top| {
            match if *i == 0 { top.backrefs.last() } else { top.backrefs.get(i - 1) } {
                Some(x) => Ok(x.clone()),
                None => Err(NErr::IndexError("no such backref".to_string())),
            }
        }),
        Expr::Paren(p) => evaluate(env, &*p),
    }
}

pub fn simple_eval(code: &str) -> Obj {
    let mut env = Env::new(TopEnv { backrefs: Vec::new() });
    initialize(&mut env);

    let e = Rc::new(RefCell::new(env));
    evaluate(&e, &parse(code).unwrap().unwrap()).unwrap()
}

pub fn initialize(env: &mut Env) {
    env.insert("null".to_string(), ObjType::Null, Obj::Null);

    env.insert_builtin(TwoNumsBuiltin {
        name: "+".to_string(),
        body: |a, b| { Ok(Obj::Num(a + b)) }
    });
    env.insert_builtin(NumsBuiltin {
        name: "-".to_string(),
        body: |args| match few(args) {
            Few::Zero => Err(NErr::ArgumentError("-: received 0 args".to_string())),
            Few::One(s) => Ok(Obj::Num(-s)),
            Few::Many(mut ss) => {
                let mut s = ss.remove(0);
                for arg in ss {
                    s -= &arg;
                }
                Ok(Obj::Num(s))
            }
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
                    _ => Err(NErr::ArgumentError("sum: non-number".to_string()))?,
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
                    _ => Err(NErr::ArgumentError("product: non-number".to_string()))?,
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
    env.insert_builtin(TilBuiltin {});
    env.insert_builtin(ToBuiltin {});
    env.insert_builtin(OneArgBuiltin {
        name: "ord".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::String(s) => {
                if s.len() != 1 {
                    Err(NErr::ValueError("ord of string with length != 1".to_string()))
                } else {
                    Ok(Obj::from(s.chars().next().unwrap() as usize))
                }
            }
            _ => Err(NErr::TypeError("ord of non-string".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "chr".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::Num(n) => Ok(Obj::String(Rc::new(nnum::char_from_bigint(&into_bigint_ok(n)?).ok_or(NErr::ValueError("chr of int oob".to_string()))?.to_string()))),
            _ => Err(NErr::TypeError("chr of non-num".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "len".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::List(a) => Ok(Obj::Num(NNum::from(a.len()))),
            Obj::Dict(a, _) => Ok(Obj::Num(NNum::from(a.len()))),
            Obj::String(a) => Ok(Obj::Num(NNum::from(a.len()))),
            _ => Err(NErr::TypeError("len: list or dict only".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "then".to_string(),
        can_refer: true,
        body: |a, b| call(a, vec![b]),
    });
    env.insert_builtin(BasicBuiltin {
        name: "by".to_string(),
        can_refer: false,
        body: |_| Err(NErr::TypeError("by: cannot call".to_string())),
    });
    env.insert_builtin(BasicBuiltin {
        name: "with".to_string(),
        can_refer: false,
        body: |_| Err(NErr::TypeError("with: cannot call".to_string())),
    });
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
    env.insert_builtin(TwoArgBuiltin {
        name: ".".to_string(),
        can_refer: true,
        body: |a, b| call(b, vec![a]),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ".>".to_string(),
        can_refer: true,
        body: |a, b| call(b, vec![a]),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "<.".to_string(),
        can_refer: true,
        body: |a, b| call(b, vec![a]),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "->".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::Func(f, _), Obj::Func(g, _)) => Ok(Obj::Func(Func::Composition(Box::new(g), Box::new(f)), Precedence::zero())),
            _ => Err(NErr::TypeError(">>: not function".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "<-".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::Func(f, _), Obj::Func(g, _)) => Ok(Obj::Func(Func::Composition(Box::new(f), Box::new(g)), Precedence::zero())),
            _ => Err(NErr::TypeError("<<: not function".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "each".to_string(),
        can_refer: true,
        body: |mut a, b| {
            let it = mut_obj_into_iter(&mut a, "each")?;
            match b {
                Obj::Func(b, _) => {
                    for e in it {
                        b.run(vec![e])?;
                    }
                    Ok(Obj::Null)
                }
                _ => Err(NErr::TypeError("map: not callable".to_string()))
            }
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "map".to_string(),
        can_refer: true,
        body: |mut a, b| {
            let it = mut_obj_into_iter(&mut a, "map")?;
            match b {
                Obj::Func(b, _) => Ok(Obj::List(Rc::new(
                    it.map(|e| b.run(vec![e])).collect::<NRes<Vec<Obj>>>()?
                ))),
                _ => Err(NErr::TypeError("map: not callable".to_string()))
            }
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "map_keys".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::Dict(mut d, def), Obj::Func(b, _)) => {
                Ok(Obj::Dict(Rc::new(
                    Rc::make_mut(&mut d).drain().map(|(k, v)| Ok((to_key(b.run(vec![key_to_obj(k)])?)?, v))).collect::<NRes<HashMap<ObjKey, Obj>>>()?
                ), def))
            }
            _ => Err(NErr::TypeError("map_keys: not dict or callable".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "map_values".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::Dict(mut d, def), Obj::Func(b, _)) => {
                Ok(Obj::Dict(Rc::new(
                    Rc::make_mut(&mut d).drain().map(|(k, v)| Ok((k, b.run(vec![v])?))).collect::<NRes<HashMap<ObjKey, Obj>>>()?
                ), match def {
                    Some(def) => Some(Box::new(b.run(vec![*def])?)),
                    None => None
                }))
            }
            _ => Err(NErr::TypeError("map_keys: not dict or callable".to_string()))
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
            Ok(Obj::List(Rc::new(acc)))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "flat_map".to_string(),
        can_refer: true,
        body: |mut a, b| {
            let it = mut_obj_into_iter(&mut a, "flat_map (outer)")?;
            match b {
                Obj::Func(b, _) => {
                    let mut acc = Vec::new();
                    for e in it {
                        let mut r = b.run(vec![e])?;
                        for k in mut_obj_into_iter(&mut r, "flat_map (inner)")? {
                            acc.push(k);
                        }
                    }
                    Ok(Obj::List(Rc::new(acc)))
                }
                _ => Err(NErr::TypeError("flat_map: not callable".to_string()))
            }
        }
    });
    env.insert_builtin(Zip {});
    env.insert_builtin(TwoArgBuiltin {
        name: "filter".to_string(),
        can_refer: true,
        body: |mut a, b| {
            let it = mut_obj_into_iter(&mut a, "filter")?;
            match b {
                Obj::Func(b, _) => {
                    let mut acc = Vec::new();
                    for e in it {
                        if b.run(vec![e.clone()])?.truthy() {
                            acc.push(e)
                        }
                    }
                    Ok(Obj::List(Rc::new(acc)))
                }
                _ => Err(NErr::TypeError("filter: list and func only".to_string()))
            }
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "reject".to_string(),
        can_refer: true,
        body: |mut a, b| {
            let it = mut_obj_into_iter(&mut a, "reject")?;
            match b {
                Obj::Func(b, _) => {
                    let mut acc = Vec::new();
                    for e in it {
                        if !b.run(vec![e.clone()])?.truthy() {
                            acc.push(e)
                        }
                    }
                    Ok(Obj::List(Rc::new(acc)))
                }
                _ => Err(NErr::TypeError("reject: list and func only".to_string()))
            }
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "any".to_string(),
        can_refer: true,
        body: |args| match few2(args) {
            Few2::Zero => Err(NErr::TypeError("any: zero args".to_string())),
            Few2::One(mut a) => Ok(Obj::from(mut_obj_into_iter(&mut a, "any")?.any(|x| x.truthy()))),
            Few2::Two(mut a, Obj::Func(b, _)) => {
                for e in mut_obj_into_iter(&mut a, "any")? {
                    if b.run(vec![e.clone()])?.truthy() {
                        return Ok(Obj::from(true))
                    }
                }
                Ok(Obj::from(false))
            }
            _ => Err(NErr::TypeError("any: too many args".to_string())),
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "all".to_string(),
        can_refer: true,
        body: |args| match few2(args) {
            Few2::Zero => Err(NErr::TypeError("all: zero args".to_string())),
            Few2::One(mut a) => Ok(Obj::from(mut_obj_into_iter(&mut a, "all")?.all(|x| x.truthy()))),
            Few2::Two(mut a, Obj::Func(b, _)) => {
                for e in mut_obj_into_iter(&mut a, "all")? {
                    if !b.run(vec![e.clone()])?.truthy() {
                        return Ok(Obj::from(false))
                    }
                }
                Ok(Obj::from(true))
            }
            Few2::Two(_, b) => Err(NErr::TypeError(format!("all: second arg not func: {}", b))),
            ff => Err(NErr::TypeError(format!("all: too many args: {:?}", ff))),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "fold".to_string(),
        can_refer: true,
        body: |mut a, b| {
            let mut it = mut_obj_into_iter(&mut a, "fold")?;
            match b {
                Obj::Func(b, _) => {
                    // not sure if any standard fallible rust methods work...
                    match it.next() {
                        Some(mut cur) => {
                            for e in it {
                                cur = b.run(vec![cur, e])?;
                            }
                            Ok(cur)
                        }
                        None => Err(NErr::ValueError("fold: empty seq".to_string())),
                    }
                }
                _ => Err(NErr::TypeError("map: not callable".to_string()))
            }
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "append".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::List(mut a), b) => {
                Rc::make_mut(&mut a).push(b.clone());
                Ok(Obj::List(a))
            }
            _ => Err(NErr::TypeError("append: 2 args only".to_string()))
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "max".to_string(),
        can_refer: false,
        body: |args| match args.as_slice() {
            [] => Err(NErr::TypeError("max: at least 1 arg".to_string())),
            [Obj::List(a)] => {
                let mut ret: &Obj = &a[0];
                for b in &a[1..] {
                    if ncmp(b, &ret)? == Ordering::Greater { ret = b }
                }
                Ok(ret.clone())
            }
            [_] => Err(NErr::TypeError("max 1 not list".to_string())),
            [a, rest @ ..] => {
                let mut ret: &Obj = a;
                for b in rest {
                    if ncmp(b, &ret)? == Ordering::Greater { ret = b }
                }
                Ok(ret.clone())
            }
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "min".to_string(),
        can_refer: false,
        body: |args| match args.as_slice() {
            [] => Err(NErr::TypeError("min: at least 1 arg".to_string())),
            [Obj::List(a)] => {
                let mut ret: &Obj = &a[0];
                for b in &a[1..] {
                    if ncmp(b, &ret)? == Ordering::Less { ret = b }
                }
                Ok(ret.clone())
            }
            [_] => Err(NErr::TypeError("min 1 not list".to_string())),
            [a, rest @ ..] => {
                let mut ret: &Obj = a;
                for b in rest {
                    if ncmp(b, &ret)? == Ordering::Less { ret = b }
                }
                Ok(ret.clone())
            }
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "print".to_string(),
        can_refer: false,
        body: |args| {
            println!("{}", args.iter().map(|arg| format!("{}", arg)).collect::<Vec<String>>().join(" "));
            Ok(Obj::Null)
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "echo".to_string(),
        can_refer: false,
        body: |args| {
            print!("{}", args.iter().map(|arg| format!("{}", arg)).collect::<Vec<String>>().join(" "));
            Ok(Obj::Null)
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "debug".to_string(),
        can_refer: false,
        body: |args| {
            println!("{}", args.iter().map(|arg| format!("{:?}", arg)).collect::<Vec<String>>().join(" "));
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
    env.insert_type(ObjType::Func);
    env.insert_type(ObjType::Type);
    env.insert_builtin(BasicBuiltin {
        name: "$".to_string(),
        can_refer: false,
        body: |args| {
            let mut acc = String::new();
            for arg in args {
                acc += format!("{}", arg).as_str();
            }
            Ok(Obj::String(Rc::new(acc)))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "upper".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::String(s) => Ok(Obj::String(Rc::new(s.to_uppercase()))),
            _ => Err(NErr::TypeError("upper: expected string".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "lower".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::String(s) => Ok(Obj::String(Rc::new(s.to_lowercase()))),
            _ => Err(NErr::TypeError("upper: expected string".to_string())),
        }
    });
    // unlike python these are true on empty string. hmm...
    env.insert_builtin(OneArgBuiltin {
        name: "is_upper".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::String(s) => Ok(Obj::from(s.chars().all(char::is_uppercase))),
            _ => Err(NErr::TypeError("is_upper: expected string".to_string())),
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "is_lower".to_string(),
        can_refer: false,
        body: |arg| match arg {
            Obj::String(s) => Ok(Obj::from(s.chars().all(char::is_lowercase))),
            _ => Err(NErr::TypeError("is_upper: expected string".to_string())),
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "join".to_string(),
        can_refer: false,
        body: |mut a, b| {
            // this might coerce too hard but idk
            let mut acc = String::new();
            let mut started = false;
            for arg in mut_obj_into_iter(&mut a, "join")? {
                if started {
                    acc += format!("{}", b).as_str();
                }
                acc += format!("{}", arg).as_str();
                started = true;
            }
            Ok(Obj::String(Rc::new(acc)))
        }
    });
    env.insert_builtin(BasicBuiltin {
        name: "split".to_string(),
        can_refer: false,
        body: |args| {
            match few2(args) {
                Few2::One(Obj::String(s)) => Ok(Obj::List(Rc::new(s.split_whitespace().map(|w| Obj::String(Rc::new(w.to_string()))).collect()))),
                Few2::Two(Obj::String(s), Obj::String(t)) => Ok(Obj::List(Rc::new(s.split(&*t).map(|w| Obj::String(Rc::new(w.to_string()))).collect()))),
                _ => Err(NErr::ArgumentError("split :(".to_string())),
            }
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

    // Lists
    env.insert_builtin(TwoArgBuiltin {
        name: "++".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::List(mut a), Obj::List(mut b)) => {
                Rc::make_mut(&mut a).append(Rc::make_mut(&mut b));
                Ok(Obj::List(a))
            }
            _ => Err(NErr::ArgumentError("++: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ".+".to_string(),
        can_refer: false,
        body: |a, b| match b {
            Obj::List(mut b) => {
                Rc::make_mut(&mut b).insert(0, a);
                Ok(Obj::List(b))
            }
            _ => Err(NErr::ArgumentError(".+: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "+.".to_string(),
        can_refer: false,
        body: |a, b| match a {
            Obj::List(mut a) => {
                Rc::make_mut(&mut a).push(b);
                Ok(Obj::List(a))
            }
            _ => Err(NErr::ArgumentError("+.: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "..".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::List(Rc::new(vec![a, b])))
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "=>".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::List(Rc::new(vec![a, b])))
    });
    env.insert_builtin(CartesianProduct {});
    env.insert_builtin(OneArgBuiltin {
        name: "first".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::List(v) => match v.first() {
                Some(x) => Ok(x.clone()),
                None => Err(NErr::IndexError("first: no such index".to_string())),
            }
            _ => Err(NErr::ArgumentError("first: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "second".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::List(v) => match v.get(1) {
                Some(x) => Ok(x.clone()),
                None => Err(NErr::IndexError("second: no such index".to_string())),
            }
            _ => Err(NErr::ArgumentError("second: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "third".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::List(v) => match v.get(2) {
                Some(x) => Ok(x.clone()),
                None => Err(NErr::IndexError("third: no such index".to_string())),
            }
            _ => Err(NErr::ArgumentError("third: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "last".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::List(v) => match v.last() {
                Some(x) => Ok(x.clone()),
                None => Err(NErr::IndexError("last: no such index".to_string())),
            }
            _ => Err(NErr::ArgumentError("last: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "sort".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::List(mut v) => {
                // ????
                Rc::make_mut(&mut v).sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
                Ok(Obj::List(v))
            }
            _ => Err(NErr::ArgumentError("sort: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "reverse".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::List(mut v) => {
                Rc::make_mut(&mut v).reverse();
                Ok(Obj::List(v))
            }
            _ => Err(NErr::ArgumentError("sort: unrecognized argument types".to_string()))
        }
    });

    // Dicts
    env.insert_builtin(TwoArgBuiltin {
        name: "||".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Dict(mut a, d), Obj::Dict(mut b, _)) => {
                Rc::make_mut(&mut a).extend(Rc::make_mut(&mut b).drain());
                Ok(Obj::Dict(a, d))
            }
            _ => Err(NErr::ArgumentError("||: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "|.".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Dict(mut a, d), b) => {
                Rc::make_mut(&mut a).insert(to_key(b)?, Obj::Null);
                Ok(Obj::Dict(a, d))
            }
            _ => Err(NErr::ArgumentError("|.: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "|..".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Dict(mut a, d), Obj::List(b)) => match b.as_slice() {
                [k, v] => {
                    // TODO could take b theoretically, but, pain
                    Rc::make_mut(&mut a).insert(to_key(k.clone())?, v.clone());
                    Ok(Obj::Dict(a, d))
                }
                _ => Err(NErr::ArgumentError("|..: RHS must be pair".to_string()))
            }
            _ => Err(NErr::ArgumentError("|..: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "&&".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::Dict(mut a, d), Obj::Dict(b, _)) => {
                Rc::make_mut(&mut a).retain(|k, _| b.contains_key(k));
                Ok(Obj::Dict(a, d))
            }
            _ => Err(NErr::ArgumentError("&&: unrecognized argument types".to_string()))
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "set".to_string(),
        can_refer: false,
        body: |mut a| {
            Ok(Obj::Dict(Rc::new(mut_obj_into_iter(&mut a, "set conversion")?.map(|k| Ok((to_key(k)?, Obj::Null))).collect::<NRes<HashMap<ObjKey,Obj>>>()?), None))
        }
    });

    // TODO safety, wasm version
    env.insert_builtin(BasicBuiltin {
        name: "input".to_string(),
        can_refer: false,
        body: |args| if args.is_empty() {
            let mut input = String::new();
            match io::stdin().read_line(&mut input) {
                Ok(_) => Ok(Obj::from(input)),
                Err(msg) => Err(NErr::ValueError(format!("input failed: {}", msg))),
            }
        } else {
            Err(NErr::ArgumentError("input: unrecognized argument types".to_string()))
        }
    });

    // TODO safety, wasm version
    env.insert_builtin(OneArgBuiltin {
        name: "read_file".to_string(),
        can_refer: false,
        body: |a| match a {
            Obj::String(s) => match fs::read_to_string(&*s) {
                Ok(c) => Ok(Obj::String(Rc::new(c))),
                // TODO fix error type
                Err(e) => Err(NErr::ValueError(format!("read_file error: {}", e))),
            }
            _ => Err(NErr::ArgumentError("read_file: unrecognized argument types".to_string()))
        }
    });
}
