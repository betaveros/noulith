#[macro_use] extern crate lazy_static;

// TODO: isolate
use std::fs;

use std::cmp::Ordering;
use std::fmt;
use std::fmt::Display;
use std::fmt::Debug;
use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use std::cell::RefCell;

use num::complex::Complex64;
use num::bigint::BigInt;

mod nnum;
mod gamma;

use crate::nnum::NNum;
use crate::nnum::NTotalNum;


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

#[derive(Debug, Clone)]
pub enum Obj {
    Null,
    Num(NNum),
    // Float(f64),
    String(Rc<String>),
    List(Rc<Vec<Obj>>),
    Dict(Rc<HashMap<ObjKey, Obj>>, Option<Rc<Obj>>), // default value
    Func(Func),
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
            Obj::Func(_) => true,
        }
    }
}

impl From<bool> for Obj {
    fn from(n: bool) -> Self { Obj::Num(NNum::iverson(n)) }
}
impl From<char> for Obj {
    fn from(n: char) -> Self { Obj::String(Rc::new(n.to_string())) }
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
        Obj::Func(_) => Err(NErr::TypeError("Using a function as a dictionary key isn't supported".to_string())),
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
                    write!(formatter, "{}: {}", k, v)?;
                }
                write!(formatter, "}}")
            }
            Obj::Func(f) => write!(formatter, "{:?}", f),
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
        _ => Err(NErr::TypeError("no".to_string())),
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

fn mut_obj_into_iter(obj: &mut Obj) -> NRes<MutObjIntoIter<'_>> {
    match obj {
        Obj::List(v) => Ok(MutObjIntoIter::List(mut_rc_vec_into_iter(v))),
        Obj::Dict(v, _) => Ok(MutObjIntoIter::Dict(mut_rc_hash_map_into_iter(v))),
        Obj::String(s) => Ok(MutObjIntoIter::String(s.chars())),
        _ => Err(NErr::TypeError("no".to_string())),
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

fn mut_obj_into_iter_pairs(obj: &mut Obj) -> NRes<MutObjIntoIterPairs<'_>> {
    match obj {
        Obj::List(v) => Ok(MutObjIntoIterPairs::List(0, mut_rc_vec_into_iter(v))),
        Obj::Dict(v, _) => Ok(MutObjIntoIterPairs::Dict(mut_rc_hash_map_into_iter(v))),
        Obj::String(s) => Ok(MutObjIntoIterPairs::String(0, s.chars())),
        _ => Err(NErr::TypeError("no".to_string())),
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
        }
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match self {
            Func::Builtin(b) => b.try_chain(other),
            Func::Closure(_) => None,
            Func::PartialApp1(..) => None,
            Func::PartialApp2(..) => None,
            Func::Composition(..) => None,
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
                ))),
                Few::Many(args) => {
                    for i in 0 .. args.len() - 1 {
                        if !(self.accept)(ncmp(&args[i], &args[i+1])?) {
                            return Ok(Obj::from(0))
                        }
                    }
                    Ok(Obj::from(1))
                }
            }
        } else {
            if self.chained.len() + 2 == args.len() {
                if !(self.accept)(ncmp(&args[0], &args[1])?) {
                    return Ok(Obj::from(0))
                }
                for i in 0 .. self.chained.len() {
                    let res = self.chained[i].run(vec![args[i+1].clone(), args[i+2].clone()])?;
                    if !res.truthy() {
                        return Ok(res)
                    }
                }
                Ok(Obj::from(1))
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
                (Obj::Func(f), None) => {
                    func = Some(f.clone());
                }
                (Obj::Func(_), Some(_)) => Err(NErr::ArgumentError("zip: more than one function".to_string()))?,
                (arg, _) => iterators.push(mut_obj_into_iter(arg)?),
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
                "zip" => Some(Func::Builtin(Rc::new(self.clone()))),
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
                )))
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
                )))
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
        assign_all(&mut ee.borrow_mut(), &p, AssignRHSes::Assign(true, &args))?;
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
    Declare,
    Pop,
    Remove,
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
pub enum Expr {
    IntLit(BigInt),
    StringLit(Rc<String>),
    Ident(String),
    Call(Box<Expr>, Vec<Box<Expr>>),
    List(Vec<Box<Expr>>),
    Dict(Option<Box<Expr>>, Vec<(Box<Expr>, Option<Box<Expr>>)>),
    Index(Box<Expr>, Box<Expr>), // TODO: or slice
    Chain(Box<Expr>, Vec<(String, Box<Expr>)>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Pop(Box<Lvalue>),
    Remove(Box<Lvalue>),
    Declare(Box<Lvalue>, Box<Expr>),
    Assign(Box<Lvalue>, Box<Expr>),
    OpAssign(Box<Lvalue>, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    For(Vec<ForIteration>, bool /* yield */, Box<Expr>),
    Sequence(Vec<Box<Expr>>),
    // these get cloned in particular
    Lambda(Rc<Vec<Box<Lvalue>>>, Rc<Expr>),

    // shouldn't stay in the tree:
    CommaSeq(Vec<Box<Expr>>),
    Splat(Box<Expr>),
}

#[derive(Debug)]
pub enum Lvalue {
    IndexedIdent(String, Vec<Box<Expr>>),
    CommaSeq(Vec<Box<Lvalue>>),
    Splat(Box<Lvalue>),
}

#[derive(Debug)]
enum EvaluatedLvalue {
    IndexedIdent(String, Vec<Obj>),
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
        Expr::CommaSeq(es) => Ok(Lvalue::CommaSeq(
            es.into_iter().map(|e| Ok(Box::new(to_lvalue(*e)?))).collect::<Result<Vec<Box<Lvalue>>, String>>()?
        )),
        Expr::Splat(x) => Ok(Lvalue::Splat(Box::new(to_lvalue(*x)?))),
        _ => Err(format!("can't to_lvalue {:?}", expr)),
    }
}

pub fn lex(code: &str) -> Vec<Token> {
    lazy_static! {
        static ref OPERATOR_SYMBOLS: HashSet<char> = "!#$%&*+-./:<=>?@^|~".chars().collect::<HashSet<char>>();
    }

    // let mut i: usize = 0;
    let mut tokens = Vec::new();
    let mut chars = code.chars().peekable();

    while let Some(c) = chars.next() {
        match c {
            '(' => tokens.push(Token::LeftParen),
            ')' => tokens.push(Token::RightParen),
            '[' => tokens.push(Token::LeftBracket),
            ']' => tokens.push(Token::RightBracket),
            '{' => tokens.push(Token::LeftBrace),
            '}' => tokens.push(Token::RightBrace),
            '\\' => tokens.push(Token::Lambda),
            ',' => tokens.push(Token::Comma),
            ';' => tokens.push(Token::Semicolon),
            ' ' => (),
            '\n' => (),
            '\'' | '"' => {
                let mut acc = String::new();
                while chars.peek() != Some(&c) {
                    match chars.next() {
                        Some('\\') => acc.push(chars.next().expect("lexing: string literal: escape eof")), // FIXME
                        Some(c) => acc.push(c),
                        None => panic!("lexing: string literal hit eof")
                    }
                }
                chars.next();
                tokens.push(Token::StringLit(Rc::new(acc)))
            }
            c => {
                if c.is_digit(10) {
                    let mut acc = c.to_string();

                    while let Some(cc) = chars.peek().filter(|d| d.is_digit(10)) {
                        acc.push(*cc);
                        chars.next();
                    }
                    tokens.push(Token::IntLit(acc.parse::<BigInt>().unwrap()))
                } else if c.is_alphabetic() {
                    let mut acc = c.to_string();

                    while let Some(cc) = chars.peek().filter(|c| c.is_alphanumeric() || **c == '_') {
                        acc.push(*cc);
                        chars.next();
                    }
                    tokens.push(match acc.as_str() {
                        "if" => Token::If,
                        "else" => Token::Else,
                        "for" => Token::For,
                        "yield" => Token::Yield,
                        "and" => Token::And,
                        "or" => Token::Or,
                        "pop" => Token::Pop,
                        "remove" => Token::Remove,
                        _ => Token::Ident(acc),
                    })
                } else if OPERATOR_SYMBOLS.contains(&c) {
                    // Most operators ending in = parse weird. It's hard to pop the last character
                    // off a String because of UTF-8 stuff so keep them separate until the last
                    // possible moment.
                    let mut last = c;
                    let mut acc = String::new();

                    while let Some(cc) = chars.peek().filter(|c| OPERATOR_SYMBOLS.contains(c)) {
                        acc.push(last);
                        last = *cc;
                        chars.next();
                    }
                    match (acc.as_str(), last) {
                        ("!" | "<" | ">" | "=", '=') => {
                            acc.push(last); tokens.push(Token::Ident(acc))
                        }
                        (":", '=') => tokens.push(Token::Declare),
                        ("", '=') => tokens.push(Token::Assign),
                        (_, '=') => {
                            tokens.push(Token::Ident(acc));
                            tokens.push(Token::Assign)
                        }
                        (_, _) => {
                            acc.push(last);
                            tokens.push(match acc.as_str() {
                                "&&" => Token::And,
                                "||" => Token::Or,
                                ":" => Token::Colon,
                                "::" => Token::DoubleColon,
                                "..." => Token::Ellipsis,
                                _ => Token::Ident(acc)
                            })
                        }
                    }
                }
            }
        }
    }
    tokens
}

struct Parser {
    tokens: Vec<Token>,
    i: usize,
}

impl Parser {

    fn peek(&self) -> Option<Token> {
        self.tokens.get(self.i).cloned()
    }

    fn advance(&mut self) {
        self.i += 1;
    }

    fn require(&mut self, expected: Token, message: String) -> Result<(), String> {
        let peeked = self.peek();
        if peeked.as_ref() != Some(&expected) { // wat
            Err(format!("{}; required {:?}, got {:?}", message, expected, peeked))
        } else {
            self.advance();
            Ok(())
        }
    }

    fn atom(&mut self) -> Result<Expr, String> {
        if let Some(token) = self.peek() {
            match token {
                Token::IntLit(n) => {
                    self.advance();
                    Ok(Expr::IntLit(n))
                }
                Token::StringLit(s) => {
                    self.advance();
                    Ok(Expr::StringLit(s))
                }
                Token::Ident(s) => {
                    self.advance();
                    Ok(Expr::Ident(s.to_string()))
                }
                Token::Ellipsis => {
                    self.advance();
                    Ok(Expr::Splat(Box::new(self.single()?)))
                }
                Token::Pop => {
                    self.advance();
                    Ok(Expr::Pop(Box::new(to_lvalue(self.operand()?)?)))
                }
                Token::Remove => {
                    self.advance();
                    Ok(Expr::Remove(Box::new(to_lvalue(self.operand()?)?)))
                }
                Token::LeftParen => {
                    self.advance();
                    let e = self.expression()?;
                    self.require(Token::RightParen, "normal parenthesized expr".to_string())?;
                    Ok(e)
                }
                Token::LeftBracket => {
                    self.advance();
                    let (exs, _) = self.comma_separated()?;
                    self.require(Token::RightBracket, "list expr".to_string())?;
                    Ok(Expr::List(exs))
                }
                Token::LeftBrace => {
                    self.advance();
                    // Dict(Vec<(Box<Expr>, Option<Box<Expr>>)>),
                    let mut xs = Vec::new();
                    let mut def = None;
                    if self.peek() == Some(Token::Colon) {
                        self.advance();
                        def = Some(Box::new(self.single()?));
                        if !self.peek_csc_stopper() {
                            self.require(Token::Comma, "dict expr".to_string())?;
                        }
                    }

                    while !self.peek_csc_stopper() {
                        let c1 = Box::new(self.single()?);
                        let c2 = if self.peek() == Some(Token::Colon) {
                            self.advance();
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
                Token::RightParen => Err("unexpected right paren".to_string()),
                Token::Lambda => {
                    self.advance();
                    let (params0, _) = self.comma_separated()?;
                    let params = params0.into_iter().map(|p| Ok(Box::new(to_lvalue(*p)?))).collect::<Result<Vec<Box<Lvalue>>, String>>()?;
                    self.require(Token::Colon, "lambda start".to_string())?;
                    let body = self.single()?;
                    Ok(Expr::Lambda(Rc::new(params), Rc::new(body)))
                }
                Token::If => {
                    self.advance();
                    self.require(Token::LeftParen, "if start".to_string())?;
                    let cond = self.expression()?;
                    self.require(Token::RightParen, "if cond end".to_string())?;
                    let body = self.assignment()?;
                    let else_body = if self.peek() == Some(Token::Else) {
                        self.advance(); Some(Box::new(self.assignment()?))
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
                            k => Err(format!("for: expected right paren or semicolon after iteration, got {:?}", k))?,
                        }
                    }
                    let do_yield = if self.peek() == Some(Token::Yield) {
                        self.advance(); true
                    } else {
                        false
                    };
                    let body = self.assignment()?;
                    Ok(Expr::For(its, do_yield, Box::new(body)))
                }
                _ => Err(format!("unexpected {:?}", token)),
            }
        } else {
            Err("atom: ran out of stuff to parse".to_string())
        }
    }

    fn for_iteration(&mut self) -> Result<ForIteration, String> {
        if self.peek() == Some(Token::If) {
            self.advance();
            Ok(ForIteration::Guard(Box::new(self.single()?)))
        } else {
            let pat0 = self.pattern()?;
            let pat = to_lvalue(pat0)?;
            let ty = match self.peek() {
                Some(Token::Colon) => ForIterationType::Normal,
                Some(Token::DoubleColon) => ForIterationType::Item,
                Some(Token::Declare) => ForIterationType::Declare,
                p => return Err(format!("for: require : or :: or :=, got {:?}", p)),
            };
            self.advance();
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
                    let c = self.single()?;
                    self.require(Token::RightBracket, "index expr".to_string())?;
                    cur = Expr::Index(Box::new(cur), Box::new(c));
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
            Some(Token::Declare) => true,
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
                            self.advance();
                            ops.push((op.to_string(), Box::new(self.operand()?)));
                        }
                        Ok(Expr::Chain(Box::new(op1), ops))
                    }
                }
                _ => {
                    let ret = Expr::Call(Box::new(op1), vec![Box::new(second)]);
                    if !self.peek_chain_stopper() {
                        Err(format!("saw non-identifier in operator position: these chains must be short, got {:?} after", self.peek()))
                    } else {
                        Ok(ret)
                    }
                }
            }
        }
    }

    fn logic_and(&mut self) -> Result<Expr, String> {
        let mut op1 = self.chain()?;
        while self.peek() == Some(Token::And) {
            self.advance();
            op1 = Expr::And(Box::new(op1), Box::new(self.chain()?));
        }
        Ok(op1)
    }

    fn single(&mut self) -> Result<Expr, String> {
        let mut op1 = self.logic_and()?;
        while self.peek() == Some(Token::Or) {
            self.advance();
            op1 = Expr::Or(Box::new(op1), Box::new(self.logic_and()?));
        }
        Ok(op1)
    }

    // No semicolons allowed, but can be empty. List literals; function declarations; LHSes of
    // assignments. Not for function calls, I think? f(x; y) might actually be ok...
    // bool is whether a comma was found, to distinguish (x) from (x,)
    fn comma_separated(&mut self) -> Result<(Vec<Box<Expr>>, bool), String> {
        if self.peek_csc_stopper() {
            return Ok((Vec::new(), false));
        }

        let mut xs = vec![Box::new(self.single()?)];
        let mut comma = false;
        while self.peek() == Some(Token::Comma) {
            self.i += 1;
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
            (Few::Zero, _) => Err("Expected pattern, got nothing".to_string()),
            (Few::One(ex), false) => Ok(*ex),
            (Few::One(ex), true) => Ok(Expr::CommaSeq(vec![ex])),
            (Few::Many(exs), _) => Ok(Expr::CommaSeq(exs))
        }
    }

    fn assignment(&mut self) -> Result<Expr, String> {
        let pat = self.pattern()?;

        match self.peek() {
            Some(Token::Assign) => {
                self.advance();
                match pat {
                    Expr::Call(lhs, op) => match few(op) {
                        Few::One(op) => Ok(Expr::OpAssign(
                            Box::new(to_lvalue(*lhs)?),
                            Box::new(*op),
                            Box::new(self.pattern()?),
                        )),
                        _ => Err("call w not 1 arg is not assignop".to_string()),
                    }
                    _ => {
                        Ok(Expr::Assign(Box::new(to_lvalue(pat)?), Box::new(self.pattern()?)))
                    }
                }
            }
            Some(Token::Declare) => {
                self.advance();
                Ok(Expr::Declare(Box::new(to_lvalue(pat)?), Box::new(self.pattern()?)))
            }
            _ => Ok(pat)
        }
    }

    fn expression(&mut self) -> Result<Expr, String> {
        let mut ags = vec![Box::new(self.assignment()?)];

        while self.peek() == Some(Token::Semicolon) {
            self.i += 1;
            if self.peek() != None {
                ags.push(Box::new(self.assignment()?));
            }
        }

        Ok(Expr::Sequence(ags))
    }
}

pub fn parse(code: &str) -> Result<Expr, String> {
    let mut p = Parser { tokens: lex(code), i: 0 };
    p.expression()
}

#[derive(Debug)]
pub struct Env {
    vars: HashMap<String, Obj>,
    parent: Option<Rc<RefCell<Env>>>,
}
impl Env {
    pub fn new() -> Env {
        Env { vars: HashMap::new(), parent: None }
    }
    fn with_parent(env: &Rc<RefCell<Env>>) -> Rc<RefCell<Env>> {
        Rc::new(RefCell::new(
            Env { vars: HashMap::new(), parent: Some(Rc::clone(&env)) }
        ))
    }
    fn get_var(self: &Env, s: &str) -> NRes<Obj> {
        match self.vars.get(s) {
            Some(v) => Ok(v.clone()),
            None => match &self.parent {
                Some(p) => p.borrow().get_var(s),
                None => Err(NErr::NameError(format!("No such variable: {}", s))),
            }
        }
    }

    fn modify_existing_var(self: &mut Env, key: &str, f: impl FnOnce(&mut Obj) -> ()) -> bool {
        match self.vars.get_mut(key) {
            Some(target) => { f(target); true }
            None => match &self.parent {
                Some(p) => p.borrow_mut().modify_existing_var(key, f),
                None => false,
            }
        }
    }
    fn set_existing_var(self: &mut Env, key: String, val: Obj) -> bool {
        self.modify_existing_var(&key, |target| {
            *target = val
        })
    }
    fn insert(self: &mut Env, key: String, val: Obj) -> Option<Obj> {
        self.vars.insert(key, val)
    }
    fn insert_builtin(self: &mut Env, b: impl Builtin + 'static) {
        self.insert(b.builtin_name().to_string(), Obj::Func(Func::Builtin(Rc::new(b))));
    }
}

// bool: declare if true, assign if false
#[derive(Debug)]
enum AssignRHS<'a> { DeclareNull, Assign(bool, &'a Obj) }
#[derive(Debug)]
enum AssignRHSes<'a> { DeclareNull, Assign(bool, &'a[Obj])}

fn assign_all_basic(env: &mut Env, lhs: &[Box<EvaluatedLvalue>], rhs: AssignRHSes<'_>) -> NRes<()> {
    match rhs {
        AssignRHSes::DeclareNull => {
            for lhs1 in lhs.iter() {
                assign(env, lhs1, AssignRHS::DeclareNull)?;
            }
            Ok(())
        }
        AssignRHSes::Assign(d, rhs) => {
            if lhs.len() == rhs.len() {
                for (lhs1, rhs1) in lhs.iter().zip(rhs.iter()) {
                    assign(env, lhs1, AssignRHS::Assign(d, rhs1))?;
                }
                Ok(())
            } else {
                Err(NErr::ValueError(format!("Can't unpack into mismatched length {:?} {} != {:?} {}", lhs, lhs.len(), rhs, rhs.len())))
            }
        }
    }
}

fn assign_all(env: &mut Env, lhs: &[Box<EvaluatedLvalue>], rhs: AssignRHSes<'_>) -> NRes<()> {
    // still detect bad splatting even if DeclareNull
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
        Some((si, inner)) => match rhs {
            AssignRHSes::DeclareNull => {
                assign_all_basic(env, &lhs[..si], AssignRHSes::DeclareNull)?;
                assign(env, inner, AssignRHS::DeclareNull)?;
                assign_all_basic(env, &lhs[si + 1..], AssignRHSes::DeclareNull)
            }
            AssignRHSes::Assign(d, rhs) => {
                assign_all_basic(env, &lhs[..si], AssignRHSes::Assign(d, &rhs[..si]))?;
                assign(env, inner, AssignRHS::Assign(d, &Obj::List(Rc::new(rhs[si..rhs.len() - lhs.len() + si + 1].to_vec()))))?;
                assign_all_basic(env, &lhs[si + 1..], AssignRHSes::Assign(d, &rhs[rhs.len() - lhs.len() + si + 1..]))
            }
        }
        None => assign_all_basic(env, lhs, rhs),
    }
}

fn set_index(lhs: &mut Obj, indexes: &[Obj], value: Obj) -> NRes<()> {
    match (lhs, indexes) {
        (lhs, []) => { *lhs = value; Ok(()) }
        (Obj::List(v), [i, rest @ ..]) => {
            set_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, value)
        }
        (Obj::Dict(v, _), [kk, rest @ ..]) => {
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
                }, rest, value)
            }
        }
        (lhs, ii) => Err(NErr::TypeError(format!("can't index {:?} {:?}", lhs, ii))),
    }
}

fn modify_existing_index(lhs: &mut Obj, indexes: &[Obj], f: impl FnOnce(&mut Obj) -> NRes<Obj>) -> NRes<Obj> {
    match indexes.split_first() {
        None => f(lhs),
        Some((i, rest)) => {
            match (lhs, i) {
                (Obj::List(v), i) => {
                    modify_existing_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, f)
                }
                (Obj::Dict(v, def), kk) => {
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

fn assign(env: &mut Env, lhs: &EvaluatedLvalue, rhs: AssignRHS<'_>) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::IndexedIdent(s, ixs) => match rhs {
            AssignRHS::DeclareNull => {
                if ixs.is_empty() {
                    if env.insert(s.to_string(), Obj::Null).is_some() {
                        // TODO error
                        Err(NErr::TypeError(format!("Declaring variable that already exists: {:?}", s)))
                    } else {
                        Ok(())
                    }
                } else {
                    Err(NErr::TypeError(format!("Can't insert new value into index expression on nonexistent variable: {:?} {:?}", s, ixs)))
                }
            }
            AssignRHS::Assign(true, rhs) => {
                if ixs.is_empty() {
                    if env.insert(s.to_string(), rhs.clone()).is_some() {
                        // TODO error
                        Err(NErr::TypeError(format!("Declaring/assigning variable that already exists: {:?}", s)))
                    } else {
                        Ok(())
                    }
                } else {
                    return Err(NErr::TypeError(format!("Can't insert new value into index expression on nonexistent variable: {:?} {:?}", s, ixs)))
                }
            }
            AssignRHS::Assign(false, rhs) => {
                if ixs.is_empty() {
                    if env.set_existing_var(s.to_string(), rhs.clone()) {
                        Ok(())
                    } else {
                        Err(NErr::NameError(format!("Variable {:?} not found (use := to declare)", s)))?
                    }
                } else {
                    let mut ret = Err(NErr::ValueError("TODO".to_string()));
                    if env.modify_existing_var(s, |v| {
                        ret = set_index(v, ixs, rhs.clone());
                    }) {
                        ret
                    } else {
                        Err(NErr::NameError(format!("Variable {:?} not found, couldn't set into index {:?}", s, ixs)))?
                    }
                }
            }
        }
        EvaluatedLvalue::CommaSeq(ss) => {
            match rhs {
                AssignRHS::DeclareNull => assign_all(env, ss, AssignRHSes::DeclareNull),
                AssignRHS::Assign(d, Obj::List(ls)) => assign_all(env, ss, AssignRHSes::Assign(d, ls)),
                _ => Err(NErr::TypeError(format!("Can't unpack non-list {:?}", rhs))),
            }
        }
        EvaluatedLvalue::Splat(_) => Err(NErr::TypeError(format!("Can't assign to raw splat {:?}", lhs))),
    }
}

fn precedence(name: &str) -> NRes<u8> {
    // stolen from Scala
    match name.chars().next() {
        None => Err(NErr::SyntaxError("Can't compute precedence of empty name (internal)".to_string())),
        Some(c) => Ok(
            if c.is_alphanumeric() || c == '_' {
                0
            } else {
                match c {
                    '|' => 1,
                    '^' => 2,
                    '&' => 3,
                    '=' | '!' => 4,
                    '<' | '>' => 5,
                    ':' => 6,
                    '+' | '-' => 7,
                    '*' | '/' | '%' => 8,
                    _ => 9,
                }
            }
        )
    }
}

struct ChainEvaluator {
    operands: Vec<Vec<Obj>>,
    operators: Vec<(Func, u8)>,
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

    fn give(&mut self, operator: Func, precedence: u8, operand: Obj) -> NRes<()> {
        while self.operators.last().map_or(false, |t| t.1 >= precedence) {
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

fn eval_lvalue(env: &Rc<RefCell<Env>>, expr: &Lvalue) -> NRes<EvaluatedLvalue> {
    match expr {
        Lvalue::IndexedIdent(s, v) => Ok(EvaluatedLvalue::IndexedIdent(
            s.to_string(),
            v.iter().map(|e| Ok(evaluate(env, e)?)).collect::<NRes<Vec<Obj>>>()?
        )),
        Lvalue::CommaSeq(v) => Ok(EvaluatedLvalue::CommaSeq(
            v.iter().map(|e| Ok(Box::new(eval_lvalue(env, e)?))).collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?
        )),
        Lvalue::Splat(v) => Ok(EvaluatedLvalue::Splat(Box::new(eval_lvalue(env, v)?))),
    }
}

fn pythonic_index(xs: &Vec<Obj>, i: &Obj) -> NRes<usize> {
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

fn index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, &ir) {
        (Obj::List(xx), ii) => Ok(xx[pythonic_index(xx, ii)?].clone()),
        (Obj::Dict(xx, def), _) => {
            let k = to_key(ir)?;
            match xx.get(&k) {
                Some(e) => Ok(e.clone()),
                None => match def {
                    Some(d) => Ok((&**d).clone()),
                    None => Err(NErr::KeyError(format!("Dictionary lookup: nothing at key {:?} {:?}", xx, k))),
                }
            }
        }
        _ => Err(NErr::TypeError(format!("can't index {:?} {:?}", xr, ir))),
    }
}

fn safe_index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, &ir) {
        (Obj::Null, _) => Ok(Obj::Null),
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
        Obj::Func(ff) => ff.run(args),
        f => match few(args) {
            Few::One(Obj::Func(f2)) => Ok(Obj::Func(Func::PartialApp1(Box::new(f2), Box::new(f)))),
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
                sr = index(sr, evaluate(env, ix)?)?.clone();
            }
            Ok(sr)
        },
        Lvalue::CommaSeq(v) => Ok(Obj::List(Rc::new(
            v.iter().map(|e| Ok(eval_lvalue_as_obj(env, e)?)).collect::<NRes<Vec<Obj>>>()?
        ))),
        // maybe if commaseq eagerly looks for splats...
        Lvalue::Splat(_) => Err(NErr::SyntaxError("Can't evaluate splat on LHS of assignment??".to_string())),
    }
}

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
            let ee = Env::with_parent(env);
            let p = eval_lvalue(&ee, lvalue)?;
            match ty {
                ForIterationType::Normal => {
                    assign(&mut ee.borrow_mut(), &p, AssignRHS::DeclareNull)?;

                    for x in mut_obj_into_iter(&mut itr)? {
                        // should assign take x
                        assign(&mut ee.borrow_mut(), &p, AssignRHS::Assign(false, &x))?;
                        evaluate_for(&ee, rest, body, callback)?;
                    }
                }
                ForIterationType::Item => {
                    assign(&mut ee.borrow_mut(), &p, AssignRHS::DeclareNull)?;

                    for (k, v) in mut_obj_into_iter_pairs(&mut itr)? {
                        // should assign take x
                        assign(&mut ee.borrow_mut(), &p, AssignRHS::Assign(false, &Obj::List(Rc::new(vec![key_to_obj(k), v]))))?;
                        evaluate_for(&ee, rest, body, callback)?;
                    }
                }
                ForIterationType::Declare => {
                    assign(&mut ee.borrow_mut(), &p, AssignRHS::Assign(true, &itr))?;

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
            let ir = evaluate(env, i)?;
            index(xr, ir)
        }
        Expr::Chain(op1, ops) => {
            let mut ev = ChainEvaluator::new(evaluate(env, op1)?);
            for (oper, opd) in ops {
                // make sure this borrow_mut goes out of scope
                let oprr = env.borrow_mut().get_var(oper)?;
                if let Obj::Func(b) = oprr {
                    let prec = precedence(oper)?;
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
        Expr::Assign(pat, rhs) => {
            let p = eval_lvalue(env, pat)?;
            let res = match &**rhs {
                Expr::CommaSeq(xs) => Ok(Obj::List(Rc::new(eval_seq(env, xs)?))),
                _ => evaluate(env, rhs),
            }?;
            assign(&mut env.borrow_mut(), &p, AssignRHS::Assign(false, &res))?;
            Ok(Obj::Null)
        }
        Expr::Declare(pat, rhs) => {
            let p = eval_lvalue(env, pat)?;
            let res = match &**rhs {
                Expr::CommaSeq(xs) => Ok(Obj::List(Rc::new(eval_seq(env, xs)?))),
                _ => evaluate(env, rhs),
            }?;
            assign(&mut env.borrow_mut(), &p, AssignRHS::Assign(true, &res))?;
            Ok(Obj::Null)
        }
        Expr::Pop(pat) => {
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => {
                    let mut popped = Err(NErr::TypeError("failed to pop??".to_string()));
                    env.borrow_mut().modify_existing_var(&s, |vv| {
                        popped = modify_existing_index(vv, &ixs, |x| match x {
                            Obj::List(xs) => {
                                Rc::make_mut(xs).pop().ok_or(NErr::NameError("can't pop empty".to_string()))
                            }
                            _ => Err(NErr::TypeError("can't pop".to_string())),
                        });
                    });
                    popped
                }
                _ => Err(NErr::TypeError("can't pop, weird pattern".to_string())),
            }
        }
        Expr::Remove(pat) => {
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => match ixs.as_slice() {
                    [] => Err(NErr::ValueError("can't remove flat identifier".to_string())),
                    [rest @ .., last_i] => {
                        let mut removed = Err(NErr::TypeError("failed to remove??".to_string()));
                        env.borrow_mut().modify_existing_var(&s, |vv| {
                            removed = modify_existing_index(vv, &rest, |x| match (x, last_i) {
                                (Obj::List(xs), i) => {
                                    let ii = pythonic_index(xs, i)?;
                                    Ok(Rc::make_mut(xs).remove(ii))
                                }
                                (Obj::Dict(xs, _), i) => {
                                    Rc::make_mut(xs).remove(&to_key(i.clone())?).ok_or(NErr::KeyError("key not found in dict".to_string()))
                                }
                                _ => Err(NErr::TypeError("can't remove".to_string())),
                            });
                        });
                        removed
                    }
                }
                _ => Err(NErr::TypeError("can't pop, weird pattern".to_string())),
            }
        }
        Expr::OpAssign(pat, op, rhs) => {
            let pv = eval_lvalue_as_obj(env, pat)?;
            let p = eval_lvalue(env, pat)?;
            let opv = evaluate(env, op)?;

            match opv {
                Obj::Func(ff) => {
                    let res = match &**rhs {
                        Expr::CommaSeq(xs) => Ok(Obj::List(Rc::new(eval_seq(env, xs)?))),
                        _ => evaluate(env, rhs),
                    }?;
                    if !ff.can_refer() {
                        // Drop the Rc from the lvalue so that pure functions can try to consume it
                        assign(&mut env.borrow_mut(), &p, AssignRHS::Assign(false, &Obj::Null))?;
                    }
                    let fres = ff.run(vec![pv, res])?;
                    assign(&mut env.borrow_mut(), &p, AssignRHS::Assign(false, &fres))?;
                    Ok(Obj::Null)
                }
                _ => Err(NErr::TypeError(format!("Operator assignment: operator is not function {:?}", opv))),
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
                Some(de) => Some(Rc::new(evaluate(env, de)?)),
                None => None,
            };
            let mut acc = HashMap::new();
            for (ke, ve) in xs {
                match (&**ke, ve) {
                    (Expr::Splat(inner), None) => {
                        let mut res = evaluate(env, inner)?;
                        let it = mut_obj_into_iter_pairs(&mut res)?;
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
                            None => Obj::from(1),
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
            })))
        }
    }
}

pub fn simple_eval(code: &str) -> Obj {
    let mut env = Env::new();
    initialize(&mut env);

    let e = Rc::new(RefCell::new(env));
    evaluate(&e, &parse(code).unwrap()).unwrap()
}

pub fn initialize(env: &mut Env) {
    env.insert_builtin(NumsBuiltin {
        name: "+".to_string(),
        body: |args| { Ok(Obj::Num(args.into_iter().sum())) },
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
        name: "add".to_string(),
        body: |a, b| { Ok(Obj::Num(a + b)) }
    });
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
            for x in mut_obj_into_iter(&mut arg)? {
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
            for x in mut_obj_into_iter(&mut arg)? {
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
    env.insert_builtin(TwoNumsBuiltin {
        name: "til".to_string(),
        body: |a, b| {
            let n1 = into_bigint_ok(a)?;
            let n2 = into_bigint_ok(b)?;
            // TODO: should be lazy
            Ok(Obj::List(Rc::new(num::range(n1, n2).map(|x| Obj::Num(NNum::from(x))).collect())))
        }
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "to".to_string(),
        body: |a, b| {
            let n1 = into_bigint_ok(a)?;
            let n2 = into_bigint_ok(b)?;
            // TODO: should be lazy
            Ok(Obj::List(Rc::new(num::range_inclusive(n1, n2).map(|x| Obj::Num(NNum::from(x))).collect())))
        }
    });
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
        name: ">>".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::Func(f), Obj::Func(g)) => Ok(Obj::Func(Func::Composition(Box::new(g), Box::new(f)))),
            _ => Err(NErr::TypeError(">>: not function".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "<<".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::Func(f), Obj::Func(g)) => Ok(Obj::Func(Func::Composition(Box::new(f), Box::new(g)))),
            _ => Err(NErr::TypeError("<<: not function".to_string()))
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "map".to_string(),
        can_refer: true,
        body: |mut a, b| {
            let it = mut_obj_into_iter(&mut a)?;
            match b {
                Obj::Func(b) => Ok(Obj::List(Rc::new(
                    it.map(|e| b.run(vec![e])).collect::<NRes<Vec<Obj>>>()?
                ))),
                _ => Err(NErr::TypeError("map: not callable".to_string()))
            }
        }
    });
    env.insert_builtin(OneArgBuiltin {
        name: "flatten".to_string(),
        can_refer: false,
        body: |mut a| {
            let mut acc = Vec::new();
            for mut e in mut_obj_into_iter(&mut a)? {
                for k in mut_obj_into_iter(&mut e)? {
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
            let it = mut_obj_into_iter(&mut a)?;
            match b {
                Obj::Func(b) => {
                    let mut acc = Vec::new();
                    for e in it {
                        let mut r = b.run(vec![e])?;
                        for k in mut_obj_into_iter(&mut r)? {
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
            let it = mut_obj_into_iter(&mut a)?;
            match b {
                Obj::Func(b) => {
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
            let it = mut_obj_into_iter(&mut a)?;
            match b {
                Obj::Func(b) => {
                    let mut acc = Vec::new();
                    for e in it {
                        if !b.run(vec![e.clone()])?.truthy() {
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
        name: "fold".to_string(),
        can_refer: true,
        body: |mut a, b| {
            let mut it = mut_obj_into_iter(&mut a)?;
            match b {
                Obj::Func(b) => {
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
        name: "debug".to_string(),
        can_refer: false,
        body: |args| {
            println!("{}", args.iter().map(|arg| format!("{:?}", arg)).collect::<Vec<String>>().join(" "));
            Ok(Obj::Null)
        }
    });
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
            for arg in mut_obj_into_iter(&mut a)? {
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
        name: "->".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::List(Rc::new(vec![a, b])))
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "<-".to_string(),
        can_refer: false,
        body: |a, b| Ok(Obj::List(Rc::new(vec![b, a])))
    });
    env.insert_builtin(CartesianProduct {});
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
