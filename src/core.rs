// TODO: isolate
use std::fs;
use std::io;
use std::io::{BufRead, Write};

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::hash::{Hash, Hasher};

use num::bigint::BigInt;
use num::complex::Complex64;
use num::BigRational;
use num::ToPrimitive;

use crate::few::*;
use crate::iter::*;
use crate::lex::*;

use crate::nint::NInt;
use crate::nnum::NNum;
use crate::rc::*;

// The fundamental unitype and all its types...
#[derive(Debug, Clone)]
pub enum Obj {
    Null,
    Num(NNum),
    Seq(Seq),
    Func(Func, Precedence),
    Instance(Struct, Vec<Obj>),
}

// Sequences produce NRes<Obj> when iterated over.
#[derive(Debug, Clone)]
pub enum Seq {
    String(Rc<String>),
    List(Rc<Vec<Obj>>),
    Dict(Rc<HashMap<ObjKey, Obj>>, Option<Box<Obj>>), // default value
    Vector(Rc<Vec<NNum>>),
    Bytes(Rc<Vec<u8>>),
    Stream(Rc<dyn Stream>),
}

impl Seq {
    pub fn is_empty(&self) -> bool {
        match self {
            Seq::String(x) => x.is_empty(),
            Seq::List(x) => x.is_empty(),
            Seq::Dict(x, _) => x.is_empty(),
            Seq::Vector(x) => x.is_empty(),
            Seq::Bytes(x) => x.is_empty(),
            Seq::Stream(x) => x.len() == Some(0),
        }
    }
    pub fn len(&self) -> Option<usize> {
        match self {
            Seq::List(d) => Some(d.len()),
            Seq::String(d) => Some(d.len()),
            Seq::Dict(d, _) => Some(d.len()),
            Seq::Vector(v) => Some(v.len()),
            Seq::Bytes(v) => Some(v.len()),
            Seq::Stream(v) => v.len(),
        }
    }
}

pub fn pythonic_index_isize<T>(xs: &[T], n: isize) -> NRes<usize> {
    if n >= 0 && n < (xs.len() as isize) {
        return Ok(n as usize);
    }

    let i2 = (n + (xs.len() as isize)) as usize;
    if i2 < xs.len() {
        return Ok(i2);
    }

    Err(NErr::index_error(format!(
        "Index out of bounds for len {}: {}",
        xs.len(),
        n
    )))
}

pub fn obj_to_isize_slice_index(x: Option<&Obj>) -> NRes<Option<isize>> {
    match x {
        None => Ok(None),
        Some(Obj::Num(n)) => Ok(Some(n.to_isize().ok_or(NErr::index_error(format!(
            "Slice index out of bounds of isize or non-integer: {:?}",
            n
        )))?)),
        Some(x) => Err(NErr::index_error(format!(
            "Invalid (non-numeric) slice index: {}",
            FmtObj::debug(x)
        ))),
    }
}

pub fn pythonic_slice_obj<T>(xs: &[T], lo: Option<&Obj>, hi: Option<&Obj>) -> NRes<(usize, usize)> {
    let lo = obj_to_isize_slice_index(lo)?;
    let hi = obj_to_isize_slice_index(hi)?;
    Ok(pythonic_slice(xs, lo, hi))
}

// for slicing
pub fn clamped_pythonic_index<T>(xs: &[T], i: isize) -> usize {
    if i >= 0 {
        return (i as usize).min(xs.len());
    }

    let i2 = i + (xs.len() as isize);
    if i2 < 0 {
        0
    } else {
        i2 as usize
    }
}

pub fn pythonic_index<T>(xs: &[T], i: &Obj) -> NRes<usize> {
    match i {
        Obj::Num(ii) => match ii.to_isize() {
            Some(n) => pythonic_index_isize(xs, n),
            _ => Err(NErr::index_error(format!(
                "Index out of bounds of isize or non-integer: {:?}",
                ii
            ))),
        },
        _ => Err(NErr::index_error(format!(
            "Invalid (non-numeric) index: {}",
            FmtObj::debug(i)
        ))),
    }
}

pub fn pythonic_mut<'a, 'b>(xs: &'a mut Vec<Obj>, i: &'b Obj) -> NRes<&'a mut Obj> {
    let ii = pythonic_index(xs, i)?;
    Ok(&mut xs[ii])
}

pub fn pythonic_slice<T>(xs: &[T], lo: Option<isize>, hi: Option<isize>) -> (usize, usize) {
    let clo = match lo {
        Some(lo) => clamped_pythonic_index(xs, lo),
        None => 0,
    };
    let chi = match hi {
        Some(hi) => clamped_pythonic_index(xs, hi),
        None => xs.len(),
    };
    (clo, chi.max(clo))
}

// to support Rc<dyn Stream>, can't have Clone, because
// https://doc.rust-lang.org/reference/items/traits.html#object-safety
//
// more using this as "lazy, possibly infinite list" rn i.e. trying to support indexing etc.
pub trait Stream: Iterator<Item = NRes<Obj>> + Display + Debug + MaybeSync + MaybeSend {
    fn peek(&self) -> Option<NRes<Obj>>;
    fn clone_box(&self) -> Box<dyn Stream>;
    // FIXME: this used to mean "length or infinity" but it increasingly looks like we actually
    // want streams where we can't determine their length by inspection, so this type doesn't make
    // sense any more. is it NErr<usize>? Option<NErr<usize>>?
    fn len(&self) -> Option<usize> {
        let mut s = self.clone_box();
        let mut ret = 0;
        while let Some(_) = s.next() {
            ret += 1;
        }
        Some(ret)
    }
    fn force(&self) -> NRes<Vec<Obj>> {
        self.clone_box().collect()
    }
    fn pythonic_index_isize(&self, i0: isize) -> NRes<Obj> {
        let mut i = i0;
        if i >= 0 {
            let mut it = self.clone_box();
            while let Some(e) = it.next() {
                if i == 0 {
                    return e;
                }
                i -= 1;
            }
            Err(NErr::index_error(format!("Index out of bounds: {}", i0)))
        } else {
            let mut v = self.force()?;
            let i2 = (i + (v.len() as isize)) as usize;
            if i2 < v.len() {
                Ok(v.swap_remove(i2))
            } else {
                Err(NErr::index_error(format!("Index out of bounds: {}", i0)))
            }
        }
    }
    fn pythonic_slice(&self, lo: Option<isize>, hi: Option<isize>) -> NRes<Seq> {
        let lo = lo.unwrap_or(0);
        match (lo, hi) {
            (lo, None) if lo >= 0 => {
                let mut it = self.clone_box();
                for _ in 0..lo {
                    if it.next().is_none() {
                        return Ok(Seq::Stream(Rc::from(it)));
                    }
                }
                Ok(Seq::Stream(Rc::from(it)))
            }
            (lo, Some(hi)) if lo >= 0 && hi >= 0 => {
                let mut it = self.clone_box();
                let mut v = Vec::new();
                for _ in 0..lo {
                    match it.next() {
                        Some(_) => {}
                        None => break,
                    }
                }
                for _ in lo..hi {
                    match it.next() {
                        Some(x) => v.push(x?),
                        None => break,
                    }
                }
                Ok(Seq::List(Rc::new(v)))
            }
            (lo, hi) => {
                let mut v = self.force()?;
                let (lo, hi) = pythonic_slice(v.as_slice(), Some(lo), hi);
                Ok(Seq::List(Rc::new(v.drain(lo..hi).collect())))
            }
        }
    }
    fn reversed(&self) -> NRes<Seq> {
        let mut xs = self.force()?;
        xs.reverse();
        Ok(Seq::List(Rc::new(xs)))
    }
}

// Sequences: iterators
pub enum ObjToCloningIter<'a> {
    List(std::slice::Iter<'a, Obj>),
    Dict(std::collections::hash_map::Iter<'a, ObjKey, Obj>),
    String(std::str::Chars<'a>),
    Vector(std::slice::Iter<'a, NNum>),
    Bytes(std::slice::Iter<'a, u8>),
    Stream(Box<dyn Stream>),
}

pub fn seq_to_cloning_iter(seq: &Seq) -> ObjToCloningIter<'_> {
    match seq {
        Seq::List(v) => ObjToCloningIter::List(v.iter()),
        Seq::Dict(v, _) => ObjToCloningIter::Dict(v.iter()),
        Seq::String(s) => ObjToCloningIter::String(s.chars()),
        Seq::Vector(v) => ObjToCloningIter::Vector(v.iter()),
        Seq::Bytes(v) => ObjToCloningIter::Bytes(v.iter()),
        Seq::Stream(v) => ObjToCloningIter::Stream(v.clone_box()),
    }
}

pub fn obj_to_cloning_iter<'a, 'b>(obj: &'a Obj, purpose: &'b str) -> NRes<ObjToCloningIter<'a>> {
    match obj {
        Obj::Seq(s) => Ok(seq_to_cloning_iter(s)),
        _ => Err(NErr::type_error(format!("{}; not iterable", purpose))),
    }
}

impl Iterator for ObjToCloningIter<'_> {
    type Item = NRes<Obj>;

    fn next(&mut self) -> Option<NRes<Obj>> {
        match self {
            ObjToCloningIter::List(it) => it.next().cloned().map(Ok),
            ObjToCloningIter::Dict(it) => Some(Ok(key_to_obj(it.next()?.0.clone()))),
            ObjToCloningIter::String(it) => Some(Ok(Obj::from(it.next()?))),
            ObjToCloningIter::Vector(it) => Some(Ok(Obj::Num(it.next()?.clone()))),
            ObjToCloningIter::Bytes(it) => Some(Ok(Obj::u8(*it.next()?))),
            ObjToCloningIter::Stream(it) => it.next(),
        }
    }
}

// iterates over elements of lists, or just keys of dictionaries (as if they were sets)
pub enum MutObjIntoIter<'a> {
    List(RcVecIter<'a, Obj>),
    Dict(RcHashMapIter<'a, ObjKey, Obj>),
    String(RcStringIter<'a>),
    Vector(RcVecIter<'a, NNum>),
    Bytes(RcVecIter<'a, u8>),
    Stream(&'a mut Rc<dyn Stream>),
}

// iterates over (index, value) or (key, value)
pub enum MutObjIntoIterPairs<'a> {
    List(usize, RcVecIter<'a, Obj>),
    Dict(RcHashMapIter<'a, ObjKey, Obj>),
    String(usize, RcStringIter<'a>),
    Vector(usize, RcVecIter<'a, NNum>),
    Bytes(usize, RcVecIter<'a, u8>),
    Stream(usize, &'a mut Rc<dyn Stream>),
}

pub fn mut_seq_into_iter(seq: &mut Seq) -> MutObjIntoIter<'_> {
    match seq {
        Seq::List(v) => MutObjIntoIter::List(RcVecIter::of(v)),
        Seq::Dict(v, _) => MutObjIntoIter::Dict(RcHashMapIter::of(v)),
        Seq::String(s) => MutObjIntoIter::String(RcStringIter::of(s)),
        Seq::Vector(v) => MutObjIntoIter::Vector(RcVecIter::of(v)),
        Seq::Bytes(v) => MutObjIntoIter::Bytes(RcVecIter::of(v)),
        Seq::Stream(v) => MutObjIntoIter::Stream(v),
    }
}

pub fn mut_seq_into_finite_iter<'a, 'b>(
    seq: &'a mut Seq,
    purpose: &'b str,
) -> NRes<MutObjIntoIter<'a>> {
    if seq.len().is_none() {
        Err(NErr::value_error(format!(
            "{}: infinite, will not terminate",
            purpose
        )))
    } else {
        Ok(mut_seq_into_iter(seq))
    }
}

pub fn mut_obj_into_iter<'a, 'b>(obj: &'a mut Obj, purpose: &'b str) -> NRes<MutObjIntoIter<'a>> {
    match obj {
        Obj::Seq(s) => Ok(mut_seq_into_iter(s)),
        e => Err(NErr::type_error(format!(
            "{}: not iterable: {}",
            purpose,
            FmtObj::debug(e)
        ))),
    }
}

impl Iterator for MutObjIntoIter<'_> {
    type Item = NRes<Obj>;

    fn next(&mut self) -> Option<NRes<Obj>> {
        match self {
            MutObjIntoIter::List(it) => it.next().map(Ok),
            MutObjIntoIter::Dict(it) => Some(Ok(key_to_obj(it.next()?.0))),
            MutObjIntoIter::String(it) => Some(Ok(Obj::from(it.next()?))),
            MutObjIntoIter::Vector(it) => Some(Ok(Obj::Num(it.next()?.clone()))),
            MutObjIntoIter::Bytes(it) => Some(Ok(Obj::u8(it.next()?))),
            MutObjIntoIter::Stream(it) => match Rc::get_mut(it) {
                Some(it) => it.next(),
                None => {
                    let mut it2 = it.clone_box();
                    let ret = it2.next();
                    **it = Rc::from(it2);
                    ret
                }
            },
        }
    }
}

pub fn mut_seq_into_iter_pairs(seq: &mut Seq) -> MutObjIntoIterPairs<'_> {
    match seq {
        Seq::List(v) => MutObjIntoIterPairs::List(0, RcVecIter::of(v)),
        Seq::Dict(v, _) => MutObjIntoIterPairs::Dict(RcHashMapIter::of(v)),
        Seq::String(s) => MutObjIntoIterPairs::String(0, RcStringIter::of(s)),
        Seq::Vector(v) => MutObjIntoIterPairs::Vector(0, RcVecIter::of(v)),
        Seq::Bytes(v) => MutObjIntoIterPairs::Bytes(0, RcVecIter::of(v)),
        Seq::Stream(v) => MutObjIntoIterPairs::Stream(0, v),
    }
}

pub fn mut_obj_into_iter_pairs<'a, 'b>(
    obj: &'a mut Obj,
    purpose: &'b str,
) -> NRes<MutObjIntoIterPairs<'a>> {
    match obj {
        Obj::Seq(s) => Ok(mut_seq_into_iter_pairs(s)),
        _ => Err(NErr::type_error(format!("{}: not iterable", purpose))),
    }
}

impl Iterator for MutObjIntoIterPairs<'_> {
    type Item = NRes<(ObjKey, Obj)>;

    fn next(&mut self) -> Option<NRes<(ObjKey, Obj)>> {
        match self {
            MutObjIntoIterPairs::List(i, it) => {
                let o = it.next()?;
                let j = *i;
                *i += 1;
                Some(Ok((ObjKey::from(j), o)))
            }
            MutObjIntoIterPairs::Dict(it) => it.next().map(Ok),
            MutObjIntoIterPairs::String(i, it) => {
                let o = it.next()?;
                let j = *i;
                *i += 1;
                Some(Ok((ObjKey::from(j), Obj::from(o))))
            }
            MutObjIntoIterPairs::Vector(i, it) => {
                let o = it.next()?;
                let j = *i;
                *i += 1;
                Some(Ok((ObjKey::from(j), Obj::Num(o))))
            }
            MutObjIntoIterPairs::Bytes(i, it) => {
                let o = it.next()?;
                let j = *i;
                *i += 1;
                Some(Ok((ObjKey::from(j), Obj::u8(o))))
            }
            MutObjIntoIterPairs::Stream(i, s) => {
                let o = match Rc::get_mut(s) {
                    Some(it) => it.next()?,
                    None => {
                        let mut it2 = s.clone_box();
                        let ret = it2.next();
                        **s = Rc::from(it2);
                        ret?
                    }
                };
                match o {
                    Ok(o) => {
                        let j = *i;
                        *i += 1;
                        Some(Ok((ObjKey::from(j), o)))
                    }
                    Err(e) => Some(Err(e)),
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct WrappedVec<T>(pub Rc<Vec<T>>, pub usize);

impl<T: Clone + Into<Obj>> Iterator for WrappedVec<T> {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        if self.1 >= self.0.len() {
            None
        } else {
            let ret = self.0[self.1].clone().into();
            self.1 += 1;
            Some(Ok(ret))
        }
    }
}
impl<T: Display> Display for WrappedVec<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(
            formatter,
            "stream(({})[{}])",
            CommaSeparated(&**self.0),
            self.1
        )
    }
}
impl<T: Clone + Into<Obj> + Display + Debug + 'static> Stream for WrappedVec<T> {
    fn peek(&self) -> Option<NRes<Obj>> {
        if self.1 >= self.0.len() {
            None
        } else {
            Some(Ok(self.0[self.1].clone().into()))
        }
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        None
    }
    fn force(&self) -> NRes<Vec<Obj>> {
        Err(NErr::value_error(
            "Cannot force repeat because it's infinite".to_string(),
        ))
    }
    // fn pythonic_index_isize...
    // fn pythonic_slice...
    // fn reversed...
}

// Functions

#[derive(Debug, Clone, Copy)]
pub enum Assoc {
    Left,
    Right,
}
#[derive(Debug, Clone, Copy)]
pub struct Precedence(pub f64, pub Assoc);
impl Precedence {
    pub fn zero() -> Self {
        Precedence(0.0, Assoc::Left)
    }
    pub fn tighter_than_when_before(&self, other: &Precedence) -> bool {
        match self.0.partial_cmp(&other.0) {
            Some(Ordering::Greater) => true,
            Some(Ordering::Less) => false,
            // oh my god nan as a precedence
            Some(Ordering::Equal) | None => match self.1 {
                // maybe we should error if opposite-associativity things of the same precedence
                // are all in a row... shrug
                Assoc::Left => true,
                Assoc::Right => false,
            },
        }
    }
}

// Structs
static STRUCT_COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

#[derive(Debug, Clone)]
pub struct Struct {
    pub id: usize,
    pub name: Rc<String>,
    pub fields: Rc<Vec<(String, Option<Obj>)>>,
}
impl PartialEq for Struct {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Struct {}

impl Struct {
    pub fn new(name: Rc<String>, fields: Rc<Vec<(String, Option<Obj>)>>) -> Self {
        Struct {
            id: STRUCT_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst),
            name,
            fields,
        }
    }
}

// more like an arbitrary predicate. want to add subscripted types to this later
#[derive(Debug, Clone)]
pub enum ObjType {
    Null,
    Int,
    Rational,
    Float,
    Complex,
    Number,
    String,
    List,
    Dict,
    Vector,
    Bytes,
    Stream,
    Func,
    Type,
    Any,
    StructInstance,
    Struct(Struct),
    Satisfying(REnv, Box<Func>),
}

impl ObjType {
    pub fn name(&self) -> String {
        match self {
            ObjType::Null => "nulltype",
            ObjType::Int => "int",
            ObjType::Rational => "rational",
            ObjType::Float => "float",
            ObjType::Complex => "complex",
            ObjType::Number => "number",
            ObjType::List => "list",
            ObjType::String => "str",
            ObjType::Dict => "dict",
            ObjType::Vector => "vector",
            ObjType::Bytes => "bytes",
            ObjType::Stream => "stream",
            ObjType::Type => "type",
            ObjType::Func => "func",
            ObjType::Any => "anything",
            ObjType::Struct(s) => (&**s.name).clone(),
            ObjType::StructInstance => "struct_instance",
            ObjType::Satisfying(..) => "satisfying(???)",
        }
        .to_string()
    }
}

pub fn type_of(obj: &Obj) -> ObjType {
    match obj {
        Obj::Null => ObjType::Null,
        Obj::Num(NNum::Int(_)) => ObjType::Int,
        Obj::Num(NNum::Rational(_)) => ObjType::Rational,
        Obj::Num(NNum::Float(_)) => ObjType::Float,
        Obj::Num(NNum::Complex(_)) => ObjType::Complex,
        Obj::Seq(Seq::List(_)) => ObjType::List,
        Obj::Seq(Seq::String(_)) => ObjType::String,
        Obj::Seq(Seq::Dict(..)) => ObjType::Dict,
        Obj::Seq(Seq::Vector(_)) => ObjType::Vector,
        Obj::Seq(Seq::Bytes(..)) => ObjType::Bytes,
        Obj::Seq(Seq::Stream(_)) => ObjType::Stream,
        Obj::Func(Func::Type(_), _) => ObjType::Type,
        Obj::Func(..) => ObjType::Func,
        Obj::Instance(..) => ObjType::StructInstance,
    }
}

pub fn expect_one(args: Vec<Obj>, msg: &str) -> NRes<Obj> {
    match few(args) {
        Few::One(arg) => Ok(arg),
        t => Err(NErr::type_error(format!(
            "{} expected one argument, got {}",
            msg,
            t.len()
        ))),
    }
}

pub fn call_type1(ty: &ObjType, arg: Obj) -> NRes<Obj> {
    match ty {
        ObjType::Int => match arg {
            Obj::Num(n) => Ok(Obj::Num(
                n.trunc()
                    .ok_or(NErr::value_error("can't coerce to int".to_string()))?,
            )),
            Obj::Seq(Seq::String(s)) => match s.parse::<BigInt>() {
                Ok(x) => Ok(Obj::from(x)),
                Err(s) => Err(NErr::value_error(format!("can't parse: {}", s))),
            },
            _ => Err(NErr::type_error(
                "int: expected number or string".to_string(),
            )),
        },
        ObjType::Float => match arg {
            Obj::Num(n) => Ok(Obj::from(to_f64_ok(&n)?)),
            Obj::Seq(Seq::String(s)) => match s.parse::<f64>() {
                Ok(x) => Ok(Obj::from(x)),
                Err(s) => Err(NErr::value_error(format!("can't parse: {}", s))),
            },
            _ => Err(NErr::type_error(
                "float: expected number or string".to_string(),
            )),
        },
        ObjType::Number => match arg {
            Obj::Num(n) => Ok(Obj::Num(n)),
            Obj::Seq(Seq::String(s)) => match s.parse::<BigInt>() {
                Ok(x) => Ok(Obj::from(x)),
                Err(_) => match s.parse::<f64>() {
                    Ok(x) => Ok(Obj::from(x)),
                    Err(s) => Err(NErr::value_error(format!("can't parse: {}", s))),
                },
            },
            _ => Err(NErr::type_error(
                "number: expected number or string".to_string(),
            )),
        },
        ObjType::List => match arg {
            Obj::Seq(Seq::List(xs)) => Ok(Obj::Seq(Seq::List(xs))),
            mut arg => Ok(Obj::list(
                mut_obj_into_iter(&mut arg, "list conversion")?.collect::<NRes<Vec<Obj>>>()?,
            )),
        },
        ObjType::String => Ok(Obj::from(format!("{}", arg))),
        ObjType::Bytes => match arg {
            Obj::Seq(Seq::Bytes(xs)) => Ok(Obj::Seq(Seq::Bytes(xs))),
            Obj::Seq(Seq::String(s)) => Ok(Obj::Seq(Seq::Bytes(Rc::new(s.as_bytes().to_vec())))),
            mut arg => Ok(Obj::Seq(Seq::Bytes(Rc::new(
                mut_obj_into_iter(&mut arg, "bytes conversion")?
                    .map(|e| to_byte(e?, "bytes conversion"))
                    .collect::<NRes<Vec<u8>>>()?,
            )))),
        },
        ObjType::Vector => match arg {
            Obj::Seq(Seq::Vector(s)) => Ok(Obj::Seq(Seq::Vector(s))),
            mut arg => to_obj_vector(mut_obj_into_iter(&mut arg, "vector conversion")?),
        },
        ObjType::Dict => match arg {
            Obj::Seq(Seq::Dict(x, d)) => Ok(Obj::Seq(Seq::Dict(x, d))),
            // nonsensical but maybe this is something some day
            /*
            mut arg => Ok(Obj::Dict(
                    Rc::new(mut_obj_into_iter_pairs(&mut arg, "dict conversion")?.collect::<HashMap<ObjKey, Obj>>()), None)),
                    */
            mut arg => Ok(Obj::dict(
                mut_obj_into_iter(&mut arg, "dict conversion")?
                    .map(|p| match p? {
                        Obj::Seq(Seq::List(xs)) => match few2(unwrap_or_clone(xs)) {
                            Few2::Two(k, v) => Ok((to_key(k)?, v)),
                            _ => Err(NErr::type_error("dict conversion: not pair".to_string())),
                        },
                        _ => Err(NErr::type_error("dict conversion: not list".to_string())),
                    })
                    .collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                None,
            )),
        },
        ObjType::Stream => match arg {
            Obj::Seq(Seq::Stream(..)) => Ok(arg),
            Obj::Seq(Seq::List(v)) => Ok(Obj::Seq(Seq::Stream(Rc::new(WrappedVec(v, 0))))),
            Obj::Seq(Seq::String(v)) => Ok(Obj::Seq(Seq::Stream(Rc::new(WrappedVec(
                Rc::new(v.chars().map(|c| c.to_string()).collect()),
                0,
            ))))),
            Obj::Seq(Seq::Vector(v)) => Ok(Obj::Seq(Seq::Stream(Rc::new(WrappedVec(v, 0))))),
            Obj::Seq(Seq::Bytes(v)) => Ok(Obj::Seq(Seq::Stream(Rc::new(WrappedVec(v, 0))))),
            Obj::Seq(Seq::Dict(d, _)) => Ok(Obj::Seq(Seq::Stream(Rc::new(WrappedVec(
                Rc::new(
                    unwrap_or_clone(d)
                        .into_keys()
                        .map(|k| key_to_obj(k))
                        .collect(),
                ),
                0,
            ))))),
            _ => Err(NErr::type_error("stream: expected seq".to_string())),
        },
        ObjType::Type => Ok(Obj::Func(Func::Type(type_of(&arg)), Precedence::zero())),
        ObjType::Struct(_) => call_type(ty, vec![arg]),
        // TODO: complex
        _ => Err(NErr::type_error(
            "that type can't be called (maybe not implemented)".to_string(),
        )),
    }
}

pub fn call_type(ty: &ObjType, mut args: Vec<Obj>) -> NRes<Obj> {
    match ty {
        ObjType::Struct(s) => {
            args.reserve_exact(s.fields.len());
            while args.len() < s.fields.len() {
                match &s.fields[args.len()].1 {
                    None => {
                        return Err(NErr::argument_error(format!(
                            "struct construction: not enough arguments at {}, wanted {}",
                            args.len(),
                            s.fields.len(),
                        )))
                    }
                    Some(def) => args.push(def.clone()),
                }
            }
            Ok(Obj::Instance(s.clone(), args))
        }
        _ => call_type1(ty, expect_one(args, &ty.name())?),
    }
}

// Obj conversions

pub fn to_nnum(obj: Obj, reason: &'static str) -> NRes<NNum> {
    match obj {
        Obj::Num(n) => Ok(n),
        x => Err(NErr::type_error(format!(
            "{}: non-number: {}",
            reason,
            FmtObj::debug(&x)
        ))),
    }
}

pub fn to_byte(obj: Obj, reason: &'static str) -> NRes<u8> {
    match obj {
        Obj::Num(n) => n.to_u8().ok_or(NErr::value_error(format!(
            "{}: can't convert number to byte: {}",
            reason, n
        ))),
        x => Err(NErr::value_error(format!(
            "{}: can't convert non-number to byte: {}",
            reason, x
        ))),
    }
}

pub fn to_obj_vector(iter: impl Iterator<Item = NRes<Obj>>) -> NRes<Obj> {
    Ok(Obj::Seq(Seq::Vector(Rc::new(
        iter.map(|e| to_nnum(e?, "can't convert to vector"))
            .collect::<NRes<Vec<NNum>>>()?,
    ))))
}

pub fn expect_nums_and_vectorize_1(body: fn(NNum) -> NRes<Obj>, a: Obj, name: &str) -> NRes<Obj> {
    match a {
        Obj::Num(a) => body(a),
        Obj::Seq(Seq::Vector(mut a)) => to_obj_vector(RcVecIter::of(&mut a).map(body)),
        x => Err(NErr::argument_error(format!(
            "{} only accepts numbers, got {}",
            name,
            FmtObj::debug(&x)
        ))),
    }
}

// TODO can we take?
pub fn to_type(arg: &Obj, msg: &str) -> NRes<ObjType> {
    match arg {
        Obj::Null => Ok(ObjType::Null),
        Obj::Func(Func::Type(t), _) => Ok(t.clone()),
        // TODO: possibly intelligently convert some objects to types?
        // e.g. "heterogenous tuples"
        a => Err(NErr::type_error(format!(
            "can't convert {} to type for {}",
            FmtObj::debug(a),
            msg
        ))),
    }
}

// from and to
impl From<NNum> for Obj {
    fn from(n: NNum) -> Self {
        Obj::Num(n)
    }
}
impl From<bool> for Obj {
    fn from(n: bool) -> Self {
        Obj::Num(NNum::iverson(n))
    }
}
// we need this one for the fake "higher-ranked" types using Bytes
impl From<u8> for Obj {
    fn from(n: u8) -> Self {
        Obj::Num(NNum::u8(n))
    }
}
impl From<char> for Obj {
    fn from(n: char) -> Self {
        Obj::Seq(Seq::String(Rc::new(n.to_string())))
    }
}
impl From<&str> for Obj {
    fn from(n: &str) -> Self {
        Obj::Seq(Seq::String(Rc::new(n.to_string())))
    }
}
impl From<String> for Obj {
    fn from(n: String) -> Self {
        Obj::Seq(Seq::String(Rc::new(n)))
    }
}
/*
impl From<Vec<Obj>> for Obj {
    fn from(n: Vec<Obj>) -> Self {
        Obj::Seq(Seq::List(Rc::new(n)))
    }
}
*/

macro_rules! forward_from {
    ($ty:ident) => {
        impl From<$ty> for Obj {
            fn from(n: $ty) -> Self {
                Obj::Num(NNum::from(n))
            }
        }
    };
}
forward_from!(NInt);
forward_from!(BigInt);
// forward_from!(i32);
forward_from!(f64);
// forward_from!(usize);
forward_from!(Complex64);

impl From<usize> for ObjKey {
    fn from(n: usize) -> Self {
        ObjKey(Obj::usize(n))
    }
}
impl From<String> for ObjKey {
    fn from(n: String) -> Self {
        ObjKey(Obj::from(n))
    }
}
impl From<&str> for ObjKey {
    fn from(n: &str) -> Self {
        ObjKey(Obj::from(n))
    }
}

/*
fn to_bigint_ok(n: &NNum) -> NRes<BigInt> {
    Ok(n.to_bigint().ok_or(NErr::value_error("bad number to int".to_string()))?.clone())
}
*/
pub fn to_usize_ok(n: &NNum) -> NRes<usize> {
    n.to_usize()
        .ok_or(NErr::value_error("bad number to usize".to_string()))
}
pub fn clamp_to_usize_ok(n: &NNum) -> NRes<usize> {
    n.clamp_to_usize()
        .ok_or(NErr::value_error("bad number to usize".to_string()))
}
pub fn obj_clamp_to_usize_ok(n: &Obj) -> NRes<usize> {
    match n {
        Obj::Num(n) => clamp_to_usize_ok(n),
        _ => Err(NErr::type_error(format!("bad scalar {}", FmtObj::debug(n)))),
    }
}
pub fn into_nint_ok(n: NNum) -> NRes<NInt> {
    n.into_nint()
        .ok_or(NErr::value_error("bad number to int".to_string()))
}
pub fn into_bigint_ok(n: NNum) -> NRes<BigInt> {
    n.into_bigint()
        .ok_or(NErr::value_error("bad number to int".to_string()))
}
pub fn to_f64_ok(n: &NNum) -> NRes<f64> {
    n.to_f64()
        .ok_or(NErr::value_error("bad number to float".to_string()))
}

// For keying hash maps. For efficiency, want to share internal structure with Obj. Eq may violate
// laws and hash may panic if called on an improperly constructed instance, so clients should not
// construct those themselves.
#[derive(PartialOrd, Clone, Debug)]
pub struct ObjKey(Obj);

// These will panic if called on things with unhashable things inside!!
fn total_eq_of_key_seqs(a: &Seq, b: &Seq) -> bool {
    match (a, b) {
        (Seq::List(a), Seq::List(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| total_eq_of_keys(a, b))
        }
        (Seq::Dict(a, _), Seq::Dict(b, _)) => {
            a.len() == b.len()
                && a.iter().all(|(k, v)| match b.get(k) {
                    Some(vv) => total_eq_of_keys(v, vv),
                    None => false,
                })
        }
        (Seq::String(a), Seq::String(b)) => a == b,
        (Seq::Vector(a), Seq::Vector(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| a.total_eq(b))
        }
        (Seq::Bytes(a), Seq::Bytes(b)) => a == b,
        _ => false,
    }
}

fn total_eq_of_keys(a: &Obj, b: &Obj) -> bool {
    match (a, b) {
        (Obj::Null, Obj::Null) => true,
        (Obj::Num(a), Obj::Num(b)) => a == b || a.is_nan() && b.is_nan(),
        (Obj::Seq(a), Obj::Seq(b)) => total_eq_of_key_seqs(a, b),
        _ => false,
    }
}

fn total_hash_of_key<H: Hasher>(a: &Obj, state: &mut H) {
    match a {
        Obj::Null => state.write_u8(0),
        Obj::Num(a) => {
            state.write_u8(1);
            a.total_hash(state);
        }
        Obj::Seq(a) => match a {
            Seq::String(s) => {
                state.write_u8(2);
                s.hash(state);
            }
            Seq::List(s) => {
                state.write_u8(3);
                state.write_usize(s.len());
                for e in s.iter() {
                    total_hash_of_key(e, state);
                }
            }
            Seq::Dict(d, _) => {
                state.write_u8(4);
                let mut acc: u64 = 0;
                let mut acc2: u64 = 0;
                for (k, v) in d.iter() {
                    let mut h1 = std::collections::hash_map::DefaultHasher::new();
                    total_hash_of_key(&k.0, &mut h1);
                    total_hash_of_key(v, &mut h1);
                    let f = h1.finish();
                    acc = acc.wrapping_add(f);
                    acc2 = acc2.wrapping_add(f.wrapping_mul(f));
                }
                state.write_u64(acc);
                state.write_u64(acc2);
            }
            Seq::Vector(v) => {
                state.write_u8(5);
                state.write_usize(v.len());
                for e in v.iter() {
                    e.total_hash(state);
                }
            }
            Seq::Bytes(b) => {
                state.write_u8(6);
                b.hash(state);
            }
            Seq::Stream(s) => {
                panic!("Attempting to hash Stream: {}", s)
            }
        },
        _ => panic!("Attempting to hash invalid Obj: {}", a),
    }
}

impl PartialEq for ObjKey {
    fn eq(&self, other: &Self) -> bool {
        total_eq_of_keys(&self.0, &other.0)
    }
}

impl Eq for ObjKey {}

impl Hash for ObjKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        total_hash_of_key(&self.0, state)
    }
}

fn check_if_valid_key(obj: &Obj) -> NRes<()> {
    match obj {
        Obj::Null => Ok(()),
        Obj::Num(_) => Ok(()),
        Obj::Seq(Seq::String(_)) => Ok(()),
        Obj::Seq(Seq::List(xs)) => {
            for e in xs.iter() {
                check_if_valid_key(e)?;
            }
            Ok(())
        }
        Obj::Seq(Seq::Dict(d, _)) => {
            for e in d.values() {
                check_if_valid_key(e)?;
            }
            Ok(())
        }
        Obj::Seq(Seq::Vector(_)) => Ok(()),
        Obj::Seq(Seq::Bytes(_)) => Ok(()),
        Obj::Seq(Seq::Stream(_)) => Err(NErr::type_error(
            "Using a stream as a dictionary key isn't supported".to_string(),
        )),
        Obj::Func(..) => Err(NErr::type_error(
            "Using a function as a dictionary key isn't supported".to_string(),
        )),
        Obj::Instance(..) => Err(NErr::type_error(
            "Using an instance as a dictionary key isn't supported".to_string(),
        )),
    }
}

pub fn to_key(obj: Obj) -> NRes<ObjKey> {
    match obj {
        Obj::Seq(Seq::Stream(s)) => to_key(Obj::list(s.force()?)),
        _ => {
            check_if_valid_key(&obj)?;
            Ok(ObjKey(obj))
        }
    }
}

pub fn key_to_obj(key: ObjKey) -> Obj {
    key.0
}

// generic Obj impls

impl Obj {
    pub fn truthy(&self) -> bool {
        match self {
            Obj::Null => false,
            Obj::Num(x) => x.is_nonzero(),
            Obj::Seq(s) => !s.is_empty(),
            Obj::Func(..) => true,
            Obj::Instance(..) => true,
        }
    }

    pub fn i64(n: i64) -> Self {
        Obj::Num(NNum::Int(NInt::Small(n)))
    }
    pub fn usize(n: usize) -> Self {
        Obj::Num(NNum::usize(n))
    }
    pub fn u8(n: u8) -> Self {
        Obj::Num(NNum::u8(n))
    }
    pub fn list(n: Vec<Obj>) -> Self {
        Obj::Seq(Seq::List(Rc::new(n)))
    }
    pub fn dict(m: HashMap<ObjKey, Obj>, def: Option<Obj>) -> Self {
        Obj::Seq(Seq::Dict(Rc::new(m), def.map(Box::new)))
    }

    pub fn zero() -> Self {
        Obj::i64(0)
    }
    pub fn one() -> Self {
        Obj::i64(1)
    }
    pub fn neg_one() -> Self {
        Obj::i64(-1)
    }
}

impl Default for Obj {
    fn default() -> Obj {
        Obj::Null
    }
}

impl PartialEq for Obj {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Obj::Null, Obj::Null) => true,
            (Obj::Num(a), Obj::Num(b)) => a == b,
            (Obj::Seq(a), Obj::Seq(b)) => a == b,
            // hmm
            // (Obj::Func(Func::SymbolAccess(a), _), Obj::Func(Func::SymbolAccess(b), _)) => a == b,
            _ => false,
        }
    }
}

impl PartialEq for Seq {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Seq::List(a), Seq::List(b)) => a == b,
            (Seq::Dict(a, _), Seq::Dict(b, _)) => a == b,
            (Seq::String(a), Seq::String(b)) => a == b,
            (Seq::Vector(a), Seq::Vector(b)) => a == b,
            (Seq::Bytes(a), Seq::Bytes(b)) => a == b,
            _ => false,
        }
    }
}

impl PartialOrd for Obj {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Obj::Null, Obj::Null) => Some(Ordering::Equal),
            (Obj::Num(a), Obj::Num(b)) => a.partial_cmp(b),
            (Obj::Seq(a), Obj::Seq(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

impl PartialOrd for Seq {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Seq::List(a), Seq::List(b)) => a.partial_cmp(b),
            (Seq::String(a), Seq::String(b)) => a.partial_cmp(b),
            (Seq::Vector(a), Seq::Vector(b)) => a.partial_cmp(b),
            (Seq::Bytes(a), Seq::Bytes(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

// all thins formatting

#[derive(Clone, Debug)]
pub enum FmtBase {
    Decimal,
    Binary,
    Octal,
    LowerHex,
    UpperHex,
}

#[derive(Clone, Debug)]
pub enum FmtAlign {
    Left,
    Right,
    Center,
}

#[derive(Clone, Debug)]
pub struct MyFmtFlags {
    pub base: FmtBase,
    pub repr: bool,
    pub pad: char,
    pub pad_length: usize,
    pub pad_align: FmtAlign,
    pub budget: usize,
}

impl MyFmtFlags {
    pub const fn new() -> MyFmtFlags {
        MyFmtFlags {
            base: FmtBase::Decimal,
            repr: false,
            pad: ' ',
            pad_length: 0,
            pad_align: FmtAlign::Right,
            budget: usize::MAX,
        }
    }
    pub const fn budgeted_repr(budget: usize) -> MyFmtFlags {
        let mut f = MyFmtFlags::new();
        f.repr = true;
        f.budget = budget;
        f
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
    fn is_null(&self) -> bool {
        false
    }
    fn fmt_with_mut(&self, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
        let s = if flags.repr {
            self.repr()
        } else {
            match flags.base {
                FmtBase::Decimal => format!("{}", self),
                FmtBase::Binary => format!("{:b}", self),
                FmtBase::Octal => format!("{:o}", self),
                FmtBase::LowerHex => format!("{:x}", self),
                FmtBase::UpperHex => format!("{:X}", self),
            }
        };
        let pad_amt = if s.len() < flags.pad_length {
            flags.pad_length - s.len()
        } else {
            0
        };
        let (left_amt, right_amt) = match flags.pad_align {
            FmtAlign::Left => (0, pad_amt),
            FmtAlign::Right => (pad_amt, 0),
            FmtAlign::Center => (pad_amt / 2, pad_amt - pad_amt / 2),
        };
        write!(
            formatter,
            "{}{}{}",
            flags.pad.to_string().repeat(left_amt),
            s,
            flags.pad.to_string().repeat(right_amt)
        )
    }
}

pub fn write_string(
    s: &str,
    formatter: &mut dyn fmt::Write,
    flags: &mut MyFmtFlags,
) -> fmt::Result {
    flags.deduct(s.len() / 2);
    if flags.repr {
        // FIXME??
        write!(formatter, "{:?}", s)
    } else {
        write!(formatter, "{}", s)
    }
}
pub fn write_slice(
    v: &[impl MyDisplay],
    formatter: &mut dyn fmt::Write,
    flags: &mut MyFmtFlags,
) -> fmt::Result {
    let old_repr = flags.repr;
    flags.repr = true;
    // Regardless of budget, always fmt first and last
    match v {
        [] => {}
        [only] => only.fmt_with_mut(formatter, flags)?,
        [first, rest @ .., last] => {
            first.fmt_with_mut(formatter, flags)?;
            write!(formatter, ", ")?;
            for x in rest {
                if flags.budget == 0 {
                    // TODO this has the "sometimes longer than what's omitted"
                    // property
                    write!(formatter, "..., ")?;
                    break;
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

pub fn write_pairs<'a, 'b>(
    it: impl Iterator<Item = (&'a (impl MyDisplay + 'a), &'b (impl MyDisplay + 'b))>,
    formatter: &mut dyn fmt::Write,
    flags: &mut MyFmtFlags,
) -> fmt::Result {
    let old_repr = flags.repr;
    flags.repr = true;
    let mut started = false;
    for (k, v) in it {
        if started {
            write!(formatter, ", ")?;
            if flags.budget == 0 {
                write!(formatter, "...")?;
                break;
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

pub struct FmtDictPairs<'f, T>(pub T, pub &'f MyFmtFlags);
impl<
        'f,
        'a,
        'b,
        A: MyDisplay + 'a,
        B: MyDisplay + 'b,
        T: Iterator<Item = (&'a A, &'b B)> + Clone,
    > Display for FmtDictPairs<'f, T>
{
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "{{")?;
        write_pairs(self.0.clone(), formatter, &mut self.1.clone())?;
        write!(formatter, "}}")
    }
}

pub fn write_bytes(
    s: &[u8],
    formatter: &mut dyn fmt::Write,
    flags: &mut MyFmtFlags,
) -> fmt::Result {
    flags.deduct(s.len());
    write!(formatter, "B[")?;
    match s {
        [] => {}
        [only] => {
            write!(formatter, "{}", only)?;
        }
        [first, rest @ .., last] => {
            write!(formatter, "{},", first)?;
            for x in rest {
                if flags.budget == 0 {
                    // TODO this has the "sometimes longer than what's omitted"
                    // property
                    write!(formatter, "...,")?;
                    break;
                }
                write!(formatter, "{},", x)?;
            }
            write!(formatter, "{}", last)?;
        }
    }
    write!(formatter, "]")
}

// ????
pub struct FmtObj<'a, 'b>(pub &'a Obj, pub &'b MyFmtFlags);
impl<'a, 'b> Display for FmtObj<'a, 'b> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt_with(formatter, self.1.clone())
    }
}

pub const DEBUG_FMT: MyFmtFlags = MyFmtFlags::budgeted_repr(6);

impl FmtObj<'_, '_> {
    pub fn debug<'a>(t: &'a Obj) -> FmtObj<'a, 'static> {
        FmtObj(t, &DEBUG_FMT)
    }
}

pub struct CommaSeparatedDebug<'a>(pub &'a [Obj]);

impl<'a> Display for CommaSeparatedDebug<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let mut started = false;
        for t in self.0 {
            if started {
                write!(formatter, ", ")?;
            }
            started = true;
            write!(formatter, "{}", FmtObj::debug(t))?;
        }
        Ok(())
    }
}

pub trait MyDisplay {
    fn is_null(&self) -> bool;
    fn fmt_with_mut(&self, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result;
}

impl MyDisplay for Obj {
    fn is_null(&self) -> bool {
        self == &Obj::Null
    } // thonk
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
                        if !xs.is_empty() {
                            write!(formatter, ", ")?;
                        }
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
            Obj::Seq(Seq::Stream(x)) => {
                write!(formatter, "{}", x)
            }
            Obj::Seq(Seq::Bytes(xs)) => write_bytes(xs.as_slice(), formatter, flags),
            Obj::Func(f, p) => write!(formatter, "<{} p:{}>", f, p.0),
            Obj::Instance(s, fields) => write!(
                formatter,
                "<{} instance: {}>",
                s.name,
                CommaSeparated(fields)
            ),
        }
    }
}

impl Obj {
    pub fn fmt_with(&self, formatter: &mut dyn fmt::Write, mut flags: MyFmtFlags) -> fmt::Result {
        self.fmt_with_mut(formatter, &mut flags)
    }
}

pub struct CommaSeparated<'a, T>(pub &'a [T]);

impl<'a, T: Display> Display for CommaSeparated<'a, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let mut started = false;
        for t in self.0 {
            if started {
                write!(formatter, ", ")?;
            }
            started = true;
            write!(formatter, "{}", t)?;
        }
        Ok(())
    }
}

pub struct FmtSectionSlot<'a>(&'a Option<Obj>);

impl<'a> Display for FmtSectionSlot<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(t) => write!(formatter, "{}", FmtObj::debug(t)),
            None => write!(formatter, "_"),
        }
    }
}

pub struct FmtSectionBoxedSlot<'a>(&'a Option<Box<Obj>>);

impl<'a> Display for FmtSectionBoxedSlot<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(t) => write!(formatter, "{}", FmtObj::debug(&**t)),
            None => write!(formatter, "_"),
        }
    }
}

pub struct FmtSectionSlots<'a>(&'a [Result<Obj, bool>]);

impl<'a> Display for FmtSectionSlots<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let mut started = false;
        for t in self.0 {
            if started {
                write!(formatter, ", ")?;
            }
            started = true;
            match t {
                Err(true) => {
                    write!(formatter, "..._")
                }
                Err(false) => {
                    write!(formatter, "_")
                }
                Ok(e) => write!(formatter, "{}", e),
            }?
        }
        Ok(())
    }
}

pub struct FmtSectionBoxedSlots<'a>(&'a [Option<Box<Obj>>]);

impl<'a> Display for FmtSectionBoxedSlots<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let mut started = false;
        for t in self.0 {
            if started {
                write!(formatter, ", ")?;
            }
            started = true;
            write!(formatter, "{}", FmtSectionBoxedSlot(t))?
        }
        Ok(())
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

impl MyDisplay for ObjKey {
    fn is_null(&self) -> bool {
        self.0 == Obj::Null
    } // thonk
    fn fmt_with_mut(&self, formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
        self.0.fmt_with_mut(formatter, flags)
    }
}

impl ObjKey {
    pub fn fmt_with(&self, formatter: &mut dyn fmt::Write, mut flags: MyFmtFlags) -> fmt::Result {
        self.fmt_with_mut(formatter, &mut flags)
    }
}

// Error handling
#[derive(Debug, Clone)]
pub enum NErr {
    Throw(
        Obj,
        Vec<(String, CodeLoc, CodeLoc, Option<(Rc<String>, Rc<String>)>)>,
    ),
    // Optional (source file, source code), added when we pass through an eval boundary roughly
    // speaking. Is this bonkers? Idk.
    Break(usize, Option<Obj>),
    Return(Obj),
    Continue(usize),
}

pub fn write_source_error(out: &mut String, src: &str, start: &CodeLoc, end: &CodeLoc) {
    use std::fmt::Write;

    let mut line = 1;
    let mut ended = false;
    for (i, c) in src.chars().enumerate() {
        if c == '\n' {
            if line >= start.line {
                write!(out, "{}", c).ok();
            }
            line += 1;
            if line > end.line {
                break;
            }
        } else {
            if i == start.index {
                write!(out, "\x1b[1;31m").ok();
            }
            if i == end.index {
                write!(out, "\x1b[0m").ok();
                ended = true;
            }
            if line >= start.line && line <= end.line {
                write!(out, "{}", c).ok();
            }
        }
    }
    if !ended {
        write!(out, "\x1b[0m").ok();
    }
}

struct FmtCodeLocRange<'a>(&'a CodeLoc, &'a CodeLoc);
impl<'a> Display for FmtCodeLocRange<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let FmtCodeLocRange(start, end) = self;
        if start.line == end.line {
            write!(formatter, "{}:{}-{}", start.line, start.col, end.col)
        } else {
            write!(
                formatter,
                "{}:{}-{}:{}",
                start.line, start.col, end.line, end.col
            )
        }
    }
}

impl NErr {
    pub fn supply_source(self: &mut NErr, src_file: Rc<String>, src: Rc<String>) {
        match self {
            NErr::Throw(_, trace) => {
                for tup in trace {
                    if tup.3.is_none() {
                        tup.3 = Some((src_file.clone(), src.clone()));
                    }
                }
            }
            _ => {}
        }
    }

    // slow
    pub fn render(self: NErr, src: &str) -> String {
        match self {
            NErr::Throw(e, trace) => {
                use std::fmt::Write;
                let mut out = String::new();
                // I'm fairly confident these writes can't fail, at least at time of writing. But
                // since we are already error handling let's just ignore errors.
                writeln!(out, "{}", e).ok();
                match trace.first() {
                    Some((_, start, end, tsrc)) => {
                        let real_src_code = match tsrc {
                            Some((_, f)) => f,
                            None => src,
                        };
                        write_source_error(&mut out, real_src_code, start, end);
                    }
                    None => {}
                }
                for (thing, start, end, tsrc) in trace {
                    write!(out, "\n    at {} (", thing).ok();
                    if let Some((src_file, _)) = tsrc {
                        write!(out, "{}:", src_file).ok();
                    }
                    write!(out, "{})", FmtCodeLocRange(&start, &end)).ok();
                }
                out
            }
            NErr::Break(n, None) => format!("break^{}", n + 1),
            NErr::Break(n, Some(e)) => format!("break^{} {}", n + 1, e),
            NErr::Continue(n) => format!("continue^{}", n + 1),
            NErr::Return(e) => format!("return {}", e),
        }
    }

    pub fn throw(s: String) -> NErr {
        NErr::Throw(Obj::from(s), Vec::new())
    }
    pub fn argument_error(s: String) -> NErr {
        NErr::throw(format!("argument error: {}", s))
    }
    pub fn index_error(s: String) -> NErr {
        NErr::throw(format!("index error: {}", s))
    }
    pub fn key_error(s: String) -> NErr {
        NErr::throw(format!("key error: {}", s))
    }
    pub fn empty_error(s: String) -> NErr {
        NErr::throw(format!("empty error: {}", s))
    }
    pub fn name_error(s: String) -> NErr {
        NErr::throw(format!("name error: {}", s))
    }
    pub fn syntax_error(s: String) -> NErr {
        NErr::throw(format!("syntax error: {}", s))
    }
    pub fn syntax_error_loc(s: String, msg: String, start: CodeLoc, end: CodeLoc) -> NErr {
        NErr::Throw(
            Obj::from(format!("syntax error: {}", s)),
            vec![(msg, start, end, None)],
        )
    }
    pub fn type_error(s: String) -> NErr {
        NErr::throw(format!("type error: {}", s))
    }
    pub fn type_error_loc(s: String, msg: String, start: CodeLoc, end: CodeLoc) -> NErr {
        NErr::Throw(
            Obj::from(format!("type error: {}", s)),
            vec![(msg, start, end, None)],
        )
    }
    pub fn value_error(s: String) -> NErr {
        NErr::throw(format!("value error: {}", s))
    }
    pub fn io_error(s: String) -> NErr {
        NErr::throw(format!("io error: {}", s))
    }
    pub fn assert_error(s: String) -> NErr {
        NErr::throw(format!("assert error: {}", s))
    }

    pub fn argument_error_args(x: &[Obj]) -> NErr {
        NErr::throw(format!(
            "unrecognized argument types/count: {}",
            CommaSeparated(&x.iter().map(|k| type_of(k).name()).collect::<Vec<String>>())
        ))
    }
    pub fn argument_error_few(x: &Few<Obj>) -> NErr {
        NErr::throw(format!(
            "unrecognized argument types/count: {}",
            CommaSeparated(&match x {
                Few::Zero => Vec::new(),
                Few::One(a) => vec![type_of(a).name()],
                Few::Many(x) => x.iter().map(|k| type_of(k).name()).collect::<Vec<String>>(),
            })
        ))
    }
    pub fn argument_error_few2(x: &Few2<Obj>) -> NErr {
        NErr::throw(format!(
            "unrecognized argument types/count: {}",
            CommaSeparated(&match x {
                Few2::Zero => Vec::new(),
                Few2::One(a) => vec![type_of(a).name()],
                Few2::Two(a, b) => vec![type_of(a).name(), type_of(b).name()],
                Few2::Many(x) => x.iter().map(|k| type_of(k).name()).collect::<Vec<String>>(),
            })
        ))
    }
    pub fn argument_error_few3(x: &Few3<Obj>) -> NErr {
        NErr::throw(format!(
            "unrecognized argument types/count: {}",
            CommaSeparated(&match x {
                Few3::Zero => Vec::new(),
                Few3::One(a) => vec![type_of(a).name()],
                Few3::Two(a, b) => vec![type_of(a).name(), type_of(b).name()],
                Few3::Three(a, b, c) =>
                    vec![type_of(a).name(), type_of(b).name(), type_of(c).name()],
                Few3::Many(x) => x.iter().map(|k| type_of(k).name()).collect::<Vec<String>>(),
            })
        ))
    }
    pub fn argument_error_1(x: &Obj) -> NErr {
        NErr::throw(format!("unrecognized argument type: {}", type_of(x).name()))
    }
    pub fn argument_error_first(x: &Obj) -> NErr {
        NErr::throw(format!(
            "unrecognized 1st argument type: {}",
            type_of(x).name()
        ))
    }
    pub fn argument_error_second(x: &Obj) -> NErr {
        NErr::throw(format!(
            "unrecognized 2nd argument type: {}",
            type_of(x).name()
        ))
    }
    pub fn argument_error_2(x: &Obj, y: &Obj) -> NErr {
        NErr::throw(format!(
            "unrecognized argument types: ({}, {})",
            type_of(x).name(),
            type_of(y).name()
        ))
    }
}

impl fmt::Display for NErr {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NErr::Throw(e, trace) => {
                write!(formatter, "{}", e)?;
                for (thing, start, end, src) in trace {
                    match src {
                        Some(srcp) => write!(
                            formatter,
                            " at {} ({}:{})",
                            thing,
                            srcp.0,
                            FmtCodeLocRange(start, end)
                        )?,
                        None => {
                            write!(formatter, " at {} ({})", thing, FmtCodeLocRange(start, end))?
                        }
                    }
                }
                Ok(())
            }
            NErr::Break(n, None) => write!(formatter, "break^{}", n + 1),
            NErr::Break(n, Some(e)) => write!(formatter, "break^{} {}", n + 1, e),
            NErr::Continue(n) => write!(formatter, "continue^{}", n + 1),
            NErr::Return(e) => write!(formatter, "return {}", e),
        }
    }
}

pub type NRes<T> = Result<T, NErr>;

// Expressions!!
// Note that Obj depends on Func depends on Closure depends on LocExpr depends on Frozen depends on
// Frozen(Obj), and also Closure depends on eval, so there isn't an obvious way to extract a
// smaller module. Rust does support cyclic module dependencies but philosophically it's not clear
// if they're good. Still, if I had to do it, turning Func into a trait to break the cycle isn't
// off the table.

#[derive(Debug, Clone, Copy)]
pub enum ForIterationType {
    Normal,
    Item,
    Declare,
}

#[derive(Debug)]
pub enum ForIteration {
    Iteration(ForIterationType, Box<Lvalue>, Box<LocExpr>),
    Guard(Box<LocExpr>),
}

#[derive(Debug)]
pub enum ForBody {
    Execute(LocExpr),
    Yield(LocExpr, Option<LocExpr>),
    YieldItem(LocExpr, LocExpr),
}

#[derive(Debug)]
pub enum IndexOrSlice {
    Index(Box<LocExpr>),
    Slice(Option<Box<LocExpr>>, Option<Box<LocExpr>>),
    Symbol(Rc<String>),
}

#[derive(Debug)]
pub struct LocExpr {
    pub start: CodeLoc,
    pub end: CodeLoc,
    pub expr: Expr,
}

#[derive(Debug, Clone, Copy)]
pub enum CallSyntax {
    Parentheses,
    Juxtapose,
    Bang,
}

#[derive(Debug)]
pub enum Expr {
    Null,
    IntLit64(i64),
    IntLit(BigInt),
    RatLit(BigRational),
    FloatLit(f64),
    ImaginaryFloatLit(f64),
    StringLit(Rc<String>),
    BytesLit(Rc<Vec<u8>>),
    FormatString(Vec<Result<char, (LocExpr, MyFmtFlags)>>),
    Ident(String),
    Symbol(Rc<String>),
    Underscore,
    Backref(usize),
    Call(Box<LocExpr>, Vec<Box<LocExpr>>, CallSyntax),
    SymbolAccess(Box<LocExpr>, Rc<String>),
    List(Vec<Box<LocExpr>>),
    Dict(
        Option<Box<LocExpr>>,
        Vec<(Box<LocExpr>, Option<Box<LocExpr>>)>,
    ),
    Vector(Vec<Box<LocExpr>>),
    Index(Box<LocExpr>, IndexOrSlice),
    Update(Box<LocExpr>, Vec<(Box<LocExpr>, Box<LocExpr>)>),
    Frozen(Obj),
    Chain(Box<LocExpr>, Vec<(Box<LocExpr>, Box<LocExpr>)>),
    And(Box<LocExpr>, Box<LocExpr>),
    Or(Box<LocExpr>, Box<LocExpr>),
    Coalesce(Box<LocExpr>, Box<LocExpr>),
    Annotation(Box<LocExpr>, Option<Rc<LocExpr>>), // FIXME Rc? :(
    Consume(Box<Lvalue>),
    Pop(Box<Lvalue>),
    Remove(Box<Lvalue>),
    Swap(Box<Lvalue>, Box<Lvalue>),
    // bool: Every
    Assign(bool, Box<Lvalue>, Box<LocExpr>),
    OpAssign(bool, Box<Lvalue>, Box<LocExpr>, Box<LocExpr>),
    If(Box<LocExpr>, Box<LocExpr>, Option<Box<LocExpr>>),
    For(Vec<ForIteration>, Box<ForBody>),
    While(Box<LocExpr>, Box<LocExpr>),
    Switch(Box<LocExpr>, Vec<(Box<Lvalue>, Box<LocExpr>)>),
    Try(Box<LocExpr>, Box<Lvalue>, Box<LocExpr>),
    Break(usize, Option<Box<LocExpr>>),
    Continue(usize),
    Return(Option<Box<LocExpr>>),
    Throw(Box<LocExpr>),
    Sequence(Vec<Box<LocExpr>>, bool), // semicolon ending to swallow nulls
    Struct(Rc<String>, Vec<(Rc<String>, Option<Box<LocExpr>>)>),
    Freeze(Box<LocExpr>),
    Import(Box<LocExpr>),
    // lvalues only
    Literally(Box<LocExpr>),

    // these get cloned in particular
    Lambda(Rc<Vec<Box<Lvalue>>>, Rc<LocExpr>),

    // shouldn't stay in the tree:
    CommaSeq(Vec<Box<LocExpr>>),
    Splat(Box<LocExpr>),

    // hic sunt dracones
    InternalFrame(Box<LocExpr>),
    InternalPush(Box<LocExpr>),
    InternalPop,
    InternalPeek(usize), // from rear
    // for each element, push it, run the body, then restore stack length
    InternalFor(Box<LocExpr>, Box<LocExpr>),
    InternalCall(usize, Box<LocExpr>),
    InternalLambda(usize, Rc<LocExpr>),
}

impl Expr {
    fn constant_value(&self) -> Option<Obj> {
        match self {
            Expr::Null => Some(Obj::Null),
            Expr::IntLit64(x) => Some(Obj::from(NInt::Small(*x))),
            Expr::IntLit(x) => Some(Obj::from(x.clone())),
            Expr::RatLit(x) => Some(Obj::from(NNum::from(x.clone()))),
            Expr::FloatLit(x) => Some(Obj::from(*x)),
            Expr::ImaginaryFloatLit(x) => Some(Obj::Num(NNum::Complex(Complex64::new(0.0, *x)))),
            Expr::StringLit(s) => Some(Obj::Seq(Seq::String(Rc::clone(s)))),
            Expr::BytesLit(s) => Some(Obj::Seq(Seq::Bytes(Rc::clone(s)))),
            Expr::Frozen(x) => Some(x.clone()),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub enum Lvalue {
    Underscore,
    Literal(Obj),
    IndexedIdent(String, Vec<IndexOrSlice>),
    Annotation(Box<Lvalue>, Option<Rc<LocExpr>>), // FIXME Rc? :(
    CommaSeq(Vec<Box<Lvalue>>),
    Splat(Box<Lvalue>),
    Or(Box<Lvalue>, Box<Lvalue>),
    Destructure(Box<LocExpr>, Vec<Box<Lvalue>>),
    ChainDestructure(Box<Lvalue>, Vec<(Box<LocExpr>, Box<Lvalue>)>),
    Literally(Box<LocExpr>),
    InternalPeek(usize),
}

impl Lvalue {
    fn any_literals(&self) -> bool {
        match self {
            Lvalue::Underscore => false,
            Lvalue::Literal(_) => true,
            Lvalue::IndexedIdent(..) => false,
            Lvalue::Annotation(x, _) => x.any_literals(),
            Lvalue::CommaSeq(x) => x.iter().any(|e| e.any_literals()),
            Lvalue::Splat(x) => x.any_literals(),
            Lvalue::Or(a, b) => a.any_literals() || b.any_literals(),
            Lvalue::Destructure(_, vs) => vs.iter().any(|e| e.any_literals()),
            Lvalue::ChainDestructure(lv, vs) => {
                lv.any_literals() || vs.iter().any(|e| e.1.any_literals())
            }
            Lvalue::Literally(_) => true,
            Lvalue::InternalPeek(_) => false,
        }
    }

    pub fn collect_identifiers(&self, declared_only: bool) -> HashSet<String> {
        match self {
            Lvalue::Underscore => HashSet::new(),
            Lvalue::Literal(_) => HashSet::new(),
            Lvalue::IndexedIdent(x, _) => {
                if declared_only {
                    HashSet::new()
                } else {
                    HashSet::from([x.clone()])
                }
            }
            Lvalue::Annotation(x, _) => x.collect_identifiers(false),
            Lvalue::CommaSeq(x) => x
                .iter()
                .flat_map(|e| e.collect_identifiers(declared_only))
                .collect(),
            Lvalue::Splat(x) => x.collect_identifiers(declared_only),
            Lvalue::Or(a, b) => {
                // sus
                let mut s = a.collect_identifiers(declared_only);
                s.extend(b.collect_identifiers(declared_only));
                s
            }
            Lvalue::Destructure(_, b) => b
                .iter()
                .flat_map(|e| e.collect_identifiers(declared_only))
                .collect(),
            Lvalue::ChainDestructure(lv, vs) => {
                let mut s = lv.collect_identifiers(declared_only);
                for x in vs {
                    s.extend(x.1.collect_identifiers(declared_only));
                }
                s
            }
            Lvalue::Literally(_) => HashSet::new(),
            Lvalue::InternalPeek(_) => HashSet::new(),
        }
    }
}

// If two lvalues have the same archetype then they pattern-match the same values, so we can
// statically catch some mistakes where a switch expression has overlapping cases or a catch-all
// case followed by later cases. Very simple for now, don't think making this much more complicated
// will catch many more mistakes.
#[derive(Hash, PartialEq, Eq, Debug)]
enum LvalueArchetype {
    Anything,
    Seq(usize),
}

fn to_archetypes(lvalue: &Lvalue) -> Vec<LvalueArchetype> {
    match lvalue {
        Lvalue::Underscore => vec![LvalueArchetype::Anything],
        Lvalue::IndexedIdent(_, ixs) if ixs.is_empty() => vec![LvalueArchetype::Anything],
        Lvalue::CommaSeq(x) => {
            if x.iter()
                .map(|e| to_archetypes(e))
                .all(|e| e.contains(&LvalueArchetype::Anything))
            {
                vec![LvalueArchetype::Seq(x.len())]
            } else {
                Vec::new()
            }
        }
        Lvalue::Or(a, b) => {
            // sus
            let mut s = to_archetypes(a);
            s.extend(to_archetypes(b));
            s
        }
        _ => Vec::new(),
    }
}

pub trait Builtin: Debug + MaybeSync + MaybeSend {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj>;

    // there are a LOT of builtins who specialize based on how many arguments they get, and a LOT
    // of paths where we know how many arguments we're passing, so allow the two to be "manually
    // fused"
    fn run1(&self, env: &REnv, arg: Obj) -> NRes<Obj> {
        self.run(env, vec![arg])
    }
    fn run2(&self, env: &REnv, arg1: Obj, arg2: Obj) -> NRes<Obj> {
        self.run(env, vec![arg1, arg2])
    }

    // Used for builtins to identify each other, since comparing pointers is bad (?)
    // https://rust-lang.github.io/rust-clippy/master/#vtable_address_comparisons
    fn builtin_name(&self) -> &str;

    fn try_chain(&self, _other: &Func) -> Option<Func> {
        None
    }

    fn catamorphism(&self) -> Option<Box<dyn Catamorphism>> {
        None
    }

    // even if lhs has literals, return them verbatim anyway
    fn destructure(&self, rvalue: Obj, _lhs: Vec<Option<Obj>>) -> NRes<Vec<Obj>> {
        Err(NErr::type_error(format!(
            "{} cannot destructure {}",
            self.builtin_name(),
            rvalue
        )))
    }
}

pub trait Catamorphism {
    // can return Break
    fn give(&mut self, arg: Obj) -> NRes<()>;
    fn finish(&mut self) -> NRes<Obj>;
}

#[derive(Debug)]
pub enum ParseErrorLoc {
    Token(LocToken),
    Expr(CodeLoc, CodeLoc),
    Eof,
}
#[derive(Debug)]
pub struct ParseError(pub String, pub ParseErrorLoc, pub Vec<(String, CodeLoc)>);
impl ParseError {
    pub fn token(msg: String, token: LocToken) -> Self {
        ParseError(msg, ParseErrorLoc::Token(token), Vec::new())
    }
    pub fn expr(msg: String, start: CodeLoc, end: CodeLoc) -> Self {
        ParseError(msg, ParseErrorLoc::Expr(start, end), Vec::new())
    }
    pub fn eof(msg: String) -> Self {
        ParseError(msg, ParseErrorLoc::Eof, Vec::new())
    }

    pub fn render(self: ParseError, src: &str) -> String {
        let ParseError(msg, loc, trace) = self;
        use std::fmt::Write;
        let mut out = String::new();
        // I'm fairly confident these writes can't fail, at least at time of writing. But
        // since we are already error handling let's just ignore errors.
        writeln!(out, "{}", msg).ok();
        match loc {
            ParseErrorLoc::Token(tok) => {
                write_source_error(&mut out, src, &tok.start, &tok.end);
                write!(
                    out,
                    "\n    {:?} (at {})",
                    tok.token,
                    FmtCodeLocRange(&tok.start, &tok.end)
                )
                .ok();
            }
            ParseErrorLoc::Expr(start, end) => {
                write_source_error(&mut out, src, &start, &end);
                write!(out, "\n    (expr {})", FmtCodeLocRange(&start, &end)).ok();
            }
            ParseErrorLoc::Eof => {
                write!(out, "\n    at EOF").ok();
            }
        }
        for (ctx, loc) in trace {
            write!(out, "\n    at {} ({}:{})", ctx, loc.line, loc.col).ok();
        }
        out
    }
}

pub fn to_lvalue(expr: LocExpr) -> Result<Lvalue, ParseError> {
    match expr.expr {
        Expr::Null => Ok(Lvalue::Literal(Obj::Null)),
        Expr::Ident(s) => Ok(Lvalue::IndexedIdent(s, Vec::new())),
        Expr::Underscore => Ok(Lvalue::Underscore),
        Expr::Index(e, i) => match to_lvalue(*e)? {
            Lvalue::IndexedIdent(idn, mut ixs) => {
                ixs.push(i);
                Ok(Lvalue::IndexedIdent(idn, ixs))
            }
            ee => Err(ParseError::expr(
                format!("can't to_lvalue index of nonident {:?}", ee),
                expr.start,
                expr.end,
            )),
        },
        Expr::SymbolAccess(e, f) => match to_lvalue(*e)? {
            Lvalue::IndexedIdent(idn, mut ixs) => {
                ixs.push(IndexOrSlice::Symbol(f));
                Ok(Lvalue::IndexedIdent(idn, ixs))
            }
            ee => Err(ParseError::expr(
                format!("can't to_lvalue symbol of nonident {:?}", ee),
                expr.start,
                expr.end,
            )),
        },
        Expr::Annotation(e, t) => Ok(Lvalue::Annotation(Box::new(to_lvalue(*e)?), t)),
        Expr::CommaSeq(es) | Expr::List(es) => Ok(Lvalue::CommaSeq(
            es.into_iter()
                .map(|e| Ok(Box::new(to_lvalue(*e)?)))
                .collect::<Result<Vec<Box<Lvalue>>, ParseError>>()?,
        )),
        Expr::Splat(x) => Ok(Lvalue::Splat(Box::new(to_lvalue(*x)?))),
        Expr::IntLit64(n) => Ok(Lvalue::Literal(Obj::from(NInt::Small(n)))),
        Expr::IntLit(n) => Ok(Lvalue::Literal(Obj::from(n))),
        Expr::StringLit(n) => Ok(Lvalue::Literal(Obj::Seq(Seq::String(n)))),
        Expr::BytesLit(n) => Ok(Lvalue::Literal(Obj::Seq(Seq::Bytes(n)))),
        Expr::Or(a, b) => Ok(Lvalue::Or(
            Box::new(to_lvalue(*a)?),
            Box::new(to_lvalue(*b)?),
        )),
        Expr::Call(f, args, _) => Ok(Lvalue::Destructure(
            f,
            args.into_iter()
                .map(|e| Ok(Box::new(to_lvalue(*e)?)))
                .collect::<Result<Vec<Box<Lvalue>>, ParseError>>()?,
        )),
        Expr::Chain(lhs, args) => Ok(Lvalue::ChainDestructure(
            Box::new(to_lvalue(*lhs)?),
            args.into_iter()
                .map(|(e, v)| Ok((e, Box::new(to_lvalue(*v)?))))
                .collect::<Result<Vec<(Box<LocExpr>, Box<Lvalue>)>, ParseError>>()?,
        )),
        Expr::Literally(e) => Ok(Lvalue::Literally(e)),
        Expr::InternalPeek(i) => Ok(Lvalue::InternalPeek(i)),
        _ => Err(ParseError::expr(
            format!("can't to_lvalue"),
            expr.start,
            expr.end,
        )),
    }
}

pub fn to_lvalue_no_literals(expr: LocExpr) -> Result<Lvalue, ParseError> {
    let LocExpr { start, end, .. } = expr;
    let lvalue = to_lvalue(expr)?;
    if lvalue.any_literals() {
        Err(ParseError::expr(
            format!("lvalue can't have any literals"),
            start,
            end,
        ))
    } else {
        Ok(lvalue)
    }
}

#[derive(Clone)]
pub struct Closure {
    pub params: Rc<Vec<Box<Lvalue>>>,
    pub body: Rc<LocExpr>,
    pub env: Rc<RefCell<Env>>,
}

// directly debug-printing env can easily recurse infinitely
impl Debug for Closure {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            fmt,
            "Closure {{ params: {:?}, body: {:?}, env: ... }}",
            self.params, self.body
        )
    }
}

pub fn strip_comments(mut tokens: Vec<LocToken>) -> (Vec<LocToken>, Vec<String>) {
    let mut comments = Vec::new();
    tokens.retain_mut(|c| match &mut c.token {
        Token::Comment(s) => {
            comments.push(std::mem::take(s));
            false
        }
        _ => true,
    });
    (tokens, comments)
}

pub struct Parser {
    tokens: Vec<LocToken>,
    i: usize,
}

// This originally implemented the "freeze" keyword but is basically just a visitor pattern at this
// point. Some constant optimizations occur.
#[derive(Clone)]
pub struct FreezeEnv {
    pub bound: HashSet<String>,
    pub env: Rc<RefCell<Env>>,
    pub warn: bool,
}

impl FreezeEnv {
    fn bind(&mut self, ids: HashSet<String>) {
        if self.warn {
            let rebound = self.bound.intersection(&ids).collect::<Vec<&String>>();
            if !rebound.is_empty() {
                eprint!("\x1b[1;33mWARNING\x1b[0;33m: rebinding variables:");
                for r in rebound {
                    eprint!(" {}", r);
                }
                eprintln!("\x1b[0m");
            }
        }
        self.bound.extend(ids);
    }
}

fn vec_box_freeze(env: &mut FreezeEnv, expr: &Vec<Box<LocExpr>>) -> NRes<Vec<Box<LocExpr>>> {
    expr.iter().map(|x| box_freeze(env, x)).collect()
}
fn vec_box_freeze_underscore_ok(
    env: &mut FreezeEnv,
    expr: &Vec<Box<LocExpr>>,
) -> NRes<Vec<Box<LocExpr>>> {
    expr.iter()
        .map(|x| box_freeze_underscore_ok(env, x))
        .collect()
}
fn box_freeze(env: &mut FreezeEnv, expr: &Box<LocExpr>) -> NRes<Box<LocExpr>> {
    Ok(Box::new(freeze(env, expr)?))
}
fn box_freeze_underscore_ok(env: &mut FreezeEnv, expr: &Box<LocExpr>) -> NRes<Box<LocExpr>> {
    match expr.expr {
        Expr::Underscore => Ok(Box::new(LocExpr {
            expr: Expr::Underscore,
            start: expr.start,
            end: expr.end,
        })),
        _ => box_freeze(env, expr),
    }
}
fn opt_box_freeze(env: &mut FreezeEnv, expr: &Option<Box<LocExpr>>) -> NRes<Option<Box<LocExpr>>> {
    match expr {
        Some(x) => Ok(Some(Box::new(freeze(env, x)?))),
        None => Ok(None),
    }
}

fn opt_rc_freeze(env: &mut FreezeEnv, expr: &Option<Rc<LocExpr>>) -> NRes<Option<Rc<LocExpr>>> {
    match expr {
        Some(x) => Ok(Some(Rc::new(freeze(env, x)?))),
        None => Ok(None),
    }
}

fn box_freeze_lvalue(env: &mut FreezeEnv, lvalue: &Box<Lvalue>) -> NRes<Box<Lvalue>> {
    Ok(Box::new(freeze_lvalue(env, lvalue)?))
}

fn freeze_lvalue(env: &mut FreezeEnv, lvalue: &Lvalue) -> NRes<Lvalue> {
    match lvalue {
        Lvalue::Underscore => Ok(Lvalue::Underscore),
        Lvalue::Literal(x) => Ok(Lvalue::Literal(x.clone())),
        Lvalue::IndexedIdent(s, ioses) => {
            if env.bound.contains(s) {
                Ok(Lvalue::IndexedIdent(
                    s.clone(),
                    ioses
                        .iter()
                        .map(|ios| freeze_ios(env, ios))
                        .collect::<NRes<Vec<IndexOrSlice>>>()?,
                ))
            } else if env.warn {
                eprintln!(
                    "\x1b[1;33mWARNING\x1b[0;33m: ident in lvalue not bound: {}\x1b[0m",
                    s
                );
                env.bound.insert(s.clone());
                Ok(Lvalue::IndexedIdent(
                    s.clone(),
                    ioses
                        .iter()
                        .map(|ios| freeze_ios(env, ios))
                        .collect::<NRes<Vec<IndexOrSlice>>>()?,
                ))
            } else {
                Err(NErr::name_error(format!(
                    "ident in lvalue not bound: {}",
                    s
                )))
            }
        }
        Lvalue::Annotation(x, e) => Ok(Lvalue::Annotation(
            box_freeze_lvalue(env, x)?,
            opt_rc_freeze(env, e)?,
        )),
        Lvalue::CommaSeq(x) => Ok(Lvalue::CommaSeq(
            x.iter()
                .map(|e| box_freeze_lvalue(env, e))
                .collect::<NRes<Vec<Box<Lvalue>>>>()?,
        )),
        Lvalue::Splat(x) => Ok(Lvalue::Splat(box_freeze_lvalue(env, x)?)),
        Lvalue::Or(a, b) => Ok(Lvalue::Or(
            box_freeze_lvalue(env, a)?,
            box_freeze_lvalue(env, b)?,
        )),
        Lvalue::Destructure(f, args) => Ok(Lvalue::Destructure(
            box_freeze(env, f)?,
            args.iter()
                .map(|e| box_freeze_lvalue(env, e))
                .collect::<NRes<Vec<Box<Lvalue>>>>()?,
        )),
        Lvalue::ChainDestructure(f, args) => Ok(Lvalue::ChainDestructure(
            box_freeze_lvalue(env, f)?,
            args.iter()
                .map(|(e, v)| Ok((box_freeze(env, e)?, box_freeze_lvalue(env, v)?)))
                .collect::<NRes<Vec<(Box<LocExpr>, Box<Lvalue>)>>>()?,
        )),
        Lvalue::Literally(e) => Ok(Lvalue::Literally(box_freeze(env, e)?)),
        Lvalue::InternalPeek(e) => Ok(Lvalue::InternalPeek(*e)),
    }
}

fn freeze_ios(env: &mut FreezeEnv, ios: &IndexOrSlice) -> NRes<IndexOrSlice> {
    match ios {
        IndexOrSlice::Index(i) => Ok(IndexOrSlice::Index(box_freeze_underscore_ok(env, i)?)),
        IndexOrSlice::Slice(i, j) => Ok(IndexOrSlice::Slice(
            opt_box_freeze(env, i)?,
            opt_box_freeze(env, j)?,
        )),
        IndexOrSlice::Symbol(s) => Ok(IndexOrSlice::Symbol(Rc::clone(s))),
    }
}

// OK what's the actual contract of this function
//
// Given an expression, go through it and resolve all free variables (those not bound by
// declarations internal to the expression) to their values in the outer env. Also collect
// bound variables. Error if
//
// - any free variable isn't found in the outer env
// - any free variables are assigned to
// - (??) any bound variable is redeclared
//
// This is fragile because it has its own idea of what things introduce scopes and one day it wil
// get out of sync with the actual evaluation code. Shrug.

pub fn freeze(env: &mut FreezeEnv, expr: &LocExpr) -> NRes<LocExpr> {
    Ok(LocExpr {
        start: expr.start,
        end: expr.end,
        expr: match &expr.expr {
            Expr::Null => Ok(Expr::Null),
            Expr::IntLit64(x) => Ok(Expr::IntLit64(*x)),
            Expr::IntLit(x) => Ok(Expr::IntLit(x.clone())),
            Expr::RatLit(x) => Ok(Expr::RatLit(x.clone())),
            Expr::FloatLit(x) => Ok(Expr::FloatLit(x.clone())),
            Expr::ImaginaryFloatLit(x) => Ok(Expr::ImaginaryFloatLit(x.clone())),
            Expr::StringLit(x) => Ok(Expr::StringLit(x.clone())),
            Expr::Symbol(x) => Ok(Expr::Symbol(x.clone())),
            Expr::BytesLit(x) => Ok(Expr::BytesLit(x.clone())),
            Expr::Backref(x) => Ok(Expr::Backref(x.clone())),
            Expr::Frozen(x) => Ok(Expr::Frozen(x.clone())),
            Expr::Struct(name, field_names) => {
                env.bind(HashSet::from([(&**name).clone()]));
                env.bind(
                    field_names
                        .iter()
                        .map(|s| (&*((*s).0)).clone())
                        .collect::<HashSet<String>>(),
                );
                Ok(Expr::Struct(
                    name.clone(),
                    field_names
                        .iter()
                        .map(|(name, def)| Ok((name.clone(), opt_box_freeze(env, def)?)))
                        .collect::<NRes<_>>()?,
                ))
            }
            Expr::FormatString(s) => Ok(Expr::FormatString(
                s.iter()
                    .map(|x| match x {
                        Ok(c) => Ok(Ok(*c)),
                        Err((e, ff)) => Ok(Err((freeze(env, e)?, ff.clone()))),
                    })
                    .collect::<NRes<Vec<Result<char, (LocExpr, MyFmtFlags)>>>>()?,
            )),
            Expr::Ident(s) => {
                if env.bound.contains(s) {
                    Ok(Expr::Ident(s.clone()))
                } else {
                    match Env::try_borrow_get_var(&env.env, s) {
                        Ok(v) => Ok(Expr::Frozen(v)),
                        Err(e) => {
                            if env.warn {
                                eprintln!(
                                    "\x1b[1;33mWARNING\x1b[0;33m: variable not found: {} (at {})\x1b[0m",
                                    s,
                                    FmtCodeLocRange(&expr.start, &expr.end)
                                );
                                env.bound.insert(s.clone());
                                Ok(Expr::Ident(s.clone()))
                            } else {
                                Err(e)
                            }
                        }
                    }
                }
            }
            Expr::Underscore => {
                if env.warn {
                    eprintln!("\x1b[1;33mWARNING\x1b[0;33m: underscore??\x1b[0m",);
                    Ok(Expr::Underscore)
                } else {
                    Err(NErr::syntax_error_loc(
                        "Can't freeze underscore".to_string(),
                        "_".to_string(),
                        expr.start,
                        expr.end,
                    ))
                }
            }
            Expr::Index(x, ios) => Ok(Expr::Index(
                box_freeze_underscore_ok(env, x)?,
                freeze_ios(env, ios)?,
            )),
            Expr::Update(x, ps) => Ok(Expr::Update(
                box_freeze_underscore_ok(env, x)?,
                ps.iter()
                    .map(|(k, v)| Ok((box_freeze(env, k)?, box_freeze(env, v)?)))
                    .collect::<NRes<Vec<(Box<LocExpr>, Box<LocExpr>)>>>()?,
            )),
            Expr::Chain(op1, ops) => Ok(Expr::Chain(
                box_freeze_underscore_ok(env, op1)?,
                ops.iter()
                    .map(|(op, d)| Ok((box_freeze(env, op)?, box_freeze_underscore_ok(env, d)?)))
                    .collect::<NRes<Vec<(Box<LocExpr>, Box<LocExpr>)>>>()?,
            )),
            Expr::And(lhs, rhs) => Ok(Expr::And(box_freeze(env, lhs)?, box_freeze(env, rhs)?)),
            Expr::Or(lhs, rhs) => Ok(Expr::Or(box_freeze(env, lhs)?, box_freeze(env, rhs)?)),
            Expr::Coalesce(lhs, rhs) => {
                Ok(Expr::Coalesce(box_freeze(env, lhs)?, box_freeze(env, rhs)?))
            }
            Expr::Assign(every, pat, rhs) => {
                // have to bind first so box_freeze_lvalue works
                // also recursive functions work ig
                env.bind(pat.collect_identifiers(true /* declared_only */));

                let lvalue = box_freeze_lvalue(env, pat)?;
                Ok(Expr::Assign(*every, lvalue, box_freeze(env, rhs)?))
            }
            Expr::Annotation(s, t) => Ok(Expr::Annotation(
                box_freeze(env, s)?,
                opt_rc_freeze(env, t)?,
            )),
            Expr::Consume(pat) => Ok(Expr::Consume(box_freeze_lvalue(env, pat)?)),
            Expr::Pop(pat) => Ok(Expr::Pop(box_freeze_lvalue(env, pat)?)),
            Expr::Remove(pat) => Ok(Expr::Remove(box_freeze_lvalue(env, pat)?)),
            Expr::Swap(a, b) => Ok(Expr::Swap(
                box_freeze_lvalue(env, a)?,
                box_freeze_lvalue(env, b)?,
            )),
            Expr::OpAssign(every, pat, op, rhs) => Ok(Expr::OpAssign(
                *every,
                box_freeze_lvalue(env, pat)?,
                box_freeze(env, op)?,
                box_freeze(env, rhs)?,
            )),
            Expr::Call(f, args, syntax) => {
                let f = box_freeze_underscore_ok(env, f)?;
                let args = vec_box_freeze_underscore_ok(env, args)?;
                let opt_result = match f.expr.constant_value() {
                    Some(Obj::Func(Func::Builtin(b), _)) => {
                        if b.builtin_name() == "-" && args.len() == 1 {
                            match args[0].expr.constant_value() {
                                Some(Obj::Num(x)) => Some(Obj::from(-x)),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                match opt_result {
                    Some(x) => Ok(Expr::Frozen(x)),
                    None => Ok(Expr::Call(f, args, *syntax)),
                }
            }
            Expr::SymbolAccess(e, f) => Ok(Expr::SymbolAccess(box_freeze(env, e)?, f.clone())),
            Expr::CommaSeq(s) => Ok(Expr::CommaSeq(vec_box_freeze(env, s)?)),
            Expr::Splat(s) => Ok(Expr::Splat(box_freeze(env, s)?)),
            Expr::List(xs) => {
                let v = vec_box_freeze_underscore_ok(env, xs)?;
                match v
                    .iter()
                    .map(|e| e.expr.constant_value())
                    .collect::<Option<Vec<Obj>>>()
                {
                    Some(xs) => Ok(Expr::Frozen(Obj::list(xs))),
                    None => Ok(Expr::List(v)),
                }
            }
            Expr::Vector(xs) => Ok(Expr::Vector(vec_box_freeze(env, xs)?)),
            Expr::Dict(def, xs) => Ok(Expr::Dict(
                opt_box_freeze(env, def)?,
                xs.iter()
                    .map(|(k, v)| Ok((box_freeze(env, k)?, opt_box_freeze(env, v)?)))
                    .collect::<NRes<Vec<(Box<LocExpr>, Option<Box<LocExpr>>)>>>()?,
            )),
            Expr::Sequence(xs, es) => Ok(Expr::Sequence(vec_box_freeze(env, xs)?, *es)),
            Expr::If(a, b, c) => Ok(Expr::If(
                box_freeze(env, a)?,
                box_freeze(env, b)?,
                opt_box_freeze(env, c)?,
            )),
            Expr::For(iteratees, body) => {
                if env.warn {
                    match &**body {
                        ForBody::Yield(
                            LocExpr {
                                expr: Expr::Sequence(_, true),
                                ..
                            },
                            _,
                        ) => {
                            eprintln!("\x1b[1;33mWARNING\x1b[0;33m: for loop yields semicolon-terminated sequence (at {})\x1b[0m",
                                    FmtCodeLocRange(&expr.start, &expr.end)
                            );
                        }
                        _ => {}
                    }
                }

                let mut env2 = env.clone();
                Ok(Expr::For(
                    iteratees
                        .iter()
                        .map(|x| match x {
                            ForIteration::Iteration(ty, lv, expr) => {
                                // have to bind first so box_freeze_lvalue works
                                // also recursive functions work ig
                                env2.bind(lv.collect_identifiers(
                                    match ty {
                                        ForIterationType::Normal => false,
                                        ForIterationType::Item => false,
                                        ForIterationType::Declare => true, // thonk
                                    }, /* declared_only */
                                ));
                                Ok(ForIteration::Iteration(
                                    *ty,
                                    box_freeze_lvalue(&mut env2, lv)?,
                                    box_freeze(&mut env2, expr)?,
                                ))
                            }
                            ForIteration::Guard(expr) => {
                                Ok(ForIteration::Guard(box_freeze(&mut env2, expr)?))
                            }
                        })
                        .collect::<NRes<Vec<ForIteration>>>()?,
                    Box::new(match &**body {
                        ForBody::Execute(b) => ForBody::Execute(freeze(&mut env2, b)?),
                        ForBody::Yield(b, None) => ForBody::Yield(freeze(&mut env2, b)?, None),
                        // this is technically wrong order
                        ForBody::Yield(b, Some(s)) => {
                            ForBody::Yield(freeze(&mut env2, b)?, Some(freeze(&mut env2, s)?))
                        }
                        ForBody::YieldItem(kb, vb) => {
                            ForBody::YieldItem(freeze(&mut env2, kb)?, freeze(&mut env2, vb)?)
                        }
                    }),
                ))
            }
            Expr::While(cond, body) => {
                let mut env2 = env.clone();
                Ok(Expr::While(
                    box_freeze(&mut env2, cond)?,
                    box_freeze(&mut env2, body)?,
                ))
            }
            Expr::Switch(scrutinee, arms) => {
                let mut seen = HashSet::new();
                Ok(Expr::Switch(
                    box_freeze(env, scrutinee)?,
                    arms.iter()
                        .map(|(pat, rhs)| {
                            if env.warn {
                                for t in to_archetypes(pat) {
                                    // FIXME: we really really should report the pat's location but
                                    // we don't track it now lmao
                                    if seen.contains(&LvalueArchetype::Anything) {
                                        eprintln!("\x1b[1;33mWARNING\x1b[0;33m: unreachable pattern in switch after a catch-all pattern (at {})\x1b[0m",
                                        FmtCodeLocRange(&rhs.start, &rhs.end));
                                    } else if !seen.insert(t) {
                                        eprintln!("\x1b[1;33mWARNING\x1b[0;33m: unreachable pattern in switch, already saw same pattern (at {})\x1b[0m",
                                        FmtCodeLocRange(&rhs.start, &rhs.end));
                                    }
                                }
                            }

                            let mut env2 = env.clone();
                            env2.bind(pat.collect_identifiers(false /* declared_only */));
                            Ok((
                                box_freeze_lvalue(&mut env2, pat)?,
                                box_freeze(&mut env2, rhs)?,
                            ))
                        })
                        .collect::<NRes<Vec<(Box<Lvalue>, Box<LocExpr>)>>>()?,
                ))
            }
            Expr::Try(a, pat, catcher) => {
                // FIXME hmmm is the main try branch really scoped this way
                let body = box_freeze(env, a)?;
                let mut env2 = env.clone();
                env2.bind(pat.collect_identifiers(false /* declared_only */));
                Ok(Expr::Try(
                    body,
                    box_freeze_lvalue(&mut env2, pat)?,
                    box_freeze(&mut env2, catcher)?,
                ))
            }
            Expr::Lambda(params, body) => {
                let mut env2 = env.clone();
                env2.bind(
                    params
                        .iter()
                        .flat_map(|x| x.collect_identifiers(false /* declared_only */))
                        .collect::<HashSet<String>>(),
                );
                Ok(Expr::Lambda(
                    params.clone(),
                    Rc::new(freeze(&mut env2, body)?),
                ))
            }
            Expr::Freeze(e) => Ok(Expr::Freeze(box_freeze(env, e)?)),
            Expr::Import(e) => {
                if env.warn {
                    match &e.expr {
                        // FIXME refactor out with freeze
                        Expr::StringLit(s) => {
                            match fs::read_to_string(&**s) {
                                Ok(c) => match parse(&c) {
                                    Ok(Some(code)) => match freeze(env, &code) {
                                        Ok(_) => {}
                                        Err(e) => {
                                            eprintln!("\x1b[1;33mWARNING\x1b[0;33m: analyzing import failed: {}\x1b[0m", e.render(&c));
                                        }
                                    },
                                    Ok(None) => {
                                        eprintln!("\x1b[1;33mWARNING\x1b[0;33m: import of empty file\x1b[0m");
                                    }
                                    Err(s) => {
                                        eprintln!(
                                            "\x1b[1;33mWARNING\x1b[0;33m: lexing import failed: {}\x1b[0m",
                                            s.render(&c)
                                        );
                                    }
                                },
                                Err(e) => {
                                    eprintln!(
                                    "\x1b[1;33mWARNING\x1b[0;33m: io error when handling import: {}\x1b[0m",
                                    e
                                );
                                }
                            }
                        }
                        inner => {
                            eprintln!(
                                "\x1b[1;33mWARNING\x1b[0;33m: can't handle nonliteral import: {:?}\x1b[0m",
                                inner
                            );
                        }
                    }
                    Ok(Expr::Import(box_freeze(env, e)?))
                } else {
                    Err(NErr::syntax_error(format!("cannot freeze import")))
                }
            }
            Expr::Literally(e) => Ok(Expr::Literally(box_freeze(env, e)?)),

            Expr::Break(n, e) => Ok(Expr::Break(*n, opt_box_freeze(env, e)?)),
            Expr::Return(e) => Ok(Expr::Return(opt_box_freeze(env, e)?)),
            Expr::Throw(e) => Ok(Expr::Throw(box_freeze(env, e)?)),
            Expr::Continue(n) => Ok(Expr::Continue(*n)),

            Expr::InternalFrame(e) => Ok(Expr::InternalFrame(box_freeze(env, e)?)),
            Expr::InternalPush(e) => Ok(Expr::InternalPush(box_freeze(env, e)?)),
            Expr::InternalPop => Ok(Expr::InternalPop),
            Expr::InternalPeek(n) => Ok(Expr::InternalPeek(*n)),
            Expr::InternalFor(iteratee, body) => Ok(Expr::InternalFor(
                box_freeze(env, iteratee)?,
                box_freeze(env, body)?,
            )),
            Expr::InternalCall(argc, e) => Ok(Expr::InternalCall(*argc, box_freeze(env, e)?)),
            Expr::InternalLambda(argc, body) => {
                Ok(Expr::InternalLambda(*argc, Rc::new(freeze(env, body)?)))
            }
        }?,
    })
}

fn err_add_context(
    a: Result<LocExpr, ParseError>,
    ctx: &str,
    loc: CodeLoc,
) -> Result<LocExpr, ParseError> {
    match a {
        Ok(t) => Ok(t),
        Err(mut s) => {
            s.2.push((ctx.to_string(), loc));
            Err(s)
        }
    }
}

fn parse_format_string(
    s: &str,
    outer_token: &LocToken,
) -> Result<Vec<Result<char, (LocExpr, MyFmtFlags)>>, ParseError> {
    let mut nesting_level = 0;
    let mut ret: Vec<Result<char, (LocExpr, MyFmtFlags)>> = Vec::new();
    let mut expr_acc = String::new(); // accumulate
    let mut p = s.chars().peekable();
    while let Some(c) = p.next() {
        match (nesting_level, c) {
            (0, '{') => {
                if p.peek() == Some(&'{') {
                    p.next();
                    ret.push(Ok('{'));
                } else {
                    nesting_level += 1;
                }
            }
            (0, '}') => {
                if p.peek() == Some(&'}') {
                    p.next();
                    ret.push(Ok('}'));
                } else {
                    return Err(ParseError::token(
                        "format string: unmatched right brace".to_string(),
                        outer_token.clone(),
                    ));
                }
            }
            (0, c) => {
                ret.push(Ok(c));
            }
            (_, '{') => {
                nesting_level += 1;
                expr_acc.push('{');
            }
            (1, '}') => {
                nesting_level -= 1;

                let mut lexer = Lexer::new(&expr_acc);
                lexer.lex();
                let mut flags = MyFmtFlags::new();
                let (tokens, comments) = strip_comments(lexer.tokens);
                if tokens.is_empty() {
                    return Err(ParseError::token(
                        "format string: empty format expr".to_string(),
                        outer_token.clone(),
                    ));
                } else {
                    for com in comments {
                        let mut it = com.chars().peekable();
                        while let Some(c) = it.next() {
                            match c {
                                'x' => {
                                    flags.base = FmtBase::LowerHex;
                                }
                                'X' => {
                                    flags.base = FmtBase::UpperHex;
                                }
                                'b' | 'B' => {
                                    flags.base = FmtBase::Binary;
                                }
                                'o' | 'O' => {
                                    flags.base = FmtBase::Octal;
                                }
                                // 'e' => { flags.base = FmtBase::LowerExp; }
                                // 'E' => { flags.base = FmtBase::UpperExp; }
                                'd' | 'D' => {
                                    flags.base = FmtBase::Decimal;
                                }
                                '<' => {
                                    flags.pad_align = FmtAlign::Left;
                                }
                                '>' => {
                                    flags.pad_align = FmtAlign::Right;
                                }
                                '^' => {
                                    flags.pad_align = FmtAlign::Center;
                                }
                                '0' => {
                                    flags.pad = '0';
                                }
                                d if d.is_digit(10) => {
                                    let mut acc = d.to_string();
                                    loop {
                                        match it.peek().filter(|d| d.is_digit(10)).cloned() {
                                            Some(d) => {
                                                it.next();
                                                acc.push(d)
                                            }
                                            None => break,
                                        }
                                    }
                                    match acc.parse::<usize>() {
                                        Ok(s) => flags.pad_length = s,
                                        Err(e) => {
                                            return Err(ParseError::token(
                                                format!(
                                                    "format string: pad length couldn't parse: {}",
                                                    e
                                                ),
                                                outer_token.clone(),
                                            ))
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    let mut p = Parser { tokens, i: 0 };
                    let fex = p.expression().map_err(|mut e| {
                        e.0 = format!("format string: failed to parse expr: {}", e.0);
                        e
                    })?;
                    if p.is_at_end() {
                        ret.push(Err((fex, flags)));
                    } else {
                        return Err(ParseError::token(
                            "format string: couldn't finish parsing format expr".to_string(),
                            outer_token.clone(),
                        ));
                    }
                }
                expr_acc.clear();
            }
            (_, '}') => {
                nesting_level -= 1;
                expr_acc.push('}');
            }
            (_, c) => expr_acc.push(c),
        }
    }
    if nesting_level != 0 {
        return Err(ParseError::token(
            "format string: unmatched left brace".to_string(),
            outer_token.clone(),
        ));
    }
    Ok(ret)
}

impl Parser {
    fn peek_loc_token(&self) -> Option<&LocToken> {
        self.tokens.get(self.i)
    }
    fn error_here(&self, msg: String) -> ParseError {
        ParseError(
            msg,
            match self.peek_loc_token() {
                Some(token) => ParseErrorLoc::Token(token.clone()),
                None => ParseErrorLoc::Eof,
            },
            Vec::new(),
        )
    }

    fn peek(&self) -> Option<&Token> {
        self.peek_loc_token().map(|lt| &lt.token)
    }

    fn advance(&mut self) {
        self.i += 1;
    }

    fn try_consume(&mut self, desired: &Token) -> Option<CodeLoc> {
        match self.peek_loc_token() {
            Some(LocToken {
                token,
                start: _,
                end,
            }) => {
                let end = *end;
                if token == desired {
                    self.advance();
                    Some(end)
                } else {
                    None
                }
            }
            None => None,
        }
    }

    // consuming an int that's not a usize is an error
    fn try_consume_usize(&mut self, message: &str) -> Result<Option<(CodeLoc, usize)>, ParseError> {
        if let Some(LocToken {
            start: _,
            end,
            token: Token::IntLit(i),
        }) = self.peek_loc_token()
        {
            let us = i
                .to_usize()
                .ok_or(self.error_here(format!("{}: not usize: {}", message, i)))?;
            let end = *end;
            self.advance();
            Ok(Some((end, us)))
        } else {
            Ok(None)
        }
    }

    // consuming an int that's not a u8 is an error
    fn try_consume_u8(&mut self, message: &str) -> Result<Option<(CodeLoc, u8)>, ParseError> {
        if let Some(LocToken {
            start: _,
            end,
            token: Token::IntLit(i),
        }) = self.peek_loc_token()
        {
            let us = i
                .to_u8()
                .ok_or(self.error_here(format!("{}: not u8: {}", message, i)))?;
            let end = *end;
            self.advance();
            Ok(Some((end, us)))
        } else {
            Ok(None)
        }
    }

    fn peek_loc(&self) -> CodeLoc {
        match self.peek_loc_token() {
            Some(t) => t.start,
            // FIXME
            None => CodeLoc {
                line: 0,
                col: 0,
                index: 0,
            },
        }
    }

    fn peek_err(&self) -> String {
        match self.tokens.get(self.i) {
            Some(LocToken { token, start, end }) => {
                format!("{:?} (at {})", token, FmtCodeLocRange(start, end))
            }
            None => "EOF".to_string(),
        }
    }

    fn require(&mut self, expected: Token, message: &str) -> Result<CodeLoc, ParseError> {
        if let Some(end) = self.try_consume(&expected) {
            // wat
            Ok(end)
        } else {
            Err(self.error_here(format!("{}; required {:?}", message, expected)))
        }
    }

    fn atom(&mut self) -> Result<LocExpr, ParseError> {
        if let Some(ltref @ LocToken { start, end, token }) = self.peek_loc_token() {
            let start = *start;
            let end = *end;
            let loc_token = ltref.clone();
            match token {
                Token::Null => {
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::Null,
                    })
                }
                Token::IntLit(n) => {
                    let n = n.clone();
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: match n.to_i64() {
                            Some(n) => Expr::IntLit64(n),
                            None => Expr::IntLit(n),
                        },
                    })
                }
                Token::RatLit(n) => {
                    let n = n.clone();
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::RatLit(n),
                    })
                }
                Token::FloatLit(n) => {
                    let n = *n;
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::FloatLit(n),
                    })
                }
                Token::ImaginaryFloatLit(n) => {
                    let n = *n;
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::ImaginaryFloatLit(n),
                    })
                }
                Token::StringLit(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::StringLit(s),
                    })
                }
                Token::BytesLit(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(LocExpr {
                        expr: Expr::BytesLit(s),
                        start,
                        end,
                    })
                }
                Token::FormatString(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::FormatString(parse_format_string(&s, &loc_token)?),
                    })
                }
                Token::Underscore => {
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::Underscore,
                    })
                }
                Token::Ident(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::Ident(s),
                    })
                }
                Token::DoubleColon => {
                    self.advance();
                    match self.peek_loc_token() {
                        Some(LocToken {
                            token: Token::Ident(name),
                            start: _id_start,
                            end: id_end,
                        }) => {
                            let name = name.clone();
                            let end = *id_end;
                            self.advance();
                            Ok(LocExpr {
                                start,
                                end,
                                expr: Expr::Symbol(Rc::new(name)),
                            })
                        }
                        _ => Err(self.error_here(format!("double colon symbol: unexpected"))),
                    }
                }
                Token::Ellipsis => {
                    self.advance();
                    let s = self.single("ellipsis")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::Splat(Box::new(s)),
                    })
                }
                Token::Consume => {
                    self.advance();
                    let s = self.single("consume")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::Consume(Box::new(to_lvalue_no_literals(s)?)),
                    })
                }
                Token::Pop => {
                    self.advance();
                    let s = self.single("pop")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::Pop(Box::new(to_lvalue_no_literals(s)?)),
                    })
                }
                Token::Remove => {
                    self.advance();
                    let s = self.single("remove")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::Remove(Box::new(to_lvalue_no_literals(s)?)),
                    })
                }
                Token::Break => {
                    self.advance();
                    let mut n: usize = 0;
                    let mut end = end;
                    while let Some(e) = self.try_consume(&Token::Break) {
                        n += 1;
                        end = e;
                    }
                    if let Some(end) = self.try_consume(&Token::Continue) {
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::Continue(n + 1),
                        })
                    } else if self.peek_csc_stopper() {
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::Break(n, None),
                        })
                    } else {
                        let s = self.single("break")?;
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::Break(n, Some(Box::new(s))),
                        })
                    }
                }
                Token::Throw => {
                    self.advance();
                    let s = self.single("throw")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::Throw(Box::new(s)),
                    })
                }
                Token::Continue => {
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::Continue(0),
                    })
                }
                Token::Return => {
                    self.advance();
                    if self.peek_csc_stopper() {
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::Return(None),
                        })
                    } else {
                        let s = self.single("return")?;
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::Return(Some(Box::new(s))),
                        })
                    }
                }
                Token::Literally => {
                    self.advance();
                    let s = self.single("literally")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::Literally(Box::new(s)),
                    })
                }
                Token::Freeze => {
                    self.advance();
                    let s = self.single("freeze")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::Freeze(Box::new(s)),
                    })
                }
                Token::Import => {
                    self.advance();
                    let s = self.single("import")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::Import(Box::new(s)),
                    })
                }
                Token::LeftParen => {
                    self.advance();
                    let e = self.expression()?;
                    self.require(Token::RightParen, "normal parenthesized expr")?;
                    Ok(e)
                }
                Token::VLeftParen => {
                    self.advance();
                    if let Some(end) = self.try_consume(&Token::RightParen) {
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::Vector(Vec::new()),
                        })
                    } else {
                        let (exs, _) =
                            self.annotated_comma_separated(false, "vector lit contents")?;
                        let end = self.require(Token::RightParen, "vector expr")?;
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::Vector(exs),
                        })
                    }
                }
                Token::LeftBracket => {
                    self.advance();
                    if let Some(end) = self.try_consume(&Token::RightBracket) {
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::List(Vec::new()),
                        })
                    } else {
                        let (exs, _) =
                            self.annotated_comma_separated(false, "list lit contents")?;
                        let end = self.require(Token::RightBracket, "list expr")?;
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::List(exs),
                        })
                    }
                }
                Token::BLeftBracket => {
                    self.advance();
                    if let Some(end) = self.try_consume(&Token::RightBracket) {
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::BytesLit(Rc::new(Vec::new())),
                        })
                    } else if let Some((_, b)) = self.try_consume_u8("bytes lit 0")? {
                        let mut bytes = vec![b];
                        while self.peek() == Some(&Token::Comma) {
                            self.advance();
                            if self.peek() == Some(&Token::RightBracket) {
                                break;
                            }
                            if let Some((_, b)) = self.try_consume_u8("bytes lit cont")? {
                                bytes.push(b);
                            } else {
                                return Err(self.error_here(format!("bytes lit: unexpected")));
                            }
                        }

                        let end = self.require(Token::RightBracket, "bytes expr")?;
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::BytesLit(Rc::new(bytes)),
                        })
                    } else {
                        Err(self.error_here(format!("bytes lit: unexpected")))
                    }
                }
                Token::LeftBrace => {
                    self.advance();
                    // Dict(Vec<(Box<Expr>, Option<Box<Expr>>)>),
                    let mut xs = Vec::new();
                    let mut def = None;
                    if let Some(_) = self.try_consume(&Token::Colon) {
                        def = Some(Box::new(self.single("default of dict literal")?));
                        if !self.peek_csc_stopper() {
                            self.require(Token::Comma, "dict expr")?;
                        }
                    }

                    while !self.peek_csc_stopper() {
                        let c1 = Box::new(self.single("key of dict literal")?);
                        let c2 = if let Some(_) = self.try_consume(&Token::Colon) {
                            Some(Box::new(self.single("value of dict literal")?))
                        } else {
                            None
                        };
                        xs.push((c1, c2));

                        if !self.peek_csc_stopper() {
                            self.require(Token::Comma, "dict expr")?;
                        }
                    }
                    let end = self.require(Token::RightBrace, "dict expr end")?;
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::Dict(def, xs),
                    })
                }
                Token::RightParen => Err(self.error_here(format!("atom: unexpected"))),
                Token::Lambda => {
                    self.advance();
                    if let Some((end, us)) = self.try_consume_usize("backref")? {
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::Backref(us),
                        })
                    } else {
                        match self.peek_loc_token() {
                            Some(LocToken {
                                token: Token::Switch,
                                start: switch_start,
                                end: switch_end,
                            }) => {
                                // "magic" variable normally inexpressible
                                let param = Lvalue::IndexedIdent("switch".to_string(), Vec::new());
                                let scrutinee = LocExpr {
                                    expr: Expr::Ident("switch".to_string()),
                                    start: *switch_start,
                                    end: *switch_end,
                                };
                                self.advance();

                                let mut v = Vec::new();
                                // FIXME copypasta...
                                while let Some(_) = self.try_consume(&Token::Case) {
                                    let pat = to_lvalue(
                                        self.annotated_pattern(true, "lambda-switch pat")?,
                                    )?;
                                    self.require(Token::RightArrow, "lambda-case mid: ->")?;
                                    let res = self.single("lambda-switch body")?;
                                    v.push((Box::new(pat), Box::new(res)));
                                }
                                match v.last() {
                                    Some((_, e)) => {
                                        let end = e.end;
                                        Ok(LocExpr {
                                            start,
                                            end: e.end,
                                            expr: Expr::Lambda(
                                                Rc::new(vec![Box::new(param)]),
                                                Rc::new(LocExpr {
                                                    expr: Expr::Switch(Box::new(scrutinee), v),
                                                    start,
                                                    end,
                                                }),
                                            ),
                                        })
                                    }
                                    None => {
                                        Err(self.error_here(format!("lambda-switch: no cases")))?
                                    }
                                }
                            }
                            _ => {
                                let params = if self.try_consume(&Token::RightArrow).is_some() {
                                    Vec::new()
                                } else {
                                    // Hmm. In a lambda, `a` and `a,` are the same, but on the LHS of an
                                    // assignment the second unpacks.
                                    let params0 =
                                        self.annotated_comma_separated(true, "lambda params")?;
                                    let ps = params0
                                        .0
                                        .into_iter()
                                        .map(|p| Ok(Box::new(to_lvalue_no_literals(*p)?)))
                                        .collect::<Result<Vec<Box<Lvalue>>, ParseError>>()?;
                                    self.require(Token::RightArrow, "lambda start: ->")?;
                                    ps
                                };
                                let body = self.single("body of lambda")?;
                                Ok(LocExpr {
                                    start,
                                    end: body.end,
                                    expr: Expr::Lambda(Rc::new(params), Rc::new(body)),
                                })
                            }
                        }
                    }
                }
                Token::If => {
                    self.advance();
                    self.require(Token::LeftParen, "if start")?;
                    let cond = self.expression()?;
                    self.require(Token::RightParen, "if cond end")?;
                    let body = self.assignment()?;
                    let (end, else_body) = if let Some(end) = self.try_consume(&Token::Else) {
                        (end, Some(Box::new(self.assignment()?)))
                    } else {
                        (body.end, None)
                    };
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::If(Box::new(cond), Box::new(body), else_body),
                    })
                }
                Token::For => {
                    self.advance();
                    self.require(Token::LeftParen, "for start")?;
                    let mut its = Vec::new();
                    loop {
                        its.push(self.for_iteration()?);
                        match self.peek() {
                            Some(Token::RightParen) => {
                                self.advance();
                                break;
                            }
                            Some(Token::Semicolon) => {
                                self.advance();
                            }
                            _ => Err(self.error_here(format!(
                                "for: expected right paren or semicolon after iteration"
                            )))?,
                        }
                    }
                    let (end, body) = if self.try_consume(&Token::Yield).is_some() {
                        let key_body = self.single("for-yield body")?;
                        if self.try_consume(&Token::Colon).is_some() {
                            let value_body = self.single("for-yield value")?;
                            (value_body.end, ForBody::YieldItem(key_body, value_body))
                        } else if self.try_consume(&Token::Into).is_some() {
                            let into_body = self.single("for-yield into")?;
                            (key_body.end, ForBody::Yield(key_body, Some(into_body)))
                        } else {
                            (key_body.end, ForBody::Yield(key_body, None))
                        }
                    } else {
                        let body = self.assignment()?;
                        (body.end, ForBody::Execute(body))
                    };
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::For(its, Box::new(body)),
                    })
                }
                Token::While => {
                    self.advance();
                    self.require(Token::LeftParen, "while start")?;
                    let cond = self.expression()?;
                    self.require(Token::RightParen, "while end")?;
                    let body = self.assignment()?;
                    Ok(LocExpr {
                        start,
                        end: body.end,
                        expr: Expr::While(Box::new(cond), Box::new(body)),
                    })
                }
                Token::Switch => {
                    self.advance();
                    self.require(Token::LeftParen, "switch start")?;
                    let scrutinee = self.expression()?;
                    self.require(Token::RightParen, "switch end")?;
                    let mut v = Vec::new();
                    while let Some(_) = self.try_consume(&Token::Case) {
                        let pat = to_lvalue(self.annotated_pattern(true, "switch pat")?)?;
                        self.require(Token::RightArrow, "case mid: ->")?;
                        let res = self.single("switch body")?;
                        v.push((Box::new(pat), Box::new(res)));
                    }
                    match v.last() {
                        Some((_, e)) => Ok(LocExpr {
                            start,
                            end: e.end,
                            expr: Expr::Switch(Box::new(scrutinee), v),
                        }),
                        None => Err(self.error_here(format!("switch: no cases")))?,
                    }
                }
                Token::Try => {
                    self.advance();
                    let body = self.expression()?;
                    self.require(Token::Catch, "try end")?;
                    let pat = to_lvalue(self.annotated_pattern(true, "catch pattern")?)?;
                    self.require(Token::RightArrow, "catch mid: ->")?;
                    let catcher = self.single("catch body")?;
                    Ok(LocExpr {
                        start,
                        end: body.end,
                        expr: Expr::Try(Box::new(body), Box::new(pat), Box::new(catcher)),
                    })
                }
                Token::Struct => {
                    self.advance();
                    if let Some(Token::Ident(name)) = self.peek() {
                        let name = Rc::new(name.clone());
                        self.advance();
                        self.require(Token::LeftParen, "struct begin")?;
                        let mut fields = Vec::new();
                        if let Some(Token::Ident(field1)) = self.peek() {
                            let field1 = field1.clone();
                            self.advance();

                            let def = if self.try_consume(&Token::Assign).is_some() {
                                Some(Box::new(self.single("field default")?))
                            } else {
                                None
                            };
                            fields.push((Rc::new(field1.clone()), def));

                            while self.try_consume(&Token::Comma).is_some() {
                                if let Some(Token::Ident(field)) = self.peek() {
                                    let field = field.clone();
                                    self.advance();

                                    let def = if self.try_consume(&Token::Assign).is_some() {
                                        Some(Box::new(self.single("field default")?))
                                    } else {
                                        None
                                    };
                                    fields.push((Rc::new(field.clone()), def));
                                } else {
                                    Err(self.error_here(format!("bad struct field")))?
                                }
                            }
                        }
                        let end = self.require(Token::RightParen, "struct end")?;

                        Ok(LocExpr {
                            expr: Expr::Struct(name, fields),
                            start,
                            end,
                        })
                    } else {
                        Err(self.error_here(format!("bad struct name")))?
                    }
                }
                Token::InternalFrame => {
                    self.advance();
                    let s = self.single("internal frame")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::InternalFrame(Box::new(s)),
                    })
                }
                Token::InternalPush => {
                    self.advance();
                    let s = self.single("internal push")?;
                    Ok(LocExpr {
                        start,
                        end: s.end,
                        expr: Expr::InternalPush(Box::new(s)),
                    })
                }
                Token::InternalPop => {
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::InternalPop,
                    })
                }
                Token::InternalPeek => {
                    self.advance();
                    if let Some((end, n)) = self.try_consume_usize("internal peek")? {
                        Ok(LocExpr {
                            start,
                            end,
                            expr: Expr::InternalPeek(n),
                        })
                    } else {
                        Err(self.error_here(format!("internal peek no n")))?
                    }
                }
                Token::InternalPeekN(n) => {
                    let n = *n;
                    self.advance();
                    Ok(LocExpr {
                        start,
                        end,
                        expr: Expr::InternalPeek(n),
                    })
                }
                Token::InternalFor => {
                    self.advance();
                    self.require(Token::LeftParen, "internal for start")?;
                    let iteratee = self.single("internal for iteratee")?;
                    self.require(Token::RightParen, "internal for end")?;
                    let body = self.single("internal for body")?;
                    Ok(LocExpr {
                        start,
                        end: body.end,
                        expr: Expr::InternalFor(Box::new(iteratee), Box::new(body)),
                    })
                }
                Token::InternalCall => {
                    self.advance();
                    if let Some((_end, n)) = self.try_consume_usize("internal call")? {
                        let body = self.single("internal call body")?;
                        Ok(LocExpr {
                            start,
                            end: body.end,
                            expr: Expr::InternalCall(n, Box::new(body)),
                        })
                    } else {
                        Err(self.error_here(format!("internal call no n")))?
                    }
                }
                Token::InternalLambda => {
                    self.advance();
                    if let Some((_end, n)) = self.try_consume_usize("internal lambda")? {
                        let body = self.single("internal lambda body")?;
                        Ok(LocExpr {
                            start,
                            end: body.end,
                            expr: Expr::InternalLambda(n, Rc::new(body)),
                        })
                    } else {
                        Err(self.error_here(format!("internal lambda no n")))?
                    }
                }
                _ => Err(self.error_here(format!("atom: Unexpected"))),
            }
        } else {
            Err(ParseError::eof(
                "atom: ran out of stuff to parse".to_string(),
            ))
        }
    }

    fn for_iteration(&mut self) -> Result<ForIteration, ParseError> {
        if self.try_consume(&Token::If).is_some() {
            Ok(ForIteration::Guard(Box::new(
                self.single("for iteration guard")?,
            )))
        } else {
            let pat0 = self.annotated_pattern(true, "for iterator")?;
            let pat = to_lvalue_no_literals(pat0)?;
            let ty = match self.peek() {
                Some(Token::LeftArrow) => {
                    self.advance();
                    ForIterationType::Normal
                }
                Some(Token::DoubleLeftArrow) => {
                    self.advance();
                    ForIterationType::Item
                }
                Some(Token::Assign) => {
                    // FIXME?
                    self.advance();
                    ForIterationType::Declare
                }
                _ => return Err(self.error_here(format!("for: require <- or <<- or ="))),
            };
            let iteratee = self.annotated_pattern(false, "for iteratee")?;
            Ok(ForIteration::Iteration(
                ty,
                Box::new(pat),
                Box::new(iteratee),
            ))
        }
    }

    fn attach_symbol_accesses(&mut self, mut expr: LocExpr) -> Result<LocExpr, ParseError> {
        while self.try_consume(&Token::DoubleColon).is_some() {
            match self.peek_loc_token() {
                Some(LocToken {
                    token: Token::Ident(name),
                    start: _id_start,
                    end: id_end,
                }) => {
                    let name = name.clone();
                    let end = *id_end;
                    self.advance();
                    expr = LocExpr {
                        start: expr.start,
                        end,
                        expr: Expr::SymbolAccess(Box::new(expr), Rc::new(name)),
                    };
                }
                _ => return Err(self.error_here(format!("double colon access: unexpected"))),
            }
        }
        Ok(expr)
    }

    fn operand(&mut self) -> Result<LocExpr, ParseError> {
        let start = self.peek_loc();
        let mut cur = self.atom()?;

        loop {
            cur = self.attach_symbol_accesses(cur)?;
            match self.peek() {
                Some(Token::LeftParen) => {
                    self.advance();
                    if let Some(end) = self.try_consume(&Token::RightParen) {
                        cur = LocExpr {
                            expr: Expr::Call(Box::new(cur), Vec::new(), CallSyntax::Parentheses),
                            start,
                            end,
                        };
                    } else {
                        let (cs, _) = self.annotated_comma_separated(false, "call arg list")?;
                        let end = self.require(Token::RightParen, "call expr")?;
                        cur = LocExpr {
                            expr: Expr::Call(Box::new(cur), cs, CallSyntax::Parentheses),
                            start,
                            end,
                        };
                    }
                }
                Some(Token::LeftBracket) => {
                    self.advance();
                    if self.try_consume(&Token::Colon).is_some() {
                        if let Some(end) = self.try_consume(&Token::RightBracket) {
                            cur = LocExpr {
                                expr: Expr::Index(Box::new(cur), IndexOrSlice::Slice(None, None)),
                                start,
                                end,
                            };
                        } else {
                            let c = self.single("slice end")?;
                            let end = self.require(Token::RightBracket, "index expr")?;
                            cur = LocExpr {
                                expr: Expr::Index(
                                    Box::new(cur),
                                    IndexOrSlice::Slice(None, Some(Box::new(c))),
                                ),
                                start,
                                end,
                            };
                        }
                    } else {
                        let c = self.single("index/slice start")?;
                        if self.try_consume(&Token::Colon).is_some() {
                            if let Some(end) = self.try_consume(&Token::RightBracket) {
                                cur = LocExpr {
                                    expr: Expr::Index(
                                        Box::new(cur),
                                        IndexOrSlice::Slice(Some(Box::new(c)), None),
                                    ),
                                    start,
                                    end,
                                };
                            } else {
                                let cc = self.single("slice end")?;
                                let end = self.require(Token::RightBracket, "index expr")?;
                                cur = LocExpr {
                                    expr: Expr::Index(
                                        Box::new(cur),
                                        IndexOrSlice::Slice(Some(Box::new(c)), Some(Box::new(cc))),
                                    ),
                                    start,
                                    end,
                                };
                            }
                        } else {
                            let end = self.require(Token::RightBracket, "index expr")?;
                            cur = LocExpr {
                                expr: Expr::Index(Box::new(cur), IndexOrSlice::Index(Box::new(c))),
                                start,
                                end,
                            };
                        }
                    }
                }
                Some(Token::LeftBrace) => {
                    self.advance();
                    let mut updates = Vec::new();
                    while !self.peek_hard_stopper() {
                        let k = self.single("update k")?;
                        self.require(Token::Assign, "update =")?;
                        let v = self.single("update v")?;
                        updates.push((Box::new(k), Box::new(v)));
                        if !self.try_consume(&Token::Comma).is_some() {
                            break;
                        }
                    }
                    let end = self.require(Token::RightBrace, "update end")?;
                    cur = LocExpr {
                        expr: Expr::Update(Box::new(cur), updates),
                        start,
                        end,
                    };
                }
                Some(Token::Bang) => {
                    // FIXME
                    let bang_end = self.peek_loc_token().unwrap().end;
                    self.advance();
                    if self.peek_csc_stopper() {
                        cur = LocExpr {
                            expr: Expr::Call(Box::new(cur), Vec::new(), CallSyntax::Bang),
                            start,
                            end: bang_end,
                        };
                    } else {
                        let (cs, _) = self.annotated_comma_separated(false, "bang arg list")?;
                        let end = match cs.last() {
                            Some(c) => c.end,
                            None => bang_end,
                        };
                        cur = LocExpr {
                            expr: Expr::Call(Box::new(cur), cs, CallSyntax::Bang),
                            start,
                            end,
                        };
                    }
                }
                _ => break Ok(cur),
            }
        }
    }

    fn peek_hard_stopper(&self) -> bool {
        match self.peek() {
            Some(Token::RightParen) => true,
            Some(Token::RightBracket) => true,
            Some(Token::RightBrace) => true,
            Some(Token::Else) => true,
            Some(Token::Case) => true,
            Some(Token::Catch) => true,
            Some(Token::Into) => true,
            None => true,
            _ => false,
        }
    }

    fn peek_csc_stopper(&self) -> bool {
        self.peek_hard_stopper()
            || match self.peek() {
                Some(Token::Assign) => true,
                Some(Token::DoubleColon) => true,
                Some(Token::Semicolon) => true,
                Some(Token::LeftArrow) => true,
                Some(Token::DoubleLeftArrow) => true,
                Some(Token::RightArrow) => true,
                _ => false,
            }
    }

    fn peek_chain_stopper(&self) -> bool {
        self.peek_csc_stopper()
            || match self.peek() {
                Some(Token::Comma) => true,
                Some(Token::Colon) => true,
                Some(Token::And) => true,
                Some(Token::Or) => true,
                Some(Token::Coalesce) => true,
                _ => false,
            }
    }

    fn chain(&mut self) -> Result<LocExpr, ParseError> {
        let start = self.peek_loc();
        let op1 = self.operand()?;
        if self.peek_chain_stopper() {
            Ok(op1)
        } else {
            // We'll specially allow some two-chains, (a b), as calls, so that negative number
            // literals and just writing an expression like "-x" works. But we will be
            // aggressive-ish about checking that the chain ends afterwards so we don't get runaway
            // syntax errors.
            let mut second = self.atom()?;
            let is_ident = match second.expr {
                Expr::Ident(_) => true,
                _ => false,
            };
            second = self.attach_symbol_accesses(second)?;
            if is_ident {
                if let Some(bang_end) = self.try_consume(&Token::Bang) {
                    let ret = LocExpr {
                        expr: Expr::Chain(
                            Box::new(op1),
                            vec![(
                                Box::new(second),
                                Box::new(self.single("operator-bang operand")?),
                            )],
                        ),
                        start,
                        end: bang_end,
                    };
                    if self.peek() == Some(&Token::Comma) {
                        Err(self.error_here("Got comma after operator-bang operand; the precedence is too confusing so this is banned".to_string()))
                    } else {
                        Ok(ret)
                    }
                } else if self.peek_chain_stopper() {
                    let end = second.end;
                    Ok(LocExpr {
                        expr: Expr::Call(
                            Box::new(op1),
                            vec![Box::new(second)],
                            CallSyntax::Juxtapose,
                        ),
                        start,
                        end,
                    })
                } else {
                    let mut ops = vec![(Box::new(second), Box::new(self.operand()?))];

                    while let Some(LocToken {
                        token: Token::Ident(op),
                        start: op_start,
                        end: op_end,
                    }) = self.peek_loc_token()
                    {
                        let op = op.to_string();
                        let op_start = *op_start;
                        let op_end = *op_end;
                        self.advance();
                        ops.push((
                            Box::new(LocExpr {
                                start: op_start,
                                end: op_end,
                                expr: Expr::Ident(op),
                            }),
                            Box::new(if self.try_consume(&Token::Bang).is_some() {
                                self.single("operator-bang operand")?
                            } else {
                                self.operand()?
                            }),
                        ));
                    }

                    Ok(LocExpr {
                        start,
                        end: ops.last().unwrap().1.end,
                        expr: Expr::Chain(Box::new(op1), ops),
                    })
                }
            } else {
                // second was not an identifier, only allowed to be a short chain
                let ret = LocExpr {
                    start,
                    end: second.end,
                    expr: Expr::Call(Box::new(op1), vec![Box::new(second)], CallSyntax::Juxtapose),
                };
                if !self.peek_chain_stopper() {
                    Err(self.error_here(format!(
                        "saw non-identifier in operator position: these chains must be short"
                    )))
                } else {
                    Ok(ret)
                }
            }
        }
    }

    fn logic_and(&mut self) -> Result<LocExpr, ParseError> {
        let start = self.peek_loc();
        let mut op1 = self.chain()?;
        while self.try_consume(&Token::And).is_some() {
            let rhs = self.chain()?;
            op1 = LocExpr {
                start,
                end: rhs.end,
                expr: Expr::And(Box::new(op1), Box::new(rhs)),
            };
        }
        Ok(op1)
    }

    fn single(&mut self, ctx: &str) -> Result<LocExpr, ParseError> {
        let start = self.peek_loc();
        let mut op1 = err_add_context(self.logic_and(), ctx, start)?;
        loop {
            match self.peek() {
                Some(Token::Or) => {
                    self.advance();
                    let rhs = err_add_context(self.logic_and(), ctx, start)?;
                    op1 = LocExpr {
                        start,
                        end: rhs.end,
                        expr: Expr::Or(Box::new(op1), Box::new(rhs)),
                    };
                }
                Some(Token::Coalesce) => {
                    self.advance();
                    let rhs = err_add_context(self.logic_and(), ctx, start)?;
                    op1 = LocExpr {
                        start,
                        end: rhs.end,
                        expr: Expr::Coalesce(Box::new(op1), Box::new(rhs)),
                    };
                }
                _ => return Ok(op1),
            }
        }
    }

    // Comma-separated things, possibly with annotations. No semicolons or assigns allowed. Should
    // be nonempty I think, as above caller should handle empty case.
    //
    // If annotations = false, colons are actively forbidden (seeing one is a syntax error instead
    // of just stopping parsing).
    //
    // This exists because we want commas and annotations to be "at the same level": it's important
    // that the annotation in `a, b := 3, 4` covers a, but it also doesn't make sense if `a: int,
    // b: list = 3, [4]` doesn't work. We trade one thing off for now: ideally `a, b: satisfying(3
    // < _ < 5) = 4` would evaluate the type expression only once, so the translated Lvalue needs
    // to be aware that substrings of variables in a flat list of things share the same annotation,
    // but that's annoying. Let's just clone the type expression.
    fn annotated_comma_separated(
        &mut self,
        annotations: bool,
        msg: &str,
    ) -> Result<(Vec<Box<LocExpr>>, bool), ParseError> {
        let mut annotated = Vec::new();
        let mut pending_annotation =
            vec![Box::new(self.single(&format!("first expr in {}", msg))?)];
        let mut comma = false;
        loop {
            match self.peek() {
                Some(Token::Comma) => {
                    self.advance();
                    comma = true;
                    if self.peek_csc_stopper() {
                        annotated.extend(pending_annotation);
                        return Ok((annotated, comma));
                    }
                    if self.peek() == Some(&Token::Colon) {
                        // we'll pick it up in the next iteration
                        continue;
                    }
                    pending_annotation.push(Box::new(
                        self.single("later expr in annotated-comma-separated")?,
                    ));
                }
                Some(Token::Colon) => {
                    if !annotations {
                        Err(self.error_here(format!("colons/annotations forbidden in {}", msg)))?
                    }
                    self.advance();
                    if pending_annotation.is_empty() {
                        Err(self.error_here(format!(
                            "annotated-comma-separated: extra colon covers nothing"
                        )))?
                    }
                    let anno = if self.peek_csc_stopper() {
                        None
                    } else {
                        Some(Rc::new(self.single("annotation")?))
                    };
                    // lol annotated expressions may not be contiguous
                    annotated.extend(pending_annotation.drain(..).map(|e| {
                        Box::new(LocExpr {
                            start: e.start,
                            end: e.end,
                            expr: Expr::Annotation(e, anno.clone()),
                        })
                    }));
                }
                _ => {
                    annotated.extend(pending_annotation);
                    return Ok((annotated, comma));
                }
            }
        }
    }
    fn annotated_pattern(&mut self, annotations: bool, msg: &str) -> Result<LocExpr, ParseError> {
        let start = self.peek_loc();
        let (exs, comma) = self.annotated_comma_separated(annotations, msg)?;
        match (few(exs), comma) {
            (Few::Zero, _) => Err(self.error_here(format!(
                "Expected annotated pattern at {}, got nothing",
                msg
            ))),
            (Few::One(ex), false) => Ok(*ex),
            (Few::One(ex), true) => Ok(LocExpr {
                start,
                end: ex.end,
                expr: Expr::CommaSeq(vec![ex]),
            }),
            (Few::Many(exs), _) => Ok(LocExpr {
                start,
                end: exs.last().unwrap().end,
                expr: Expr::CommaSeq(exs),
            }),
        }
    }

    fn assignment(&mut self) -> Result<LocExpr, ParseError> {
        let start = self.peek_loc();
        let ag_start_err = self.peek_err();
        if self.try_consume(&Token::Swap).is_some() {
            let a = to_lvalue_no_literals(self.single("swap target 1")?)?;
            self.require(
                Token::Comma,
                &format!("swap between lvalues at {}", ag_start_err),
            )?;
            let bs = self.single("swap target 2")?;
            let end = bs.end;
            let b = to_lvalue_no_literals(bs)?;
            Ok(LocExpr {
                expr: Expr::Swap(Box::new(a), Box::new(b)),
                start,
                end,
            })
        } else {
            let every = self.try_consume(&Token::Every).is_some();
            // TODO: parsing can be different after Every
            let pat = self.annotated_pattern(true, "assign LHS")?;

            match self.peek() {
                Some(Token::Assign) => {
                    self.advance();
                    match pat.expr {
                        Expr::Call(lhs, op, CallSyntax::Juxtapose | CallSyntax::Bang) => {
                            match few(op) {
                                Few::One(op) => {
                                    let rhs = self.annotated_pattern(false, "op-assign RHS")?;
                                    let end = rhs.end;
                                    Ok(LocExpr {
                                        expr: Expr::OpAssign(
                                            every,
                                            Box::new(to_lvalue_no_literals(*lhs)?),
                                            Box::new(*op),
                                            Box::new(rhs),
                                        ),
                                        start,
                                        end,
                                    })
                                }
                                _ => Err(self.error_here(format!(
                                    "call w not 1 arg is not assignop, at {}",
                                    ag_start_err
                                ))),
                            }
                        }
                        _ => {
                            let rhs = self.annotated_pattern(false, "assign RHS")?;
                            let end = rhs.end;
                            // actually gonna accept literals here
                            // sometimes a, "foo", b := x is a nice way to fail fast
                            Ok(LocExpr {
                                expr: Expr::Assign(every, Box::new(to_lvalue(pat)?), Box::new(rhs)),
                                start,
                                end,
                            })
                        }
                    }
                }
                /*
                Some(Token::Declare) => {
                    self.advance();
                    Ok(Expr::Declare(Box::new(to_lvalue(pat)?), Box::new(self.pattern()?)))
                }
                */
                _ => {
                    if every {
                        Err(self
                            .error_here(format!("`every` as not assignment at {}", ag_start_err)))
                    } else {
                        Ok(pat)
                    }
                }
            }
        }
    }

    fn expression(&mut self) -> Result<LocExpr, ParseError> {
        let mut ags = vec![Box::new(self.assignment()?)];
        let mut ending_semicolon = false;
        let start = self.peek_loc();
        let mut end = start; // fake

        while let Some(s_end) = self.try_consume(&Token::Semicolon) {
            if self.peek_hard_stopper() {
                ending_semicolon = true;
                end = s_end;
                break;
            } else {
                let a = self.assignment()?;
                end = a.end;
                ags.push(Box::new(a));
            }
        }

        Ok(if ags.len() == 1 && !ending_semicolon {
            *ags.remove(0)
        } else {
            LocExpr {
                expr: Expr::Sequence(ags, ending_semicolon),
                start,
                end,
            }
        })
    }

    fn is_at_end(&self) -> bool {
        self.i == self.tokens.len()
    }
}

pub fn lex(code: &str) -> Vec<LocToken> {
    let mut lexer = Lexer::new(code);
    lexer.lex();
    lexer.tokens
}

// allow the empty expression
pub fn parse(code: &str) -> Result<Option<LocExpr>, ParseError> {
    let (tokens, _) = strip_comments(lex(code));
    if tokens.is_empty() {
        Ok(None)
    } else {
        let mut p = Parser { tokens, i: 0 };
        match p.expression() {
            Ok(ret) => {
                if p.is_at_end() {
                    Ok(Some(ret))
                } else {
                    Err(p.error_here(format!("Didn't finish parsing")))
                }
            }
            Err(err) => Err(err),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Func {
    Builtin(Rc<dyn Builtin>),
    Closure(Closure),
    InternalLambda(usize, Rc<LocExpr>),
    // partially applied first argument (lower priority)
    PartialApp1(Box<Func>, Box<Obj>),
    // partially applied second argument (more of the default in our weird world)
    PartialApp2(Box<Func>, Box<Obj>),
    // partially applied last argument, opt-in for more complicated arity things
    PartialAppLast(Box<Func>, Box<Obj>),
    // mathematical notation, first of second
    Composition(Box<Func>, Box<Func>),
    // (f on g)(a1, a2, ...) = f(g(a1), g(a2), ...)
    OnComposition(Box<Func>, Box<Func>),
    // (a1, a2, ...) -> [f1(a1), f2(a2), ...]
    Parallel(Vec<Func>),
    // a... -> [f1(a...), f2(a...), ...]
    Fanout(Vec<Func>),
    // a... -> f(g1(a...), g2(a...), ...)
    // where, if g_i isn't a function, it's constant
    OnFanoutConst(Box<Func>, Vec<Obj>),
    // \x, y: f(y, x) (...I feel like we shouldn't special-case so many but shrug...)
    Flip(Box<Func>),
    // each Err is a slot for an argument, true if splat
    ListSection(Vec<Result<Obj, bool>>),
    IndexSection(Option<Box<Obj>>, Option<Box<Obj>>),
    // outer None is nothing; Some(None) is a slot
    // unusual boxing because bytes
    SliceSection(
        Option<Box<Obj>>,
        Option<Box<Option<Obj>>>,
        Option<Box<Option<Obj>>>,
    ),
    // only going to support the simplest kind
    UpdateSection(Vec<(Box<Obj>, Box<Obj>)>),
    ChainSection(
        Option<Box<Obj>>,
        Vec<(CodeLoc, CodeLoc, Box<Func>, Precedence, Option<Box<Obj>>)>,
    ),
    CallSection(Option<Box<Obj>>, Vec<Result<Obj, bool>>),
    Type(ObjType), // includes Struct now
    StructField(Struct, usize),
    SymbolAccess(Rc<String>),
    Memoized(Box<Func>, Rc<RefCell<HashMap<Vec<ObjKey>, Obj>>>),
}

pub trait WriteMaybeExtractable: Write + MaybeSync + MaybeSend {
    fn extract(&self) -> Option<&[u8]>;
}

impl WriteMaybeExtractable for io::Sink {
    fn extract(&self) -> Option<&[u8]> {
        None
    }
}
impl WriteMaybeExtractable for io::Stdout {
    fn extract(&self) -> Option<&[u8]> {
        None
    }
}
impl WriteMaybeExtractable for Vec<u8> {
    fn extract(&self) -> Option<&[u8]> {
        Some(self)
    }
}

pub struct TopEnv {
    pub backrefs: Vec<Obj>,
    pub input: Box<dyn BufRead + Send + Sync>,
    pub output: Box<dyn WriteMaybeExtractable>,
}

impl Debug for TopEnv {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            fmt,
            "TopEnv {{ backrefs: {:?}, input: {:p}, output: {:p} }}",
            self.backrefs, self.input, self.output
        )
    }
}

#[derive(Debug)]
pub struct Env {
    pub vars: HashMap<String, (ObjType, Box<RefCell<Obj>>)>,
    pub parent: Result<Rc<RefCell<Env>>, Rc<RefCell<TopEnv>>>,
    pub internal_stack: Vec<Obj>,
}
// simple, linear-time, and at least finds when one is a subsequence of the other.
pub fn fast_edit_distance(a: &[u8], b: &[u8]) -> usize {
    let mut ai = 0;
    let mut bi = 0;
    let mut dist = 0;
    while ai < a.len() && bi < b.len() {
        if a[ai] == b[bi] {
            ai += 1;
            bi += 1;
        } else if a.len() - ai >= b.len() - bi {
            dist += 1;
            ai += 1;
        } else {
            dist += 1;
            bi += 1;
        }
    }
    dist + a.len() - ai + b.len() - bi
}

pub fn try_borrow_nres<'a, T>(r: &'a RefCell<T>, msg1: &str, msg2: &str) -> NRes<Ref<'a, T>> {
    match cell_try_borrow(r) {
        Ok(r) => Ok(r),
        Err(b) => Err(NErr::io_error(format!(
            "internal borrow error: {}: {}: {}",
            msg1, msg2, b
        ))),
    }
}
pub fn try_borrow_mut_nres<'a, T>(
    r: &'a RefCell<T>,
    msg1: &str,
    msg2: &str,
) -> NRes<RefMut<'a, T>> {
    match cell_try_borrow_mut(r) {
        Ok(r) => Ok(r),
        Err(b) => Err(NErr::io_error(format!(
            "internal borrow mut error: {}: {}: {}",
            msg1, msg2, b
        ))),
    }
}

pub const DEFAULT_PRECEDENCE: f64 = 0.0;
pub const COMPARISON_PRECEDENCE: f64 = 1.0;
pub const STRING_PRECEDENCE: f64 = 2.0;
pub const OR_PRECEDENCE: f64 = 3.0;
pub const PLUS_PRECEDENCE: f64 = 4.0;
pub const MULTIPLY_PRECEDENCE: f64 = 5.0;
pub const EXPONENT_PRECEDENCE: f64 = 6.0;
pub const INDEX_PRECEDENCE: f64 = 7.0;
pub const DOT_PRECEDENCE: f64 = 8.0;

pub fn default_precedence(name: &str) -> f64 {
    name.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                DEFAULT_PRECEDENCE
            } else {
                // to decide: '@'
                match c {
                    '=' | '<' | '>' | '∘' | '∈' | '∉' | '∋' | '∌' | '≤' | '≥' => {
                        COMPARISON_PRECEDENCE
                    }
                    '$' => STRING_PRECEDENCE,
                    '|' => OR_PRECEDENCE,
                    '+' | '-' | '~' | '⊕' | '⧺' => PLUS_PRECEDENCE,
                    '*' | '/' | '%' | '&' | '×' => MULTIPLY_PRECEDENCE,
                    '^' => EXPONENT_PRECEDENCE,
                    '!' | '?' => INDEX_PRECEDENCE,
                    _ => DOT_PRECEDENCE, // particularly .
                }
            }
        })
        .reduce(f64::min)
        .unwrap_or(0.0)
}

pub fn add_trace<T>(
    res: NRes<T>,
    thing: impl FnOnce() -> String,
    start: CodeLoc,
    end: CodeLoc,
) -> NRes<T> {
    match res {
        Err(NErr::Throw(e, mut trace)) => {
            trace.push((thing(), start, end, None));
            Err(NErr::Throw(e, trace))
        }
        e => e,
    }
}

pub fn err_add_name<T>(res: NRes<T>, s: &str) -> NRes<T> {
    match res {
        Ok(x) => Ok(x),
        Err(NErr::Throw(msg, trace)) => {
            Err(NErr::Throw(Obj::from(format!("{}: {}", s, msg)), trace))
        }
        Err(NErr::Break(n, e)) => Err(NErr::Break(n, e)),
        Err(NErr::Return(e)) => Err(NErr::Return(e)),
        Err(NErr::Continue(n)) => Err(NErr::Continue(n)),
    }
}

impl Env {
    pub fn new(top: TopEnv) -> Env {
        Env {
            vars: HashMap::new(),
            parent: Err(Rc::new(RefCell::new(top))),
            internal_stack: Vec::new(),
        }
    }
    // ???
    pub fn empty() -> Env {
        Env::new(TopEnv {
            backrefs: Vec::new(),
            input: Box::new(io::empty()),
            output: Box::new(io::sink()),
        })
    }
    pub fn with_parent(env: &Rc<RefCell<Env>>) -> Rc<RefCell<Env>> {
        Rc::new(RefCell::new(Env {
            vars: HashMap::new(),
            parent: Ok(Rc::clone(&env)),
            internal_stack: Vec::new(),
        }))
    }
    pub fn mut_top_env<T>(&self, f: impl FnOnce(&mut TopEnv) -> T) -> T {
        match &self.parent {
            Ok(v) => cell_borrow(v).mut_top_env(f),
            Err(t) => f(&mut cell_borrow_mut(t)),
        }
    }

    pub fn try_borrow_get_var(env: &Rc<RefCell<Env>>, s: &str) -> NRes<Obj> {
        let r = try_borrow_nres(env, "env", s)?;
        match r.vars.get(s) {
            Some(v) => Ok(try_borrow_nres(&*v.1, "variable", s)?.clone()),
            None => {
                let inner = match &r.parent {
                    Ok(p) => Env::try_borrow_get_var(p, s),
                    Err(_) => Err(NErr::name_error(format!("No such variable: \"{}\".", s))),
                };
                match inner {
                    Err(NErr::Throw(x, _)) => {
                        let mut msg = format!("{}", x);
                        if let Some(k) = r
                            .vars
                            .keys()
                            .min_by_key(|k| fast_edit_distance(k.as_bytes(), s.as_bytes()))
                        {
                            msg += &format!(" Did you mean: \"{}\"?", k);
                        }
                        Err(NErr::throw(msg))
                    }
                    x => x,
                }
            }
        }
    }

    pub fn try_borrow_peek(env: &Rc<RefCell<Env>>, i: usize) -> NRes<Obj> {
        let r = try_borrow_nres(env, "internal", "peek")?;
        let s = &r.internal_stack;
        let x = s[s.len() - i - 1].clone();
        std::mem::drop(r);
        Ok(x)
    }

    pub fn try_borrow_set_peek(env: &Rc<RefCell<Env>>, i: usize, x: Obj) -> NRes<()> {
        let mut r = try_borrow_mut_nres(env, "internal", "peek set")?;
        let s = &mut r.internal_stack;
        let n = s.len();
        s[n - i - 1] = x;
        Ok(())
    }

    pub fn modify_existing_var<T>(
        &self,
        key: &str,
        f: impl FnOnce(&(ObjType, Box<RefCell<Obj>>)) -> T,
    ) -> Option<T> {
        match self.vars.get(key) {
            Some(target) => Some(f(target)),
            None => match &self.parent {
                Ok(p) => cell_borrow(p).modify_existing_var(key, f),
                Err(_) => None,
            },
        }
    }

    pub fn insert(&mut self, key: String, ty: ObjType, val: Obj) -> NRes<()> {
        match self.vars.entry(key) {
            std::collections::hash_map::Entry::Occupied(e) => {
                Err(NErr::name_error(format!("Declaring/assigning variable that already exists: {:?}. If in pattern with other declarations, parenthesize existent variables", e.key())))
            }
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert((ty, Box::new(RefCell::new(val))));
                Ok(())
            }
        }
    }
    pub fn insert_type(&mut self, b: ObjType) {
        self.insert(
            b.name(),
            ObjType::Any,
            Obj::Func(Func::Type(b), Precedence::zero()),
        )
        .unwrap()
    }
    pub fn insert_builtin_with_precedence(&mut self, b: impl Builtin + 'static, p: Precedence) {
        self.insert(
            b.builtin_name().to_string(),
            ObjType::Any,
            Obj::Func(Func::Builtin(Rc::new(b)), p),
        )
        .unwrap()
    }
    pub fn insert_builtin(&mut self, b: impl Builtin + 'static) {
        let p = Precedence(default_precedence(b.builtin_name()), Assoc::Left);
        self.insert_builtin_with_precedence(b, p)
    }
    pub fn insert_rassoc_builtin(&mut self, b: impl Builtin + 'static) {
        let p = Precedence(default_precedence(b.builtin_name()), Assoc::Right);
        self.insert_builtin_with_precedence(b, p)
    }
    pub fn insert_builtin_with_alias(&mut self, b: impl Builtin + 'static + Clone, alias: &str) {
        let p = Precedence(default_precedence(b.builtin_name()), Assoc::Left);
        self.insert_builtin_with_precedence(b.clone(), p);
        self.insert(
            alias.to_string(),
            ObjType::Any,
            Obj::Func(Func::Builtin(Rc::new(b)), p),
        )
        .unwrap()
    }
}

pub type REnv = Rc<RefCell<Env>>;

impl Display for Func {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Func::Builtin(b) => write!(formatter, "Builtin({})", b.builtin_name()),
            Func::Closure(_) => write!(formatter, "Closure"),
            Func::InternalLambda(n, ..) => write!(formatter, "InternalLambda({}, ?)", n),
            Func::PartialApp1(f, x) => write!(formatter, "Partial({}({}, ?))", f, FmtObj::debug(x)),
            Func::PartialApp2(f, x) => write!(formatter, "Partial({}(?, {}))", f, FmtObj::debug(x)),
            Func::PartialAppLast(f, x) => {
                write!(formatter, "Partial({}(...?, {}))", f, FmtObj::debug(x))
            }
            Func::Composition(f, g) => write!(formatter, "Comp({} . {})", f, g),
            Func::OnComposition(f, g) => write!(formatter, "OnComp({} . {})", f, g),
            Func::Parallel(fs) => {
                write!(formatter, "Parallel({})", CommaSeparated(fs))
            }
            Func::Fanout(fs) => write!(formatter, "Fanout({})", CommaSeparated(fs)),
            Func::OnFanoutConst(f, gs) => {
                write!(formatter, "OnFanoutConst({} . {})", f, CommaSeparated(gs))
            }
            Func::Flip(f) => write!(formatter, "Flip({})", f),
            // TODO
            Func::ListSection(xs) => {
                write!(formatter, "ListSection({})", FmtSectionSlots(xs.as_slice()))
            }
            Func::CallSection(f, xs) => write!(
                formatter,
                "CallSection({} {})",
                FmtSectionBoxedSlot(f),
                FmtSectionSlots(xs)
            ),
            Func::UpdateSection(xs) => {
                write!(formatter, "UpdateSection(")?;
                for (k, v) in xs {
                    write!(formatter, "{} = {},", k, v)?;
                }
                write!(formatter, ")")
            }
            Func::ChainSection(xs, ys) => {
                write!(formatter, "ChainSection({}", FmtSectionBoxedSlot(xs))?;
                for (_start, _end, func, _prec, operand) in ys {
                    write!(formatter, " {} {}", func, FmtSectionBoxedSlot(operand))?;
                }
                write!(formatter, ")")
            }
            Func::IndexSection(x, i) => write!(
                formatter,
                "IndexSection({}[{}])",
                FmtSectionBoxedSlot(x),
                FmtSectionBoxedSlot(i)
            ),
            Func::SliceSection(x, lo, hi) => {
                write!(
                    formatter,
                    "SliceSection({} {:?} {:?})",
                    FmtSectionBoxedSlot(x),
                    lo,
                    hi
                )
            }
            Func::Type(t) => write!(formatter, "{}", t.name()),
            Func::StructField(s, i) => write!(formatter, "<{} field {}>", s.name, i),
            Func::SymbolAccess(s) => write!(formatter, "::{}", s),
            Func::Memoized(..) => write!(formatter, "<memoized>"),
        }
    }
}
