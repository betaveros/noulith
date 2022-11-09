#[macro_use]
extern crate lazy_static;

// TODO: isolate
use std::fs;
use std::io;
use std::io::{BufRead, Read, Write};

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::rc::Rc;

use regex::Regex;

use num::bigint::{BigInt, RandBigInt, Sign};
use num::complex::Complex64;
use num::BigRational;
use num::Signed;
use num::ToPrimitive;

use chrono::prelude::*;

use std::time::SystemTime;

use base64;
use rand;

#[cfg(feature = "request")]
use reqwest;

#[cfg(feature = "crypto")]
use aes;
#[cfg(feature = "crypto")]
use aes::cipher::{generic_array, BlockDecrypt, BlockEncrypt, KeyInit};
#[cfg(feature = "crypto")]
use blake3;
#[cfg(feature = "crypto")]
use md5::{Digest, Md5};
#[cfg(feature = "crypto")]
use sha2::Sha256;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

pub mod few;
mod gamma;
mod iter;
pub mod nnum;
use crate::few::*;
use crate::iter::*;

use crate::nnum::NNum;
use crate::nnum::NTotalNum;

#[derive(Debug, Clone, Copy)]
pub enum Assoc {
    Left,
    Right,
}
#[derive(Debug, Clone, Copy)]
pub struct Precedence(f64, Assoc);
impl Precedence {
    fn zero() -> Self {
        Precedence(0.0, Assoc::Left)
    }
    fn tighter_than_when_before(&self, other: &Precedence) -> bool {
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

static STRUCT_COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Struct {
    id: usize,
    size: usize,
    name: Rc<String>,
}

impl Struct {
    fn new(size: usize, name: Rc<String>) -> Self {
        Struct {
            id: STRUCT_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst),
            size,
            name,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Obj {
    Null,
    Num(NNum),
    Seq(Seq),
    Func(Func, Precedence),
    Instance(Struct, Vec<Obj>),
}

// to support Rc<dyn Stream>, can't have Clone, because
// https://doc.rust-lang.org/reference/items/traits.html#object-safety
//
// more using this as "lazy, possibly infinite list" rn i.e. trying to support indexing etc.
pub trait Stream: Iterator<Item = Obj> + Display + Debug {
    fn peek(&self) -> Option<Obj>;
    fn clone_box(&self) -> Box<dyn Stream>;
    // for now this means length or infinity, not sure yet
    fn len(&self) -> Option<usize> {
        let mut s = self.clone_box();
        let mut ret = 0;
        while let Some(_) = s.next() {
            ret += 1;
        }
        Some(ret)
    }
    fn force(&self) -> Option<Vec<Obj>> {
        Some(self.clone_box().collect())
    }
    fn pythonic_index_isize(&self, mut i: isize) -> Option<Obj> {
        if i >= 0 {
            let mut it = self.clone_box();
            while let Some(e) = it.next() {
                if i == 0 {
                    return Some(e);
                }
                i -= 1;
            }
            None
        } else {
            let mut v = self.force()?;
            let i2 = (i + (v.len() as isize)) as usize;
            if i2 < v.len() {
                Some(v.swap_remove(i2))
            } else {
                None
            }
        }
    }
    fn pythonic_slice(&self, lo: Option<isize>, hi: Option<isize>) -> Option<Seq> {
        let lo = lo.unwrap_or(0);
        match (lo, hi) {
            (lo, None) if lo >= 0 => {
                let mut it = self.clone_box();
                for _ in 0..lo {
                    if it.next().is_none() {
                        return Some(Seq::Stream(Rc::from(it)));
                    }
                }
                Some(Seq::Stream(Rc::from(it)))
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
                        Some(x) => v.push(x),
                        None => break,
                    }
                }
                Some(Seq::List(Rc::new(v)))
            }
            (lo, hi) => {
                let mut v = self.force()?;
                let (lo, hi) = pythonic_slice(v.as_slice(), Some(lo), hi);
                Some(Seq::List(Rc::new(v.drain(lo..hi).collect())))
            }
        }
    }
    fn reversed(&self) -> Option<Seq> {
        let mut xs = self.force()?;
        xs.reverse();
        Some(Seq::List(Rc::new(xs)))
    }
}
#[derive(Debug, Clone)]
struct Repeat(Obj);
impl Iterator for Repeat {
    type Item = Obj;
    fn next(&mut self) -> Option<Obj> {
        Some(self.0.clone())
    }
}
impl Display for Repeat {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "repeat({})", self.0)
    }
}
impl Stream for Repeat {
    fn peek(&self) -> Option<Obj> {
        Some(self.0.clone())
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        None
    }
    fn force(&self) -> Option<Vec<Obj>> {
        None
    }
    fn pythonic_index_isize(&self, _: isize) -> Option<Obj> {
        Some(self.0.clone())
    }
    fn pythonic_slice(&self, lo: Option<isize>, hi: Option<isize>) -> Option<Seq> {
        let lo = match lo {
            Some(x) => {
                if x < 0 {
                    x - 1
                } else {
                    x
                }
            }
            None => 0,
        };
        let hi = match hi {
            Some(x) => {
                if x < 0 {
                    x - 1
                } else {
                    x
                }
            }
            None => -1,
        };
        Some(match (lo < 0, hi < 0) {
            (true, true) | (false, false) => {
                Seq::List(Rc::new(vec![self.0.clone(); (hi - lo).max(0) as usize]))
            }
            (true, false) => Seq::List(Rc::new(Vec::new())),
            (false, true) => Seq::Stream(Rc::new(self.clone())),
        })
    }
    fn reversed(&self) -> Option<Seq> {
        Some(Seq::Stream(Rc::new(self.clone())))
    }
}
#[derive(Debug, Clone)]
// just gonna say this has to be nonempty
struct Cycle(Rc<Vec<Obj>>, usize);
impl Iterator for Cycle {
    type Item = Obj;
    fn next(&mut self) -> Option<Obj> {
        let ret = self.0[self.1].clone();
        self.1 = (self.1 + 1) % self.0.len();
        Some(ret)
    }
}
impl Display for Cycle {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "cycle({})", CommaSeparated(&**self.0))
    }
}
impl Stream for Cycle {
    fn peek(&self) -> Option<Obj> {
        Some(self.0[self.1].clone())
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        None
    }
    fn force(&self) -> Option<Vec<Obj>> {
        None
    }
    fn pythonic_index_isize(&self, i: isize) -> Option<Obj> {
        Some(self.0[(self.1 as isize + i).rem_euclid(self.0.len() as isize) as usize].clone())
    }
    fn reversed(&self) -> Option<Seq> {
        let mut v: Vec<Obj> = (*self.0).clone();
        v.reverse();
        // 0 -> 0, 1 -> n - 1...
        let i = (v.len() - self.1) % v.len();
        Some(Seq::Stream(Rc::new(Cycle(Rc::new(v), i))))
    }
}
#[derive(Debug, Clone)]
struct Range(BigInt, Option<BigInt>, BigInt);
impl Range {
    fn empty(&self) -> bool {
        let Range(start, end, step) = self;
        match (step.sign(), end) {
            (_, None) => false,
            (Sign::Minus, Some(end)) => start <= end,
            (Sign::NoSign | Sign::Plus, Some(end)) => start >= end,
        }
    }
}
impl Iterator for Range {
    type Item = Obj;
    fn next(&mut self) -> Option<Obj> {
        if self.empty() {
            None
        } else {
            let Range(start, _end, step) = self;
            let ret = start.clone();
            *start += &*step;
            Some(Obj::from(ret))
        }
    }
}
impl Display for Range {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(end) => write!(formatter, "{} til {} by {}", self.0, end, self.2),
            None => write!(formatter, "{} til ... by {}", self.0, self.2),
        }
    }
}
impl Stream for Range {
    fn peek(&self) -> Option<Obj> {
        if self.empty() {
            None
        } else {
            Some(Obj::from(self.0.clone()))
        }
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        let Range(start, end, step) = self;
        let end = end.as_ref()?;
        match step.sign() {
            // weird
            Sign::NoSign => {
                if start < end {
                    None
                } else {
                    Some(0)
                }
            }
            Sign::Minus => {
                ((end - start - step + 1usize).max(BigInt::from(0)) / (-step)).to_usize()
            }
            Sign::Plus => ((end - start + step - 1usize).max(BigInt::from(0)) / step).to_usize(),
        }
    }
}

#[derive(Debug, Clone)]
struct Permutations(Rc<Vec<Obj>>, Option<Rc<Vec<usize>>>);
impl Iterator for Permutations {
    type Item = Obj;
    fn next(&mut self) -> Option<Obj> {
        let v = Rc::make_mut(self.1.as_mut()?);
        let ret = Obj::list(v.iter().map(|i| self.0[*i].clone()).collect());

        // 1 6 4 2 -> 2 1 4 6
        // last increase, and the largest index of something larger than it
        let mut up = None;
        for i in 0..(v.len() - 1) {
            if v[i] < v[i + 1] {
                up = Some((i, i + 1));
            } else {
                match &mut up {
                    Some((inc, linc)) => {
                        if v[i + 1] > v[*inc] {
                            *linc = i + 1;
                        }
                    }
                    None => {}
                }
            }
        }
        match up {
            Some((inc, linc)) => {
                v.swap(inc, linc);
                v[inc + 1..].reverse();
            }
            None => {
                self.1 = None;
            }
        }
        Some(ret)
    }
}
impl Display for Permutations {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(x) => {
                write!(
                    formatter,
                    "permutations({} @ {})",
                    CommaSeparated(&**self.0),
                    CommaSeparated(&**x)
                )
            }
            None => write!(formatter, "permutations(done)"),
        }
    }
}
impl Stream for Permutations {
    fn peek(&self) -> Option<Obj> {
        Some(Obj::list(
            self.1
                .as_ref()?
                .iter()
                .map(|i| self.0[*i].clone())
                .collect(),
        ))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
}

#[derive(Debug, Clone)]
struct Combinations(Rc<Vec<Obj>>, Option<Rc<Vec<usize>>>);
impl Iterator for Combinations {
    type Item = Obj;
    fn next(&mut self) -> Option<Obj> {
        let v = Rc::make_mut(self.1.as_mut()?);
        let ret = Obj::list(v.iter().map(|i| self.0[*i].clone()).collect());

        let mut last = self.0.len();
        for i in (0..v.len()).rev() {
            if v[i] + 1 < last {
                // found the next
                v[i] += 1;
                for j in i + 1..v.len() {
                    v[j] = v[j - 1] + 1;
                }
                return Some(ret);
            }
            last -= 1;
        }
        self.1 = None;
        Some(ret)
    }
}
impl Display for Combinations {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(x) => {
                write!(
                    formatter,
                    "combinations({} @ {})",
                    CommaSeparated(&**self.0),
                    CommaSeparated(&**x)
                )
            }
            None => write!(formatter, "combinations(done)"),
        }
    }
}
impl Stream for Combinations {
    fn peek(&self) -> Option<Obj> {
        Some(Obj::list(
            self.1
                .as_ref()?
                .iter()
                .map(|i| self.0[*i].clone())
                .collect(),
        ))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
}

#[derive(Debug, Clone)]
struct Subsequences(Rc<Vec<Obj>>, Option<Rc<Vec<bool>>>);
impl Iterator for Subsequences {
    type Item = Obj;
    fn next(&mut self) -> Option<Obj> {
        let v = Rc::make_mut(self.1.as_mut()?);
        let ret = Obj::list(
            v.iter()
                .zip(self.0.iter())
                .filter_map(|(b, x)| if *b { Some(x.clone()) } else { None })
                .collect(),
        );

        for i in (0..v.len()).rev() {
            if !v[i] {
                v[i] = true;
                for j in i + 1..v.len() {
                    v[j] = false;
                }
                return Some(ret);
            }
        }
        self.1 = None;
        Some(ret)
    }
}
impl Display for Subsequences {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(x) => {
                write!(
                    formatter,
                    "subsequences({} @ {})",
                    CommaSeparated(&**self.0),
                    CommaSeparated(&**x)
                )
            }
            None => write!(formatter, "subsequences(done)"),
        }
    }
}
impl Stream for Subsequences {
    fn peek(&self) -> Option<Obj> {
        Some(Obj::list(
            self.1
                .as_ref()?
                .iter()
                .zip(self.0.iter())
                .filter_map(|(b, x)| if *b { Some(x.clone()) } else { None })
                .collect(),
        ))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
}

#[derive(Debug, Clone)]
struct CartesianPower(Rc<Vec<Obj>>, Option<Rc<Vec<usize>>>);
impl Iterator for CartesianPower {
    type Item = Obj;
    fn next(&mut self) -> Option<Obj> {
        let v = Rc::make_mut(self.1.as_mut()?);
        let ret = Obj::list(v.iter().map(|i| self.0[*i].clone()).collect());

        // let mut last = self.0.len();
        for i in (0..v.len()).rev() {
            v[i] += 1;
            if v[i] == self.0.len() {
                v[i] = 0;
            } else {
                return Some(ret);
            }
        }
        self.1 = None;
        Some(ret)
    }
}
impl Display for CartesianPower {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(x) => {
                write!(
                    formatter,
                    "CartesianPower({} @ {})",
                    CommaSeparated(&**self.0),
                    CommaSeparated(&**x)
                )
            }
            None => write!(formatter, "CartesianPower(done)"),
        }
    }
}
impl Stream for CartesianPower {
    fn peek(&self) -> Option<Obj> {
        Some(Obj::list(
            self.1
                .as_ref()?
                .iter()
                .map(|i| self.0[*i].clone())
                .collect(),
        ))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
}

// very illegal
#[derive(Clone)]
struct Iterate(Option<(Obj, Func, REnv)>);
// directly debug-printing env can easily recurse infinitely
impl Debug for Iterate {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "Iterate???")
    }
}
impl Iterator for Iterate {
    type Item = Obj;
    fn next(&mut self) -> Option<Obj> {
        let (obj, func, renv) = self.0.as_mut()?;
        let ret = obj.clone();
        let cur = std::mem::take(obj);
        match func.run(&renv, vec![cur]) {
            Ok(nxt) => {
                *obj = nxt;
            }
            Err(e) => {
                eprintln!(
                    "INTERNAL ERROR: iterate function failed! {} terminating...",
                    e
                );
                self.0 = None;
            }
        }
        Some(ret)
    }
}
impl Display for Iterate {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "Iterate???")
    }
}
impl Stream for Iterate {
    fn peek(&self) -> Option<Obj> {
        Some(self.0.as_ref()?.0.clone())
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
}

#[derive(Debug, Clone)]
pub enum Seq {
    String(Rc<String>),
    List(Rc<Vec<Obj>>),
    Dict(Rc<HashMap<ObjKey, Obj>>, Option<Box<Obj>>), // default value
    Vector(Rc<Vec<NNum>>),
    Bytes(Rc<Vec<u8>>),
    Stream(Rc<dyn Stream>),
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
        (ObjType::Vector, Obj::Seq(Seq::Vector(..))) => true,
        (ObjType::Bytes, Obj::Seq(Seq::Bytes(..))) => true,
        (ObjType::Stream, Obj::Seq(Seq::Stream(..))) => true,
        (ObjType::Func, Obj::Func(..)) => true,
        (ObjType::Type, Obj::Func(Func::Type(_), _)) => true,
        (ObjType::Any, _) => true,
        (ObjType::Struct(s1), Obj::Instance(s2, _)) => s1.id == s2.id,
        (ObjType::Satisfying(renv, func), x) => match func.run(renv, vec![x.clone()]) {
            Ok(res) => res.truthy(),
            Err(e) => {
                eprintln!("INTERNAL ERROR: running the predicate for a 'satisfying'-type-check failed with; {}! trudging on...", e);
                false // FIXME yikes
            }
        },
        _ => false,
    }
}

fn expect_one(args: Vec<Obj>, msg: &str) -> NRes<Obj> {
    match few(args) {
        Few::One(arg) => Ok(arg),
        _ => Err(NErr::type_error(format!("{} expected one argument", msg))),
    }
}

fn call_type(ty: &ObjType, arg: Vec<Obj>) -> NRes<Obj> {
    match ty {
        ObjType::Int => match expect_one(arg, "int")? {
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
        ObjType::Float => match expect_one(arg, "float")? {
            Obj::Num(n) => Ok(Obj::from(to_f64_ok(&n)?)),
            Obj::Seq(Seq::String(s)) => match s.parse::<f64>() {
                Ok(x) => Ok(Obj::from(x)),
                Err(s) => Err(NErr::value_error(format!("can't parse: {}", s))),
            },
            _ => Err(NErr::type_error(
                "float: expected number or string".to_string(),
            )),
        },
        ObjType::Number => match expect_one(arg, "number")? {
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
        ObjType::List => match expect_one(arg, "list")? {
            Obj::Seq(Seq::List(xs)) => Ok(Obj::Seq(Seq::List(xs))),
            mut arg => Ok(Obj::list(
                mut_obj_into_iter(&mut arg, "list conversion")?.collect(),
            )),
        },
        ObjType::String => Ok(Obj::from(format!("{}", expect_one(arg, "str")?))),
        ObjType::Bytes => match expect_one(arg, "bytes")? {
            Obj::Seq(Seq::Bytes(xs)) => Ok(Obj::Seq(Seq::Bytes(xs))),
            Obj::Seq(Seq::String(s)) => Ok(Obj::Seq(Seq::Bytes(Rc::new(s.as_bytes().to_vec())))),
            mut arg => Ok(Obj::Seq(Seq::Bytes(Rc::new(
                mut_obj_into_iter(&mut arg, "bytes conversion")?
                    .map(|e| to_byte(e, "bytes conversion"))
                    .collect::<NRes<Vec<u8>>>()?,
            )))),
        },
        ObjType::Vector => match expect_one(arg, "vector")? {
            Obj::Seq(Seq::Vector(s)) => Ok(Obj::Seq(Seq::Vector(s))),
            mut arg => to_obj_vector(mut_obj_into_iter(&mut arg, "vector conversion")?.map(Ok)),
        },
        ObjType::Dict => match expect_one(arg, "dict")? {
            Obj::Seq(Seq::Dict(x, d)) => Ok(Obj::Seq(Seq::Dict(x, d))),
            // nonsensical but maybe this is something some day
            /*
            mut arg => Ok(Obj::Dict(
                    Rc::new(mut_obj_into_iter_pairs(&mut arg, "dict conversion")?.collect::<HashMap<ObjKey, Obj>>()), None)),
                    */
            mut arg => Ok(Obj::dict(
                mut_obj_into_iter(&mut arg, "dict conversion")?
                    .map(|p| match p {
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
        ObjType::Type => Ok(Obj::Func(
            Func::Type(type_of(&expect_one(arg, "type")?)),
            Precedence::zero(),
        )),
        ObjType::Struct(s) => {
            if arg.len() == 0 {
                Ok(Obj::Instance(s.clone(), vec![Obj::Null; s.size]))
            } else if arg.len() == s.size {
                Ok(Obj::Instance(s.clone(), arg))
            } else {
                Err(NErr::argument_error(format!(
                    "struct construction: wrong number of arguments: {}, wanted {}",
                    arg.len(),
                    s.size
                )))
            }
        }
        // TODO: complex
        _ => Err(NErr::type_error(
            "that type can't be called (maybe not implemented)".to_string(),
        )),
    }
}

// TODO can we take?
fn to_type(arg: &Obj, msg: &str) -> NRes<ObjType> {
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
            Obj::Seq(s) => !s.is_empty(),
            Obj::Func(..) => true,
            Obj::Instance(..) => true,
        }
    }

    pub fn i32(n: i32) -> Self {
        Obj::Num(NNum::Int(BigInt::from(n)))
    }
    fn list(n: Vec<Obj>) -> Self {
        Obj::Seq(Seq::List(Rc::new(n)))
    }
    fn dict(m: HashMap<ObjKey, Obj>, def: Option<Obj>) -> Self {
        Obj::Seq(Seq::Dict(Rc::new(m), def.map(Box::new)))
    }

    fn zero() -> Self {
        Obj::Num(NNum::Int(BigInt::from(0)))
    }
    fn one() -> Self {
        Obj::Num(NNum::Int(BigInt::from(1)))
    }
}

impl Default for Obj {
    fn default() -> Obj {
        Obj::Null
    }
}

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
impl From<u8> for Obj {
    fn from(n: u8) -> Self {
        Obj::Num(NNum::Int(BigInt::from(n)))
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
forward_from!(BigInt);
// forward_from!(i32);
forward_from!(f64);
forward_from!(usize);
forward_from!(Complex64);

impl From<usize> for ObjKey {
    fn from(n: usize) -> Self {
        ObjKey::Num(NTotalNum(NNum::from(n)))
    }
}
impl From<&str> for ObjKey {
    fn from(n: &str) -> Self {
        ObjKey::String(Rc::new(n.to_string()))
    }
}

impl PartialEq for Obj {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Obj::Null, Obj::Null) => true,
            (Obj::Num(a), Obj::Num(b)) => a == b,
            (Obj::Seq(a), Obj::Seq(b)) => a == b,
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

/*
fn to_bigint_ok(n: &NNum) -> NRes<BigInt> {
    Ok(n.to_bigint().ok_or(NErr::value_error("bad number to int".to_string()))?.clone())
}
*/
fn to_usize_ok(n: &NNum) -> NRes<usize> {
    n.to_usize()
        .ok_or(NErr::value_error("bad number to usize".to_string()))
}
fn clamp_to_usize_ok(n: &NNum) -> NRes<usize> {
    n.clamp_to_usize()
        .ok_or(NErr::value_error("bad number to usize".to_string()))
}
fn obj_clamp_to_usize_ok(n: &Obj) -> NRes<usize> {
    match n {
        Obj::Num(n) => clamp_to_usize_ok(n),
        _ => Err(NErr::type_error(format!("bad scalar {}", FmtObj::debug(n)))),
    }
}
fn into_bigint_ok(n: NNum) -> NRes<BigInt> {
    n.into_bigint()
        .ok_or(NErr::value_error("bad number to int".to_string()))
}
fn to_f64_ok(n: &NNum) -> NRes<f64> {
    n.to_f64()
        .ok_or(NErr::value_error("bad number to float".to_string()))
}

fn to_key(obj: Obj) -> NRes<ObjKey> {
    match obj {
        Obj::Null => Ok(ObjKey::Null),
        Obj::Num(x) => Ok(ObjKey::Num(NTotalNum(x))),
        Obj::Seq(Seq::String(x)) => Ok(ObjKey::String(x)),
        Obj::Seq(Seq::List(mut xs)) => Ok(ObjKey::List(Rc::new(
            RcVecIter::of(&mut xs)
                .map(|e| to_key(e))
                .collect::<NRes<Vec<ObjKey>>>()?,
        ))),
        Obj::Seq(Seq::Dict(mut d, _)) => {
            let mut pairs = RcHashMapIter::of(&mut d)
                .map(|(k, v)| Ok((k, to_key(v)?)))
                .collect::<NRes<Vec<(ObjKey, ObjKey)>>>()?;
            pairs.sort();
            Ok(ObjKey::Dict(Rc::new(pairs)))
        }
        Obj::Seq(Seq::Vector(x)) => Ok(ObjKey::Vector(Rc::new(
            x.iter().map(|e| NTotalNum(e.clone())).collect(),
        ))),
        Obj::Seq(Seq::Bytes(x)) => Ok(ObjKey::Bytes(x)),
        Obj::Seq(Seq::Stream(s)) => Ok(ObjKey::List(Rc::new(
            s.force()
                .ok_or(NErr::type_error("infinite stream as key".to_string()))?
                .into_iter()
                .map(|e| to_key(e))
                .collect::<NRes<Vec<ObjKey>>>()?,
        ))),
        Obj::Func(..) => Err(NErr::type_error(
            "Using a function as a dictionary key isn't supported".to_string(),
        )),
        Obj::Instance(..) => Err(NErr::type_error(
            "Using an instance as a dictionary key isn't supported".to_string(),
        )),
    }
}

fn key_to_obj(key: ObjKey) -> Obj {
    match key {
        ObjKey::Null => Obj::Null,
        ObjKey::Num(NTotalNum(x)) => Obj::Num(x),
        ObjKey::String(x) => Obj::Seq(Seq::String(x)),
        ObjKey::List(mut xs) => Obj::list(
            RcVecIter::of(&mut xs)
                .map(|e| key_to_obj(e.clone()))
                .collect::<Vec<Obj>>(),
        ),
        ObjKey::Dict(mut d) => Obj::dict(
            RcVecIter::of(&mut d)
                .map(|(k, v)| (k, key_to_obj(v)))
                .collect::<HashMap<ObjKey, Obj>>(),
            None,
        ),
        ObjKey::Vector(v) => Obj::Seq(Seq::Vector(Rc::new(
            v.iter().map(|x| x.0.clone()).collect(),
        ))),
        ObjKey::Bytes(v) => Obj::Seq(Seq::Bytes(v)),
    }
}

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
    base: FmtBase,
    repr: bool,
    pad: char,
    pad_length: usize,
    pad_align: FmtAlign,
    budget: usize,
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
impl MyDisplay for NTotalNum {
    fn is_null(&self) -> bool {
        false
    }
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
fn write_slice(
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

fn write_pairs<'a, 'b>(
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

struct FmtDictPairs<'f, T>(T, &'f MyFmtFlags);
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

fn write_bytes(s: &[u8], formatter: &mut dyn fmt::Write, flags: &mut MyFmtFlags) -> fmt::Result {
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
                    write!(formatter, "..., ")?;
                    break;
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
            Obj::Instance(_, fields) => write!(formatter, "<instance: {}>", CommaSeparated(fields)),
        }
    }
}

impl Obj {
    pub fn fmt_with(&self, formatter: &mut dyn fmt::Write, mut flags: MyFmtFlags) -> fmt::Result {
        self.fmt_with_mut(formatter, &mut flags)
    }
}

// ????
pub struct FmtObj<'a, 'b>(pub &'a Obj, pub &'b MyFmtFlags);
impl<'a, 'b> Display for FmtObj<'a, 'b> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt_with(formatter, self.1.clone())
    }
}

const DEBUG_FMT: MyFmtFlags = MyFmtFlags::budgeted_repr(6);

impl FmtObj<'_, '_> {
    fn debug<'a>(t: &'a Obj) -> FmtObj<'a, 'static> {
        FmtObj(t, &DEBUG_FMT)
    }
}

struct CommaSeparatedDebug<'a>(&'a [Obj]);

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
        self == &ObjKey::Null
    } // thonk
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
            ObjKey::Bytes(xs) => write_bytes(xs.as_slice(), formatter, flags),
        }
    }
}

impl ObjKey {
    pub fn fmt_with(&self, formatter: &mut dyn fmt::Write, mut flags: MyFmtFlags) -> fmt::Result {
        self.fmt_with_mut(formatter, &mut flags)
    }
}

pub enum ObjToCloningIter<'a> {
    List(std::slice::Iter<'a, Obj>),
    Dict(std::collections::hash_map::Iter<'a, ObjKey, Obj>),
    String(std::str::Chars<'a>),
    Vector(std::slice::Iter<'a, NNum>),
    Bytes(std::slice::Iter<'a, u8>),
    Stream(Box<dyn Stream>),
}

fn seq_to_cloning_iter(seq: &Seq) -> ObjToCloningIter<'_> {
    match seq {
        Seq::List(v) => ObjToCloningIter::List(v.iter()),
        Seq::Dict(v, _) => ObjToCloningIter::Dict(v.iter()),
        Seq::String(s) => ObjToCloningIter::String(s.chars()),
        Seq::Vector(v) => ObjToCloningIter::Vector(v.iter()),
        Seq::Bytes(v) => ObjToCloningIter::Bytes(v.iter()),
        Seq::Stream(v) => ObjToCloningIter::Stream(v.clone_box()),
    }
}

fn obj_to_cloning_iter<'a, 'b>(obj: &'a Obj, purpose: &'b str) -> NRes<ObjToCloningIter<'a>> {
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
            ObjToCloningIter::Stream(it) => Some(Obj::from(it.next()?)),
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
    Stream(Box<dyn Stream>),
}

// iterates over (index, value) or (key, value)
pub enum MutObjIntoIterPairs<'a> {
    List(usize, RcVecIter<'a, Obj>),
    Dict(RcHashMapIter<'a, ObjKey, Obj>),
    String(usize, RcStringIter<'a>),
    Vector(usize, RcVecIter<'a, NNum>),
    Bytes(usize, RcVecIter<'a, u8>),
    Stream(usize, Box<dyn Stream>),
}

fn mut_seq_into_iter(seq: &mut Seq) -> MutObjIntoIter<'_> {
    match seq {
        Seq::List(v) => MutObjIntoIter::List(RcVecIter::of(v)),
        Seq::Dict(v, _) => MutObjIntoIter::Dict(RcHashMapIter::of(v)),
        Seq::String(s) => MutObjIntoIter::String(RcStringIter::of(s)),
        Seq::Vector(v) => MutObjIntoIter::Vector(RcVecIter::of(v)),
        Seq::Bytes(v) => MutObjIntoIter::Bytes(RcVecIter::of(v)),
        Seq::Stream(v) => MutObjIntoIter::Stream(v.clone_box()),
    }
}

fn mut_obj_into_iter<'a, 'b>(obj: &'a mut Obj, purpose: &'b str) -> NRes<MutObjIntoIter<'a>> {
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
    type Item = Obj;

    fn next(&mut self) -> Option<Obj> {
        match self {
            MutObjIntoIter::List(it) => it.next(),
            MutObjIntoIter::Dict(it) => Some(key_to_obj(it.next()?.0)),
            MutObjIntoIter::String(it) => Some(Obj::from(it.next()?)),
            MutObjIntoIter::Vector(it) => Some(Obj::Num(it.next()?.clone())),
            MutObjIntoIter::Bytes(it) => Some(Obj::from(it.next()? as usize)),
            MutObjIntoIter::Stream(it) => Some(Obj::from(it.next()?)),
        }
    }
}

fn mut_seq_into_iter_pairs(seq: &mut Seq) -> MutObjIntoIterPairs<'_> {
    match seq {
        Seq::List(v) => MutObjIntoIterPairs::List(0, RcVecIter::of(v)),
        Seq::Dict(v, _) => MutObjIntoIterPairs::Dict(RcHashMapIter::of(v)),
        Seq::String(s) => MutObjIntoIterPairs::String(0, RcStringIter::of(s)),
        Seq::Vector(v) => MutObjIntoIterPairs::Vector(0, RcVecIter::of(v)),
        Seq::Bytes(v) => MutObjIntoIterPairs::Bytes(0, RcVecIter::of(v)),
        Seq::Stream(v) => MutObjIntoIterPairs::Stream(0, v.clone_box()),
    }
}

fn mut_obj_into_iter_pairs<'a, 'b>(
    obj: &'a mut Obj,
    purpose: &'b str,
) -> NRes<MutObjIntoIterPairs<'a>> {
    match obj {
        Obj::Seq(s) => Ok(mut_seq_into_iter_pairs(s)),
        _ => Err(NErr::type_error(format!("{}: not iterable", purpose))),
    }
}

impl Iterator for MutObjIntoIterPairs<'_> {
    type Item = (ObjKey, Obj);

    fn next(&mut self) -> Option<(ObjKey, Obj)> {
        match self {
            MutObjIntoIterPairs::List(i, it) => {
                let o = it.next()?;
                let j = *i;
                *i += 1;
                Some((ObjKey::from(j), o))
            }
            MutObjIntoIterPairs::Dict(it) => it.next(),
            MutObjIntoIterPairs::String(i, it) => {
                let o = it.next()?;
                let j = *i;
                *i += 1;
                Some((ObjKey::from(j), Obj::from(o)))
            }
            MutObjIntoIterPairs::Vector(i, it) => {
                let o = it.next()?;
                let j = *i;
                *i += 1;
                Some((ObjKey::from(j), Obj::Num(o)))
            }
            MutObjIntoIterPairs::Bytes(i, it) => {
                let o = it.next()?;
                let j = *i;
                *i += 1;
                Some((ObjKey::from(j), Obj::from(o as usize)))
            }
            MutObjIntoIterPairs::Stream(i, s) => {
                let o = s.next()?;
                let j = *i;
                *i += 1;
                Some((ObjKey::from(j), Obj::from(o)))
            }
        }
    }
}

impl Seq {
    fn is_empty(&self) -> bool {
        match self {
            Seq::String(x) => x.is_empty(),
            Seq::List(x) => x.is_empty(),
            Seq::Dict(x, _) => x.is_empty(),
            Seq::Vector(x) => x.is_empty(),
            Seq::Bytes(x) => x.is_empty(),
            Seq::Stream(x) => x.len() == Some(0),
        }
    }
    fn len(&self) -> Option<usize> {
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

#[derive(Debug)]
pub enum NErr {
    Throw(
        Obj,
        Vec<(String, CodeLoc, Option<(Rc<String>, Rc<String>)>)>,
    ),
    // Optional (source file, source code), added when we pass through an eval boundary roughly
    // speaking. Is this bonkers? Idk.
    Break(Obj),
    Return(Obj),
    Continue,
}

fn write_source_error(out: &mut String, src: &str, start: &CodeLoc, end: Option<&CodeLoc>) {
    use std::fmt::Write;

    let end: CodeLoc = match end {
        Some(k) => k.clone(),
        None => CodeLoc {
            line: start.line,
            col: start.col + 1,
            index: start.index + 1,
        },
    };
    let mut line = 1;
    let mut ended = false;
    for (i, c) in src.chars().enumerate() {
        if c == '\n' {
            line += 1;
            if line > end.line {
                break;
            }
        } else {
            if i == start.index {
                write!(out, "\x1b[1;31m").ok();
            }
            if line >= start.line && line <= end.line {
                write!(out, "{}", c).ok();
            }
            if i == end.index {
                write!(out, "\x1b[0m").ok();
                ended = true;
            }
        }
    }
    if !ended {
        write!(out, "\x1b[0m").ok();
    }
}

impl NErr {
    fn supply_source(self: &mut NErr, src_file: Rc<String>, src: Rc<String>) {
        match self {
            NErr::Throw(_, trace) => {
                for tup in trace {
                    if tup.2.is_none() {
                        tup.2 = Some((src_file.clone(), src.clone()));
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
                    Some((_, loc, tsrc)) => {
                        let real_src_code = match tsrc {
                            Some((_, f)) => f,
                            None => src,
                        };
                        write_source_error(&mut out, real_src_code, loc, None)
                    }
                    None => {}
                }
                for (thing, loc, tsrc) in trace {
                    match tsrc {
                        Some((src_file, _)) => write!(
                            out,
                            "\n    at {} ({}:{}:{})",
                            thing, src_file, loc.line, loc.col
                        )
                        .ok(),
                        None => write!(out, "\n    at {} ({}:{})", thing, loc.line, loc.col).ok(),
                    };
                }
                out
            }
            NErr::Break(e) => format!("break {}", e),
            NErr::Continue => format!("continue"),
            NErr::Return(e) => format!("return {}", e),
        }
    }

    fn throw(s: String) -> NErr {
        NErr::Throw(Obj::from(s), Vec::new())
    }
    fn argument_error(s: String) -> NErr {
        NErr::throw(format!("argument error: {}", s))
    }
    fn index_error(s: String) -> NErr {
        NErr::throw(format!("index error: {}", s))
    }
    fn key_error(s: String) -> NErr {
        NErr::throw(format!("key error: {}", s))
    }
    fn empty_error(s: String) -> NErr {
        NErr::throw(format!("empty error: {}", s))
    }
    fn name_error(s: String) -> NErr {
        NErr::throw(format!("name error: {}", s))
    }
    fn syntax_error(s: String) -> NErr {
        NErr::throw(format!("syntax error: {}", s))
    }
    fn syntax_error_loc(s: String, msg: String, loc: CodeLoc) -> NErr {
        NErr::Throw(
            Obj::from(format!("syntax error: {}", s)),
            vec![(msg, loc, None)],
        )
    }
    fn type_error(s: String) -> NErr {
        NErr::throw(format!("type error: {}", s))
    }
    fn value_error(s: String) -> NErr {
        NErr::throw(format!("value error: {}", s))
    }
    fn io_error(s: String) -> NErr {
        NErr::throw(format!("io error: {}", s))
    }
    fn assert_error(s: String) -> NErr {
        NErr::throw(format!("assert error: {}", s))
    }

    fn argument_error_args(x: &[Obj]) -> NErr {
        NErr::throw(format!(
            "unrecognized argument types/count: {}",
            CommaSeparated(&x.iter().map(|k| type_of(k).name()).collect::<Vec<String>>())
        ))
    }
    fn argument_error_few2(x: &Few2<Obj>) -> NErr {
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
    fn argument_error_1(x: &Obj) -> NErr {
        NErr::throw(format!("unrecognized argument type: {}", type_of(x).name()))
    }
    fn argument_error_first(x: &Obj) -> NErr {
        NErr::throw(format!(
            "unrecognized 1st argument type: {}",
            type_of(x).name()
        ))
    }
    fn argument_error_second(x: &Obj) -> NErr {
        NErr::throw(format!(
            "unrecognized 2nd argument type: {}",
            type_of(x).name()
        ))
    }
    fn argument_error_2(x: &Obj, y: &Obj) -> NErr {
        NErr::throw(format!(
            "unrecognized argument types: ({}, {})",
            type_of(x).name(),
            type_of(y).name()
        ))
    }
}

fn add_trace<T>(res: NRes<T>, thing: String, loc: CodeLoc) -> NRes<T> {
    match res {
        Err(NErr::Throw(e, mut trace)) => {
            trace.push((thing, loc, None));
            Err(NErr::Throw(e, trace))
        }
        e => e,
    }
}

fn err_add_name<T>(res: NRes<T>, s: &str) -> NRes<T> {
    match res {
        Ok(x) => Ok(x),
        Err(NErr::Throw(msg, trace)) => {
            Err(NErr::Throw(Obj::from(format!("{}: {}", s, msg)), trace))
        }
        Err(NErr::Break(e)) => Err(NErr::Break(e)),
        Err(NErr::Return(e)) => Err(NErr::Return(e)),
        Err(NErr::Continue) => Err(NErr::Continue),
    }
}

impl fmt::Display for NErr {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NErr::Throw(e, trace) => {
                write!(formatter, "{}", e)?;
                for (thing, loc, src) in trace {
                    match src {
                        Some(srcp) => write!(
                            formatter,
                            " at {} ({}:{}:{})",
                            thing, srcp.0, loc.line, loc.col
                        )?,
                        None => write!(formatter, " at {} ({}:{})", thing, loc.line, loc.col)?,
                    }
                }
                Ok(())
            }
            NErr::Break(e) => write!(formatter, "break {}", e),
            NErr::Continue => write!(formatter, "continue"),
            NErr::Return(e) => write!(formatter, "return {}", e),
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
    // \x, y: f(y, x) (...I feel like we shouldn't special-case so many but shrug...)
    Flip(Box<Func>),
    // each None is a slot for an argument
    ListSection(Vec<Option<Obj>>),
    IndexSection(Option<Box<Obj>>, Option<Box<Obj>>),
    // outer None is nothing; Some(None) is a slot
    SliceSection(
        Option<Box<Obj>>,
        Option<Option<Box<Obj>>>,
        Option<Option<Box<Obj>>>,
    ),
    ChainSection(
        Option<Box<Obj>>,
        Vec<(CodeLoc, Box<Func>, Precedence, Option<Box<Obj>>)>,
    ),
    CallSection(Option<Box<Obj>>, Vec<Option<Obj>>),
    Type(ObjType), // includes Struct now
    StructField(Struct, usize),
    Memoized(Box<Func>, Rc<RefCell<HashMap<Vec<ObjKey>, Obj>>>),
}

type REnv = Rc<RefCell<Env>>;

impl Func {
    fn run(&self, env: &REnv, mut args: Vec<Obj>) -> NRes<Obj> {
        match self {
            Func::Builtin(b) => b.run(env, args),
            Func::Closure(c) => c.run(args),
            Func::PartialApp1(f, x) => match few(args) {
                Few::One(arg) => f.run(env, vec![(**x).clone(), arg]),
                a => Err(NErr::argument_error(format!("partially applied functions can only be called with one more argument, but {} {} got {}", f, FmtObj::debug(x), a)))
            }
            Func::PartialApp2(f, x) => match few(args) {
                Few::One(arg) => f.run(env, vec![arg, (**x).clone()]),
                a => Err(NErr::argument_error(format!("partially applied functions can only be called with one more argument, but {} {} got {}", f, FmtObj::debug(x), a)))
            }
            Func::PartialAppLast(f, x) => {
                args.push(*x.clone());
                f.run(env, args)
            }
            Func::Composition(f, g) => f.run(env, vec![g.run(env, args)?]),
            Func::OnComposition(f, g) => {
                let mut mapped_args = Vec::new();
                for e in args {
                    mapped_args.push(g.run(env, vec![e])?);
                }
                f.run(env, mapped_args)
            }
            Func::Parallel(fs) => {
                let mut res = Vec::new();
                match few(args) {
                    Few::One(Obj::Seq(mut seq)) => {
                        match seq.len() {
                            Some(n) if n == fs.len() => {
                                for (f, a) in fs.iter().zip(mut_seq_into_iter(&mut seq)) {
                                    res.push(f.run(env, vec![a])?);
                                }
                            }
                            Some(n) => return Err(NErr::type_error(format!("Parallel argument seq has wrong length {}: {:?}", n, seq))),
                            None => return Err(NErr::type_error(format!("Parallel argument seq has infinite length?: {:?}", seq)))
                        }
                    }
                    Few::Zero => {
                        return Err(NErr::argument_error(format!("can't call Parallel with no args")))
                    }
                    Few::One(x) => {
                        return Err(NErr::type_error(format!("can't call Parallel with one non-seq {}", FmtObj::debug(&x))))
                    }
                    Few::Many(args) => {
                        for (f, a) in fs.iter().zip(args) {
                            res.push(f.run(env, vec![a])?);
                        }
                    }
                }
                Ok(Obj::list(res))
            }
            Func::Fanout(fs) => {
                let mut res = Vec::new();
                for f in fs {
                    res.push(f.run(env, args.clone())?);
                }
                Ok(Obj::list(res))
            }
            Func::Flip(f) => match few2(args) {
                // weird lol
                Few2::One(a) => Ok(Obj::Func(Func::PartialApp1(f.clone(), Box::new(a)), Precedence::zero())),
                Few2::Two(a, b) => f.run(env, vec![b, a]),
                _ => Err(NErr::argument_error("Flipped function can only be called on two arguments".to_string()))
            }
            Func::ListSection(x) => {
                let mut it = args.into_iter();
                match x.iter().map(|e| match e {
                    Some(e) => Some(e.clone()),
                    None => it.next()
                }).collect() {
                    None => Err(NErr::argument_error("list section: too few arguments".to_string())),
                    Some(v) => match it.next() {
                        None => Ok(Obj::list(v)),
                        Some(_) => Err(NErr::argument_error("list section: too many arguments".to_string())),
                    }
                }
            }
            Func::ChainSection(seed, ops) => {
                let mut it = args.into_iter();
                let mut ce = ChainEvaluator::new(match seed {
                    Some(x) => *x.clone(),
                    None => match it.next() {
                        Some(e) => e,
                        None => return Err(NErr::argument_error("chain section: too few arguments".to_string())),
                    }
                });
                for (loc, op, prec, opd) in ops {
                    ce.give(env, *op.clone(), *prec, match opd {
                        Some(x) => *x.clone(),
                        None => match it.next() {
                            Some(e) => e,
                            None => return Err(NErr::argument_error("chain section: too few arguments".to_string())),
                        }
                    }, *loc)?;
                }
                match it.next() {
                    None => ce.finish(env),
                    Some(_) => Err(NErr::argument_error("chain section: too many arguments".to_string())),
                }
            }
            Func::CallSection(callee, sec_args) => {
                let mut it = args.into_iter();
                let callee = match callee {
                    Some(x) => *x.clone(),
                    None => match it.next() {
                        Some(e) => e,
                        None => return Err(NErr::argument_error("call section: too few arguments".to_string())),
                    }
                };
                let real_args = sec_args.into_iter().map(|e| match e {
                    Some(x) => Some(x.clone()),
                    None => it.next(),
                }).collect::<Option<Vec<Obj>>>().ok_or(NErr::argument_error("call section: too few arguments".to_string()))?;
                match it.next() {
                    None => call(env, callee, real_args),
                    Some(_) => Err(NErr::argument_error("call section: too many arguments".to_string())),
                }
            }
            Func::IndexSection(x, i) => {
                let mut it = args.into_iter();
                let x = match x {
                    Some(e) => (**e).clone(),
                    None => it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?,
                };
                let i = match i {
                    Some(e) => (**e).clone(),
                    None => it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?,
                };
                index(x, i)
            }
            Func::SliceSection(x, lo, hi) => {
                let mut it = args.into_iter();
                let x = match x {
                    Some(e) => (**e).clone(),
                    None => it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?,
                };
                let lo = match lo {
                    None => None,
                    Some(None) => Some(it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?),
                    Some(Some(e)) => Some((**e).clone()),
                };
                let hi = match hi {
                    None => None,
                    Some(None) => Some(it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?),
                    Some(Some(e)) => Some((**e).clone()),
                };
                slice(x, lo, hi)
            }
            Func::Type(t) => call_type(t, args),
            Func::StructField(struc, field_index) => match few(args) {
                Few::One(Obj::Instance(s, fields)) => {
                    if *struc == s {
                        Ok(fields[*field_index].clone())
                    } else {
                        Err(NErr::argument_error(format!("wrong kind of struct")))
                    }
                }
                _ => Err(NErr::argument_error("fields can only take one argument".to_string()))
            }
            Func::Memoized(f, memo) => {
                let kargs = args.into_iter().map(to_key).collect::<NRes<Vec<ObjKey>>>()?;
                match memo.try_borrow() {
                    Ok(memo) => match memo.get(&kargs) {
                        Some(res) => return Ok(res.clone()),
                        None => {}
                    }
                    Err(e) => Err(NErr::io_error(format!("memo: borrow failed: {}", e)))?
                };
                let res = f.run(env, kargs.iter().cloned().map(key_to_obj).collect())?;
                match memo.try_borrow_mut() {
                    Ok(mut memo) => memo.insert(kargs, res.clone()),
                    Err(e) => Err(NErr::io_error(format!("memo: borrow failed: {}", e)))?
                };
                Ok(res)
            }
        }
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match self {
            Func::Builtin(b) => b.try_chain(other),
            Func::Closure(_) => None,
            Func::PartialApp1(..) => None,
            Func::PartialApp2(..) => None,
            Func::PartialAppLast(..) => None,
            Func::Composition(..) => None,
            Func::OnComposition(..) => None,
            Func::Parallel(_) => None,
            Func::Fanout(_) => None,
            Func::Flip(..) => None,
            Func::ListSection(_) => None,
            Func::ChainSection(..) => None,
            Func::CallSection(..) => None,
            Func::IndexSection(..) => None,
            Func::SliceSection(..) => None,
            Func::Type(_) => None,
            Func::StructField(..) => None,
            Func::Memoized(..) => None,
        }
    }
}

impl Display for Func {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Func::Builtin(b) => write!(formatter, "Builtin({})", b.builtin_name()),
            Func::Closure(_) => write!(formatter, "Closure"),
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
            Func::ChainSection(xs, ys) => {
                write!(formatter, "ChainSection({}", FmtSectionBoxedSlot(xs))?;
                for (_loc, func, _prec, operand) in ys {
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
            Func::Memoized(..) => write!(formatter, "<memoized>"),
        }
    }
}

pub trait Builtin: Debug {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj>;

    // Used for builtins to identify each other, since comparing pointers is bad (?)
    // https://rust-lang.github.io/rust-clippy/master/#vtable_address_comparisons
    fn builtin_name(&self) -> &str;

    fn try_chain(&self, _other: &Func) -> Option<Func> {
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

// can "destructure"
#[derive(Debug, Clone)]
struct Plus;

impl Builtin for Plus {
    // copypasta
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg @ (Obj::Num(_) | Obj::Seq(Seq::Vector(_)))) => {
                Ok(clone_and_part_app_2(self, arg))
            }
            Few2::One(a) => Err(NErr::argument_error(format!(
                "+ only accepts numbers (or vectors), got {}",
                a
            ))),
            Few2::Two(a, b) => err_add_name(
                expect_nums_and_vectorize_2(|a, b| Ok(Obj::Num(a + b)), a, b),
                "+",
            ),
            f => Err(NErr::argument_error(format!(
                "+ only accepts two numbers, got {}",
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        "+"
    }

    // Haskell deprecated NPlusKPatterns for a good reason but we don't care about good reason over
    // here
    fn destructure(&self, rvalue: Obj, lhs: Vec<Option<Obj>>) -> NRes<Vec<Obj>> {
        match (rvalue, few2(lhs)) {
            (Obj::Num(r), Few2::Two(Some(Obj::Num(a)), None)) => {
                let diff = r - &a;
                if diff >= NNum::from(0) {
                    Ok(vec![Obj::Num(a), Obj::Num(diff)])
                } else {
                    Err(NErr::value_error("+ computed negative".to_string()))
                }
            }
            (Obj::Num(r), Few2::Two(None, Some(Obj::Num(a)))) => {
                let diff = r - &a;
                if diff >= NNum::from(0) {
                    Ok(vec![Obj::Num(diff), Obj::Num(a)])
                } else {
                    Err(NErr::value_error("+ computed negative".to_string()))
                }
            }
            _ => Err(NErr::type_error("+ failed to destructure".to_string())),
        }
    }
}

// can "destructure" (mainly to support casing by negative literals)
#[derive(Debug, Clone)]
struct Minus;

impl Builtin for Minus {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::Zero => Err(NErr::argument_error("received 0 args".to_string())),
            Few2::One(s) => expect_nums_and_vectorize_1(|x| Ok(Obj::Num(-x)), s),
            Few2::Two(a, b) => expect_nums_and_vectorize_2(|a, b| Ok(Obj::Num(a - b)), a, b),
            Few2::Many(_) => Err(NErr::argument_error("received >2 args".to_string())),
        }
    }

    fn builtin_name(&self) -> &str {
        "-"
    }

    fn destructure(&self, rvalue: Obj, lhs: Vec<Option<Obj>>) -> NRes<Vec<Obj>> {
        if lhs.len() == 1 {
            Ok(vec![expect_nums_and_vectorize_1(
                |x| Ok(Obj::Num(-x)),
                rvalue,
            )?])
        } else {
            Err(NErr::type_error(
                "- can only destructure 1 (for now)".to_string(),
            ))
        }
    }
}

// thonk
#[derive(Debug, Clone)]
struct Times;

impl Builtin for Times {
    // copypasta
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg @ (Obj::Num(_) | Obj::Seq(Seq::Vector(_)))) => {
                Ok(clone_and_part_app_2(self, arg))
            }
            Few2::One(a) => Err(NErr::argument_error(format!(
                "* only accepts numbers (or vectors), got {}",
                a
            ))),
            Few2::Two(a, b) => err_add_name(
                expect_nums_and_vectorize_2(|a, b| Ok(Obj::Num(a * b)), a, b),
                "*",
            ),
            f => Err(NErr::argument_error(format!(
                "* only accepts two numbers, got {}",
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        "*"
    }

    // even worse than NPlusKPatterns maybe (TODO there's like paired divmod stuff right)
    fn destructure(&self, rvalue: Obj, lhs: Vec<Option<Obj>>) -> NRes<Vec<Obj>> {
        match (rvalue, few2(lhs)) {
            (Obj::Num(r), Few2::Two(Some(Obj::Num(a)), None)) => {
                if (&r % &a).is_nonzero() {
                    Err(NErr::value_error("* had remainder".to_string()))
                } else {
                    let k = Obj::Num(r.div_floor(&a));
                    Ok(vec![Obj::Num(a), k])
                }
            }
            (Obj::Num(r), Few2::Two(None, Some(Obj::Num(a)))) => {
                if (&r % &a).is_nonzero() {
                    Err(NErr::value_error("* had remainder".to_string()))
                } else {
                    let k = Obj::Num(r.div_floor(&a));
                    Ok(vec![k, Obj::Num(a)])
                }
            }
            _ => Err(NErr::type_error("* failed to destructure".to_string())),
        }
    }
}

// thonk
#[derive(Debug, Clone)]
struct Divide;

impl Builtin for Divide {
    // copypasta
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg @ (Obj::Num(_) | Obj::Seq(Seq::Vector(_)))) => {
                Ok(clone_and_part_app_2(self, arg))
            }
            Few2::One(a) => Err(NErr::argument_error(format!(
                "/ only accepts numbers (or vectors), got {}",
                a
            ))),
            Few2::Two(a, b) => err_add_name(
                expect_nums_and_vectorize_2(|a, b| Ok(Obj::Num(a / b)), a, b),
                "/",
            ),
            f => Err(NErr::argument_error(format!(
                "/ only accepts two numbers, got {}",
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        "/"
    }

    // this one actually makes sense now???
    fn destructure(&self, rvalue: Obj, _lhs: Vec<Option<Obj>>) -> NRes<Vec<Obj>> {
        match rvalue {
            Obj::Num(r) => match r.to_rational() {
                Some(r) => Ok(vec![
                    Obj::from(r.numer().clone()),
                    Obj::from(r.denom().clone()),
                ]),
                None => Err(NErr::value_error("/ destructured non-rational".to_string())),
            },
            _ => Err(NErr::type_error("/ failed to destructure".to_string())),
        }
    }
}

#[derive(Clone)]
struct ComparisonOperator {
    name: String, // will be "illegal" for chained operators
    chained: Vec<Func>,
    accept: fn(&Obj, &Obj) -> NRes<bool>,
}
impl Debug for ComparisonOperator {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            fmt,
            concat!(
                stringify!($name),
                " {{ name: {:?}, chained: {:?}, accept: {:?} }}"
            ),
            self.name, self.chained, self.accept as usize
        )
    }
}

impl ComparisonOperator {
    fn of(name: &str, accept: fn(&Obj, &Obj) -> NRes<bool>) -> ComparisonOperator {
        ComparisonOperator {
            name: name.to_string(),
            chained: Vec::new(),
            accept,
        }
    }
}

fn ncmp(aa: &Obj, bb: &Obj) -> NRes<Ordering> {
    match (aa, bb) {
        (Obj::Num(a), Obj::Num(b)) => a.partial_cmp(b).ok_or(NErr::type_error(format!(
            "Can't compare nums {:?} and {:?}",
            a, b
        ))),
        (Obj::Seq(a), Obj::Seq(b)) => a.partial_cmp(b).ok_or(NErr::type_error(format!(
            "Can't compare seqs {:?} and {:?}",
            a, b
        ))),
        _ => Err(NErr::type_error(format!(
            "Can't compare {:?} and {:?}",
            aa, bb
        ))),
    }
}

fn clone_and_part_app_2(f: &(impl Builtin + Clone + 'static), arg: Obj) -> Obj {
    Obj::Func(
        Func::PartialApp2(Box::new(Func::Builtin(Rc::new(f.clone()))), Box::new(arg)),
        Precedence::zero(),
    )
}

fn clone_and_part_app_last(f: &(impl Builtin + Clone + 'static), arg: Obj) -> Obj {
    Obj::Func(
        Func::PartialAppLast(Box::new(Func::Builtin(Rc::new(f.clone()))), Box::new(arg)),
        Precedence::zero(),
    )
}

impl Builtin for ComparisonOperator {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        if self.chained.is_empty() {
            match few(args) {
                Few::Zero => Err(NErr::argument_error(format!(
                    "Comparison operator {:?} needs 2+ args",
                    self.name
                ))),
                Few::One(arg) => Ok(clone_and_part_app_2(self, arg)),
                Few::Many(args) => {
                    for i in 0..args.len() - 1 {
                        if !(self.accept)(&args[i], &args[i + 1])? {
                            return Ok(Obj::from(false));
                        }
                    }
                    Ok(Obj::from(true))
                }
            }
        } else {
            if self.chained.len() + 2 == args.len() {
                if !(self.accept)(&args[0], &args[1])? {
                    return Ok(Obj::from(false));
                }
                for i in 0..self.chained.len() {
                    let res =
                        self.chained[i].run(env, vec![args[i + 1].clone(), args[i + 2].clone()])?;
                    if !res.truthy() {
                        return Ok(res);
                    }
                }
                Ok(Obj::from(true))
            } else {
                Err(NErr::argument_error(format!(
                    "Chained comparison operator got the wrong number of args"
                )))
            }
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                other_name @ ("==" | "!=" | "<" | ">" | "<=" | ">=") => {
                    Some(Func::Builtin(Rc::new(ComparisonOperator {
                        name: format!("{},{}", self.name, other_name),
                        chained: {
                            let mut k = self.chained.clone();
                            k.push(Func::clone(other));
                            k
                        },
                        accept: self.accept,
                    })))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn destructure(&self, rvalue: Obj, lhs: Vec<Option<Obj>>) -> NRes<Vec<Obj>> {
        if self.chained.len() + 2 != lhs.len() {
            Err(NErr::argument_error(format!(
                "Chained comparison operator destructuring got the wrong number of args"
            )))?
        }

        // Just copy rvalue into slots
        // then run the comparison
        let slots = lhs.iter().filter(|x| x.is_none()).count();
        if slots == 0 {
            Err(NErr::argument_error(format!(
                "Chained comparison operator destructuring: all literals??"
            )))?
        }
        let rvalues = if slots == 1 {
            vec![rvalue]
        } else {
            obj_to_cloning_iter(&rvalue, "comparison unpacking")?.collect::<Vec<Obj>>()
        };
        let mut ret = Vec::new();
        let mut riter = rvalues.into_iter();
        for x in lhs {
            match x {
                None => match riter.next() {
                    Some(t) => ret.push(t),
                    None => Err(NErr::argument_error(format!(
                        "Chained comparison operator ran out of ok rvalues"
                    )))?,
                },
                Some(x) => ret.push(x.clone()),
            }
        }
        if riter.next().is_some() {
            Err(NErr::argument_error(format!(
                "Chained comparison operator too many rvalues"
            )))?
        }

        // FIXME because we only chain with comparison operators we should be able to do stuff but
        // it's hard/annoying
        if self
            .run(&Rc::new(RefCell::new(Env::empty())), ret.clone())?
            .truthy()
        {
            Ok(ret)
        } else {
            Err(NErr::value_error(
                "comparison destructure failed".to_string(),
            ))
        }
    }
}

// min or max. conditional partial application
#[derive(Debug, Clone)]
struct Extremum {
    name: String,
    bias: Ordering,
}
impl Builtin for Extremum {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::Zero => Err(NErr::type_error(format!("{}: at least 1 arg", self.name))),
            Few::One(Obj::Seq(mut s)) => {
                let mut ret: Option<Obj> = None;
                for b in mut_seq_into_iter(&mut s) {
                    if match &ret {
                        None => true,
                        Some(r) => ncmp(&b, r)? == self.bias,
                    } {
                        ret = Some(b)
                    }
                }
                Ok(ret
                    .ok_or(NErr::empty_error(format!("{}: empty", self.name)))?
                    .clone())
            }
            Few::One(a) => Ok(clone_and_part_app_last(self, a)),
            Few::Many(mut t) => {
                let mut i_func = None;
                for (i, e) in t.iter().enumerate() {
                    match (&e, &i_func) {
                        (Obj::Func(f, _), None) => i_func = Some((i, f.clone())),
                        (Obj::Func(..), Some(_)) => {
                            return Err(NErr::argument_error(format!(
                                "{}: two functions",
                                self.name
                            )))
                        }
                        _ => {}
                    }
                }
                match i_func {
                    Some((i, _)) => {
                        t.remove(i);
                    }
                    None => {}
                }
                match (i_func, few(t)) {
                    (None, Few::One(mut a)) => {
                        let mut ret: Option<Obj> = None;
                        for b in mut_obj_into_iter(&mut a, &self.name)? {
                            if match &ret {
                                None => true,
                                Some(r) => ncmp(&b, r)? == self.bias,
                            } {
                                ret = Some(b)
                            }
                        }
                        Ok(ret
                            .ok_or(NErr::empty_error(format!("{}: empty", self.name)))?
                            .clone())
                    }
                    (None, Few::Many(a)) => {
                        let mut ret: Option<Obj> = None;
                        for b in a {
                            if match &ret {
                                None => true,
                                Some(r) => ncmp(&b, r)? == self.bias,
                            } {
                                ret = Some(b)
                            }
                        }
                        Ok(ret
                            .ok_or(NErr::empty_error(format!("{}: empty", self.name)))?
                            .clone())
                    }
                    (Some((_, f)), Few::One(mut a)) => {
                        let mut ret: Option<Obj> = None;
                        for b in mut_obj_into_iter(&mut a, &self.name)? {
                            if match &ret {
                                None => true,
                                Some(r) => {
                                    ncmp(&f.run(env, vec![b.clone(), r.clone()])?, &Obj::zero())?
                                        == self.bias
                                }
                            } {
                                ret = Some(b)
                            }
                        }
                        Ok(ret
                            .ok_or(NErr::empty_error(format!("{}: empty", self.name)))?
                            .clone())
                    }
                    (Some((_, f)), Few::Many(a)) => {
                        let mut ret: Option<Obj> = None;
                        for b in a {
                            if match &ret {
                                None => true,
                                Some(r) => {
                                    ncmp(&f.run(env, vec![b.clone(), r.clone()])?, &Obj::zero())?
                                        == self.bias
                                }
                            } {
                                ret = Some(b)
                            }
                        }
                        Ok(ret
                            .ok_or(NErr::empty_error(format!("{}: empty", self.name)))?
                            .clone())
                    }
                    _ => Err(NErr::empty_error(format!("{}: empty", self.name))),
                }
            }
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }

    fn try_chain(&self, _other: &Func) -> Option<Func> {
        None
    }
}

#[derive(Debug, Clone)]
struct TilBuiltin;

impl Builtin for TilBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few3::Two(Obj::Num(a), Obj::Num(b)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                Ok(Obj::Seq(Seq::Stream(Rc::new(Range(
                    n1,
                    Some(n2),
                    BigInt::from(1),
                )))))
            }
            Few3::Three(Obj::Num(a), Obj::Num(b), Obj::Num(c)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                let n3 = into_bigint_ok(c)?;
                Ok(Obj::Seq(Seq::Stream(Rc::new(Range(n1, Some(n2), n3)))))
            }
            _ => Err(NErr::argument_error(format!("Bad args for til"))),
        }
    }

    fn builtin_name(&self) -> &str {
        "til"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "by" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
struct ToBuiltin;

impl Builtin for ToBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few3::Two(Obj::Num(a), Obj::Num(b)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                Ok(Obj::Seq(Seq::Stream(Rc::new(Range(
                    n1,
                    Some(n2 + 1usize),
                    BigInt::from(1),
                )))))
            }
            Few3::Two(a, Obj::Func(Func::Type(t), _)) => call_type(&t, vec![a]), // sugar lmao
            Few3::Three(Obj::Num(a), Obj::Num(b), Obj::Num(c)) => {
                let n1 = into_bigint_ok(a)?;
                let n2 = into_bigint_ok(b)?;
                let n3 = into_bigint_ok(c)?;
                Ok(Obj::Seq(Seq::Stream(Rc::new(Range(
                    n1,
                    Some(if n3.is_negative() {
                        n2 - 1usize
                    } else {
                        n2 + 1usize
                    }),
                    n3,
                )))))
            }
            _ => Err(NErr::argument_error(format!("Bad args for to"))),
        }
    }

    fn builtin_name(&self) -> &str {
        "to"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "by" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// self-chainable
#[derive(Debug, Clone)]
struct Zip;

impl Builtin for Zip {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::Zero => Err(NErr::argument_error("zip: no args".to_string())),
            Few::One(a) => Ok(clone_and_part_app_last(self, a)),
            Few::Many(mut args) => {
                let mut func = None;
                // I can't believe this works (type annotation for me not the compiler)
                let mut iterators: Vec<MutObjIntoIter<'_>> = Vec::new();
                for arg in args.iter_mut() {
                    match (arg, &mut func) {
                        (Obj::Func(f, _), None) => {
                            func = Some(f.clone());
                        }
                        (Obj::Func(..), Some(_)) => Err(NErr::argument_error(
                            "zip: more than one function".to_string(),
                        ))?,
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

    fn builtin_name(&self) -> &str {
        "zip"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "zip" | "with" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// self-chainable
#[derive(Debug, Clone)]
struct ZipLongest;

impl Builtin for ZipLongest {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::Zero => Err(NErr::argument_error("ziplongest: no args".to_string())),
            Few::One(a) => Ok(clone_and_part_app_last(self, a)),
            Few::Many(mut args) => {
                let mut func = None;
                // I can't believe this works (type annotation for me not the compiler)
                let mut iterators: Vec<MutObjIntoIter<'_>> = Vec::new();
                for arg in args.iter_mut() {
                    match (arg, &mut func) {
                        (Obj::Func(f, _), None) => {
                            func = Some(f.clone());
                        }
                        (Obj::Func(..), Some(_)) => Err(NErr::argument_error(
                            "ziplongest: more than one function".to_string(),
                        ))?,
                        (arg, _) => iterators.push(mut_obj_into_iter(arg, "ziplongest")?),
                    }
                }
                if iterators.is_empty() {
                    Err(NErr::argument_error(
                        "ziplongest: zero iterables".to_string(),
                    ))?
                }
                let mut ret = Vec::new();
                loop {
                    let mut batch = iterators.iter_mut().flat_map(|a| a.next());
                    match batch.next() {
                        None => return Ok(Obj::list(ret)),
                        Some(mut x) => match &func {
                            Some(f) => {
                                for y in batch {
                                    x = f.run(env, vec![x, y])?;
                                }
                                ret.push(x)
                            }
                            None => {
                                let mut v = vec![x];
                                v.extend(batch);
                                ret.push(Obj::list(v))
                            }
                        },
                    }
                }
            }
        }
    }

    fn builtin_name(&self) -> &str {
        "ziplongest"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "ziplongest" | "with" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// self-chainable
#[derive(Debug, Clone)]
struct CartesianProduct;

// surprisingly rare function where we really can't consume the iterators
fn cartesian_foreach(
    acc: &mut Vec<Obj>,
    seqs: &[Seq],
    f: &mut impl FnMut(&Vec<Obj>) -> NRes<()>,
) -> NRes<()> {
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
                            Some(_) => Err(NErr::argument_error(
                                "cartesian product: more than one integer (^ is exponentiation)"
                                    .to_string(),
                            ))?,
                        },
                        _ => Err(NErr::argument_error(
                            "cartesian product: non-sequence non-integer".to_string(),
                        ))?,
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
                    _ => Err(NErr::argument_error(
                        "cartesian product: bad combo of scalars and sequences".to_string(),
                    ))?,
                }
            }
        }
    }

    fn builtin_name(&self) -> &str {
        "**"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "**" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// takes an optional starting value
#[derive(Debug, Clone)]
struct Fold;

impl Builtin for Fold {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
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
                    },
                    _ => Err(NErr::type_error("fold: not callable".to_string())),
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
                    _ => Err(NErr::type_error("fold: not callable".to_string())),
                }
            }
            Few3::Many(_) => Err(NErr::argument_error("fold: too many args".to_string())),
        }
    }

    fn builtin_name(&self) -> &str {
        "fold"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "from" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// takes an optional starting value
#[derive(Debug, Clone)]
struct Scan;

impl Builtin for Scan {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::Zero => Err(NErr::argument_error("scan: no args".to_string())),
            Few3::One(arg) => Ok(clone_and_part_app_2(self, arg)),
            Few3::Two(mut s, f) => {
                let mut it = mut_obj_into_iter(&mut s, "scan")?;
                match f {
                    Obj::Func(f, _) => match it.next() {
                        Some(mut cur) => {
                            let mut acc = vec![cur.clone()];
                            for e in it {
                                cur = f.run(env, vec![cur, e])?;
                                acc.push(cur.clone());
                            }
                            Ok(Obj::list(acc))
                        }
                        None => Ok(Obj::list(Vec::new())),
                    },
                    _ => Err(NErr::type_error("fold: not callable".to_string())),
                }
            }
            Few3::Three(mut s, f, mut cur) => {
                let it = mut_obj_into_iter(&mut s, "scan")?;
                match f {
                    Obj::Func(f, _) => {
                        let mut acc = vec![cur.clone()];
                        for e in it {
                            cur = f.run(env, vec![cur, e])?;
                            acc.push(cur.clone());
                        }
                        Ok(Obj::list(acc))
                    }
                    _ => Err(NErr::type_error("fold: not callable".to_string())),
                }
            }
            Few3::Many(_) => Err(NErr::argument_error("fold: too many args".to_string())),
        }
    }

    fn builtin_name(&self) -> &str {
        "scan"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "from" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// self-chainable
#[derive(Debug, Clone)]
struct Merge;

impl Builtin for Merge {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::Zero => Err(NErr::argument_error("merge: no args".to_string())),
            Few::One(a) => Ok(clone_and_part_app_last(self, a)),
            Few::Many(args) => {
                let mut func = None;
                let mut dicts: Vec<Rc<HashMap<ObjKey, Obj>>> = Vec::new();
                let mut first_def = None;
                for arg in args {
                    match (arg, &mut func) {
                        (Obj::Func(f, _), None) => {
                            func = Some(f);
                        }
                        (Obj::Func(..), Some(_)) => Err(NErr::argument_error(
                            "merge: more than one function".to_string(),
                        ))?,
                        (Obj::Seq(Seq::Dict(d, def)), _) => {
                            dicts.push(d);
                            if first_def == None {
                                first_def = Some(def)
                            }
                        }
                        _ => {
                            return Err(NErr::argument_error(
                                "merge: neither func nor dict".to_string(),
                            ))
                        }
                    }
                }
                let mut ret = HashMap::<ObjKey, Obj>::new();
                for dict in dicts {
                    let dict = unwrap_or_clone(dict);
                    for (k, v) in dict {
                        match ret.entry(k) {
                            std::collections::hash_map::Entry::Vacant(e) => {
                                e.insert(v);
                            }
                            std::collections::hash_map::Entry::Occupied(mut e) => match &func {
                                None => *e.get_mut() = v,
                                Some(f) => {
                                    let slot = e.get_mut();
                                    *slot = f.run(env, vec![std::mem::take(slot), v])?;
                                }
                            },
                        }
                    }
                }
                Ok(Obj::Seq(Seq::Dict(Rc::new(ret), first_def.flatten())))
            }
        }
    }

    fn builtin_name(&self) -> &str {
        "merge"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "merge" | "with" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

fn captures_to_obj(regex: &Regex, captures: &regex::Captures<'_>) -> Obj {
    if regex.capture_locations().len() == 1 {
        Obj::from(captures.get(0).unwrap().as_str())
    } else {
        Obj::list(
            captures
                .iter()
                .map(|cap| match cap {
                    None => Obj::Null, // didn't participate
                    Some(s) => Obj::from(s.as_str()),
                })
                .collect(),
        )
    }
}

// it's just "with" lmao
#[derive(Debug, Clone)]
struct Replace;

impl Builtin for Replace {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::Three(
                Obj::Seq(Seq::String(a)),
                Obj::Seq(Seq::String(b)),
                Obj::Seq(Seq::String(c)),
            ) => {
                // rust's replacement syntax is $n or ${n} for nth group
                let r = Regex::new(&b)
                    .map_err(|e| NErr::value_error(format!("replace: invalid regex: {}", e)))?;
                Ok(Obj::from(r.replace_all(&a, &*c).into_owned()))
            }
            Few3::Three(
                Obj::Seq(Seq::String(a)),
                Obj::Seq(Seq::String(b)),
                Obj::Func(f, _prec),
            ) => {
                let r = Regex::new(&b)
                    .map_err(|e| NErr::value_error(format!("replace: invalid regex: {}", e)))?;
                let mut status = Ok(());
                let res = Obj::from(
                    r.replace_all(&a, |caps: &regex::Captures<'_>| {
                        if status.is_err() {
                            return String::new();
                        }
                        match f.run(env, vec![captures_to_obj(&r, caps)]) {
                            Ok(s) => format!("{}", s),
                            Err(e) => {
                                status = Err(e);
                                String::new()
                            }
                        }
                    })
                    .into_owned(),
                );
                status?;
                Ok(res)
            }
            _ => Err(NErr::type_error(
                "replace: must get three strings".to_string(),
            )),
        }
    }

    fn builtin_name(&self) -> &str {
        "replace"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "with" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// self-chainable
#[derive(Debug, Clone)]
struct Parallel;

impl Builtin for Parallel {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        let mut res = Vec::new();
        for arg in args {
            match arg {
                Obj::Func(f, _) => res.push(f),
                _ => return Err(NErr::type_error("parallel: functions only".to_string())),
            }
        }
        Ok(Obj::Func(Func::Parallel(res), Precedence::zero()))
    }

    fn builtin_name(&self) -> &str {
        "***"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "***" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// self-chainable
#[derive(Debug, Clone)]
struct Fanout;

impl Builtin for Fanout {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        let mut res = Vec::new();
        for arg in args {
            match arg {
                Obj::Func(f, _) => res.push(f),
                _ => return Err(NErr::type_error("fanout: functions only".to_string())),
            }
        }
        Ok(Obj::Func(Func::Fanout(res), Precedence::zero()))
    }

    fn builtin_name(&self) -> &str {
        "&&&"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "&&&" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// not actually chainable, but conditional partial application, and also I want aliases
#[derive(Debug, Clone)]
pub struct Group;

impl Builtin for Group {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(Obj::Seq(s)) => Ok(Obj::list(multi_group_by_eq(s)?)),
            Few2::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few2::Two(Obj::Seq(s), Obj::Num(n)) => match to_usize_ok(&n)? {
                0 => Err(NErr::value_error("can't group into 0".to_string())),
                n => Ok(Obj::list(multi_group(s, n)?)),
            },
            Few2::Two(Obj::Seq(s), Obj::Func(f, _)) => Ok(Obj::list(multi_group_by(env, f, s)?)),
            _ => Err(NErr::type_error("not number or func".to_string())),
        }
    }

    fn builtin_name(&self) -> &str {
        "group"
    }
}

// conditional partial application, and also I want aliases
#[derive(Debug, Clone)]
pub struct Sort;

impl Builtin for Sort {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(Obj::Seq(s)) => Ok(Obj::Seq(multi_sort(s)?)),
            Few2::One(f @ Obj::Func(..)) => Ok(clone_and_part_app_2(self, f)),
            Few2::Two(Obj::Seq(s), Obj::Func(f, _)) => Ok(Obj::Seq(multi_sort_by(env, f, s)?)),
            _ => Err(NErr::type_error("sort: not number or func".to_string())),
        }
    }

    fn builtin_name(&self) -> &str {
        "sort"
    }
}

#[derive(Debug, Clone)]
pub struct Preposition(String);

impl Builtin for Preposition {
    fn run(&self, _env: &REnv, _: Vec<Obj>) -> NRes<Obj> {
        Err(NErr::type_error(format!("{}: cannot call", self.0)))
    }

    fn builtin_name(&self) -> &str {
        &self.0
    }
}

#[derive(Clone)]
pub struct BasicBuiltin {
    name: String,
    body: fn(env: &REnv, args: Vec<Obj>) -> NRes<Obj>,
}

// https://github.com/rust-lang/rust/issues/45048
macro_rules! standard_three_part_debug {
    ($name:ident) => {
        impl Debug for $name {
            fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                write!(
                    fmt,
                    concat!(stringify!($name), " {{ name: {:?}, body: {:?} }}"),
                    self.name, self.body as usize
                )
            }
        }
    };
}
standard_three_part_debug!(BasicBuiltin);

impl Builtin for BasicBuiltin {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        err_add_name((self.body)(env, args), &self.name)
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug, Clone)]
pub struct OneArgBuiltin {
    name: String,
    body: fn(a: Obj) -> NRes<Obj>,
}

impl Builtin for OneArgBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(arg) => {
                let ty = type_of(&arg);
                err_add_name((self.body)(arg), &format!("{}({})", self.name, ty.name()))
            }
            f => Err(NErr::argument_error(format!(
                "{} only accepts one argument, got {}",
                self.name,
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug, Clone)]
pub struct TwoArgBuiltin {
    name: String,
    body: fn(a: Obj, b: Obj) -> NRes<Obj>,
}

impl Builtin for TwoArgBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg) => Ok(clone_and_part_app_2(self, arg)),
            Few2::Two(a, b) => err_add_name((self.body)(a, b), &self.name),
            f => Err(NErr::argument_error(format!(
                "{} only accepts two arguments (or one for partial application), got {}",
                self.name,
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug, Clone)]
pub struct OneNumBuiltin {
    name: String,
    body: fn(a: NNum) -> NRes<Obj>,
}

#[derive(Clone)]
pub struct EnvOneArgBuiltin {
    name: String,
    body: fn(env: &REnv, a: Obj) -> NRes<Obj>,
}
standard_three_part_debug!(EnvOneArgBuiltin);

impl Builtin for EnvOneArgBuiltin {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(arg) => err_add_name((self.body)(env, arg), &self.name),
            f => Err(NErr::argument_error(format!(
                "{} only accepts one argument, got {}",
                self.name,
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

#[derive(Clone)]
pub struct EnvTwoArgBuiltin {
    name: String,
    body: fn(env: &REnv, a: Obj, b: Obj) -> NRes<Obj>,
}
standard_three_part_debug!(EnvTwoArgBuiltin);

impl Builtin for EnvTwoArgBuiltin {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg) => Ok(clone_and_part_app_2(self, arg)),
            Few2::Two(a, b) => err_add_name((self.body)(env, a, b), &self.name),
            f => Err(NErr::argument_error(format!(
                "{} only accepts two arguments (or one for partial application), got {}",
                self.name,
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

fn to_nnum(obj: Obj, reason: &'static str) -> NRes<NNum> {
    match obj {
        Obj::Num(n) => Ok(n),
        x => Err(NErr::type_error(format!(
            "{}: non-number: {}",
            reason,
            FmtObj::debug(&x)
        ))),
    }
}

fn to_byte(obj: Obj, reason: &'static str) -> NRes<u8> {
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

fn to_obj_vector(iter: impl Iterator<Item = NRes<Obj>>) -> NRes<Obj> {
    Ok(Obj::Seq(Seq::Vector(Rc::new(
        iter.map(|e| to_nnum(e?, "can't convert to vector"))
            .collect::<NRes<Vec<NNum>>>()?,
    ))))
}

fn expect_nums_and_vectorize_1(body: fn(NNum) -> NRes<Obj>, a: Obj) -> NRes<Obj> {
    match a {
        Obj::Num(a) => body(a),
        Obj::Seq(Seq::Vector(mut a)) => to_obj_vector(RcVecIter::of(&mut a).map(body)),
        x => Err(NErr::argument_error(format!(
            "only accepts numbers, got {:?}",
            x
        ))),
    }
}

impl Builtin for OneNumBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(x) => err_add_name(expect_nums_and_vectorize_1(self.body, x), &self.name),
            f => Err(NErr::argument_error(format!(
                "{} only accepts one argument, got {}",
                self.name,
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug, Clone)]
pub struct NumsBuiltin {
    name: String,
    body: fn(args: Vec<NNum>) -> NRes<Obj>,
}

impl Builtin for NumsBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        err_add_name(
            (self.body)(
                args.into_iter()
                    .map(|x| match x {
                        Obj::Num(n) => Ok(n),
                        _ => Err(NErr::argument_error(format!(
                            "only accepts numbers, got {:?}",
                            x
                        ))),
                    })
                    .collect::<NRes<Vec<NNum>>>()?,
            ),
            &self.name,
        )
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug, Clone)]
pub struct TwoNumsBuiltin {
    name: String,
    body: fn(a: NNum, b: NNum) -> NRes<Obj>,
}

fn expect_nums_and_vectorize_2(body: fn(NNum, NNum) -> NRes<Obj>, a: Obj, b: Obj) -> NRes<Obj> {
    match (a, b) {
        (Obj::Num(a), Obj::Num(b)) => body(a, b),
        (Obj::Num(a), Obj::Seq(Seq::Vector(mut b))) => {
            to_obj_vector(RcVecIter::of(&mut b).map(|e| body(a.clone(), e)))
        }
        (Obj::Seq(Seq::Vector(mut a)), Obj::Num(b)) => {
            to_obj_vector(RcVecIter::of(&mut a).map(|e| body(e, b.clone())))
        }
        (Obj::Seq(Seq::Vector(mut a)), Obj::Seq(Seq::Vector(mut b))) => {
            if a.len() == b.len() {
                to_obj_vector(
                    RcVecIter::of(&mut a)
                        .zip(RcVecIter::of(&mut b))
                        .map(|(a, b)| body(a, b)),
                )
            } else {
                Err(NErr::value_error(format!(
                    "vectorized op: different lengths: {}, {}",
                    a.len(),
                    b.len()
                )))
            }
        }
        (a, b) => Err(NErr::argument_error(format!(
            "only accepts numbers (or vectors), got {}, {}",
            a, b
        ))),
    }
}

impl Builtin for TwoNumsBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            // partial application, spicy
            Few2::One(arg @ (Obj::Num(_) | Obj::Seq(Seq::Vector(_)))) => {
                Ok(clone_and_part_app_2(self, arg))
            }
            Few2::One(a) => Err(NErr::argument_error(format!(
                "{} only accepts numbers (or vectors), got {}",
                self.name, a
            ))),
            Few2::Two(a, b) => {
                err_add_name(expect_nums_and_vectorize_2(self.body, a, b), &self.name)
            }
            f => Err(NErr::argument_error(format!(
                "{} only accepts two numbers, got {}",
                self.name,
                f.len()
            ))),
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

#[derive(Clone)]
pub struct Closure {
    params: Rc<Vec<Box<Lvalue>>>,
    body: Rc<LocExpr>,
    env: Rc<RefCell<Env>>,
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

impl Closure {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        let ee = Env::with_parent(&self.env);
        let p = self
            .params
            .iter()
            .map(|e| Ok(Box::new(eval_lvalue(&ee, e)?)))
            .collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?;
        add_trace(
            assign_all(
                &ee,
                &p,
                Some(&ObjType::Any),
                args.len(),
                || args,
                AssignMode::Assign,
                "Wrong number of arguments",
            ),
            "argument receiving".to_string(),
            self.body.0,
        )?;
        match evaluate(&ee, &self.body) {
            Err(NErr::Return(k)) => Ok(k),
            x => add_trace(x, "closure call".to_string(), self.body.0),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Invalid(String),
    IntLit(BigInt),
    RatLit(BigRational),
    FloatLit(f64),
    ImaginaryFloatLit(f64),
    StringLit(Rc<String>),
    BytesLit(Rc<Vec<u8>>),
    FormatString(Rc<String>),
    Ident(String),
    LeftParen,
    VLeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    Null,
    And,
    Or,
    Coalesce,
    While,
    For,
    Yield,
    If,
    Else,
    Switch,
    Case,
    Try,
    Catch,
    Break,
    Continue,
    Return,
    Throw,
    Bang,
    QuestionMark,
    Colon,
    LeftArrow,
    RightArrow,
    DoubleLeftArrow,
    DoubleColon,
    Semicolon,
    Ellipsis,
    Lambda,
    Comma,
    Assign,
    Consume,
    Pop,
    Remove,
    Swap,
    Every,
    Struct,
    Freeze,
    Literally,
    Underscore,

    // strip me before parsing
    Comment(String),
    // Newline,
}

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
pub enum IndexOrSlice {
    Index(Box<LocExpr>),
    Slice(Option<Box<LocExpr>>, Option<Box<LocExpr>>),
}

#[derive(Debug)]
pub struct LocExpr(CodeLoc, Expr);

#[derive(Debug)]
pub enum Expr {
    Null,
    IntLit(BigInt),
    RatLit(BigRational),
    FloatLit(f64),
    ImaginaryFloatLit(f64),
    StringLit(Rc<String>),
    BytesLit(Rc<Vec<u8>>),
    FormatString(Vec<Result<char, (LocExpr, MyFmtFlags)>>),
    Ident(String),
    Underscore,
    Backref(usize),
    Call(Box<LocExpr>, Vec<Box<LocExpr>>),
    List(Vec<Box<LocExpr>>),
    Dict(
        Option<Box<LocExpr>>,
        Vec<(Box<LocExpr>, Option<Box<LocExpr>>)>,
    ),
    Vector(Vec<Box<LocExpr>>),
    Index(Box<LocExpr>, IndexOrSlice),
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
    For(Vec<ForIteration>, bool /* yield */, Box<LocExpr>),
    While(Box<LocExpr>, Box<LocExpr>),
    Switch(Box<LocExpr>, Vec<(Box<Lvalue>, Box<LocExpr>)>),
    Try(Box<LocExpr>, Box<Lvalue>, Box<LocExpr>),
    Break(Option<Box<LocExpr>>),
    Continue,
    Return(Option<Box<LocExpr>>),
    Throw(Box<LocExpr>),
    Sequence(Vec<Box<LocExpr>>, bool), // semicolon ending to swallow nulls
    Struct(Rc<String>, Vec<Rc<String>>),
    Freeze(Box<LocExpr>),
    // lvalues only
    Literally(Box<LocExpr>),

    // these get cloned in particular
    Lambda(Rc<Vec<Box<Lvalue>>>, Rc<LocExpr>),

    // shouldn't stay in the tree:
    CommaSeq(Vec<Box<LocExpr>>),
    Splat(Box<LocExpr>),
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
        }
    }

    fn collect_identifiers(&self, declared_only: bool) -> HashSet<String> {
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
        }
    }
}

#[derive(Debug)]
enum EvaluatedIndexOrSlice {
    Index(Obj),
    Slice(Option<Obj>, Option<Obj>),
}

#[derive(Debug)]
enum EvaluatedLvalue {
    Underscore,
    IndexedIdent(String, Vec<EvaluatedIndexOrSlice>),
    Annotation(Box<EvaluatedLvalue>, Option<Obj>),
    CommaSeq(Vec<Box<EvaluatedLvalue>>),
    Splat(Box<EvaluatedLvalue>),
    Or(Box<EvaluatedLvalue>, Box<EvaluatedLvalue>),
    Literal(Obj),
    Destructure(Rc<dyn Builtin>, Vec<Box<EvaluatedLvalue>>),
}

impl Display for EvaluatedLvalue {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EvaluatedLvalue::Underscore => write!(formatter, "_"),
            EvaluatedLvalue::IndexedIdent(s, ixs) => {
                write!(formatter, "{}", s)?;
                for ix in ixs {
                    // FIXME
                    write!(formatter, "[{:?}]", ix)?;
                }
                Ok(())
            }
            EvaluatedLvalue::Annotation(s, Some(anno)) => {
                write!(formatter, "{}: {}", s, anno)
            }
            EvaluatedLvalue::Annotation(s, None) => {
                write!(formatter, "({}:)", s)
            }
            EvaluatedLvalue::CommaSeq(vs) => {
                write!(formatter, "(")?;
                for v in vs {
                    write!(formatter, "{},", v)?;
                }
                write!(formatter, ")")
            }
            EvaluatedLvalue::Splat(s) => {
                write!(formatter, "(...{})", s)
            }
            EvaluatedLvalue::Or(a, b) => {
                write!(formatter, "({} or {})", a, b)
            }
            EvaluatedLvalue::Literal(a) => {
                write!(formatter, "literal({})", a)
            }
            EvaluatedLvalue::Destructure(f, vs) => {
                write!(formatter, "{}(", f.builtin_name())?;
                for v in vs {
                    write!(formatter, "{},", v)?;
                }
                write!(formatter, ")")
            }
        }
    }
}

fn to_lvalue(expr: LocExpr) -> Result<Lvalue, ParseError> {
    let loc = expr.0;
    match expr.1 {
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
                loc,
            )),
        },
        Expr::Annotation(e, t) => Ok(Lvalue::Annotation(Box::new(to_lvalue(*e)?), t)),
        Expr::CommaSeq(es) | Expr::List(es) => Ok(Lvalue::CommaSeq(
            es.into_iter()
                .map(|e| Ok(Box::new(to_lvalue(*e)?)))
                .collect::<Result<Vec<Box<Lvalue>>, ParseError>>()?,
        )),
        Expr::Splat(x) => Ok(Lvalue::Splat(Box::new(to_lvalue(*x)?))),
        Expr::IntLit(n) => Ok(Lvalue::Literal(Obj::from(n))),
        Expr::StringLit(n) => Ok(Lvalue::Literal(Obj::Seq(Seq::String(n)))),
        Expr::BytesLit(n) => Ok(Lvalue::Literal(Obj::Seq(Seq::Bytes(n)))),
        Expr::Or(a, b) => Ok(Lvalue::Or(
            Box::new(to_lvalue(*a)?),
            Box::new(to_lvalue(*b)?),
        )),
        Expr::Call(f, args) => Ok(Lvalue::Destructure(
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
        _ => Err(ParseError::expr(format!("can't to_lvalue"), expr.0)),
    }
}

fn to_lvalue_no_literals(expr: LocExpr) -> Result<Lvalue, ParseError> {
    let loc = expr.0;
    let lvalue = to_lvalue(expr)?;
    if lvalue.any_literals() {
        Err(ParseError::expr(
            format!("lvalue can't have any literals"),
            loc,
        ))
    } else {
        Ok(lvalue)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CodeLoc {
    pub line: usize,
    pub col: usize,
    pub index: usize,
}

#[derive(Clone, Debug)]
pub struct LocToken {
    pub token: Token,
    pub start: CodeLoc,
    pub end: CodeLoc,
}

struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    start: CodeLoc,

    // maintained at what chars.next() would give
    cur: CodeLoc,
    tokens: Vec<LocToken>,
}

impl<'a> Lexer<'a> {
    fn new(code: &'a str) -> Self {
        Lexer {
            chars: code.chars().peekable(),
            start: CodeLoc {
                line: 1,
                col: 1,
                index: 0,
            },
            cur: CodeLoc {
                line: 1,
                col: 1,
                index: 0,
            },
            tokens: Vec::new(),
        }
    }

    fn peek(&mut self) -> Option<&char> {
        self.chars.peek()
    }

    fn next(&mut self) -> Option<char> {
        let c = self.chars.next();
        match c {
            Some('\n') => {
                self.cur.line += 1;
                self.cur.col = 1;
                self.cur.index += 1;
            }
            Some(_) => {
                self.cur.col += 1;
                self.cur.index += 1;
            }
            None => {}
        }
        c
    }

    fn emit(&mut self, token: Token) {
        // eprintln!("emitting: {:?} {:?} {:?}", token, self.start, self.cur);
        self.tokens.push(LocToken {
            token,
            start: self.start,
            end: self.cur,
        });
        self.start = self.cur;
    }

    fn emit_but_last(&mut self, token1: Token, token2: Token) {
        let cur_but_last = CodeLoc {
            line: self.cur.line,
            col: self.cur.col - 1,
            index: self.cur.index - 1,
        };
        self.tokens.push(LocToken {
            token: token1,
            start: self.start,
            end: cur_but_last,
        });
        self.tokens.push(LocToken {
            token: token2,
            start: cur_but_last,
            end: self.cur,
        });
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
                    Some(c) => {
                        self.emit(Token::Invalid(format!(
                            "lexing: string literal: unknown escape {}",
                            c
                        )));
                        break;
                    }
                    None => {
                        self.emit(Token::Invalid(format!(
                            "lexing: string literal: escape eof"
                        )));
                        break;
                    }
                },
                Some(c) => acc.push(c),
                None => {
                    self.emit(Token::Invalid(format!("lexing: string literal hit eof")));
                    break;
                }
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

    fn try_emit_imaginary_float(&mut self, acc: String) {
        match acc.parse::<f64>() {
            Ok(f) => self.emit(Token::ImaginaryFloatLit(f)),
            Err(e) => self.emit(Token::Invalid(format!(
                "lexing: invalid imaginary float: {}",
                e
            ))),
        }
    }

    fn try_emit_float(&mut self, acc: String) {
        match acc.parse::<f64>() {
            Ok(f) => self.emit(Token::FloatLit(f)),
            Err(e) => self.emit(Token::Invalid(format!("lexing: invalid float: {}", e))),
        }
    }

    fn lex(&mut self) {
        lazy_static! {
            static ref OPERATOR_SYMBOLS: HashSet<char> = "!$%&*+-./<=>?@^|~×∈∉∋∌∘∧∨≠≤≥⊕⧺"
                .chars()
                .collect::<HashSet<char>>();
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
                ' ' | '\n' => self.start = self.cur,
                '#' => {
                    let mut comment = String::new();
                    match self.next() {
                        None | Some('\n') => {}
                        Some('(') => {
                            let mut depth = 1;
                            loop {
                                match self.next() {
                                    None => {
                                        self.emit(Token::Invalid(
                                            "lexing: runaway range comment".to_string(),
                                        ));
                                        return;
                                    }
                                    Some(c) => {
                                        if c == '(' {
                                            depth += 1;
                                        }
                                        if c == ')' {
                                            depth -= 1;
                                            if depth == 0 {
                                                break;
                                            }
                                        }
                                        comment.push(c);
                                    }
                                }
                            }
                        }
                        Some(c) => {
                            comment.push(c);
                            loop {
                                match self.next() {
                                    None | Some('\n') => break,
                                    Some(c) => comment.push(c),
                                }
                            }
                        }
                    }
                    self.emit(Token::Comment(comment))
                }
                '\'' | '"' => {
                    let s = self.lex_simple_string_after_start(c);
                    self.emit(Token::StringLit(Rc::new(s)))
                }
                '∧' => self.emit(Token::And),
                '∨' => self.emit(Token::Or),
                '?' => self.emit(Token::QuestionMark),
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
                                    self.try_emit_imaginary_float(acc)
                                }
                                Some('e' | 'E') => {
                                    acc.push('e');
                                    self.next();
                                    if self.peek() == Some(&'-') {
                                        acc.push('-');
                                        self.next();
                                    }
                                    while let Some(cc) = self.peek().filter(|d| d.is_digit(10)) {
                                        acc.push(*cc);
                                        self.next();
                                    }
                                    self.try_emit_float(acc)
                                }
                                Some('f' | 'F') => {
                                    self.next();
                                    self.try_emit_float(acc)
                                }
                                _ => self.try_emit_float(acc),
                            }
                        } else {
                            match (acc.as_str(), self.peek()) {
                                ("0", Some('x' | 'X')) => {
                                    self.next();
                                    self.lex_base_and_emit(16)
                                }
                                ("0", Some('b' | 'B')) => {
                                    self.next();
                                    self.lex_base_and_emit(2)
                                }
                                ("0", Some('o' | 'O')) => {
                                    self.next();
                                    self.lex_base_and_emit(8)
                                }
                                (_, Some('r' | 'R')) => {
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
                                        _ => {
                                            self.emit(Token::IntLit(acc.parse::<BigInt>().unwrap()))
                                        }
                                    }
                                }
                                (_, Some('i' | 'I' | 'j' | 'J')) => {
                                    self.next();
                                    self.try_emit_imaginary_float(acc)
                                }
                                (_, Some('q' | 'Q')) => {
                                    self.next();
                                    self.emit(Token::RatLit(BigRational::from(
                                        acc.parse::<BigInt>().unwrap(),
                                    )))
                                }
                                (_, Some('f' | 'F')) => {
                                    self.next();
                                    self.try_emit_float(acc)
                                }
                                (_, Some('e' | 'E')) => {
                                    acc.push('e');
                                    self.next();
                                    if self.peek() == Some(&'-') {
                                        acc.push('-');
                                        self.next();
                                    }
                                    while let Some(cc) = self.peek().filter(|d| d.is_digit(10)) {
                                        acc.push(*cc);
                                        self.next();
                                    }
                                    self.try_emit_float(acc)
                                }
                                _ => self.emit(Token::IntLit(acc.parse::<BigInt>().unwrap())),
                            }
                        }
                    } else if c.is_alphabetic() || c == '_' {
                        let mut acc = c.to_string();

                        while let Some(cc) = self.peek().filter(|c| {
                            c.is_alphanumeric() || **c == '_' || **c == '\'' || **c == '?'
                        }) {
                            if c.is_uppercase() && acc.len() == 1 && *cc == '\'' {
                                // F', R', etc. start strings
                                break;
                            }
                            acc.push(*cc);
                            self.next();
                        }
                        if acc == "B" {
                            match self.next() {
                                Some(delim @ ('\'' | '"')) => {
                                    // TODO this isn't how it works we need to deal with hex
                                    // escapes differently at least
                                    let s = self.lex_simple_string_after_start(delim);
                                    self.emit(Token::BytesLit(Rc::new(s.into_bytes())))
                                }
                                Some('[') => self.emit(Token::Invalid(
                                    "lexing: bytes: literal is TODO".to_string(),
                                )),
                                _ => {
                                    self.emit(Token::Invalid("lexing: bytes: no quote".to_string()))
                                }
                            }
                        } else if acc == "F" {
                            // wow
                            // i guess we lex and parse at evaluation?? idk
                            match self.next() {
                                Some(delim @ ('\'' | '"')) => {
                                    let s = self.lex_simple_string_after_start(delim);
                                    self.emit(Token::FormatString(Rc::new(s)))
                                }
                                _ => self.emit(Token::Invalid(
                                    "lexing: format string: no quote".to_string(),
                                )),
                            }
                        } else if acc == "R" {
                            // wow
                            match self.next() {
                                Some(delim @ ('\'' | '"')) => {
                                    let mut acc = String::new();
                                    while self.peek() != Some(&delim) {
                                        match self.next() {
                                            Some(c) => acc.push(c),
                                            None => {
                                                self.emit(Token::Invalid(
                                                    "lexing: string literal hit eof".to_string(),
                                                ));
                                                break;
                                            }
                                        }
                                    }
                                    self.next();
                                    self.emit(Token::StringLit(Rc::new(acc)))
                                }
                                _ => self.emit(Token::Invalid(
                                    "lexing: raw string literal: no quote".to_string(),
                                )),
                            }
                        } else if acc == "V" {
                            match self.next() {
                                Some('(') => self.emit(Token::VLeftParen),
                                _ => self.emit(Token::Invalid("lexing: V: what".to_string())),
                            }
                        } else {
                            self.emit(match acc.as_str() {
                                "if" => Token::If,
                                "else" => Token::Else,
                                "while" => Token::While,
                                "for" => Token::For,
                                "yield" => Token::Yield,
                                "switch" => Token::Switch,
                                "case" => Token::Case,
                                "null" => Token::Null,
                                "and" => Token::And,
                                "or" => Token::Or,
                                "coalesce" => Token::Coalesce,
                                "break" => Token::Break,
                                "try" => Token::Try,
                                "catch" => Token::Catch,
                                "throw" => Token::Throw,
                                "continue" => Token::Continue,
                                "return" => Token::Return,
                                "consume" => Token::Consume,
                                "pop" => Token::Pop,
                                "remove" => Token::Remove,
                                "swap" => Token::Swap,
                                "every" => Token::Every,
                                "struct" => Token::Struct,
                                "freeze" => Token::Freeze,
                                "literally" => Token::Literally,
                                "_" => Token::Underscore,
                                _ => Token::Ident(acc),
                            })
                        }
                    } else if OPERATOR_SYMBOLS.contains(&c) && c != '?' {
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
                                acc.push(last);
                                self.emit(Token::Ident(acc))
                            }
                            ("", '=') => self.emit(Token::Assign),
                            (_, '=') => {
                                self.emit_but_last(Token::Ident(acc), Token::Assign);
                            }
                            (_, _) => {
                                acc.push(last);
                                self.emit(match acc.as_str() {
                                    "!" => Token::Bang,
                                    "..." => Token::Ellipsis,
                                    "<-" => Token::LeftArrow,
                                    "->" => Token::RightArrow,
                                    "<<-" => Token::DoubleLeftArrow,
                                    _ => Token::Ident(acc),
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

struct Parser {
    tokens: Vec<LocToken>,
    i: usize,
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

#[derive(Debug)]
pub enum ParseErrorLoc {
    Token(LocToken),
    Expr(CodeLoc),
    Eof,
}
#[derive(Debug)]
pub struct ParseError(String, ParseErrorLoc, Vec<(String, CodeLoc)>);
impl ParseError {
    fn token(msg: String, token: LocToken) -> Self {
        ParseError(msg, ParseErrorLoc::Token(token), Vec::new())
    }
    fn expr(msg: String, loc: CodeLoc) -> Self {
        ParseError(msg, ParseErrorLoc::Expr(loc), Vec::new())
    }
    fn eof(msg: String) -> Self {
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
                write_source_error(&mut out, src, &tok.start, Some(&tok.end));
                write!(
                    out,
                    "\n    {:?} (at {}:{}-{})",
                    tok.token, tok.start.line, tok.start.col, tok.end.col
                )
                .ok();
            }
            ParseErrorLoc::Expr(loc) => {
                write_source_error(&mut out, src, &loc, None);
                write!(out, "\n    (expr starting {}:{})", loc.line, loc.col).ok();
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

    fn try_consume(&mut self, desired: &Token) -> bool {
        if self.peek() == Some(desired) {
            self.advance();
            true
        } else {
            false
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
                format!("{:?} (at {}:{}-{})", token, start.line, start.col, end.col)
            }
            None => "EOF".to_string(),
        }
    }

    fn require(&mut self, expected: Token, message: String) -> Result<(), ParseError> {
        if self.try_consume(&expected) {
            // wat
            Ok(())
        } else {
            Err(self.error_here(format!("{}; required {:?}", message, expected)))
        }
    }

    fn atom(&mut self) -> Result<LocExpr, ParseError> {
        if let Some(
            ltref @ LocToken {
                start,
                end: _,
                token,
            },
        ) = self.peek_loc_token()
        {
            let loc = *start;
            let loc_token = ltref.clone();
            match token {
                Token::Null => {
                    self.advance();
                    Ok(LocExpr(loc, Expr::Null))
                }
                Token::IntLit(n) => {
                    let n = n.clone();
                    self.advance();
                    Ok(LocExpr(loc, Expr::IntLit(n)))
                }
                Token::RatLit(n) => {
                    let n = n.clone();
                    self.advance();
                    Ok(LocExpr(loc, Expr::RatLit(n)))
                }
                Token::FloatLit(n) => {
                    let n = *n;
                    self.advance();
                    Ok(LocExpr(loc, Expr::FloatLit(n)))
                }
                Token::ImaginaryFloatLit(n) => {
                    let n = *n;
                    self.advance();
                    Ok(LocExpr(loc, Expr::ImaginaryFloatLit(n)))
                }
                Token::StringLit(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(LocExpr(loc, Expr::StringLit(s)))
                }
                Token::BytesLit(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(LocExpr(loc, Expr::BytesLit(s)))
                }
                Token::FormatString(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(LocExpr(
                        loc,
                        Expr::FormatString(parse_format_string(&s, &loc_token)?),
                    ))
                }
                Token::Underscore => {
                    self.advance();
                    Ok(LocExpr(loc, Expr::Underscore))
                }
                Token::Ident(s) => {
                    let s = s.clone();
                    self.advance();
                    Ok(LocExpr(loc, Expr::Ident(s)))
                }
                Token::Ellipsis => {
                    self.advance();
                    Ok(LocExpr(
                        loc,
                        Expr::Splat(Box::new(self.single("ellipsis")?)),
                    ))
                }
                Token::Consume => {
                    self.advance();
                    Ok(LocExpr(
                        loc,
                        Expr::Consume(Box::new(to_lvalue_no_literals(self.single("consume")?)?)),
                    ))
                }
                Token::Pop => {
                    self.advance();
                    Ok(LocExpr(
                        loc,
                        Expr::Pop(Box::new(to_lvalue_no_literals(self.single("pop")?)?)),
                    ))
                }
                Token::Remove => {
                    self.advance();
                    Ok(LocExpr(
                        loc,
                        Expr::Remove(Box::new(to_lvalue_no_literals(self.single("remove")?)?)),
                    ))
                }
                Token::Break => {
                    self.advance();
                    if self.peek_csc_stopper() {
                        Ok(LocExpr(loc, Expr::Break(None)))
                    } else {
                        Ok(LocExpr(
                            loc,
                            Expr::Break(Some(Box::new(self.single("break")?))),
                        ))
                    }
                }
                Token::Throw => {
                    self.advance();
                    Ok(LocExpr(loc, Expr::Throw(Box::new(self.single("throw")?))))
                }
                Token::Continue => {
                    self.advance();
                    Ok(LocExpr(loc, Expr::Continue))
                }
                Token::Return => {
                    self.advance();
                    if self.peek_csc_stopper() {
                        Ok(LocExpr(loc, Expr::Return(None)))
                    } else {
                        Ok(LocExpr(
                            loc,
                            Expr::Return(Some(Box::new(self.single("return")?))),
                        ))
                    }
                }
                Token::Literally => {
                    self.advance();
                    Ok(LocExpr(
                        loc,
                        Expr::Literally(Box::new(self.single("literally")?)),
                    ))
                }
                Token::Freeze => {
                    self.advance();
                    Ok(LocExpr(loc, Expr::Freeze(Box::new(self.single("throw")?))))
                }
                Token::LeftParen => {
                    self.advance();
                    let e = self.expression()?;
                    self.require(Token::RightParen, "normal parenthesized expr".to_string())?;
                    Ok(e)
                }
                Token::VLeftParen => {
                    self.advance();
                    if self.try_consume(&Token::RightParen) {
                        Ok(LocExpr(loc, Expr::Vector(Vec::new())))
                    } else {
                        let (exs, _) = self.comma_separated()?;
                        self.require(Token::RightParen, "vector expr".to_string())?;
                        Ok(LocExpr(loc, Expr::Vector(exs)))
                    }
                }
                Token::LeftBracket => {
                    self.advance();
                    if self.try_consume(&Token::RightBracket) {
                        Ok(LocExpr(loc, Expr::List(Vec::new())))
                    } else {
                        let (exs, _) = self.comma_separated()?;
                        self.require(Token::RightBracket, "list expr".to_string())?;
                        Ok(LocExpr(loc, Expr::List(exs)))
                    }
                }
                Token::LeftBrace => {
                    self.advance();
                    // Dict(Vec<(Box<Expr>, Option<Box<Expr>>)>),
                    let mut xs = Vec::new();
                    let mut def = None;
                    if self.try_consume(&Token::Colon) {
                        def = Some(Box::new(self.single("default of dict literal")?));
                        if !self.peek_csc_stopper() {
                            self.require(Token::Comma, "dict expr".to_string())?;
                        }
                    }

                    while !self.peek_csc_stopper() {
                        let c1 = Box::new(self.single("key of dict literal")?);
                        let c2 = if self.try_consume(&Token::Colon) {
                            Some(Box::new(self.single("value of dict literal")?))
                        } else {
                            None
                        };
                        xs.push((c1, c2));

                        if !self.peek_csc_stopper() {
                            self.require(Token::Comma, "dict expr".to_string())?;
                        }
                    }
                    self.require(Token::RightBrace, "dict expr end".to_string())?;
                    Ok(LocExpr(loc, Expr::Dict(def, xs)))
                }
                Token::RightParen => Err(self.error_here(format!("atom: unexpected"))),
                Token::Lambda => {
                    self.advance();
                    if let Some(Token::IntLit(x)) = self.peek().cloned() {
                        let us = x
                            .to_usize()
                            .ok_or(self.error_here(format!("backref: not usize: {}", x)))?;
                        self.advance();
                        Ok(LocExpr(loc, Expr::Backref(us)))
                    } else {
                        let params = if self.try_consume(&Token::RightArrow) {
                            Vec::new()
                        } else {
                            // Hmm. In a lambda, `a` and `a,` are the same, but on the LHS of an
                            // assignment the second unpacks.
                            let params0 = self.annotated_comma_separated("lambda params")?;
                            let ps = params0
                                .0
                                .into_iter()
                                .map(|p| Ok(Box::new(to_lvalue_no_literals(*p)?)))
                                .collect::<Result<Vec<Box<Lvalue>>, ParseError>>()?;
                            self.require(Token::RightArrow, "lambda start: ->".to_string())?;
                            ps
                        };
                        let body = self.single("body of lambda")?;
                        Ok(LocExpr(loc, Expr::Lambda(Rc::new(params), Rc::new(body))))
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
                    Ok(LocExpr(
                        loc,
                        Expr::If(Box::new(cond), Box::new(body), else_body),
                    ))
                }
                Token::For => {
                    self.advance();
                    self.require(Token::LeftParen, "for start".to_string())?;
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
                    let do_yield = self.try_consume(&Token::Yield);
                    let body = self.assignment()?;
                    Ok(LocExpr(loc, Expr::For(its, do_yield, Box::new(body))))
                }
                Token::While => {
                    self.advance();
                    self.require(Token::LeftParen, "while start".to_string())?;
                    let cond = self.expression()?;
                    self.require(Token::RightParen, "while end".to_string())?;
                    let body = self.assignment()?;
                    Ok(LocExpr(loc, Expr::While(Box::new(cond), Box::new(body))))
                }
                Token::Switch => {
                    self.advance();
                    self.require(Token::LeftParen, "switch start".to_string())?;
                    let scrutinee = self.expression()?;
                    self.require(Token::RightParen, "switch end".to_string())?;
                    let mut v = Vec::new();
                    while self.try_consume(&Token::Case) {
                        let pat = to_lvalue(self.annotated_pattern("switch pat")?)?;
                        self.require(Token::RightArrow, "case mid: ->".to_string())?;
                        let res = self.single("switch body")?;
                        v.push((Box::new(pat), Box::new(res)));
                    }
                    Ok(LocExpr(loc, Expr::Switch(Box::new(scrutinee), v)))
                }
                Token::Try => {
                    self.advance();
                    let body = self.expression()?;
                    self.require(Token::Catch, "try end".to_string())?;
                    let pat = to_lvalue(self.annotated_pattern("catch pattern")?)?;
                    self.require(Token::RightArrow, "catch mid: ->".to_string())?;
                    let catcher = self.single("catch body")?;
                    Ok(LocExpr(
                        loc,
                        Expr::Try(Box::new(body), Box::new(pat), Box::new(catcher)),
                    ))
                }
                Token::Struct => {
                    self.advance();
                    if let Some(Token::Ident(name)) = self.peek() {
                        let name = Rc::new(name.clone());
                        self.advance();
                        self.require(Token::LeftParen, "struct begin".to_string())?;
                        let mut fields = Vec::new();
                        if let Some(Token::Ident(field1)) = self.peek() {
                            fields.push(Rc::new(field1.clone()));
                            self.advance();
                            while self.try_consume(&Token::Comma) {
                                if let Some(Token::Ident(field)) = self.peek() {
                                    fields.push(Rc::new(field.clone()));
                                    self.advance();
                                } else {
                                    Err(self.error_here(format!("bad struct field")))?
                                }
                            }
                        }
                        self.require(Token::RightParen, "struct end".to_string())?;

                        Ok(LocExpr(loc, Expr::Struct(name, fields)))
                    } else {
                        Err(self.error_here(format!("bad struct name")))?
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
        if self.try_consume(&Token::If) {
            Ok(ForIteration::Guard(Box::new(
                self.single("for iteration guard")?,
            )))
        } else {
            let pat0 = self.annotated_pattern("for iterator")?;
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
            let iteratee = self.pattern()?;
            Ok(ForIteration::Iteration(
                ty,
                Box::new(pat),
                Box::new(iteratee),
            ))
        }
    }

    fn operand(&mut self) -> Result<LocExpr, ParseError> {
        let loc = self.peek_loc();
        let mut cur = self.atom()?;

        loop {
            match self.peek() {
                Some(Token::LeftParen) => {
                    self.advance();
                    if self.try_consume(&Token::RightParen) {
                        cur = LocExpr(loc, Expr::Call(Box::new(cur), Vec::new()));
                    } else {
                        let (cs, _) = self.comma_separated()?;
                        self.require(Token::RightParen, "call expr".to_string())?;
                        cur = LocExpr(loc, Expr::Call(Box::new(cur), cs));
                    }
                }
                Some(Token::LeftBracket) => {
                    self.advance();
                    if self.try_consume(&Token::Colon) {
                        if self.try_consume(&Token::RightBracket) {
                            cur = LocExpr(
                                loc,
                                Expr::Index(Box::new(cur), IndexOrSlice::Slice(None, None)),
                            );
                        } else {
                            let c = self.single("slice end")?;
                            self.require(Token::RightBracket, "index expr".to_string())?;
                            cur = LocExpr(
                                loc,
                                Expr::Index(
                                    Box::new(cur),
                                    IndexOrSlice::Slice(None, Some(Box::new(c))),
                                ),
                            );
                        }
                    } else {
                        let c = self.single("index/slice start")?;
                        if self.try_consume(&Token::Colon) {
                            if self.try_consume(&Token::RightBracket) {
                                cur = LocExpr(
                                    loc,
                                    Expr::Index(
                                        Box::new(cur),
                                        IndexOrSlice::Slice(Some(Box::new(c)), None),
                                    ),
                                );
                            } else {
                                let cc = self.single("slice end")?;
                                self.require(Token::RightBracket, "index expr".to_string())?;
                                cur = LocExpr(
                                    loc,
                                    Expr::Index(
                                        Box::new(cur),
                                        IndexOrSlice::Slice(Some(Box::new(c)), Some(Box::new(cc))),
                                    ),
                                );
                            }
                        } else {
                            self.require(Token::RightBracket, "index expr".to_string())?;
                            cur = LocExpr(
                                loc,
                                Expr::Index(Box::new(cur), IndexOrSlice::Index(Box::new(c))),
                            );
                        }
                    }
                }
                Some(Token::Bang) => {
                    self.advance();
                    if self.peek_csc_stopper() {
                        cur = LocExpr(loc, Expr::Call(Box::new(cur), Vec::new()));
                    } else {
                        let (cs, _) = self.comma_separated()?;
                        cur = LocExpr(loc, Expr::Call(Box::new(cur), cs));
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
            None => true,
            _ => false,
        }
    }

    fn peek_csc_stopper(&self) -> bool {
        self.peek_hard_stopper()
            || match self.peek() {
                Some(Token::Assign) => true,
                Some(Token::Colon) => true,
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
                Some(Token::And) => true,
                Some(Token::Or) => true,
                Some(Token::Coalesce) => true,
                _ => false,
            }
    }

    fn chain(&mut self) -> Result<LocExpr, ParseError> {
        let loc = self.peek_loc();
        let op1 = self.operand()?;
        if self.peek_chain_stopper() {
            Ok(op1)
        } else {
            // We'll specially allow some two-chains, (a b), as calls, so that negative number
            // literals and just writing an expression like "-x" works. But we will be
            // aggressive-ish about checking that the chain ends afterwards so we don't get runaway
            // syntax errors.
            let second = self.atom()?;
            match second.1 {
                Expr::Ident(op) => {
                    if self.try_consume(&Token::Bang) {
                        let ret = LocExpr(
                            loc,
                            Expr::Chain(
                                Box::new(op1),
                                vec![(
                                    Box::new(LocExpr(second.0, Expr::Ident(op))),
                                    Box::new(self.single("operator-bang operand")?),
                                )],
                            ),
                        );
                        if self.peek() == Some(&Token::Comma) {
                            Err(self.error_here("Got comma after operator-bang operand; the precedence is too confusing so this is banned".to_string()))
                        } else {
                            Ok(ret)
                        }
                    } else if self.peek_chain_stopper() {
                        Ok(LocExpr(
                            loc,
                            Expr::Call(
                                Box::new(op1),
                                vec![Box::new(LocExpr(second.0, Expr::Ident(op)))],
                            ),
                        ))
                    } else {
                        let mut ops = vec![(
                            Box::new(LocExpr(second.0, Expr::Ident(op))),
                            Box::new(self.operand()?),
                        )];

                        while let Some(Token::Ident(op)) = self.peek() {
                            let oploc = self.peek_loc();
                            let op = op.to_string();
                            self.advance();
                            ops.push((
                                Box::new(LocExpr(oploc, Expr::Ident(op))),
                                Box::new(if self.try_consume(&Token::Bang) {
                                    self.single("operator-bang operand")?
                                } else {
                                    self.operand()?
                                }),
                            ));
                        }
                        Ok(LocExpr(loc, Expr::Chain(Box::new(op1), ops)))
                    }
                }
                _ => {
                    let ret = LocExpr(loc, Expr::Call(Box::new(op1), vec![Box::new(second)]));
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
    }

    fn logic_and(&mut self) -> Result<LocExpr, ParseError> {
        let loc = self.peek_loc();
        let mut op1 = self.chain()?;
        while self.try_consume(&Token::And) {
            op1 = LocExpr(loc, Expr::And(Box::new(op1), Box::new(self.chain()?)));
        }
        Ok(op1)
    }

    fn single(&mut self, ctx: &str) -> Result<LocExpr, ParseError> {
        let loc = self.peek_loc();
        let mut op1 = err_add_context(self.logic_and(), ctx, loc)?;
        loop {
            match self.peek() {
                Some(Token::Or) => {
                    self.advance();
                    op1 = LocExpr(
                        loc,
                        Expr::Or(
                            Box::new(op1),
                            Box::new(err_add_context(self.logic_and(), ctx, loc)?),
                        ),
                    );
                }
                Some(Token::Coalesce) => {
                    self.advance();
                    op1 = LocExpr(
                        loc,
                        Expr::Coalesce(
                            Box::new(op1),
                            Box::new(err_add_context(self.logic_and(), ctx, loc)?),
                        ),
                    );
                }
                _ => return Ok(op1),
            }
        }
    }

    // Nonempty (caller should check empty condition); no semicolons or annotations allowed. List
    // literals; function declarations; LHSes of assignments. Not for function calls, I think? f(x;
    // y) might actually be ok...  bool is whether a comma was found, to distinguish (x) from (x,)
    fn comma_separated(&mut self) -> Result<(Vec<Box<LocExpr>>, bool), ParseError> {
        let mut xs = vec![Box::new(self.single("comma-separated starter")?)];
        let mut comma = false;
        while self.try_consume(&Token::Comma) {
            comma = true;
            if self.peek_csc_stopper() {
                return Ok((xs, comma));
            }
            xs.push(Box::new(self.single("comma-separated next")?));
        }
        return Ok((xs, comma));
    }

    // Nonempty comma-separated things, as above, but packaged as a single expr. No semicolons or
    // assigns allowed. Should be nonempty I think. RHSes of assignments.
    fn pattern(&mut self) -> Result<LocExpr, ParseError> {
        let loc = self.peek_loc();
        let (exs, comma) = self.comma_separated()?;
        match (few(exs), comma) {
            (Few::Zero, _) => Err(self.error_here(format!("Expected pattern, got nothing"))),
            (Few::One(ex), false) => Ok(*ex),
            (Few::One(ex), true) => Ok(LocExpr(loc, Expr::CommaSeq(vec![ex]))),
            (Few::Many(exs), _) => Ok(LocExpr(loc, Expr::CommaSeq(exs))),
        }
    }

    // Comma-separated things. No semicolons or assigns allowed. Should be nonempty I think, as
    // above caller should handle empty case.
    //
    // This exists because we want commas and annotations to be "at the same level": it's important
    // that the annotation in `a, b := 3, 4` covers a, but it also doesn't make sense if `a: int,
    // b: list = 3, [4]` doesn't work. We trade one thing off for now: ideally `a, b: satisfying(3
    // < _ < 5) = 4` would evaluate the type expression only once, so the translated Lvalue needs
    // to be aware that substrings of variables in a flat list of things share the same annotation,
    // but that's annoying. Let's just clone the type expression.
    fn annotated_comma_separated(
        &mut self,
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
                    pending_annotation.push(Box::new(
                        self.single("later expr in annotated-comma-separated")?,
                    ));
                }
                Some(Token::Colon) => {
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
                    annotated.extend(
                        pending_annotation
                            .drain(..)
                            .map(|e| Box::new(LocExpr(e.0, Expr::Annotation(e, anno.clone())))),
                    );
                }
                _ => {
                    annotated.extend(pending_annotation);
                    return Ok((annotated, comma));
                }
            }
        }
    }
    fn annotated_pattern(&mut self, msg: &str) -> Result<LocExpr, ParseError> {
        let loc = self.peek_loc();
        let (exs, comma) = self.annotated_comma_separated(msg)?;
        match (few(exs), comma) {
            (Few::Zero, _) => Err(self.error_here(format!(
                "Expected annotated pattern at {}, got nothing",
                msg
            ))),
            (Few::One(ex), false) => Ok(*ex),
            (Few::One(ex), true) => Ok(LocExpr(loc, Expr::CommaSeq(vec![ex]))),
            (Few::Many(exs), _) => Ok(LocExpr(loc, Expr::CommaSeq(exs))),
        }
    }

    fn assignment(&mut self) -> Result<LocExpr, ParseError> {
        let loc = self.peek_loc();
        let ag_start_err = self.peek_err();
        if self.try_consume(&Token::Swap) {
            let a = to_lvalue_no_literals(self.single("swap target 1")?)?;
            self.require(
                Token::Comma,
                format!("swap between lvalues at {}", ag_start_err),
            )?;
            let b = to_lvalue_no_literals(self.single("swap target 2")?)?;
            Ok(LocExpr(loc, Expr::Swap(Box::new(a), Box::new(b))))
        } else {
            let every = self.try_consume(&Token::Every);
            // TODO: parsing can be different after Every
            let pat = self.annotated_pattern("assign LHS")?;

            match self.peek() {
                Some(Token::Assign) => {
                    self.advance();
                    match pat.1 {
                        Expr::Call(lhs, op) => match few(op) {
                            Few::One(op) => Ok(LocExpr(
                                loc,
                                Expr::OpAssign(
                                    every,
                                    Box::new(to_lvalue_no_literals(*lhs)?),
                                    Box::new(*op),
                                    Box::new(self.pattern()?),
                                ),
                            )),
                            _ => Err(self.error_here(format!(
                                "call w not 1 arg is not assignop, at {}",
                                ag_start_err
                            ))),
                        },
                        _ => Ok(LocExpr(
                            loc,
                            Expr::Assign(
                                every,
                                Box::new(to_lvalue_no_literals(pat)?),
                                Box::new(self.pattern()?),
                            ),
                        )),
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

        while self.try_consume(&Token::Semicolon) {
            if self.peek_hard_stopper() {
                ending_semicolon = true;
                break;
            } else {
                ags.push(Box::new(self.assignment()?));
            }
        }

        Ok(if ags.len() == 1 && !ending_semicolon {
            *ags.remove(0)
        } else {
            LocExpr(start, Expr::Sequence(ags, ending_semicolon))
        })
    }

    fn is_at_end(&self) -> bool {
        self.i == self.tokens.len()
    }
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

pub trait WriteMaybeExtractable: Write {
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
    pub input: Box<dyn BufRead>,
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

fn try_borrow_nres<'a, T>(
    r: &'a RefCell<T>,
    msg1: &str,
    msg2: &str,
) -> NRes<std::cell::Ref<'a, T>> {
    match r.try_borrow() {
        Ok(r) => Ok(r),
        Err(b) => Err(NErr::io_error(format!(
            "internal borrow error: {}: {}: {}",
            msg1, msg2, b
        ))),
    }
}
fn try_borrow_mut_nres<'a, T>(
    r: &'a RefCell<T>,
    msg1: &str,
    msg2: &str,
) -> NRes<std::cell::RefMut<'a, T>> {
    match r.try_borrow_mut() {
        Ok(r) => Ok(r),
        Err(b) => Err(NErr::io_error(format!(
            "internal borrow mut error: {}: {}: {}",
            msg1, msg2, b
        ))),
    }
}

#[derive(Debug)]
pub struct Env {
    pub vars: HashMap<String, (ObjType, Box<RefCell<Obj>>)>,
    pub parent: Result<Rc<RefCell<Env>>, Rc<RefCell<TopEnv>>>,
}
impl Env {
    pub fn new(top: TopEnv) -> Env {
        Env {
            vars: HashMap::new(),
            parent: Err(Rc::new(RefCell::new(top))),
        }
    }
    // ???
    fn empty() -> Env {
        Env::new(TopEnv {
            backrefs: Vec::new(),
            input: Box::new(io::empty()),
            output: Box::new(io::sink()),
        })
    }
    fn with_parent(env: &Rc<RefCell<Env>>) -> Rc<RefCell<Env>> {
        Rc::new(RefCell::new(Env {
            vars: HashMap::new(),
            parent: Ok(Rc::clone(&env)),
        }))
    }
    pub fn mut_top_env<T>(&self, f: impl FnOnce(&mut TopEnv) -> T) -> T {
        match &self.parent {
            Ok(v) => v.borrow().mut_top_env(f),
            Err(t) => f(&mut t.borrow_mut()),
        }
    }

    fn try_borrow_get_var(env: &Rc<RefCell<Env>>, s: &str) -> NRes<Obj> {
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
                            .filter(|k| {
                                // TODO: better similarity comparison lol
                                k.contains(s) || s.contains(&**k)
                            })
                            .min_by_key(|k| k.len().abs_diff(s.len()))
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

    fn modify_existing_var<T>(
        &self,
        key: &str,
        f: impl FnOnce(&(ObjType, Box<RefCell<Obj>>)) -> T,
    ) -> Option<T> {
        match self.vars.get(key) {
            Some(target) => Some(f(target)),
            None => match &self.parent {
                Ok(p) => p.borrow().modify_existing_var(key, f),
                Err(_) => None,
            },
        }
    }
    fn insert(&mut self, key: String, ty: ObjType, val: Obj) -> NRes<()> {
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
    fn insert_type(&mut self, b: ObjType) {
        self.insert(
            b.name(),
            ObjType::Any,
            Obj::Func(Func::Type(b), Precedence::zero()),
        )
        .unwrap()
    }
    fn insert_builtin_with_precedence(&mut self, b: impl Builtin + 'static, p: Precedence) {
        self.insert(
            b.builtin_name().to_string(),
            ObjType::Any,
            Obj::Func(Func::Builtin(Rc::new(b)), p),
        )
        .unwrap()
    }
    fn insert_builtin(&mut self, b: impl Builtin + 'static) {
        let p = Precedence(default_precedence(b.builtin_name()), Assoc::Left);
        self.insert_builtin_with_precedence(b, p)
    }
    fn insert_rassoc_builtin(&mut self, b: impl Builtin + 'static) {
        let p = Precedence(default_precedence(b.builtin_name()), Assoc::Right);
        self.insert_builtin_with_precedence(b, p)
    }
    fn insert_builtin_with_alias(&mut self, b: impl Builtin + 'static + Clone, alias: &str) {
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

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum AssignMode {
    Assign,             // assign or declare, as type annotations declare
    IgnoreExistingType, // just ignore types of existing variables; for LHS-dropping
    PatternMatch,       // unannotated variables should be checked against instead of updated
}

// the ObjType is provided iff it's a declaration

fn assign_all_basic(
    env: &REnv,
    lhs: &[Box<EvaluatedLvalue>],
    rt: Option<&ObjType>,
    rhs: Vec<Obj>,
    mode: AssignMode,
    err_msg: &str,
) -> NRes<()> {
    if lhs.len() == rhs.len() {
        for (lhs1, rhs1) in lhs.iter().zip(rhs.into_iter()) {
            assign(env, lhs1, rt, rhs1, mode)?;
        }
        Ok(())
    } else {
        Err(NErr::value_error(format!(
            "{}: expected {} ({}), got {} ({})",
            err_msg,
            lhs.len(),
            CommaSeparated(lhs),
            rhs.len(),
            CommaSeparatedDebug(&rhs)
        )))
    }
}

// Delay computing the rhs if possible because it might be a big vector for which cloning is
// expensive and our pattern might blatantly not match (this is pretty ad hoc lol)
fn assign_all(
    env: &REnv,
    lhs: &[Box<EvaluatedLvalue>],
    rt: Option<&ObjType>,
    rhs_len: usize,
    lazy_rhs: impl FnOnce() -> Vec<Obj>,
    mode: AssignMode,
    err_msg: &str,
) -> NRes<()> {
    let mut splat = None;
    for (i, lhs1) in lhs.iter().enumerate() {
        match &**lhs1 {
            EvaluatedLvalue::Splat(inner) => match splat {
                Some(_) => {
                    return Err(NErr::syntax_error(format!(
                        "Can't have two splats in same sequence on left-hand side of assignment"
                    )))
                }
                None => {
                    splat = Some((i, Ok(inner)));
                }
            },
            // FIXME? probably another consequence of forcing annotations into CommaSeq
            EvaluatedLvalue::Annotation(mid, anno) => match &**mid {
                EvaluatedLvalue::Splat(inner) => match splat {
                    Some(_) => {
                        return Err(NErr::syntax_error(format!(
                            "Can't have two splats in same sequence on left-hand side of assignment"
                        )))
                    }
                    None => {
                        splat = Some((i, Err((inner, anno))));
                    }
                },
                _ => {}
            },
            _ => {}
        }
    }
    match splat {
        Some((si, inner)) => {
            // mmm we could compare against rhs len eagerly to not call it, but the bad cases don't
            // involve a splat
            let mut rhs = lazy_rhs();
            let rrhs = rhs.drain(rhs.len() - lhs.len() + si + 1..).collect();
            let srhs = rhs.drain(si..).collect();
            assign_all_basic(env, &lhs[..si], rt, rhs, mode, err_msg)?;
            match inner {
                Ok(inner) => assign(env, inner, rt, Obj::list(srhs), mode)?,
                Err((inner, anno)) => {
                    let t = match anno {
                        None => Some(ObjType::Any),
                        Some(t) => Some(to_type(t, "splat anno")?),
                    };
                    assign(env, inner, t.as_ref(), Obj::list(srhs), mode)?
                }
            };
            assign_all_basic(env, &lhs[si + 1..], rt, rrhs, mode, err_msg)
        }
        None => {
            if lhs.len() == rhs_len {
                assign_all_basic(env, lhs, rt, lazy_rhs(), mode, err_msg)
            } else if rhs_len <= 8 {
                Err(NErr::value_error(format!(
                    "{}: expected {} ({}), got {} ({})",
                    err_msg,
                    lhs.len(),
                    CommaSeparated(lhs),
                    rhs_len,
                    CommaSeparatedDebug(&lazy_rhs())
                )))
            } else {
                Err(NErr::value_error(format!(
                    "{}: expected {} ({}), got {}",
                    err_msg,
                    lhs.len(),
                    CommaSeparated(lhs),
                    rhs_len
                )))
            }
        }
    }
}

// Modifying parts of a &mut Obj
// =============================

fn set_index(
    lhs: &mut Obj,
    indexes: &[EvaluatedIndexOrSlice],
    value: Obj,
    every: bool,
) -> NRes<()> {
    // hack
    match (&*lhs, indexes) {
        (Obj::Seq(Seq::Stream(m)), [_, ..]) => {
            let mm = m.clone_box();
            *lhs = Obj::list(mm.force().ok_or(NErr::type_error(format!(
                "Can't assign to unforceable stream"
            )))?)
        }
        _ => {}
    }
    match (lhs, indexes) {
        (lhs, []) => {
            *lhs = value;
            Ok(())
        }
        (Obj::Seq(s), [fi, rest @ ..]) => match (s, fi) {
            (Seq::List(v), EvaluatedIndexOrSlice::Index(i)) => {
                set_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, value, every)
            }
            (Seq::List(v), EvaluatedIndexOrSlice::Slice(i, j)) => {
                if every {
                    let v = Rc::make_mut(v);
                    let (lo, hi) = pythonic_slice_obj(v, i.as_ref(), j.as_ref())?;
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
                                return Err(e);
                            }
                        };
                        owned[i..i + 1].copy_from_slice(v.as_bytes());
                        match String::from_utf8(owned) {
                            Ok(r) => {
                                *mut_s = r;
                                Ok(())
                            }
                            Err(err) => {
                                *mut_s = String::from_utf8_lossy(err.as_bytes()).into_owned();
                                Err(NErr::value_error(format!(
                                    "assigning to string result not utf-8 (string corrupted)"
                                )))
                            }
                        }
                    } else {
                        Err(NErr::value_error(format!(
                            "assigning to string index, not a byte"
                        )))
                    }
                }
                _ => Err(NErr::value_error(format!(
                    "assigning to string index, not a string"
                ))),
            },
            (Seq::String(_), _) => Err(NErr::type_error(format!("string bad slice"))),
            (Seq::Dict(v, _), EvaluatedIndexOrSlice::Index(kk)) => {
                let k = to_key(kk.clone())?;
                let mut_d = Rc::make_mut(v);
                // We might create a new map entry, but only at the end, which is a bit of a
                // mismatch for Rust's map API if we want to recurse all the way
                if rest.is_empty() {
                    mut_d.insert(k, value);
                    Ok(())
                } else {
                    set_index(
                        match mut_d.get_mut(&k) {
                            Some(vvv) => vvv,
                            None => Err(NErr::type_error(format!(
                                "setting dictionary: nothing at key {}[{}]",
                                FmtDictPairs(mut_d.iter(), &DEBUG_FMT),
                                k
                            )))?,
                        },
                        rest,
                        value,
                        every,
                    )
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
                    Err(NErr::type_error(format!(
                        "can't slice dictionaries except with every"
                    )))
                }
            }
            (Seq::Dict(..), _) => Err(NErr::type_error(format!("dict bad slice"))),
            (Seq::Vector(v), EvaluatedIndexOrSlice::Index(i)) if rest.is_empty() => match value {
                Obj::Num(n) => {
                    let i = pythonic_index(v, i)?;
                    Rc::make_mut(v)[i] = n;
                    Ok(())
                }
                _ => Err(NErr::type_error(format!("vec bad value assgn"))),
            },
            (Seq::Vector(_), _) => Err(NErr::type_error(format!("vec bad slice / not impl"))),
            (Seq::Bytes(v), EvaluatedIndexOrSlice::Index(i)) if rest.is_empty() => match value {
                Obj::Num(ref n) => {
                    let i = pythonic_index(v, i)?;
                    Rc::make_mut(v)[i] = n.to_u8().ok_or(NErr::value_error(format!(
                        "can't to byte: {}",
                        FmtObj::debug(&value)
                    )))?;
                    Ok(())
                }
                _ => Err(NErr::type_error(format!("bytes bad value assgn"))),
            },
            (Seq::Bytes(_), _) => Err(NErr::type_error(format!("vec bad slice / not impl"))),
            (Seq::Stream(_), _) => panic!("stream handled above"),
        },
        (
            Obj::Func(_, Precedence(p, _)),
            [EvaluatedIndexOrSlice::Index(Obj::Seq(Seq::String(r)))],
        ) => match &***r {
            "precedence" => match value {
                Obj::Num(f) => match f.to_f64() {
                    Some(f) => {
                        *p = f;
                        Ok(())
                    }
                    None => Err(NErr::value_error(format!(
                        "precedence must be convertible to float: {}",
                        f
                    ))),
                },
                f => Err(NErr::type_error(format!(
                    "precedence must be number, got {}",
                    f
                ))),
            },
            k => Err(NErr::key_error(format!(
                "function key must be 'precedence', got {}",
                k
            ))),
        },
        (
            Obj::Instance(struc, fields),
            [EvaluatedIndexOrSlice::Index(Obj::Func(Func::StructField(istruc, field_index), _)), rest @ ..],
        ) => {
            if struc == istruc {
                set_index(&mut fields[*field_index], rest, value, every)
            } else {
                Err(NErr::index_error(format!("wrong struct type",)))
            }
        }
        (lhs, ii) => Err(NErr::index_error(format!(
            "can't set index {:?} {:?}",
            lhs, ii
        ))),
    }
}

// be careful not to call this with both lhs holding a mutable reference into a RefCell and rhs
// trying to take such a reference!
fn modify_existing_index(
    lhs: &mut Obj,
    indexes: &[EvaluatedIndexOrSlice],
    f: impl FnOnce(&mut Obj) -> NRes<Obj>,
) -> NRes<Obj> {
    // hack
    match (&*lhs, indexes) {
        (Obj::Seq(Seq::Stream(m)), [_, ..]) => {
            let mm = m.clone_box();
            *lhs = Obj::list(mm.force().ok_or(NErr::type_error(format!(
                "Can't assign to unforceable stream"
            )))?)
        }
        _ => {}
    }
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
                    match mut_d.entry(k) {
                        std::collections::hash_map::Entry::Occupied(mut e) => {
                            modify_existing_index(e.get_mut(), rest, f)
                        }
                        std::collections::hash_map::Entry::Vacant(e) => match def {
                            Some(d) => modify_existing_index(e.insert((&**d).clone()), rest, f),
                            None => {
                                return Err(NErr::key_error(format!(
                                    "nothing at key {}[{}]",
                                    FmtDictPairs(mut_d.iter(), &DEBUG_FMT),
                                    kk
                                )))
                            }
                        },
                    }
                }
                (
                    Obj::Instance(struc, fields),
                    EvaluatedIndexOrSlice::Index(Obj::Func(
                        Func::StructField(istruc, field_index),
                        _,
                    )),
                ) => {
                    if struc == istruc {
                        modify_existing_index(&mut fields[*field_index], rest, f)
                    } else {
                        Err(NErr::index_error(format!("wrong struct type",)))
                    }
                }
                // TODO everything
                (lhs2, ii) => Err(NErr::type_error(format!(
                    "can't modify index {:?} {:?}",
                    lhs2, ii
                ))),
            }
        }
    }
}

// same here...
fn modify_every_existing_index(
    lhs: &mut Obj,
    indexes: &[EvaluatedIndexOrSlice],
    f: &mut impl FnMut(&mut Obj) -> NRes<()>,
) -> NRes<()> {
    // hack
    match (&*lhs, indexes) {
        (Obj::Seq(Seq::Stream(m)), [_, ..]) => {
            let mm = m.clone_box();
            *lhs = Obj::list(mm.force().ok_or(NErr::type_error(format!(
                "Can't assign to unforceable stream"
            )))?)
        }
        _ => {}
    }
    match indexes.split_first() {
        None => f(lhs),
        Some((i, rest)) => {
            match (lhs, i) {
                (Obj::Seq(Seq::List(v)), EvaluatedIndexOrSlice::Index(i)) => {
                    modify_every_existing_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, f)
                }
                (Obj::Seq(Seq::List(v)), EvaluatedIndexOrSlice::Slice(lo, hi)) => {
                    let (lo, hi) = pythonic_slice_obj(v, lo.as_ref(), hi.as_ref())?;
                    for m in &mut Rc::make_mut(v)[lo..hi] {
                        modify_every_existing_index(m, rest, f)?;
                    }
                    Ok(())
                }
                (Obj::Seq(Seq::Dict(v, def)), EvaluatedIndexOrSlice::Index(kk)) => {
                    let k = to_key(kk.clone())?;
                    let mut_d = Rc::make_mut(v);
                    match mut_d.entry(k) {
                        std::collections::hash_map::Entry::Occupied(mut e) => {
                            modify_every_existing_index(e.get_mut(), rest, f)
                        }
                        std::collections::hash_map::Entry::Vacant(e) => match def {
                            Some(d) => {
                                modify_every_existing_index(e.insert((&**d).clone()), rest, f)
                            }
                            None => {
                                return Err(NErr::key_error(format!(
                                    "nothing at key {}[{}]",
                                    FmtDictPairs(mut_d.iter(), &DEBUG_FMT),
                                    kk
                                )))
                            }
                        },
                    }
                }
                (
                    Obj::Instance(struc, fields),
                    EvaluatedIndexOrSlice::Index(Obj::Func(
                        Func::StructField(istruc, field_index),
                        _,
                    )),
                ) => {
                    if struc == istruc {
                        modify_every_existing_index(&mut fields[*field_index], rest, f)
                    } else {
                        Err(NErr::index_error(format!("wrong struct type",)))
                    }
                }
                // TODO everything
                (lhs2, ii) => Err(NErr::type_error(format!(
                    "can't modify every index {:?} {:?}",
                    lhs2, ii
                ))),
            }
        }
    }
}

fn insert_declare(env: &REnv, s: &str, ty: ObjType, rhs: Obj) -> NRes<()> {
    if !is_type(&ty, &rhs) {
        Err(NErr::name_error(format!(
            "Declaring, type mismatch: {} is not of type {}",
            rhs,
            ty.name()
        )))
    } else {
        try_borrow_mut_nres(env, "variable declaration", s)?.insert(s.to_string(), ty, rhs)
    }
}

fn assign_respecting_type(
    env: &REnv,
    s: &str,
    ixs: &[EvaluatedIndexOrSlice],
    rhs: Obj,
    every: bool,
    typecheck: bool,
) -> NRes<()> {
    try_borrow_nres(env, "env for assigning", s)?.modify_existing_var(s, |(ty, v)| {
        // Eagerly check type only if ixs is empty, otherwise we can't really do
        // that (at least not in full generality)
        // FIXME is there possibly a double borrow here? maybe not because we only use immutable
        // borrows, so we'd only conflict with mutable borrows, and the type couldn't have been
        // constructed to mutably borrow the variable it's for?
        if typecheck && ixs.is_empty() && !is_type(ty, &rhs) {
            Err(NErr::type_error(format!("Assignment to {} type check failed: {} not {}", s, FmtObj::debug(&rhs), ty.name())))?
        }
        set_index(&mut *try_borrow_mut_nres(v, "var for assigning", s)?, ixs, rhs, every)?;
        // Check type after the fact. TODO if we ever do subscripted types: this
        // will be super inefficient lmao, we can be smart tho
        if typecheck && !ixs.is_empty() && !is_type(ty, &*try_borrow_nres(v, "assignment late type check", s)?) {
            Err(NErr::type_error(format!("Assignment to {} LATE type check failed (the assignment still happened): not {}", s, ty.name())))
        } else {
            Ok(())
        }
    }).ok_or(NErr::name_error(if ixs.is_empty() {
         format!("Variable {:?} not found (use := to declare)", s)
    } else {
         format!("Variable {:?} not found, couldn't set into index {:?}", s, ixs)
    }))?
}

fn assign(
    env: &REnv,
    lhs: &EvaluatedLvalue,
    rt: Option<&ObjType>,
    rhs: Obj,
    mode: AssignMode,
) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::Underscore => {
            match rt {
                Some(ty) => {
                    if !is_type(&ty, &rhs) {
                        return Err(NErr::type_error(format!(
                            "Assigning to underscore type mismatch: {} is not of type {}",
                            rhs,
                            ty.name()
                        )));
                    }
                }
                None => (),
            }
            Ok(())
        }
        EvaluatedLvalue::IndexedIdent(s, ixs) => match rt {
            Some(ty) => {
                // declaration
                if ixs.is_empty() {
                    insert_declare(env, s, ty.clone(), rhs.clone())
                } else {
                    return Err(NErr::name_error(format!(
                        "Can't declare new value into index expression: {:?} {:?}",
                        s, ixs
                    )));
                }
            }
            None => {
                let typecheck = match mode {
                    AssignMode::Assign => true,
                    AssignMode::IgnoreExistingType => false,
                    AssignMode::PatternMatch => {
                        let obj = eval_lvalue_as_obj(env, lhs)?;
                        return if obj == rhs.clone() {
                            Ok(())
                        } else {
                            Err(NErr::type_error(format!(
                                "Equality against variable pattern didn't match: {} {}",
                                obj, rhs
                            )))
                        };
                    }
                };
                assign_respecting_type(env, s, ixs, rhs, /* every */ false, typecheck)
            }
        },
        EvaluatedLvalue::CommaSeq(ss) => match rhs {
            Obj::Seq(Seq::List(ls)) => assign_all(
                env,
                ss,
                rt,
                ls.len(),
                || unwrap_or_clone(ls),
                mode,
                "Can't unpack into mismatched length",
            ),
            Obj::Seq(seq) => match seq.len() {
                Some(len) => assign_all(
                    env,
                    ss,
                    rt,
                    len,
                    || seq_to_cloning_iter(&seq).collect::<Vec<Obj>>(),
                    mode,
                    "Can't unpack into mismatched length",
                ),
                None => Err(NErr::type_error(
                    "Can't unpack from infinite sequence".to_string(),
                )),
            },
            _ => Err(NErr::type_error(
                "Unpacking failed: not iterable".to_string(),
            )),
        },
        EvaluatedLvalue::Annotation(s, ann) => match ann {
            None => assign(env, s, Some(&ObjType::Any), rhs, mode),
            Some(t) => assign(env, s, Some(&to_type(t, "annotation")?), rhs, mode),
        },
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!(
            "Can't assign to raw splat {:?}",
            lhs
        ))),
        EvaluatedLvalue::Or(a, b) => match assign(env, a, rt, rhs.clone(), mode) {
            Ok(()) => Ok(()),
            Err(_) => assign(env, b, rt, rhs, mode),
        },
        EvaluatedLvalue::Literal(obj) => {
            if obj == &rhs {
                Ok(())
            } else {
                Err(NErr::type_error(format!(
                    "Literal pattern didn't match: {} {}",
                    FmtObj::debug(obj),
                    FmtObj::debug(&rhs)
                )))
            }
        }
        EvaluatedLvalue::Destructure(f, args) => {
            let known = args
                .iter()
                .map(|e| match &**e {
                    EvaluatedLvalue::Literal(obj) => Some(obj.clone()),
                    _ => None,
                })
                .collect::<Vec<Option<Obj>>>();
            let res = f.destructure(rhs.clone(), known)?;
            if res.len() == args.len() {
                assign_all(
                    env,
                    args,
                    rt,
                    res.len(),
                    || res,
                    mode,
                    "Can't destructure into mismatched length",
                )
            } else {
                Err(NErr::type_error(format!(
                    "{} destructure length didn't match: {:?} {:?}",
                    f.builtin_name(),
                    res,
                    args
                )))
            }
        }
    }
}

fn assign_every(
    env: &REnv,
    lhs: &EvaluatedLvalue,
    rt: Option<&ObjType>,
    rhs: Obj,
    mode: AssignMode,
) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::Underscore => Ok(()),
        EvaluatedLvalue::IndexedIdent(s, ixs) => match rt {
            Some(ty) => {
                // declaration
                if ixs.is_empty() {
                    insert_declare(env, s, ty.clone(), rhs.clone())
                } else {
                    return Err(NErr::name_error(format!(
                        "Can't declare new value into index expression: {:?} {:?}",
                        s, ixs
                    )));
                }
            }
            None => {
                let typecheck = match mode {
                    AssignMode::Assign => true,
                    AssignMode::IgnoreExistingType => false,
                    AssignMode::PatternMatch => {
                        return Err(NErr::type_error(format!(
                            "why are we pattern matching literally every?"
                        )))
                    }
                };
                assign_respecting_type(env, s, ixs, rhs, /* every */ true, typecheck)
            }
        },
        EvaluatedLvalue::CommaSeq(ss) => {
            for v in ss {
                assign_every(env, v, rt, rhs.clone(), mode)?;
            }
            Ok(())
        }
        EvaluatedLvalue::Annotation(s, ann) => match ann {
            None => assign_every(env, s, Some(&ObjType::Any), rhs, mode),
            Some(t) => assign_every(env, s, Some(&to_type(t, "annotation")?), rhs, mode),
        },
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!(
            "Can't assign to raw splat {:?}",
            lhs
        ))),
        EvaluatedLvalue::Or(..) => Err(NErr::type_error(format!(
            "Can't assign-every to or {:?}",
            lhs
        ))),
        EvaluatedLvalue::Literal(obj) => {
            if obj == &rhs {
                Ok(())
            } else {
                Err(NErr::type_error(format!(
                    "Literal pattern didn't match: {} {}",
                    obj, rhs
                )))
            }
        }
        EvaluatedLvalue::Destructure(f, args) => {
            let known = args
                .iter()
                .map(|e| match &**e {
                    EvaluatedLvalue::Literal(obj) => Some(obj.clone()),
                    _ => None,
                })
                .collect::<Vec<Option<Obj>>>();
            let res = f.destructure(rhs.clone(), known)?;
            if res.len() == args.len() {
                assign_all(
                    env,
                    args,
                    rt,
                    res.len(),
                    || res,
                    mode,
                    "Can't destructure into mismatched length",
                )
            } else {
                Err(NErr::type_error(format!(
                    "{} destructure length didn't match: {:?} {:?}",
                    f.builtin_name(),
                    res,
                    args
                )))
            }
        }
    }
}

// different: doesn't hold a mutable borrow to the environment when calling rhs; doesn't accept
// declarations
fn modify_every(
    env: &Rc<RefCell<Env>>,
    lhs: &EvaluatedLvalue,
    rhs: &mut impl FnMut(Obj) -> NRes<Obj>,
) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::Underscore => Err(NErr::type_error(format!("Can't modify underscore"))),
        EvaluatedLvalue::IndexedIdent(s, ixs) => {
            // drop borrow immediately
            let mut old: Obj = Env::try_borrow_get_var(env, s)?;

            if ixs.is_empty() {
                let new = rhs(old)?;
                try_borrow_nres(env, "env for modify every", s)?
                    .modify_existing_var(s, |(ty, old)| {
                        // FIXME is there possibly another double borrow here?
                        if is_type(ty, &new) {
                            *try_borrow_mut_nres(old, "var for modify every", s)? = new.clone();
                            Ok(())
                        } else {
                            Err(NErr::name_error(format!(
                                "Modify every: assignment to {} type check failed: {} not {}",
                                s,
                                new,
                                ty.name()
                            )))
                        }
                    })
                    .ok_or(NErr::name_error(format!(
                        "Variable {:?} not found in modify every",
                        s
                    )))?
            } else {
                modify_every_existing_index(&mut old, ixs, &mut |x: &mut Obj| {
                    *x = rhs(std::mem::take(x))?;
                    Ok(())
                })?;
                assign_respecting_type(
                    env,
                    s,
                    &[],
                    old,
                    false, /* every */
                    true,  /* typecheck */
                )
            }
        }
        EvaluatedLvalue::CommaSeq(ss) => {
            for v in ss {
                modify_every(env, v, rhs)?;
            }
            Ok(())
        }
        EvaluatedLvalue::Annotation(..) => Err(NErr::type_error(format!(
            "No annotations in modify every: {:?}",
            lhs
        ))),
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!(
            "Can't modify raw splat {:?}",
            lhs
        ))),
        EvaluatedLvalue::Or(..) => Err(NErr::type_error(format!("Can't modify or {:?}", lhs))),
        EvaluatedLvalue::Literal(x) => Err(NErr::type_error(format!(
            "Can't modify literal {}",
            FmtObj::debug(x)
        ))),
        EvaluatedLvalue::Destructure(..) => Err(NErr::type_error(format!(
            "Can't modify destructure {:?}",
            lhs
        ))),
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

struct ChainEvaluator {
    operands: Vec<Vec<Obj>>,
    operators: Vec<(Func, Precedence, CodeLoc)>,
}

impl ChainEvaluator {
    fn new(operand: Obj) -> ChainEvaluator {
        ChainEvaluator {
            operands: vec![vec![operand]],
            operators: Vec::new(),
        }
    }

    fn run_top_popped(&mut self, env: &REnv, op: Func, loc: CodeLoc) -> NRes<()> {
        let mut rhs = self.operands.pop().expect("sync");
        let mut lhs = self.operands.pop().expect("sync");
        lhs.append(&mut rhs); // concats and drains rhs of elements
        self.operands.push(vec![add_trace(
            op.run(env, lhs),
            format!("chain {}", op),
            loc,
        )?]);
        Ok(())
    }

    fn run_top(&mut self, env: &REnv) -> NRes<()> {
        let (op, _, loc) = self.operators.pop().expect("sync");
        self.run_top_popped(env, op, loc)
    }

    fn give(
        &mut self,
        env: &REnv,
        operator: Func,
        precedence: Precedence,
        operand: Obj,
        loc: CodeLoc,
    ) -> NRes<()> {
        while self
            .operators
            .last()
            .map_or(false, |t| t.1.tighter_than_when_before(&precedence))
        {
            let (top, prec, loc) = self.operators.pop().expect("sync");
            match top.try_chain(&operator) {
                Some(new_op) => {
                    self.operators.push((new_op, prec, loc));
                    self.operands.last_mut().expect("sync").push(operand);
                    return Ok(());
                }
                None => {
                    self.run_top_popped(env, top, loc)?;
                }
            }
        }

        self.operators.push((operator, precedence, loc));
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

struct LvalueChainEvaluator {
    operands: Vec<Vec<Box<EvaluatedLvalue>>>,
    operators: Vec<(Func, Precedence)>,
}

impl LvalueChainEvaluator {
    fn new(operand: EvaluatedLvalue) -> LvalueChainEvaluator {
        LvalueChainEvaluator {
            operands: vec![vec![Box::new(operand)]],
            operators: Vec::new(),
        }
    }

    fn run_top_popped(&mut self, op: Func) -> NRes<()> {
        let mut rhs = self.operands.pop().expect("sync");
        let mut lhs = self.operands.pop().expect("sync");
        match op {
            Func::Builtin(b) => {
                lhs.append(&mut rhs); // concats and drains rhs of elements
                self.operands
                    .push(vec![Box::new(EvaluatedLvalue::Destructure(b, lhs))]);
                Ok(())
            }
            nop => Err(NErr::type_error(format!(
                "can't destructure with non-builtin {:?}",
                nop
            ))),
        }
    }

    fn run_top(&mut self) -> NRes<()> {
        let (op, _) = self.operators.pop().expect("sync");
        self.run_top_popped(op)
    }

    fn give(
        &mut self,
        operator: Func,
        precedence: Precedence,
        operand: EvaluatedLvalue,
    ) -> NRes<()> {
        while self
            .operators
            .last()
            .map_or(false, |t| t.1.tighter_than_when_before(&precedence))
        {
            let (top, prec) = self.operators.pop().expect("sync");
            match top.try_chain(&operator) {
                Some(new_op) => {
                    self.operators.push((new_op, prec));
                    self.operands
                        .last_mut()
                        .expect("sync")
                        .push(Box::new(operand));
                    return Ok(());
                }
                None => {
                    self.run_top_popped(top)?;
                }
            }
        }

        self.operators.push((operator, precedence));
        self.operands.push(vec![Box::new(operand)]);
        Ok(())
    }

    fn finish(&mut self) -> NRes<EvaluatedLvalue> {
        while !self.operators.is_empty() {
            self.run_top()?;
        }
        if self.operands.len() == 1 {
            Ok(*self.operands.remove(0).remove(0))
        } else {
            panic!("chain eval out of sync")
        }
    }
}

// allow splats
fn eval_seq(env: &Rc<RefCell<Env>>, exprs: &Vec<Box<LocExpr>>) -> NRes<Vec<Obj>> {
    let mut acc = Vec::new();
    for x in exprs {
        match &((**x).1) {
            Expr::Splat(inner) => {
                let mut res = evaluate(env, inner)?;
                acc.extend(mut_obj_into_iter(&mut res, "splat")?);
            }
            _ => acc.push(evaluate(env, x)?),
        }
    }
    Ok(acc)
}

fn eval_index_or_slice(env: &Rc<RefCell<Env>>, expr: &IndexOrSlice) -> NRes<EvaluatedIndexOrSlice> {
    match expr {
        IndexOrSlice::Index(v) => Ok(EvaluatedIndexOrSlice::Index(evaluate(env, v)?)),
        IndexOrSlice::Slice(a, b) => Ok(EvaluatedIndexOrSlice::Slice(
            match a {
                Some(a) => Some(evaluate(env, a)?),
                None => None,
            },
            match b {
                Some(b) => Some(evaluate(env, b)?),
                None => None,
            },
        )),
    }
}

fn eval_lvalue(env: &Rc<RefCell<Env>>, expr: &Lvalue) -> NRes<EvaluatedLvalue> {
    match expr {
        Lvalue::Underscore => Ok(EvaluatedLvalue::Underscore),
        Lvalue::IndexedIdent(s, v) => Ok(EvaluatedLvalue::IndexedIdent(
            s.to_string(),
            v.iter()
                .map(|e| Ok(eval_index_or_slice(env, e)?))
                .collect::<NRes<Vec<EvaluatedIndexOrSlice>>>()?,
        )),
        Lvalue::Annotation(s, t) => Ok(EvaluatedLvalue::Annotation(
            Box::new(eval_lvalue(env, s)?),
            match t {
                Some(e) => Some(evaluate(env, e)?),
                None => None,
            },
        )),
        Lvalue::CommaSeq(v) => Ok(EvaluatedLvalue::CommaSeq(
            v.iter()
                .map(|e| Ok(Box::new(eval_lvalue(env, e)?)))
                .collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?,
        )),
        Lvalue::Splat(v) => Ok(EvaluatedLvalue::Splat(Box::new(eval_lvalue(env, v)?))),
        Lvalue::Or(a, b) => Ok(EvaluatedLvalue::Or(
            Box::new(eval_lvalue(env, a)?),
            Box::new(eval_lvalue(env, b)?),
        )),
        Lvalue::Literal(obj) => Ok(EvaluatedLvalue::Literal(obj.clone())),
        Lvalue::Destructure(f, args) => match evaluate(env, f)? {
            Obj::Func(Func::Builtin(b), _) => Ok(EvaluatedLvalue::Destructure(
                b,
                args.iter()
                    .map(|e| Ok(Box::new(eval_lvalue(env, e)?)))
                    .collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?,
            )),
            ef => Err(NErr::type_error(format!(
                "destructure callee was not builtin, got {}",
                ef
            ))),
        },
        Lvalue::ChainDestructure(lv, vs) => {
            let mut ce = LvalueChainEvaluator::new(eval_lvalue(env, lv)?);
            for (oper, opd) in vs {
                let oprr = evaluate(env, oper)?;
                if let Obj::Func(b, prec) = oprr {
                    let oprd = eval_lvalue(env, opd)?;
                    ce.give(b, prec, oprd)?;
                } else {
                    return Err(NErr::type_error(format!(
                        "Destructure chain cannot use nonblock in operand position: {:?}",
                        oprr
                    )));
                }
            }
            ce.finish()
        }
        Lvalue::Literally(e) => Ok(EvaluatedLvalue::Literal(evaluate(env, e)?)),
    }
}

fn pythonic_index_isize<T>(xs: &[T], n: isize) -> NRes<usize> {
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

fn pythonic_index<T>(xs: &[T], i: &Obj) -> NRes<usize> {
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

fn pythonic_mut<'a, 'b>(xs: &'a mut Vec<Obj>, i: &'b Obj) -> NRes<&'a mut Obj> {
    let ii = pythonic_index(xs, i)?;
    Ok(&mut xs[ii])
}

// for slicing
fn clamped_pythonic_index<T>(xs: &[T], i: isize) -> usize {
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

fn pythonic_slice<T>(xs: &[T], lo: Option<isize>, hi: Option<isize>) -> (usize, usize) {
    (
        match lo {
            Some(lo) => clamped_pythonic_index(xs, lo),
            None => 0,
        },
        match hi {
            Some(hi) => clamped_pythonic_index(xs, hi),
            None => xs.len(),
        },
    )
}

fn obj_to_isize_slice_index(x: Option<&Obj>) -> NRes<Option<isize>> {
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

fn pythonic_slice_obj<T>(xs: &[T], lo: Option<&Obj>, hi: Option<&Obj>) -> NRes<(usize, usize)> {
    let lo = obj_to_isize_slice_index(lo)?;
    let hi = obj_to_isize_slice_index(hi)?;
    Ok(pythonic_slice(xs, lo, hi))
}

fn cyclic_index<T>(xs: &[T], i: &Obj) -> NRes<usize> {
    match i {
        Obj::Num(ii) => match ii.to_isize() {
            Some(n) => {
                if xs.len() == 0 {
                    Err(NErr::index_error("Empty, can't cyclic index".to_string()))
                } else {
                    Ok(n.rem_euclid(xs.len() as isize) as usize)
                }
            }
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

fn soft_from_utf8(bs: Vec<u8>) -> Obj {
    match String::from_utf8(bs) {
        Ok(s) => Obj::from(s),
        Err(e) => Obj::Seq(Seq::Bytes(Rc::new(e.into_bytes()))),
    }
}

// caller has done as_bytes and any pythonic index calculations
// weird semantics but fine I guess
fn weird_string_as_bytes_index(s: &[u8], i: usize) -> Obj {
    soft_from_utf8(s[i..i + 1].to_vec())
}

fn linear_index_isize(xr: Seq, i: isize) -> NRes<Obj> {
    match xr {
        Seq::List(xx) => Ok(xx[pythonic_index_isize(&xx, i)?].clone()),
        Seq::Vector(x) => Ok(Obj::Num(x[pythonic_index_isize(&x, i)?].clone())),
        Seq::Bytes(x) => Ok(Obj::from(x[pythonic_index_isize(&x, i)?] as usize)),
        Seq::String(s) => {
            let bs = s.as_bytes();
            let i = pythonic_index_isize(bs, i)?;
            Ok(soft_from_utf8(bs[i..i + 1].to_vec()))
        }
        Seq::Stream(v) => v.pythonic_index_isize(i).ok_or(NErr::type_error(format!(
            "Can't index stream {:?}[{:?}]",
            v, i
        ))),
        Seq::Dict(..) => Err(NErr::type_error(
            "dict is not a linear sequence".to_string(),
        )),
    }
}

fn index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, ir) {
        (Obj::Seq(s), ii) => match s {
            Seq::List(xx) => Ok(xx[pythonic_index(xx, &ii)?].clone()),
            Seq::String(s) => {
                let bs = s.as_bytes();
                let i = pythonic_index(bs, &ii)?;
                Ok(weird_string_as_bytes_index(bs, i))
            }
            Seq::Dict(xx, def) => {
                let k = to_key(ii)?;
                match xx.get(&k) {
                    Some(e) => Ok(e.clone()),
                    None => match def {
                        Some(d) => Ok((&**d).clone()),
                        None => Err(NErr::key_error(format!(
                            "Dictionary lookup: nothing at key {}[{}]",
                            FmtDictPairs(xx.iter(), &MyFmtFlags::budgeted_repr(6)),
                            k
                        ))),
                    },
                }
            }
            Seq::Vector(v) => Ok(Obj::Num(v[pythonic_index(v, &ii)?].clone())),
            Seq::Bytes(v) => Ok(Obj::from(v[pythonic_index(v, &ii)?] as usize)),
            Seq::Stream(v) => match ii {
                Obj::Num(ii) => match ii.to_isize() {
                    Some(n) => v.pythonic_index_isize(n).ok_or(NErr::type_error(format!(
                        "Can't index stream {:?}[{:?}]",
                        v, ii
                    ))),
                    _ => Err(NErr::index_error(format!(
                        "Index out of bounds of isize or non-integer: {:?}",
                        ii
                    ))),
                },
                _ => Err(NErr::index_error(format!(
                    "Invalid (non-numeric) index: {}",
                    FmtObj::debug(&ii)
                ))),
            },
        },
        (Obj::Func(_, Precedence(p, _)), Obj::Seq(Seq::String(k))) => match &**k {
            "precedence" => Ok(Obj::from(*p)),
            _ => Err(NErr::type_error(format!("can't index into func {:?}", k))),
        },
        (Obj::Instance(struc, fields), Obj::Func(Func::StructField(istruc, field_index), _)) => {
            if struc == &istruc {
                Ok(fields[field_index].clone())
            } else {
                Err(NErr::index_error(format!("wrong struct type",)))
            }
        }
        (xr, ir) => Err(NErr::type_error(format!(
            "can't index {}[{}]",
            FmtObj::debug(&xr),
            FmtObj::debug(&ir)
        ))),
    }
}

fn obj_cyclic_index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, ir) {
        (Obj::Seq(s), ii) => match s {
            Seq::List(xx) => Ok(xx[cyclic_index(xx, &ii)?].clone()),
            Seq::String(s) => {
                let bs = s.as_bytes();
                let i = cyclic_index(bs, &ii)?;
                Ok(weird_string_as_bytes_index(bs, i))
            }
            Seq::Dict(..) => Err(NErr::type_error(format!(
                "can't cyclically index {}[{}]",
                FmtObj::debug(&xr),
                FmtObj::debug(&ii)
            ))),
            Seq::Vector(xx) => Ok(Obj::Num(xx[cyclic_index(xx, &ii)?].clone())),
            Seq::Bytes(xx) => Ok(Obj::from(xx[cyclic_index(xx, &ii)?] as usize)),
            Seq::Stream(v) => Err(NErr::type_error(format!(
                "Can't cyclically index stream {:?}[{}]",
                v,
                FmtObj::debug(&ii)
            ))),
        },
        (xr, ir) => Err(NErr::type_error(format!(
            "can't cyclically index {}[{}]",
            FmtObj::debug(xr),
            FmtObj::debug(&ir)
        ))),
    }
}

fn slice_seq(xr: Seq, lo: Option<Obj>, hi: Option<Obj>) -> NRes<Obj> {
    match (&xr, lo, hi) {
        (Seq::List(xx), lo, hi) => {
            let (lo, hi) = pythonic_slice_obj(xx, lo.as_ref(), hi.as_ref())?;
            Ok(Obj::list(xx[lo..hi].to_vec()))
        }
        (Seq::String(s), lo, hi) => {
            let bs = s.as_bytes();
            let (lo, hi) = pythonic_slice_obj(bs, lo.as_ref(), hi.as_ref())?;
            Ok(soft_from_utf8(bs[lo..hi].to_vec()))
        }
        (Seq::Vector(s), lo, hi) => {
            let (lo, hi) = pythonic_slice_obj(s, lo.as_ref(), hi.as_ref())?;
            Ok(Obj::Seq(Seq::Vector(Rc::new(s[lo..hi].to_vec()))))
        }
        (Seq::Bytes(s), lo, hi) => {
            let (lo, hi) = pythonic_slice_obj(s, lo.as_ref(), hi.as_ref())?;
            Ok(Obj::Seq(Seq::Bytes(Rc::new(s[lo..hi].to_vec()))))
        }
        (Seq::Stream(s), lo, hi) => {
            let lo = obj_to_isize_slice_index(lo.as_ref())?;
            let hi = obj_to_isize_slice_index(hi.as_ref())?;
            Ok(Obj::Seq(s.pythonic_slice(lo, hi).ok_or(
                NErr::type_error(format!("can't slice {:?} {:?} {:?}", s, lo, hi)),
            )?))
        }
        (Seq::Dict(..), _, _) => Err(NErr::type_error(
            "can't slice dictionary".to_string()
        )),
    }
}

fn slice(xr: Obj, lo: Option<Obj>, hi: Option<Obj>) -> NRes<Obj> {
    match xr {
        Obj::Seq(s) => slice_seq(s, lo, hi),
        xr => Err(NErr::type_error(format!(
            "can't slice {} {:?} {:?}",
            FmtObj::debug(&xr),
            lo,
            hi
        ))),
    }
}

fn index_or_slice(xr: Obj, ir: &EvaluatedIndexOrSlice) -> NRes<Obj> {
    match ir {
        // FIXME can or should we push these clones down
        EvaluatedIndexOrSlice::Index(i) => index(xr, i.clone()),
        EvaluatedIndexOrSlice::Slice(i, j) => slice(xr, i.clone(), j.clone()),
    }
}

fn safe_index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, &ir) {
        (Obj::Null, _) => Ok(Obj::Null),
        (Obj::Seq(s), ii) => match s {
            Seq::String(s) => {
                let bs = s.as_bytes();
                match pythonic_index(bs, ii) {
                    Ok(i) => Ok(weird_string_as_bytes_index(bs, i)),
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
                    },
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
            Seq::Stream(v) => Err(NErr::type_error(format!(
                "Can't safe index stream {:?}[{}]",
                v,
                FmtObj::debug(&ir)
            ))),
        },
        _ => Err(NErr::type_error(format!(
            "Can't safe index {}[{}]",
            FmtObj::debug(&xr),
            FmtObj::debug(&ir)
        ))),
    }
}

fn call(env: &REnv, f: Obj, args: Vec<Obj>) -> NRes<Obj> {
    match f {
        Obj::Func(ff, _) => ff.run(env, args),
        _ => Err(NErr::type_error(format!(
            "Can't call non-function {}",
            FmtObj::debug(&f)
        ))),
    }
}

fn call_or_part_apply(env: &REnv, f: Obj, args: Vec<Obj>) -> NRes<Obj> {
    match f {
        Obj::Func(ff, _) => ff.run(env, args),
        f => match few(args) {
            Few::One(Obj::Func(f2, _)) => Ok(Obj::Func(
                Func::PartialApp1(Box::new(f2), Box::new(f)),
                Precedence::zero(),
            )),
            Few::One(f2) => Err(NErr::type_error(format!(
                "Can't call non-function {} (and argument {} not callable)",
                FmtObj::debug(&f),
                FmtObj::debug(&f2)
            ))),
            _ => Err(NErr::type_error(format!(
                "Can't call non-function {} (and more than one argument)",
                FmtObj::debug(&f)
            ))),
        },
    }
}

fn eval_lvalue_as_obj(env: &REnv, expr: &EvaluatedLvalue) -> NRes<Obj> {
    match expr {
        EvaluatedLvalue::Underscore => Err(NErr::syntax_error(
            "Can't evaluate underscore on LHS of assignment??".to_string(),
        )),
        EvaluatedLvalue::IndexedIdent(s, v) => {
            let mut sr = Env::try_borrow_get_var(env, s)?;
            for ix in v {
                sr = index_or_slice(sr, ix)?.clone();
            }
            Ok(sr)
        }
        EvaluatedLvalue::Annotation(s, _) => eval_lvalue_as_obj(env, s),
        EvaluatedLvalue::CommaSeq(v) => Ok(Obj::list(
            v.iter()
                .map(|e| Ok(eval_lvalue_as_obj(env, e)?))
                .collect::<NRes<Vec<Obj>>>()?,
        )),
        // maybe if commaseq eagerly looks for splats...
        EvaluatedLvalue::Splat(_) => Err(NErr::syntax_error(
            "Can't evaluate splat on LHS of assignment??".to_string(),
        )),
        EvaluatedLvalue::Or(..) => Err(NErr::syntax_error(
            "Can't evaluate or on LHS of assignment??".to_string(),
        )),
        // seems questionable
        EvaluatedLvalue::Literal(x) => Ok(x.clone()),
        EvaluatedLvalue::Destructure(..) => Err(NErr::syntax_error(
            "Can't evaluate destructure on LHS of assignment??".to_string(),
        )),
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

fn evaluate_for(
    env: &Rc<RefCell<Env>>,
    its: &[ForIteration],
    body: &LocExpr,
    callback: &mut impl FnMut(Obj) -> (),
) -> NRes<()> {
    match its {
        [] => match evaluate(env, body) {
            Ok(k) => Ok(callback(k)),
            // don't catch break, thonking
            Err(NErr::Continue) => Ok(()),
            Err(e) => Err(e),
        },
        [ForIteration::Iteration(ty, lvalue, expr), rest @ ..] => {
            let mut itr = evaluate(env, expr)?;
            match ty {
                ForIterationType::Normal => {
                    for x in mut_obj_into_iter(&mut itr, "for iteration")? {
                        let ee = Env::with_parent(env);
                        let p = eval_lvalue(&ee, lvalue)?;

                        // should assign take x
                        assign(&ee, &p, Some(&ObjType::Any), x, AssignMode::Assign)?;
                        evaluate_for(&ee, rest, body, callback)?;
                    }
                }
                ForIterationType::Item => {
                    for (k, v) in mut_obj_into_iter_pairs(&mut itr, "for (item) iteration")? {
                        let ee = Env::with_parent(env);
                        let p = eval_lvalue(&ee, lvalue)?;

                        // should assign take x
                        assign(
                            &ee,
                            &p,
                            Some(&ObjType::Any),
                            Obj::list(vec![key_to_obj(k), v]),
                            AssignMode::Assign,
                        )?;
                        evaluate_for(&ee, rest, body, callback)?;
                    }
                }
                ForIterationType::Declare => {
                    let ee = Env::with_parent(env);
                    let p = eval_lvalue(&ee, lvalue)?;
                    assign(&ee, &p, Some(&ObjType::Any), itr, AssignMode::Assign)?;

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

pub fn evaluate(env: &Rc<RefCell<Env>>, expr: &LocExpr) -> NRes<Obj> {
    match &expr.1 {
        Expr::Null => Ok(Obj::Null),
        Expr::IntLit(n) => Ok(Obj::from(n.clone())),
        Expr::RatLit(n) => Ok(Obj::from(NNum::from(n.clone()))),
        Expr::FloatLit(n) => Ok(Obj::from(*n)),
        Expr::ImaginaryFloatLit(n) => Ok(Obj::Num(NNum::Complex(Complex64::new(0.0, *n)))),
        Expr::StringLit(s) => Ok(Obj::Seq(Seq::String(Rc::clone(s)))),
        Expr::BytesLit(s) => Ok(Obj::Seq(Seq::Bytes(Rc::clone(s)))),
        Expr::Frozen(x) => Ok(x.clone()),
        Expr::FormatString(s) => {
            let mut acc = String::new();
            for x in s.iter() {
                match x {
                    Ok(c) => acc.push(*c),
                    Err((expr, flags)) => {
                        evaluate(env, &expr)?
                            .fmt_with(&mut acc, flags.clone())
                            .map_err(|e| NErr::io_error(format!("format string issue: {}", e)))?
                    }
                }
            }
            Ok(Obj::from(acc))
        }
        Expr::Ident(s) => add_trace(Env::try_borrow_get_var(env, s), format!("ident"), expr.0),
        Expr::Underscore => Err(NErr::syntax_error_loc(
            "Can't evaluate underscore".to_string(),
            "_".to_string(),
            expr.0,
        )),
        Expr::Index(x, i) => match (&**x, i) {
            (LocExpr(_, Expr::Underscore), IndexOrSlice::Index(i)) => match &**i {
                LocExpr(_, Expr::Underscore) => Ok(Obj::Func(
                    Func::IndexSection(None, None),
                    Precedence::zero(),
                )),
                i => Ok(Obj::Func(
                    Func::IndexSection(None, Some(Box::new(evaluate(env, i)?))),
                    Precedence::zero(),
                )),
            },
            (x, i) => {
                let xr = evaluate(env, x)?;
                let ir = eval_index_or_slice(env, i)?;
                index_or_slice(xr, &ir)
            }
        },
        Expr::Chain(op1, ops) => {
            if match &((**op1).1) {
                Expr::Underscore => true,
                _ => false,
            } || ops.iter().any(|(_op, e)| match &((**e).1) {
                Expr::Underscore => true,
                _ => false,
            }) {
                let v1 = match &((**op1).1) {
                    Expr::Underscore => None,
                    _ => Some(Box::new(evaluate(env, op1)?)),
                };
                let mut acc = Vec::new();
                for (oper, opd) in ops {
                    let oprr = evaluate(env, oper)?;
                    if let Obj::Func(b, prec) = oprr {
                        match &((**opd).1) {
                            Expr::Underscore => {
                                acc.push((oper.0, Box::new(b), prec, None));
                            }
                            _ => {
                                let oprd = evaluate(env, opd)?;
                                acc.push((oper.0, Box::new(b), prec, Some(Box::new(oprd))));
                            }
                        }
                    } else {
                        return Err(NErr::type_error(format!(
                            "Chain section cannot use nonblock in operand position: {:?}",
                            oprr
                        )));
                    }
                }
                Ok(Obj::Func(Func::ChainSection(v1, acc), Precedence::zero()))
            } else {
                let mut ev = ChainEvaluator::new(evaluate(env, op1)?);
                for (oper, opd) in ops {
                    let oprr = evaluate(env, oper)?;
                    if let Obj::Func(b, prec) = oprr {
                        let oprd = evaluate(env, opd)?;
                        ev.give(env, b, prec, oprd, oper.0)?;
                    } else {
                        return Err(NErr::type_error(format!(
                            "Chain cannot use nonblock in operand position: {:?}",
                            oprr
                        )));
                    }
                }
                ev.finish(env)
            }
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
        Expr::Coalesce(lhs, rhs) => {
            let lr = evaluate(env, lhs)?;
            if lr != Obj::Null {
                Ok(lr)
            } else {
                evaluate(env, rhs)
            }
        }
        Expr::Assign(every, pat, rhs) => {
            let p = add_trace(eval_lvalue(env, pat), format!("assign lvalue"), expr.0)?;
            let res = match &**rhs {
                LocExpr(_, Expr::CommaSeq(xs)) => Ok(Obj::list(eval_seq(env, xs)?)),
                _ => evaluate(env, rhs),
            }?;

            let ret = if *every {
                assign_every(&env, &p, None, res, AssignMode::Assign)
            } else {
                assign(&env, &p, None, res, AssignMode::Assign)
            };
            add_trace(ret, format!("assign"), expr.0)?;
            Ok(Obj::Null)
        }
        Expr::Annotation(s, _) => evaluate(env, s),
        Expr::Consume(pat) => match eval_lvalue(env, pat)? {
            EvaluatedLvalue::IndexedIdent(s, ixs) => try_borrow_nres(env, "env for pop", &s)?
                .modify_existing_var(&s, |(_type, vv)| {
                    modify_existing_index(
                        &mut *try_borrow_mut_nres(vv, "var for consume", &s)?,
                        &ixs,
                        |x| Ok(std::mem::take(x)),
                    )
                })
                .ok_or(NErr::type_error("failed to consume??".to_string()))?,
            _ => Err(NErr::type_error("can't consume, weird pattern".to_string())),
        },
        Expr::Pop(pat) => match eval_lvalue(env, pat)? {
            EvaluatedLvalue::IndexedIdent(s, ixs) => try_borrow_nres(env, "env for pop", &s)?
                .modify_existing_var(&s, |(_type, vv)| {
                    modify_existing_index(
                        &mut *try_borrow_mut_nres(vv, "var for pop", &s)?,
                        &ixs,
                        |x| match x {
                            Obj::Seq(Seq::List(xs)) => Rc::make_mut(xs)
                                .pop()
                                .ok_or(NErr::name_error("can't pop empty".to_string())),
                            _ => Err(NErr::type_error("can't pop".to_string())),
                        },
                    )
                })
                .ok_or(NErr::type_error("failed to pop??".to_string()))?,
            _ => Err(NErr::type_error("can't pop, weird pattern".to_string())),
        },
        Expr::Remove(pat) => {
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => match ixs.as_slice() {
                    [] => Err(NErr::value_error(
                        "can't remove flat identifier".to_string(),
                    )),
                    [rest @ .., last_i] => {
                        try_borrow_nres(env, "env for remove", &s)?
                            .modify_existing_var(&s, |(_type, vv)| {
                                modify_existing_index(
                                    &mut *try_borrow_mut_nres(vv, "var for remove", &s)?,
                                    &rest,
                                    |x| {
                                        match (x, last_i) {
                                            (
                                                Obj::Seq(Seq::List(xs)),
                                                EvaluatedIndexOrSlice::Index(i),
                                            ) => {
                                                let ii = pythonic_index(xs, i)?;
                                                Ok(Rc::make_mut(xs).remove(ii))
                                            }
                                            (
                                                Obj::Seq(Seq::List(xs)),
                                                EvaluatedIndexOrSlice::Slice(i, j),
                                            ) => {
                                                let (lo, hi) =
                                                    pythonic_slice_obj(xs, i.as_ref(), j.as_ref())?;
                                                Ok(Obj::list(
                                                    Rc::make_mut(xs).drain(lo..hi).collect(),
                                                ))
                                            }
                                            (
                                                Obj::Seq(Seq::Dict(xs, _)),
                                                EvaluatedIndexOrSlice::Index(i),
                                            ) => Rc::make_mut(xs)
                                                .remove(&to_key(i.clone())?)
                                                .ok_or(NErr::key_error(
                                                    "key not found in dict".to_string(),
                                                )),
                                            // TODO: remove parts of strings...
                                            // TODO: vecs, bytes...
                                            _ => Err(NErr::type_error("can't remove".to_string())),
                                        }
                                    },
                                )
                            })
                            .ok_or(NErr::name_error("var not found to remove".to_string()))?
                    }
                },
                _ => Err(NErr::type_error("can't pop, weird pattern".to_string())),
            }
        }
        Expr::Swap(a, b) => {
            let al = eval_lvalue(env, a)?;
            let bl = eval_lvalue(env, b)?;
            let ao = eval_lvalue_as_obj(env, &al)?;
            let bo = eval_lvalue_as_obj(env, &bl)?;
            assign(&env, &al, None, bo, AssignMode::Assign)?;
            assign(&env, &bl, None, ao, AssignMode::Assign)?;
            Ok(Obj::Null)
        }
        Expr::OpAssign(every, pat, op, rhs) => {
            if *every {
                let p = eval_lvalue(env, pat)?;
                match evaluate(env, op)? {
                    Obj::Func(ff, _) => {
                        let res = match &**rhs {
                            LocExpr(_, Expr::CommaSeq(xs)) => Ok(Obj::list(eval_seq(env, xs)?)),
                            _ => evaluate(env, rhs),
                        }?;
                        add_trace(
                            modify_every(env, &p, &mut |x| ff.run(env, vec![x, res.clone()])),
                            format!("op({})-assign", ff),
                            expr.0,
                        )?;
                        Ok(Obj::Null)
                    }
                    opv => Err(NErr::type_error(format!(
                        "Operator assignment: operator is not function {:?}",
                        opv
                    ))),
                }
            } else {
                let p = eval_lvalue(env, pat)?;
                let pv = eval_lvalue_as_obj(env, &p)?;
                match evaluate(env, op)? {
                    Obj::Func(ff, _) => {
                        let res = match &**rhs {
                            LocExpr(_, Expr::CommaSeq(xs)) => Ok(Obj::list(eval_seq(env, xs)?)),
                            _ => evaluate(env, rhs),
                        }?;
                        // Drop the Rc from the lvalue so that functions can try to consume it. We
                        // used to only do this when the function was pure, but that required a
                        // stupid amount of code to bookkeep and prevents users from writing
                        // consuming modifiers. Instead it's now enshrined into the semantics.
                        add_trace(
                            assign(&env, &p, None, Obj::Null, AssignMode::IgnoreExistingType),
                            format!("null-assign"),
                            expr.0,
                        )?;
                        let fres = ff.run(env, vec![pv, res])?;
                        add_trace(
                            assign(&env, &p, None, fres, AssignMode::Assign),
                            format!("op({})-assign", ff),
                            expr.0,
                        )?;
                        Ok(Obj::Null)
                    }
                    opv => Err(NErr::type_error(format!(
                        "Operator assignment: operator is not function {:?}",
                        opv
                    ))),
                }
            }
        }
        Expr::Call(f, args) => {
            let fr = match &**f {
                LocExpr(_, Expr::Underscore) => None,
                f => Some(evaluate(env, f)?),
            };
            // let a = eval_seq(env, args)?;
            //
            // check for underscores indicating a call section
            let mut acc: Result<Vec<Obj>, Vec<Option<Obj>>> = Ok(Vec::new());
            for x in args {
                acc = match (&**x, acc) {
                    (LocExpr(_, Expr::Underscore), Ok(v)) => {
                        let mut r = v.into_iter().map(|x| Some(x)).collect::<Vec<Option<Obj>>>();
                        r.push(None);
                        Err(r)
                    }
                    (LocExpr(_, Expr::Underscore), Err(mut a)) => {
                        a.push(None);
                        Err(a)
                    }
                    (e, Ok(mut v)) => {
                        v.push(evaluate(env, &e)?);
                        Ok(v)
                    }
                    (e, Err(mut a)) => {
                        a.push(Some(evaluate(env, &e)?));
                        Err(a)
                    }
                }
            }

            match (fr, acc) {
                // no section
                (Some(f), Ok(v)) => {
                    let fs = format!("call to {}", f);
                    add_trace(call_or_part_apply(env, f, v), fs, expr.0)
                }

                // some section
                (None, Ok(v)) => Ok(Obj::Func(
                    Func::CallSection(
                        None,
                        v.into_iter().map(|x| Some(x)).collect::<Vec<Option<Obj>>>(),
                    ),
                    Precedence::zero(),
                )),
                (f, Err(v)) => Ok(Obj::Func(
                    Func::CallSection(f.map(Box::new), v),
                    Precedence::zero(),
                )),
            }
        }
        Expr::CommaSeq(_) => Err(NErr::syntax_error_loc(
            "Comma seqs only allowed directly on a side of an assignment (for now)".to_string(),
            "seq".to_string(),
            expr.0,
        )),
        Expr::Splat(_) => Err(NErr::syntax_error_loc(
            "Splats only allowed on an assignment-related place or in call or list (?)".to_string(),
            "splat".to_string(),
            expr.0,
        )),
        Expr::List(xs) => {
            let mut acc: Result<Vec<Obj>, Vec<Option<Obj>>> = Ok(Vec::new());
            for x in xs {
                acc = match (&**x, acc) {
                    (LocExpr(_, Expr::Underscore), Ok(v)) => {
                        let mut r = v.into_iter().map(|x| Some(x)).collect::<Vec<Option<Obj>>>();
                        r.push(None);
                        Err(r)
                    }
                    (LocExpr(_, Expr::Underscore), Err(mut a)) => {
                        a.push(None);
                        Err(a)
                    }
                    (e, Ok(mut v)) => {
                        v.push(evaluate(env, &e)?);
                        Ok(v)
                    }
                    (e, Err(mut a)) => {
                        a.push(Some(evaluate(env, &e)?));
                        Err(a)
                    }
                }
            }
            match acc {
                Ok(v) => Ok(Obj::list(v)),
                Err(e) => Ok(Obj::Func(Func::ListSection(e), Precedence::zero())),
            }
        }
        Expr::Vector(xs) => to_obj_vector(eval_seq(env, xs)?.into_iter().map(Ok)),
        Expr::Dict(def, xs) => {
            let dv = match def {
                Some(de) => Some(evaluate(env, de)?),
                None => None,
            };
            let mut acc = HashMap::new();
            for (ke, ve) in xs {
                match (&((**ke).1), ve) {
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
        Expr::Sequence(xs, ending_semicolon) => {
            for (i, x) in xs[..xs.len() - 1].iter().enumerate() {
                add_trace(
                    evaluate(env, x),
                    format!(";-sequence({}/{})", i + 1, xs.len()),
                    expr.0,
                )?;
            }
            let ret = add_trace(
                evaluate(env, xs.last().unwrap()),
                format!(";-sequence({}/{})", xs.len(), xs.len()),
                expr.0,
            )?;
            if *ending_semicolon {
                Ok(Obj::Null)
            } else {
                Ok(ret)
            }
        }
        Expr::If(cond, if_body, else_body) => {
            let cr = add_trace(evaluate(env, cond), "if-cond".to_string(), expr.0)?;
            if cr.truthy() {
                add_trace(evaluate(env, if_body), "if-branch".to_string(), expr.0)
            } else {
                match else_body {
                    Some(b) => add_trace(evaluate(env, b), "else-branch".to_string(), expr.0),
                    None => Ok(Obj::Null),
                }
            }
        }
        Expr::For(iteratees, do_yield, body) => {
            add_trace(
                if *do_yield {
                    let mut acc = Vec::new();
                    let mut f = |e| acc.push(e);
                    match evaluate_for(env, iteratees.as_slice(), body, &mut f) {
                        Ok(()) | Err(NErr::Break(Obj::Null)) => Ok(Obj::list(acc)),
                        Err(NErr::Break(e)) => Ok(e), // ??????
                        Err(e) => Err(e),
                    }
                } else {
                    match evaluate_for(env, iteratees.as_slice(), body, &mut |_| ()) {
                        Ok(()) => Ok(Obj::Null),
                        Err(NErr::Break(e)) => Ok(e),
                        Err(e) => Err(e),
                    }
                },
                "for loop".to_string(),
                expr.0,
            )
        }
        Expr::While(cond, body) => {
            // FIXME :(
            loop {
                let ee = Env::with_parent(env);
                if !(add_trace(evaluate(&ee, cond), "while-cond".to_string(), expr.0)?.truthy()) {
                    return Ok(Obj::Null);
                }
                match add_trace(evaluate(&ee, body), "while-body".to_string(), expr.0) {
                    Ok(_) => (),
                    Err(NErr::Break(e)) => return Ok(e),
                    Err(NErr::Continue) => continue,
                    Err(e) => return Err(e),
                }
            }
        }
        Expr::Switch(scrutinee, arms) => {
            let s = add_trace(evaluate(env, scrutinee), "switchee".to_string(), expr.0)?;
            for (pat, body) in arms {
                let ee = Env::with_parent(env);
                let p = eval_lvalue(&ee, pat)?;
                // drop asap
                // TODO this clone isn't great but isn't trivial to eliminate. maybe pattern match
                // errors should return the assigned object back or something?? idk
                // TODO: only catch pattern match errors tbh
                let ret = assign(
                    &ee,
                    &p,
                    Some(&ObjType::Any),
                    s.clone(),
                    AssignMode::PatternMatch,
                );
                match ret {
                    Ok(()) => {
                        std::mem::drop(s);
                        return add_trace(evaluate(&ee, body), "switch-case".to_string(), expr.0);
                    }
                    Err(_) => continue,
                };
            }
            // error??
            Ok(Obj::Null)
        }
        Expr::Try(body, pat, catcher) => {
            match evaluate(env, body) {
                x @ (Ok(_) | Err(NErr::Break(_) | NErr::Continue | NErr::Return(_))) => x,
                Err(NErr::Throw(e, trace)) => {
                    let ee = Env::with_parent(env);
                    let p = eval_lvalue(&ee, pat)?;
                    // drop asap
                    // TODO as above, this clone isn't great but isn't trivial to eliminate
                    let ret = assign(
                        &ee,
                        &p,
                        Some(&ObjType::Any),
                        e.clone(),
                        AssignMode::PatternMatch,
                    );
                    match ret {
                        Ok(()) => {
                            std::mem::drop(e);
                            return evaluate(&ee, catcher);
                        }
                        Err(_) => Err(NErr::Throw(e, trace)),
                    }
                }
            }
        }
        Expr::Throw(body) => Err(NErr::Throw(
            evaluate(&env, body)?,
            vec![("throw".to_string(), expr.0, None)],
        )),
        Expr::Lambda(params, body) => Ok(Obj::Func(
            Func::Closure(Closure {
                params: Rc::clone(params),
                body: Rc::clone(body),
                env: Rc::clone(env),
            }),
            Precedence::zero(),
        )),
        Expr::Backref(i) => {
            try_borrow_nres(env, "backref", &format!("{}", i))?.mut_top_env(|top| {
                match if *i == 0 {
                    top.backrefs.last()
                } else {
                    top.backrefs.get(i - 1)
                } {
                    Some(x) => Ok(x.clone()),
                    None => Err(NErr::index_error("no such backref".to_string())),
                }
            })
        }
        Expr::Struct(name, field_names) => {
            let s = Struct::new(field_names.len(), name.clone());
            assign(
                &env,
                &EvaluatedLvalue::IndexedIdent((&**name).clone(), Vec::new()),
                Some(&ObjType::Func),
                Obj::Func(Func::Type(ObjType::Struct(s.clone())), Precedence::zero()),
                AssignMode::Assign,
            )?;
            for (i, field) in field_names.iter().enumerate() {
                assign(
                    &env,
                    &EvaluatedLvalue::IndexedIdent((&**field).clone(), Vec::new()),
                    Some(&ObjType::Func),
                    Obj::Func(Func::StructField(s.clone(), i), Precedence::zero()),
                    AssignMode::Assign,
                )?;
            }
            Ok(Obj::Null)
        }
        Expr::Freeze(expr) => {
            let mut bound = HashSet::new();
            evaluate(env, &freeze(&mut bound, env, expr)?)
        }
        Expr::Literally(_) => Err(NErr::syntax_error_loc(
            "'literally' can only be in lvalues / patterns".to_string(),
            "literally".to_string(),
            expr.0,
        )),
        Expr::Break(Some(e)) => Err(NErr::Break(evaluate(env, e)?)),
        Expr::Break(None) => Err(NErr::Break(Obj::Null)),
        Expr::Continue => Err(NErr::Continue),
        Expr::Return(Some(e)) => Err(NErr::Return(evaluate(env, e)?)),
        Expr::Return(None) => Err(NErr::Return(Obj::Null)),
    }
}

fn vec_box_freeze(
    bound: &mut HashSet<String>,
    env: &Rc<RefCell<Env>>,
    expr: &Vec<Box<LocExpr>>,
) -> NRes<Vec<Box<LocExpr>>> {
    expr.iter().map(|x| box_freeze(bound, env, x)).collect()
}
fn box_freeze(
    bound: &mut HashSet<String>,
    env: &Rc<RefCell<Env>>,
    expr: &Box<LocExpr>,
) -> NRes<Box<LocExpr>> {
    Ok(Box::new(freeze(bound, env, expr)?))
}
fn opt_box_freeze(
    bound: &mut HashSet<String>,
    env: &Rc<RefCell<Env>>,
    expr: &Option<Box<LocExpr>>,
) -> NRes<Option<Box<LocExpr>>> {
    match expr {
        Some(x) => Ok(Some(Box::new(freeze(bound, env, x)?))),
        None => Ok(None),
    }
}

fn opt_rc_freeze(
    bound: &mut HashSet<String>,
    env: &Rc<RefCell<Env>>,
    expr: &Option<Rc<LocExpr>>,
) -> NRes<Option<Rc<LocExpr>>> {
    match expr {
        Some(x) => Ok(Some(Rc::new(freeze(bound, env, x)?))),
        None => Ok(None),
    }
}

fn box_freeze_lvalue(
    bound: &mut HashSet<String>,
    env: &Rc<RefCell<Env>>,
    lvalue: &Box<Lvalue>,
) -> NRes<Box<Lvalue>> {
    Ok(Box::new(freeze_lvalue(bound, env, lvalue)?))
}

fn freeze_lvalue(
    bound: &mut HashSet<String>,
    env: &Rc<RefCell<Env>>,
    lvalue: &Lvalue,
) -> NRes<Lvalue> {
    match lvalue {
        Lvalue::Underscore => Ok(Lvalue::Underscore),
        Lvalue::Literal(x) => Ok(Lvalue::Literal(x.clone())),
        Lvalue::IndexedIdent(s, ioses) => {
            if bound.contains(s) {
                Ok(Lvalue::IndexedIdent(
                    s.clone(),
                    ioses
                        .iter()
                        .map(|ios| freeze_ios(bound, env, ios))
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
            box_freeze_lvalue(bound, env, x)?,
            opt_rc_freeze(bound, env, e)?,
        )),
        Lvalue::CommaSeq(x) => Ok(Lvalue::CommaSeq(
            x.iter()
                .map(|e| box_freeze_lvalue(bound, env, e))
                .collect::<NRes<Vec<Box<Lvalue>>>>()?,
        )),
        Lvalue::Splat(x) => Ok(Lvalue::Splat(box_freeze_lvalue(bound, env, x)?)),
        Lvalue::Or(a, b) => Ok(Lvalue::Or(
            box_freeze_lvalue(bound, env, a)?,
            box_freeze_lvalue(bound, env, b)?,
        )),
        Lvalue::Destructure(f, args) => Ok(Lvalue::Destructure(
            box_freeze(bound, env, f)?,
            args.iter()
                .map(|e| box_freeze_lvalue(bound, env, e))
                .collect::<NRes<Vec<Box<Lvalue>>>>()?,
        )),
        Lvalue::ChainDestructure(f, args) => Ok(Lvalue::ChainDestructure(
            box_freeze_lvalue(bound, env, f)?,
            args.iter()
                .map(|(e, v)| {
                    Ok((
                        box_freeze(bound, env, e)?,
                        box_freeze_lvalue(bound, env, v)?,
                    ))
                })
                .collect::<NRes<Vec<(Box<LocExpr>, Box<Lvalue>)>>>()?,
        )),
        Lvalue::Literally(e) => Ok(Lvalue::Literally(box_freeze(bound, env, e)?)),
    }
}

fn freeze_ios(
    bound: &mut HashSet<String>,
    env: &Rc<RefCell<Env>>,
    ios: &IndexOrSlice,
) -> NRes<IndexOrSlice> {
    match ios {
        IndexOrSlice::Index(i) => Ok(IndexOrSlice::Index(box_freeze(bound, env, i)?)),
        IndexOrSlice::Slice(i, j) => Ok(IndexOrSlice::Slice(
            opt_box_freeze(bound, env, i)?,
            opt_box_freeze(bound, env, j)?,
        )),
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

fn freeze(bound: &mut HashSet<String>, env: &Rc<RefCell<Env>>, expr: &LocExpr) -> NRes<LocExpr> {
    Ok(LocExpr(
        expr.0,
        match &expr.1 {
            Expr::Null => Ok(Expr::Null),
            Expr::IntLit(x) => Ok(Expr::IntLit(x.clone())),
            Expr::RatLit(x) => Ok(Expr::RatLit(x.clone())),
            Expr::FloatLit(x) => Ok(Expr::FloatLit(x.clone())),
            Expr::ImaginaryFloatLit(x) => Ok(Expr::ImaginaryFloatLit(x.clone())),
            Expr::StringLit(x) => Ok(Expr::StringLit(x.clone())),
            Expr::BytesLit(x) => Ok(Expr::BytesLit(x.clone())),
            Expr::Backref(x) => Ok(Expr::Backref(x.clone())),
            Expr::Frozen(x) => Ok(Expr::Frozen(x.clone())),
            Expr::Struct(name, field_names) => Ok(Expr::Struct(name.clone(), field_names.clone())),

            Expr::FormatString(s) => Ok(Expr::FormatString(
                s.iter()
                    .map(|x| match x {
                        Ok(c) => Ok(Ok(*c)),
                        Err((e, ff)) => Ok(Err((freeze(bound, env, e)?, ff.clone()))),
                    })
                    .collect::<NRes<Vec<Result<char, (LocExpr, MyFmtFlags)>>>>()?,
            )),
            Expr::Ident(s) => {
                if bound.contains(s) {
                    Ok(Expr::Ident(s.clone()))
                } else {
                    Ok(Expr::Frozen(Env::try_borrow_get_var(env, s)?))
                }
            }
            Expr::Underscore => Err(NErr::syntax_error("Can't freeze underscore".to_string())),
            Expr::Index(x, ios) => Ok(Expr::Index(
                box_freeze(bound, env, x)?,
                freeze_ios(bound, env, ios)?,
            )),
            Expr::Chain(op1, ops) => Ok(Expr::Chain(
                box_freeze(bound, env, op1)?,
                ops.iter()
                    .map(|(op, d)| Ok((box_freeze(bound, env, op)?, box_freeze(bound, env, d)?)))
                    .collect::<NRes<Vec<(Box<LocExpr>, Box<LocExpr>)>>>()?,
            )),
            Expr::And(lhs, rhs) => Ok(Expr::And(
                box_freeze(bound, env, lhs)?,
                box_freeze(bound, env, rhs)?,
            )),
            Expr::Or(lhs, rhs) => Ok(Expr::Or(
                box_freeze(bound, env, lhs)?,
                box_freeze(bound, env, rhs)?,
            )),
            Expr::Coalesce(lhs, rhs) => Ok(Expr::Coalesce(
                box_freeze(bound, env, lhs)?,
                box_freeze(bound, env, rhs)?,
            )),
            Expr::Assign(every, pat, rhs) => {
                // have to bind first so box_freeze_lvalue works
                // also recursive functions work ig
                bound.extend(pat.collect_identifiers(true /* declared_only */));

                let lvalue = box_freeze_lvalue(bound, env, pat)?;
                Ok(Expr::Assign(*every, lvalue, box_freeze(bound, env, rhs)?))
            }
            Expr::Annotation(s, t) => Ok(Expr::Annotation(
                box_freeze(bound, env, s)?,
                opt_rc_freeze(bound, env, t)?,
            )),
            Expr::Consume(pat) => Ok(Expr::Consume(box_freeze_lvalue(bound, env, pat)?)),
            Expr::Pop(pat) => Ok(Expr::Pop(box_freeze_lvalue(bound, env, pat)?)),
            Expr::Remove(pat) => Ok(Expr::Remove(box_freeze_lvalue(bound, env, pat)?)),
            Expr::Swap(a, b) => Ok(Expr::Swap(
                box_freeze_lvalue(bound, env, a)?,
                box_freeze_lvalue(bound, env, b)?,
            )),
            Expr::OpAssign(every, pat, op, rhs) => Ok(Expr::OpAssign(
                *every,
                box_freeze_lvalue(bound, env, pat)?,
                box_freeze(bound, env, op)?,
                box_freeze(bound, env, rhs)?,
            )),
            Expr::Call(f, args) => Ok(Expr::Call(
                box_freeze(bound, env, f)?,
                vec_box_freeze(bound, env, args)?,
            )),
            Expr::CommaSeq(s) => Ok(Expr::CommaSeq(vec_box_freeze(bound, env, s)?)),
            Expr::Splat(s) => Ok(Expr::Splat(box_freeze(bound, env, s)?)),
            Expr::List(xs) => Ok(Expr::List(vec_box_freeze(bound, env, xs)?)),
            Expr::Vector(xs) => Ok(Expr::Vector(vec_box_freeze(bound, env, xs)?)),
            Expr::Dict(def, xs) => Ok(Expr::Dict(
                opt_box_freeze(bound, env, def)?,
                xs.iter()
                    .map(|(k, v)| Ok((box_freeze(bound, env, k)?, opt_box_freeze(bound, env, v)?)))
                    .collect::<NRes<Vec<(Box<LocExpr>, Option<Box<LocExpr>>)>>>()?,
            )),
            Expr::Sequence(xs, es) => Ok(Expr::Sequence(vec_box_freeze(bound, env, xs)?, *es)),
            Expr::If(a, b, c) => Ok(Expr::If(
                box_freeze(bound, env, a)?,
                box_freeze(bound, env, b)?,
                opt_box_freeze(bound, env, c)?,
            )),
            Expr::For(iteratees, do_yield, body) => {
                let mut bound2 = bound.clone();
                Ok(Expr::For(
                    iteratees
                        .iter()
                        .map(|x| match x {
                            ForIteration::Iteration(ty, lv, expr) => {
                                // have to bind first so box_freeze_lvalue works
                                // also recursive functions work ig
                                bound2.extend(lv.collect_identifiers(
                                    match ty {
                                        ForIterationType::Normal => false,
                                        ForIterationType::Item => false,
                                        ForIterationType::Declare => true, // thonk
                                    }, /* declared_only */
                                ));
                                Ok(ForIteration::Iteration(
                                    *ty,
                                    box_freeze_lvalue(&mut bound2, env, lv)?,
                                    box_freeze(&mut bound2, env, expr)?,
                                ))
                            }
                            ForIteration::Guard(expr) => {
                                Ok(ForIteration::Guard(box_freeze(&mut bound2, env, expr)?))
                            }
                        })
                        .collect::<NRes<Vec<ForIteration>>>()?,
                    *do_yield,
                    box_freeze(&mut bound2, env, body)?,
                ))
            }
            Expr::While(cond, body) => {
                let mut bound2 = bound.clone();
                Ok(Expr::While(
                    box_freeze(&mut bound2, env, cond)?,
                    box_freeze(&mut bound2, env, body)?,
                ))
            }
            Expr::Switch(scrutinee, arms) => Ok(Expr::Switch(
                box_freeze(bound, env, scrutinee)?,
                arms.iter()
                    .map(|(pat, rhs)| {
                        let mut bound2 = bound.clone();
                        bound2.extend(pat.collect_identifiers(false /* declared_only */));
                        Ok((
                            box_freeze_lvalue(&mut bound2, env, pat)?,
                            box_freeze(&mut bound2, env, rhs)?,
                        ))
                    })
                    .collect::<NRes<Vec<(Box<Lvalue>, Box<LocExpr>)>>>()?,
            )),
            Expr::Try(a, pat, catcher) => {
                // FIXME hmmm is the main try branch really scoped this way
                let body = box_freeze(bound, env, a)?;
                let mut bound2 = bound.clone();
                bound2.extend(pat.collect_identifiers(false /* declared_only */));
                Ok(Expr::Try(
                    body,
                    box_freeze_lvalue(&mut bound2, env, pat)?,
                    box_freeze(&mut bound2, env, catcher)?,
                ))
            }
            Expr::Lambda(params, body) => {
                let mut bound2 = bound.clone();
                bound2.extend(
                    params
                        .iter()
                        .flat_map(|x| x.collect_identifiers(false /* declared_only */)),
                );
                Ok(Expr::Lambda(
                    params.clone(),
                    Rc::new(freeze(&mut bound2, env, body)?),
                ))
            }
            Expr::Freeze(e) => Ok(Expr::Freeze(box_freeze(bound, env, e)?)),
            Expr::Literally(e) => Ok(Expr::Literally(box_freeze(bound, env, e)?)),

            Expr::Break(e) => Ok(Expr::Break(opt_box_freeze(bound, env, e)?)),
            Expr::Return(e) => Ok(Expr::Return(opt_box_freeze(bound, env, e)?)),
            Expr::Throw(e) => Ok(Expr::Throw(box_freeze(bound, env, e)?)),
            Expr::Continue => Ok(Expr::Continue),
        }?,
    ))
}

pub fn simple_eval(code: &str) -> Obj {
    let mut env = Env::empty();
    initialize(&mut env);

    let e = Rc::new(RefCell::new(env));
    evaluate(&e, &parse(code).unwrap().unwrap()).unwrap()
}

struct CommaSeparated<'a, T>(&'a [T]);

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

struct FmtSectionSlot<'a>(&'a Option<Obj>);

impl<'a> Display for FmtSectionSlot<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(t) => write!(formatter, "{}", FmtObj::debug(t)),
            None => write!(formatter, "_"),
        }
    }
}

struct FmtSectionBoxedSlot<'a>(&'a Option<Box<Obj>>);

impl<'a> Display for FmtSectionBoxedSlot<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(t) => write!(formatter, "{}", FmtObj::debug(&**t)),
            None => write!(formatter, "_"),
        }
    }
}

struct FmtSectionSlots<'a>(&'a [Option<Obj>]);

impl<'a> Display for FmtSectionSlots<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let mut started = false;
        for t in self.0 {
            if started {
                write!(formatter, ", ")?;
            }
            started = true;
            write!(formatter, "{}", FmtSectionSlot(t))?
        }
        Ok(())
    }
}

struct FmtSectionBoxedSlots<'a>(&'a [Option<Box<Obj>>]);

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

fn to_rc_vec_obj(a: Obj) -> NRes<Rc<Vec<Obj>>> {
    match a {
        Obj::Seq(Seq::List(v)) => Ok(v),
        mut a => Ok(Rc::new(mut_obj_into_iter(&mut a, "to_rc_vec")?.collect())),
    }
}

fn datetime_to_obj<Tz: TimeZone>(dt: DateTime<Tz>) -> Obj {
    let m = vec![
        ("year", Obj::from(BigInt::from(dt.year()))),
        ("month", Obj::from(BigInt::from(dt.month()))),
        ("day", Obj::from(BigInt::from(dt.day()))),
        ("hour", Obj::from(BigInt::from(dt.hour()))),
        ("minute", Obj::from(BigInt::from(dt.minute()))),
        ("second", Obj::from(BigInt::from(dt.second()))),
        ("nanosecond", Obj::from(BigInt::from(dt.nanosecond()))),
    ]
    .into_iter()
    .map(|(s, t)| (ObjKey::from(s), t))
    .collect::<HashMap<ObjKey, Obj>>();

    Obj::Seq(Seq::Dict(Rc::new(m), None))
}

// TODO some of these unwrap_or_clone's should be smarter, you can unwrap or iter
macro_rules! multi {
    ($name:ident, $expr:expr) => {
        match $name {
            Seq::List($name) => {
                let $name = unwrap_or_clone($name);
                Ok(Seq::List(Rc::new($expr?)))
            }
            Seq::String($name) => {
                let $name = unwrap_or_clone($name).drain(..).collect::<Vec<char>>();
                Ok(Seq::String(Rc::new($expr?.into_iter().collect::<String>())))
            }
            Seq::Dict($name, _def) => {
                let $name = unwrap_or_clone($name)
                    .into_keys()
                    .map(|k| key_to_obj(k))
                    .collect();
                Ok(Seq::List(Rc::new($expr?)))
            }
            Seq::Vector($name) => {
                let $name = unwrap_or_clone($name);
                Ok(Seq::Vector(Rc::new($expr?)))
            }
            Seq::Bytes($name) => {
                let $name = unwrap_or_clone($name);
                Ok(Seq::Bytes(Rc::new($expr?)))
            }
            Seq::Stream($name) => {
                let $name = $name
                    .force()
                    .ok_or(NErr::type_error("can't force this stream".to_string()))?;
                Ok(Seq::List(Rc::new($expr?)))
            }
        }
    };
}

fn reversed<T>(mut v: Vec<T>) -> NRes<Vec<T>> {
    v.reverse();
    Ok(v)
}
fn multi_reverse(v: Seq) -> NRes<Seq> {
    match v {
        Seq::Stream(s) => s.reversed().ok_or(NErr::type_error(format!(
            "can't reverse this stream {:?}",
            s
        ))),
        v => multi!(v, reversed(v)),
    }
}
fn sorted<T: PartialOrd>(mut v: Vec<T>) -> NRes<Vec<T>> {
    let mut ret = Ok(());
    v.sort_by(|a, b| {
        if ret.is_err() {
            return Ordering::Equal;
        }
        match a.partial_cmp(b) {
            Some(k) => k,
            None => {
                ret = Err(NErr::value_error("not comparable".to_string()));
                Ordering::Equal
            }
        }
    });
    ret?;
    Ok(v)
}
fn multi_sort(v: Seq) -> NRes<Seq> {
    multi!(v, sorted(v))
}
fn filtered<T: Clone + Into<Obj>>(env: &REnv, f: Func, v: Vec<T>, neg: bool) -> NRes<Vec<T>> {
    let mut ret = Vec::new();
    for x in v {
        if f.run(env, vec![x.clone().into()])?.truthy() != neg {
            ret.push(x)
        }
    }
    Ok(ret)
}
fn multi_filter(env: &REnv, f: Func, v: Seq, neg: bool) -> NRes<Seq> {
    multi!(v, filtered(env, f, v, neg))
}
fn sorted_by<T: Clone + Into<Obj>>(env: &REnv, f: Func, mut v: Vec<T>) -> NRes<Vec<T>> {
    let mut ret = Ok(());
    v.sort_by(|a, b| {
        if ret.is_err() {
            return Ordering::Equal;
        }
        match f.run(env, vec![a.clone().into(), b.clone().into()]) {
            Ok(k) => match ncmp(&k, &Obj::zero()) {
                Ok(ord) => ord,
                Err(e) => {
                    ret = Err(e);
                    Ordering::Equal
                }
            },
            Err(e) => {
                ret = Err(e);
                Ordering::Equal
            }
        }
    });
    ret?;
    Ok(v)
}
fn multi_sort_by(env: &REnv, f: Func, v: Seq) -> NRes<Seq> {
    multi!(v, sorted_by(env, f, v))
}
fn uniqued<T: Clone + Into<Obj>>(v: Vec<T>) -> NRes<Vec<T>> {
    let mut seen = HashSet::new();
    let mut ret = Vec::new();
    for x in v {
        if seen.insert(to_key(x.clone().into())?) {
            ret.push(x)
        }
    }
    Ok(ret)
}
fn multi_unique(v: Seq) -> NRes<Seq> {
    multi!(v, uniqued(v))
}

fn grouped<T>(mut it: impl Iterator<Item = T>, n: usize) -> Vec<Vec<T>> {
    let mut acc = Vec::new();
    let mut group = Vec::new();
    loop {
        for _ in 0..n {
            match it.next() {
                Some(obj) => group.push(obj),
                None => {
                    if !group.is_empty() {
                        acc.push(group);
                    }
                    return acc;
                }
            }
        }
        acc.push(std::mem::take(&mut group))
    }
}
fn grouped_by<T: Clone + Into<Obj>>(
    mut it: impl Iterator<Item = T>,
    mut f: impl FnMut(Obj, Obj) -> NRes<bool>,
) -> NRes<Vec<Vec<T>>> {
    let mut acc = Vec::new();
    let mut group: Vec<T> = Vec::new();
    loop {
        match it.next() {
            Some(obj) => {
                match group.last() {
                    None => {}
                    Some(prev) => {
                        if !f(prev.clone().into(), obj.clone().into())? {
                            acc.push(std::mem::take(&mut group))
                        }
                    }
                }
                group.push(obj)
            }
            None => {
                if !group.is_empty() {
                    acc.push(group)
                }
                return Ok(acc);
            }
        }
    }
}

fn windowed<T: Clone>(mut it: impl Iterator<Item = T>, n: usize) -> Vec<Vec<T>> {
    let mut window = VecDeque::new();
    window.reserve_exact(n);
    for _ in 0..n {
        match it.next() {
            Some(obj) => window.push_back(obj),
            None => return Vec::new(),
        }
    }
    let mut acc = vec![window.iter().cloned().collect()];
    while let Some(next) = it.next() {
        window.pop_front();
        window.push_back(next);
        acc.push(window.iter().cloned().collect());
    }
    acc
}

fn take_while_inner<T: Clone + Into<Obj>>(
    mut it: impl Iterator<Item = T>,
    env: &REnv,
    f: Func,
) -> NRes<Vec<T>> {
    let mut acc = Vec::new();
    while let Some(x) = it.next() {
        if f.run(env, vec![x.clone().into()])?.truthy() {
            acc.push(x)
        } else {
            return Ok(acc);
        }
    }
    Ok(acc)
}

// weird lil guy that doesn't fit
fn take_while(s: Seq, f: Func, env: &REnv) -> NRes<Obj> {
    match s {
        Seq::List(mut s) => Ok(Obj::list(take_while_inner(RcVecIter::of(&mut s), env, f)?)),
        Seq::String(mut s) => Ok(Obj::from(
            take_while_inner(RcStringIter::of(&mut s), env, f)?
                .into_iter()
                .collect::<String>(),
        )),
        Seq::Dict(mut s, _def) => Ok(Obj::list(take_while_inner(
            RcHashMapIter::of(&mut s).map(|(k, _v)| key_to_obj(k)),
            env,
            f,
        )?)),
        Seq::Vector(mut s) => Ok(Obj::Seq(Seq::Vector(Rc::new(take_while_inner(
            RcVecIter::of(&mut s),
            env,
            f,
        )?)))),
        Seq::Bytes(mut s) => Ok(Obj::Seq(Seq::Bytes(Rc::new(take_while_inner(
            RcVecIter::of(&mut s),
            env,
            f,
        )?)))),
        Seq::Stream(s) => Ok(Obj::list(take_while_inner(s.clone_box(), env, f)?)),
    }
}

fn drop_while_inner<T: Clone + Into<Obj>>(
    it: impl Iterator<Item = T>,
    env: &REnv,
    f: Func,
) -> NRes<impl Iterator<Item = T>> {
    let mut it = it.peekable();
    while let Some(x) = it.peek() {
        if f.run(env, vec![x.clone().into()])?.truthy() {
            it.next();
        } else {
            return Ok(it);
        }
    }
    Ok(it)
}

fn drop_while(s: Seq, f: Func, env: &REnv) -> NRes<Obj> {
    match s {
        Seq::List(mut s) => Ok(Obj::list(
            drop_while_inner(RcVecIter::of(&mut s), env, f)?.collect(),
        )),
        Seq::String(mut s) => Ok(Obj::from(
            drop_while_inner(RcStringIter::of(&mut s), env, f)?.collect::<String>(),
        )),
        Seq::Dict(mut s, _def) => Ok(Obj::list(
            drop_while_inner(
                RcHashMapIter::of(&mut s).map(|(k, _v)| key_to_obj(k)),
                env,
                f,
            )?
            .collect(),
        )),
        Seq::Vector(mut s) => Ok(Obj::Seq(Seq::Vector(Rc::new(
            drop_while_inner(RcVecIter::of(&mut s), env, f)?.collect(),
        )))),
        Seq::Bytes(mut s) => Ok(Obj::Seq(Seq::Bytes(Rc::new(
            drop_while_inner(RcVecIter::of(&mut s), env, f)?.collect(),
        )))),
        Seq::Stream(s) => {
            let mut t = s.clone_box();
            while let Some(x) = t.peek() {
                if f.run(env, vec![x.clone()])?.truthy() {
                    t.next();
                }
            }
            Ok(Obj::Seq(Seq::Stream(Rc::from(t))))
        }
    }
}

// also doesn't fit...
fn uncons(s: Seq) -> Option<(Obj, Seq)> {
    match s {
        Seq::List(mut s) => {
            if s.is_empty() {
                None
            } else {
                let head = Rc::make_mut(&mut s).remove(0);
                Some((head, Seq::List(s)))
            }
        }

        Seq::String(mut s) => {
            if s.is_empty() {
                None
            } else {
                let head = Rc::make_mut(&mut s).remove(0);
                Some((Obj::from(head), Seq::String(s)))
            }
        }
        Seq::Dict(mut s, def) => match s.keys().next().cloned() {
            Some(k) => match Rc::make_mut(&mut s).remove_entry(&k) {
                Some((kk, v)) => Some((Obj::list(vec![key_to_obj(kk), v]), Seq::Dict(s, def))),
                None => panic!("no"),
            },
            None => None,
        },
        Seq::Vector(mut s) => {
            if s.is_empty() {
                None
            } else {
                let head = Rc::make_mut(&mut s).remove(0);
                Some((Obj::from(head), Seq::Vector(s)))
            }
        }
        Seq::Bytes(mut s) => {
            if s.is_empty() {
                None
            } else {
                let head = Rc::make_mut(&mut s).remove(0);
                Some((Obj::from(head), Seq::Bytes(s)))
            }
        }
        Seq::Stream(s) => {
            let mut t = s.clone_box();
            match t.next() {
                None => None,
                Some(e) => Some((e, Seq::Stream(Rc::from(t)))),
            }
        }
    }
}
fn unsnoc(s: Seq) -> Option<(Seq, Obj)> {
    match s {
        Seq::List(mut s) => match Rc::make_mut(&mut s).pop() {
            None => None,
            Some(e) => Some((Seq::List(s), e)),
        },
        Seq::String(mut s) => match Rc::make_mut(&mut s).pop() {
            None => None,
            Some(e) => Some((Seq::String(s), Obj::from(e))),
        },
        dd @ Seq::Dict(..) => match uncons(dd) {
            None => None,
            Some((e, s)) => Some((s, e)),
        },
        Seq::Vector(mut s) => match Rc::make_mut(&mut s).pop() {
            None => None,
            Some(e) => Some((Seq::Vector(s), Obj::from(e))),
        },
        Seq::Bytes(mut s) => match Rc::make_mut(&mut s).pop() {
            None => None,
            Some(e) => Some((Seq::Bytes(s), Obj::from(e))),
        },
        Seq::Stream(s) => {
            match s.force() {
                None => None, // ???
                Some(v) => unsnoc(Seq::List(Rc::new(v))),
            }
        }
    }
}

fn prefixes<T: Clone>(mut it: impl Iterator<Item = T>) -> Vec<Vec<T>> {
    let mut prefix = Vec::new();
    let mut acc = vec![Vec::new()];
    while let Some(obj) = it.next() {
        prefix.push(obj);
        acc.push(prefix.clone());
    }
    acc
}
fn reversed_prefixes<T: Clone>(mut it: impl Iterator<Item = T>) -> Vec<Vec<T>> {
    let mut prefix = Vec::new();
    let mut acc = vec![Vec::new()];
    while let Some(obj) = it.next() {
        prefix.push(obj);
        let mut p = prefix.clone();
        p.reverse();
        acc.push(p);
    }
    acc
}

// just return Vec<Obj>
macro_rules! multimulti {
    ($name:ident, $expr:expr) => {
        match $name {
            Seq::List($name) => {
                let $name = unwrap_or_clone($name).into_iter();
                Ok($expr?.into_iter().map(|x| Obj::list(x)).collect())
            }
            Seq::String($name) => {
                let mut $name = unwrap_or_clone($name);
                let $name = $name.drain(..);
                Ok($expr?
                    .into_iter()
                    .map(|x| Obj::from(x.into_iter().collect::<String>()))
                    .collect())
            }
            Seq::Dict($name, _def) => {
                let $name = unwrap_or_clone($name).into_keys().map(|k| key_to_obj(k));
                Ok($expr?.into_iter().map(|x| Obj::list(x)).collect())
            }
            Seq::Vector($name) => {
                let $name = unwrap_or_clone($name).into_iter();
                Ok($expr?
                    .into_iter()
                    .map(|x| Obj::Seq(Seq::Vector(Rc::new(x))))
                    .collect())
            }
            Seq::Bytes($name) => {
                let $name = unwrap_or_clone($name).into_iter();
                Ok($expr?
                    .into_iter()
                    .map(|x| Obj::Seq(Seq::Bytes(Rc::new(x))))
                    .collect())
            }
            Seq::Stream($name) => {
                let $name = $name.clone_box();
                Ok($expr?.into_iter().map(|x| Obj::list(x)).collect())
            }
        }
    };
}

fn multi_group(v: Seq, n: usize) -> NRes<Vec<Obj>> {
    multimulti!(v, Ok(grouped(v, n)))
}
fn multi_group_by_eq(v: Seq) -> NRes<Vec<Obj>> {
    multimulti!(v, grouped_by(v, |a, b| Ok(a == b)))
}
fn multi_group_by(env: &REnv, f: Func, v: Seq) -> NRes<Vec<Obj>> {
    multimulti!(
        v,
        grouped_by(v, |a, b| Ok(f.run(env, vec![a, b])?.truthy()))
    )
}
fn multi_window(v: Seq, n: usize) -> NRes<Vec<Obj>> {
    multimulti!(v, Ok(windowed(v, n)))
}
fn multi_prefixes(v: Seq) -> NRes<Vec<Obj>> {
    multimulti!(v, Ok(prefixes(v)))
}
fn multi_suffixes(v: Seq) -> NRes<Vec<Obj>> {
    let v = multi_reverse(v)?;
    multimulti!(v, Ok(reversed_prefixes(v)))
}

fn json_encode(x: Obj) -> NRes<serde_json::Value> {
    match x {
        Obj::Null => Ok(serde_json::Value::Null),
        Obj::Num(NNum::Int(x)) => {
            if let Some(t) = x.to_i64() {
                Ok(serde_json::Value::from(t))
            } else {
                Ok(serde_json::Value::from(x.to_f64()))
            }
        }
        Obj::Num(x) => Ok(serde_json::Value::from(x.to_f64())),
        Obj::Seq(s) => match s {
            Seq::String(s) => Ok(serde_json::Value::String((&*s).clone())),
            Seq::Dict(d, _) => Ok(serde_json::Value::Object(
                unwrap_or_clone(d)
                    .into_iter()
                    .map(|(k, v)| Ok((format!("{}", k), json_encode(v.clone())?)))
                    .collect::<NRes<Vec<(String, serde_json::Value)>>>()?
                    .into_iter()
                    .collect::<serde_json::Map<String, serde_json::Value>>(),
            )),
            mut s => Ok(serde_json::Value::Array(
                mut_seq_into_iter(&mut s)
                    .into_iter()
                    .map(json_encode)
                    .collect::<NRes<Vec<serde_json::Value>>>()?,
            )),
        },
        s => Err(NErr::type_error(format!(
            "Can't serialize into JSON: {}",
            FmtObj::debug(&s)
        ))),
    }
}

fn json_decode(v: serde_json::Value) -> Obj {
    match v {
        serde_json::Value::Null => Obj::Null,
        serde_json::Value::Bool(x) => Obj::from(x),
        serde_json::Value::Number(n) => match n.as_i64() {
            Some(k) => Obj::from(BigInt::from(k)),
            None => Obj::from(n.as_f64().expect("json number should be f64 or i64")),
        },
        serde_json::Value::String(s) => Obj::from(s),
        serde_json::Value::Array(a) => {
            Obj::list(a.into_iter().map(json_decode).collect::<Vec<Obj>>())
        }
        serde_json::Value::Object(d) => Obj::Seq(Seq::Dict(
            Rc::new(
                d.into_iter()
                    .map(|(k, v)| (ObjKey::String(Rc::new(k)), json_decode(v)))
                    .collect::<HashMap<ObjKey, Obj>>(),
            ),
            None,
        )),
    }
}

pub fn initialize(env: &mut Env) {
    env.insert("true".to_string(), ObjType::Int, Obj::one())
        .unwrap();
    env.insert("false".to_string(), ObjType::Int, Obj::zero())
        .unwrap();
    env.insert_builtin(TwoArgBuiltin {
        name: "and'".to_string(),
        body: |a, b| Ok(if a.truthy() { b } else { a }),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "or'".to_string(),
        body: |a, b| Ok(if a.truthy() { a } else { b }),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "not".to_string(),
        body: |arg| Ok(Obj::from(!arg.truthy())),
    });

    env.insert_builtin(Plus);
    env.insert_builtin(Minus);
    env.insert_builtin(BasicBuiltin {
        name: "~".to_string(),
        body: |_env, args| match few2(args) {
            Few2::Zero => Err(NErr::argument_error("received 0 args".to_string())),
            Few2::One(s) => expect_nums_and_vectorize_1(|x| Ok(Obj::Num(!x)), s),
            Few2::Two(a, b) => expect_nums_and_vectorize_2(|a, b| Ok(Obj::Num(a ^ b)), a, b),
            Few2::Many(_) => Err(NErr::argument_error("received >2 args".to_string())),
        },
    });
    // for partial application
    env.insert_builtin(TwoNumsBuiltin {
        name: "subtract".to_string(),
        body: |a, b| Ok(Obj::Num(a - b)),
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "xor".to_string(),
        body: |a, b| Ok(Obj::Num(a ^ b)),
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "⊕".to_string(),
        body: |a, b| Ok(Obj::Num(a ^ b)),
    });
    env.insert_builtin(Times);
    env.insert_builtin(OneArgBuiltin {
        name: "sum".to_string(),
        body: |mut arg| {
            let mut acc = Obj::zero();
            for x in mut_obj_into_iter(&mut arg, "sum")? {
                acc = expect_nums_and_vectorize_2(|a, b| Ok(Obj::Num(a + b)), acc, x)?;
            }
            Ok(acc)
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "product".to_string(),
        body: |mut arg| {
            let mut acc = Obj::one();
            for x in mut_obj_into_iter(&mut arg, "product")? {
                acc = expect_nums_and_vectorize_2(|a, b| Ok(Obj::Num(a * b)), acc, x)?;
            }
            Ok(acc)
        },
    });
    env.insert_builtin(ComparisonOperator::of("==", |a, b| Ok(a == b)));
    env.insert_builtin(ComparisonOperator::of("!=", |a, b| Ok(a != b)));
    env.insert_builtin(ComparisonOperator::of("<", |a, b| {
        Ok(ncmp(a, b)? == Ordering::Less)
    }));
    env.insert_builtin(ComparisonOperator::of(">", |a, b| {
        Ok(ncmp(a, b)? == Ordering::Greater)
    }));
    env.insert_builtin_with_alias(
        ComparisonOperator::of("<=", |a, b| Ok(ncmp(a, b)? != Ordering::Greater)),
        "≤",
    );
    env.insert_builtin_with_alias(
        ComparisonOperator::of(">=", |a, b| Ok(ncmp(a, b)? != Ordering::Less)),
        "≥",
    );
    env.insert_builtin(Divide);
    env.insert_builtin(TwoNumsBuiltin {
        name: "%".to_string(),
        body: |a, b| Ok(Obj::Num(a % b)),
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "//".to_string(),
        body: |a, b| {
            if b.is_nonzero() {
                Ok(Obj::Num(a.div_floor(&b)))
            } else {
                Err(NErr::value_error("division by zero".to_string()))
            }
        },
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "%%".to_string(),
        body: |a, b| {
            if b.is_nonzero() {
                Ok(Obj::Num(a.mod_floor(&b)))
            } else {
                Err(NErr::value_error("division by zero".to_string()))
            }
        },
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "gcd".to_string(),
        body: |a, b| Ok(Obj::Num(a.gcd(&b))),
    });
    env.insert_rassoc_builtin(TwoNumsBuiltin {
        name: "^".to_string(),
        body: |a, b| Ok(Obj::Num(a.pow_num(&b))),
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "&".to_string(),
        body: |a, b| Ok(Obj::Num(a & b)),
    });
    env.insert_builtin(TwoNumsBuiltin {
        name: "|".to_string(),
        body: |a, b| Ok(Obj::Num(a | b)),
    });
    /*
    env.insert_builtin(TwoNumsBuiltin {
        name: "@".to_string(),
        body: |a, b| Ok(Obj::Num(a ^ b)),
    });
    */
    env.insert_builtin_with_precedence(
        TwoNumsBuiltin {
            name: "<<".to_string(),
            body: |a, b| Ok(Obj::Num(a << b)),
        },
        Precedence(EXPONENT_PRECEDENCE, Assoc::Left),
    );
    env.insert_builtin_with_precedence(
        TwoNumsBuiltin {
            name: ">>".to_string(),
            body: |a, b| Ok(Obj::Num(a >> b)),
        },
        Precedence(EXPONENT_PRECEDENCE, Assoc::Left),
    );
    env.insert_builtin(OneNumBuiltin {
        name: "abs".to_string(),
        body: |a| Ok(Obj::Num(a.abs())),
    });
    env.insert_builtin(OneNumBuiltin {
        name: "floor".to_string(),
        body: |a| {
            Ok(Obj::Num(a.floor().ok_or(NErr::value_error(
                "can't coerce to int".to_string(),
            ))?))
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "ceil".to_string(),
        body: |a| {
            Ok(Obj::Num(a.ceil().ok_or(NErr::value_error(
                "can't coerce to int".to_string(),
            ))?))
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "round".to_string(),
        body: |a| {
            Ok(Obj::Num(a.round().ok_or(NErr::value_error(
                "can't coerce to int".to_string(),
            ))?))
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "signum".to_string(),
        body: |a| Ok(Obj::Num(a.signum())),
    });
    env.insert_builtin(OneNumBuiltin {
        name: "even".to_string(),
        body: |a| {
            Ok(Obj::Num(NNum::iverson(
                !a.mod_floor(&NNum::from(2)).is_nonzero(),
            )))
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "odd".to_string(),
        body: |a| {
            Ok(Obj::Num(NNum::iverson(
                a.mod_floor(&NNum::from(2)) == NNum::from(1),
            )))
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "numerator".to_string(),
        body: |a| {
            a.numerator().map(Obj::from).ok_or(NErr::type_error(format!(
                "can't take numerator of non-rational"
            )))
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "denominator".to_string(),
        body: |a| {
            a.denominator()
                .map(Obj::from)
                .ok_or(NErr::type_error(format!(
                    "can't take denominator of non-rational"
                )))
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "real_part".to_string(),
        body: |a| match a.to_f64_or_inf_or_complex() {
            Ok(f) => Ok(Obj::from(f)),
            Err(c) => Ok(Obj::from(c.re)),
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "imag_part".to_string(),
        body: |a| match a.to_f64_or_inf_or_complex() {
            Ok(_) => Ok(Obj::from(0.0)),
            Err(c) => Ok(Obj::from(c.im)),
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "complex_parts".to_string(),
        body: |a| match a.to_f64_or_inf_or_complex() {
            Ok(f) => Ok(Obj::list(vec![Obj::from(f), Obj::from(0.0)])),
            Err(c) => Ok(Obj::list(vec![Obj::from(c.re), Obj::from(c.im)])),
        },
    });

    macro_rules! forward_f64 {
        ($name:ident) => {
            env.insert_builtin(OneNumBuiltin {
                name: stringify!($name).to_string(),
                body: |a| match a.to_f64_or_inf_or_complex() {
                    Ok(f) => Ok(Obj::from(f.$name())),
                    Err(c) => Ok(Obj::from(c.$name())),
                },
            });
        };
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
    forward_f64!(sqrt);
    forward_f64!(cbrt);
    forward_f64!(exp);
    forward_f64!(ln);
    forward_f64!(log10);
    forward_f64!(log2);
    env.insert_builtin(TwoNumsBuiltin {
        name: "atan2".to_string(),
        body: |a, b| match (a.to_f64(), b.to_f64()) {
            (Some(a), Some(b)) => Ok(Obj::from(f64::atan2(a, b))),
            (_, _) => Err(NErr::value_error("can't convert to float".to_string())),
        },
    });
    // forward_f64!(fract);
    // forward_f64!(exp_m1);
    // forward_f64!(ln_1p);

    env.insert_builtin(OneNumBuiltin {
        name: "is_prime".to_string(),
        body: |a| {
            Ok(Obj::Num(NNum::iverson(nnum::lazy_is_prime(
                &into_bigint_ok(a)?,
            ))))
        },
    });
    env.insert_builtin(OneNumBuiltin {
        name: "factorize".to_string(),
        body: |a| {
            Ok(Obj::list(
                nnum::lazy_factorize(into_bigint_ok(a)?)
                    .into_iter()
                    .map(|(a, e)| Obj::list(vec![Obj::from(a), Obj::from(e)]))
                    .collect(),
            ))
        },
    });
    env.insert_builtin(TilBuiltin);
    env.insert_builtin(ToBuiltin);
    env.insert_builtin(OneArgBuiltin {
        name: "ord".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => {
                if s.len() != 1 {
                    Err(NErr::value_error("arg string length != 1".to_string()))
                } else {
                    Ok(Obj::from(s.chars().next().unwrap() as usize))
                }
            }
            _ => Err(NErr::type_error("arg non-string".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "chr".to_string(),
        body: |arg| match arg {
            Obj::Num(n) => Ok(Obj::from(
                nnum::char_from_bigint(&into_bigint_ok(n)?)
                    .ok_or(NErr::value_error("chr of int oob".to_string()))?
                    .to_string(),
            )),
            _ => Err(NErr::type_error("not number".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "len".to_string(),
        body: |arg| match arg {
            Obj::Seq(s) => match s.len() {
                Some(n) => Ok(Obj::from(n)),
                None => Ok(Obj::from(f64::INFINITY)),
            },
            e => Err(NErr::type_error(format!(
                "sequence only, got {}",
                FmtObj::debug(&e)
            ))),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "then".to_string(),
        body: |env, a, b| call(env, b, vec![a]),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "apply".to_string(),
        body: |env, mut a, b| call(env, b, mut_obj_into_iter(&mut a, "apply")?.collect()),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "of".to_string(),
        body: |env, a, mut b| call(env, a, mut_obj_into_iter(&mut b, "of")?.collect()),
    });
    env.insert_builtin(Preposition("by".to_string()));
    env.insert_builtin(Preposition("with".to_string()));
    env.insert_builtin(Preposition("from".to_string()));
    env.insert_builtin(Preposition("default".to_string()));
    env.insert_builtin(TwoArgBuiltin {
        name: "in".to_string(),
        body: |a, b| Ok(Obj::from(obj_in(a, b)?)),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "∈".to_string(),
        body: |a, b| Ok(Obj::from(obj_in(a, b)?)),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "not_in".to_string(),
        body: |a, b| Ok(Obj::from(!obj_in(a, b)?)),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "∉".to_string(),
        body: |a, b| Ok(Obj::from(!obj_in(a, b)?)),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "contains".to_string(),
        body: |a, b| Ok(Obj::from(obj_in(b, a)?)),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "∋".to_string(),
        body: |a, b| Ok(Obj::from(obj_in(b, a)?)),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "∌".to_string(),
        body: |a, b| Ok(Obj::from(!obj_in(b, a)?)),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: ".".to_string(),
        body: |env, a, b| call(env, b, vec![a]),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: ".>".to_string(),
        body: |env, a, b| call(env, b, vec![a]),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "<.".to_string(),
        body: |env, a, b| call(env, a, vec![b]),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ">>>".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Func(f, _), Obj::Func(g, _)) => Ok(Obj::Func(
                Func::Composition(Box::new(g), Box::new(f)),
                Precedence::zero(),
            )),
            _ => Err(NErr::type_error("not function".to_string())),
        },
    });
    env.insert_builtin_with_alias(
        TwoArgBuiltin {
            name: "<<<".to_string(),
            body: |a, b| match (a, b) {
                (Obj::Func(f, _), Obj::Func(g, _)) => Ok(Obj::Func(
                    Func::Composition(Box::new(f), Box::new(g)),
                    Precedence::zero(),
                )),
                _ => Err(NErr::type_error("not function".to_string())),
            },
        },
        "∘",
    );
    env.insert_builtin(TwoArgBuiltin {
        name: "on".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Func(f, _), Obj::Func(g, _)) => Ok(Obj::Func(
                Func::OnComposition(Box::new(f), Box::new(g)),
                Precedence::zero(),
            )),
            _ => Err(NErr::type_error("not function".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "repeat".to_string(),
        body: |a| Ok(Obj::Seq(Seq::Stream(Rc::new(Repeat(a))))),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "cycle".to_string(),
        body: |a| Ok(Obj::Seq(Seq::Stream(Rc::new(Cycle(to_rc_vec_obj(a)?, 0))))),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "iota".to_string(),
        body: |a| match a {
            Obj::Num(NNum::Int(x)) => Ok(Obj::Seq(Seq::Stream(Rc::new(Range(
                x,
                None,
                BigInt::from(1),
            ))))),
            e => Err(NErr::argument_error_1(&e)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "permutations".to_string(),
        body: |a| {
            let v = to_rc_vec_obj(a)?;
            let iv = Rc::new((0..v.len()).collect());
            Ok(Obj::Seq(Seq::Stream(Rc::new(Permutations(v, Some(iv))))))
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "combinations".to_string(),
        body: |a, b| {
            let v = to_rc_vec_obj(a)?;
            match b {
                Obj::Num(n) => {
                    let u = n
                        .to_usize()
                        .ok_or(NErr::value_error("bad combo".to_string()))?;
                    let iv = Rc::new((0..u).collect());
                    Ok(Obj::Seq(Seq::Stream(Rc::new(Combinations(v, Some(iv))))))
                }
                b => Err(NErr::argument_error_second(&b)),
            }
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "subsequences".to_string(),
        body: |a| {
            let v = to_rc_vec_obj(a)?;
            let iv = Rc::new(vec![false; v.len()]);
            Ok(Obj::Seq(Seq::Stream(Rc::new(Subsequences(v, Some(iv))))))
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "iterate".to_string(),
        body: |env, a, f| match f {
            Obj::Func(f, _) => Ok(Obj::Seq(Seq::Stream(Rc::new(Iterate(Some((
                a,
                f,
                env.clone(),
            ))))))),
            f => Err(NErr::argument_error_2(&a, &f)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "each".to_string(),
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "each")?;
            match b {
                Obj::Func(b, _) => {
                    for e in it {
                        b.run(env, vec![e])?;
                    }
                    Ok(Obj::Null)
                }
                _ => Err(NErr::type_error("not callable".to_string())),
            }
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "map".to_string(),
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "map")?;
            match b {
                Obj::Func(b, _) => Ok(Obj::list(
                    it.map(|e| b.run(env, vec![e]))
                        .collect::<NRes<Vec<Obj>>>()?,
                )),
                _ => Err(NErr::type_error("not callable".to_string())),
            }
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "map_keys".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut d, def)), Obj::Func(b, _)) => Ok(Obj::dict(
                Rc::make_mut(&mut d)
                    .drain()
                    .map(|(k, v)| Ok((to_key(b.run(env, vec![key_to_obj(k)])?)?, v)))
                    .collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                def.map(|x| *x),
            )),
            _ => Err(NErr::type_error("not dict or callable".to_string())),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "map_values".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut d, def)), Obj::Func(b, _)) => Ok(Obj::dict(
                Rc::make_mut(&mut d)
                    .drain()
                    .map(|(k, v)| Ok((k, b.run(env, vec![v])?)))
                    .collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                match def {
                    Some(def) => Some(b.run(env, vec![*def])?),
                    None => None,
                },
            )),
            _ => Err(NErr::type_error("not dict or callable".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "flatten".to_string(),
        body: |mut a| {
            let mut acc = Vec::new();
            for mut e in mut_obj_into_iter(&mut a, "flatten (outer)")? {
                for k in mut_obj_into_iter(&mut e, "flatten (inner)")? {
                    acc.push(k);
                }
            }
            Ok(Obj::list(acc))
        },
    });
    // haxx
    env.insert_builtin(OneArgBuiltin {
        name: "keys".to_string(),
        body: |mut a| {
            let mut acc = Vec::new();
            for (k, _) in mut_obj_into_iter_pairs(&mut a, "keys")? {
                acc.push(key_to_obj(k));
            }
            Ok(Obj::list(acc))
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "values".to_string(),
        body: |mut a| {
            let mut acc = Vec::new();
            for (_, v) in mut_obj_into_iter_pairs(&mut a, "values")? {
                acc.push(v);
            }
            Ok(Obj::list(acc))
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "flat_map".to_string(),
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
                    Ok(Obj::list(acc))
                }
                _ => Err(NErr::type_error("not callable".to_string())),
            }
        },
    });
    // name from python itertools?
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "pairwise".to_string(),
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "pairwise")?;
            match b {
                Obj::Func(b, _) => Ok(Obj::list(
                    it.scan(None, |prev, a| {
                        let ret = match prev.take() {
                            Some(prev) => Some(b.run(env, vec![prev, a.clone()])),
                            None => None,
                        };
                        *prev = Some(a);
                        // this outer Some is used by the iterator protocol to mean continue
                        // iteration
                        Some(ret)
                    })
                    .flatten()
                    .collect::<NRes<Vec<Obj>>>()?,
                )),
                _ => Err(NErr::type_error("not callable".to_string())),
            }
        },
    });
    env.insert_builtin(Zip);
    env.insert_builtin(ZipLongest);
    env.insert_builtin(Parallel);
    env.insert_builtin(Fanout);
    env.insert_builtin(EnvOneArgBuiltin {
        name: "transpose".to_string(),
        body: |_env, a| {
            let mut v = to_rc_vec_obj(a)?;
            let v = Rc::make_mut(&mut v);
            let mut iterators: Vec<MutObjIntoIter<'_>> = Vec::new();
            for arg in v.iter_mut() {
                iterators.push(mut_obj_into_iter(arg, "zip")?)
            }
            let mut ret = Vec::new();
            loop {
                let batch = iterators
                    .iter_mut()
                    .flat_map(|a| a.next())
                    .collect::<Vec<Obj>>();
                if batch.is_empty() {
                    return Ok(Obj::list(ret));
                }
                ret.push(Obj::list(batch))
            }
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "filter".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(s), Obj::Func(f, _)) => {
                Ok(Obj::Seq(multi_filter(env, f, s, false /* neg */)?))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "reject".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(s), Obj::Func(f, _)) => {
                Ok(Obj::Seq(multi_filter(env, f, s, false /* neg */)?))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "partition".to_string(),
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "partition")?;
            match b {
                Obj::Func(b, _) => {
                    let mut acc_t = Vec::new();
                    let mut acc_f = Vec::new();
                    for e in it {
                        if b.run(env, vec![e.clone()])?.truthy() {
                            acc_t.push(e)
                        } else {
                            acc_f.push(e)
                        }
                    }
                    Ok(Obj::list(vec![Obj::list(acc_t), Obj::list(acc_f)]))
                }
                _ => Err(NErr::type_error("seq and func only".to_string())),
            }
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "any".to_string(),
        body: |env, args| match few2(args) {
            Few2::Zero => Err(NErr::argument_error("zero args".to_string())),
            Few2::One(mut a) => Ok(Obj::from(
                mut_obj_into_iter(&mut a, "any")?.any(|x| x.truthy()),
            )),
            Few2::Two(mut a, Obj::Func(b, _)) => {
                for e in mut_obj_into_iter(&mut a, "any")? {
                    if b.run(env, vec![e])?.truthy() {
                        return Ok(Obj::from(true));
                    }
                }
                Ok(Obj::from(false))
            }
            _ => Err(NErr::argument_error("too many args".to_string())),
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "all".to_string(),
        body: |env, args| match few2(args) {
            Few2::Zero => Err(NErr::argument_error("zero args".to_string())),
            Few2::One(mut a) => Ok(Obj::from(
                mut_obj_into_iter(&mut a, "all")?.all(|x| x.truthy()),
            )),
            Few2::Two(mut a, Obj::Func(b, _)) => {
                for e in mut_obj_into_iter(&mut a, "all")? {
                    if !b.run(env, vec![e])?.truthy() {
                        return Ok(Obj::from(false));
                    }
                }
                Ok(Obj::from(true))
            }
            Few2::Two(_, b) => Err(NErr::type_error(format!(
                "second arg not func: {}",
                FmtObj::debug(&b)
            ))),
            ff => Err(NErr::argument_error(format!("too many args: {:?}", ff))),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "count".to_string(),
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "count")?;
            let mut c = 0usize;
            match b {
                Obj::Func(b, _) => {
                    for e in it {
                        if b.run(env, vec![e])?.truthy() {
                            c += 1;
                        }
                    }
                }
                b => {
                    for e in it {
                        if e == b {
                            c += 1;
                        }
                    }
                }
            }
            Ok(Obj::from(c))
        },
    });
    env.insert_builtin(Group);
    env.insert_builtin(Merge);
    env.insert_builtin(OneArgBuiltin {
        name: "unique".to_string(),
        body: |a| match a {
            Obj::Seq(s) => Ok(Obj::Seq(multi_unique(s)?)),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "window".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(s), Obj::Num(n)) => match to_usize_ok(&n)? {
                0 => Err(NErr::value_error("can't window 0".to_string())),
                n => Ok(Obj::list(multi_window(s, n)?)),
            },
            _ => Err(NErr::value_error("not number".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "prefixes".to_string(),
        body: |a| match a {
            Obj::Seq(s) => Ok(Obj::list(multi_prefixes(s)?)),
            _ => Err(NErr::value_error("not number".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "suffixes".to_string(),
        body: |a| match a {
            Obj::Seq(s) => Ok(Obj::list(multi_suffixes(s)?)),
            _ => Err(NErr::value_error("not number".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "frequencies".to_string(),
        body: |mut a| {
            let it = mut_obj_into_iter(&mut a, "frequencies")?;
            let mut c = HashMap::<ObjKey, usize>::new();
            for e in it {
                *c.entry(to_key(e)?).or_insert(0) += 1;
            }
            Ok(Obj::Seq(Seq::Dict(
                Rc::new(c.into_iter().map(|(k, v)| (k, Obj::from(v))).collect()),
                Some(Box::new(Obj::zero())),
            )))
        },
    });
    env.insert_builtin(Fold);
    env.insert_builtin(Scan);
    env.insert_builtin(TwoArgBuiltin {
        name: "<=>".to_string(),
        body: |a, b| match ncmp(&a, &b) {
            Ok(Ordering::Less) => Ok(Obj::Num(-NNum::from(1))),
            Ok(Ordering::Equal) => Ok(Obj::zero()),
            Ok(Ordering::Greater) => Ok(Obj::Num(NNum::from(1))),
            Err(e) => Err(e),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ">=<".to_string(),
        body: |a, b| match ncmp(&a, &b) {
            Ok(Ordering::Less) => Ok(Obj::Num(NNum::from(1))),
            Ok(Ordering::Equal) => Ok(Obj::Num(NNum::from(0))),
            Ok(Ordering::Greater) => Ok(Obj::Num(-NNum::from(1))),
            Err(e) => Err(e),
        },
    });
    env.insert_builtin(Extremum {
        name: "max".to_string(),
        bias: Ordering::Greater,
    });
    env.insert_builtin(Extremum {
        name: "min".to_string(),
        bias: Ordering::Less,
    });
    env.insert_builtin(BasicBuiltin {
        name: "print".to_string(),
        body: |env, args| {
            try_borrow_nres(env, "print", &format!("{}", args.len()))?
                .mut_top_env(|t| -> io::Result<()> {
                    let mut started = false;
                    for arg in args.iter() {
                        if started {
                            write!(t.output, " ")?;
                        }
                        started = true;
                        write!(t.output, "{}", arg)?;
                    }
                    writeln!(t.output, "")?;
                    Ok(())
                })
                .map_err(|e| NErr::io_error(format!("writing {}", e)))?;
            Ok(Obj::Null)
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "write".to_string(),
        body: |env, args| {
            try_borrow_nres(env, "write", &format!("{}", args.len()))?
                .mut_top_env(|t| -> io::Result<()> {
                    for arg in args.iter() {
                        write!(t.output, "{}", arg)?;
                    }
                    Ok(())
                })
                .map_err(|e| NErr::io_error(format!("writing {}", e)))?;
            Ok(Obj::Null)
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "echo".to_string(),
        body: |env, args| {
            try_borrow_nres(env, "echo", &format!("{}", args.len()))?
                .mut_top_env(|t| -> io::Result<()> {
                    let mut started = false;
                    for arg in args.iter() {
                        if started {
                            write!(t.output, " ")?;
                        }
                        started = true;
                        write!(t.output, "{}", arg)?;
                    }
                    Ok(())
                })
                .map_err(|e| NErr::io_error(format!("writing {}", e)))?;
            Ok(Obj::Null)
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "debug".to_string(),
        body: |env, args| {
            try_borrow_nres(env, "debug", &format!("{}", args.len()))?
                .mut_top_env(|t| -> io::Result<()> {
                    let mut started = false;
                    for arg in args.iter() {
                        if started {
                            write!(t.output, " ")?;
                        }
                        started = true;
                        write!(t.output, "{}", FmtObj::debug(arg))?;
                    }
                    Ok(())
                })
                .map_err(|e| NErr::io_error(format!("writing {}", e)))?;
            Ok(Obj::Null)
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "is".to_string(),
        body: |a, b| Ok(Obj::from(is_type(&to_type(&b, "builtin 'is'")?, &a))),
    });
    env.insert_type(ObjType::Null);
    env.insert_type(ObjType::Int);
    env.insert_type(ObjType::Rational);
    env.insert_type(ObjType::Float);
    env.insert_type(ObjType::Complex);
    env.insert_type(ObjType::Number);
    env.insert_type(ObjType::String);
    env.insert_type(ObjType::List);
    env.insert_type(ObjType::Dict);
    env.insert_type(ObjType::Vector);
    env.insert_type(ObjType::Bytes);
    env.insert_type(ObjType::Stream);
    env.insert_type(ObjType::Func);
    env.insert_type(ObjType::Type);
    env.insert_type(ObjType::Any);
    env.insert_builtin(EnvOneArgBuiltin {
        name: "satisfying".to_string(),
        body: |env, arg| match arg {
            Obj::Func(f, _) => Ok(Obj::Func(
                Func::Type(ObjType::Satisfying(env.clone(), Box::new(f))),
                Precedence::zero(),
            )),
            _ => Err(NErr::type_error("expected func".to_string())),
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "$".to_string(),
        body: |_env, args| {
            let mut acc = String::new();
            for arg in args {
                acc += format!("{}", arg).as_str();
            }
            Ok(Obj::from(acc))
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "$$".to_string(),
        body: |a, b| Ok(Obj::from(format!("{}{}", a, b))),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "*$".to_string(),
        body: |a, b| {
            Ok(Obj::from(
                format!("{}", b).repeat(obj_clamp_to_usize_ok(&a)?),
            ))
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "$*".to_string(),
        body: |a, b| {
            Ok(Obj::from(
                format!("{}", a).repeat(obj_clamp_to_usize_ok(&b)?),
            ))
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "upper".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.to_uppercase())),
            _ => Err(NErr::type_error("expected string".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "lower".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.to_lowercase())),
            _ => Err(NErr::type_error("expected string".to_string())),
        },
    });
    // unlike python these are true on empty string. hmm...
    macro_rules! forward_char {
        ($name:expr, $pred:expr) => {
            env.insert_builtin(OneArgBuiltin {
                name: $name.to_string(),
                body: |arg| match arg {
                    Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.chars().all($pred))),
                    _ => Err(NErr::type_error("expected string".to_string())),
                },
            });
        };
    }
    forward_char!("is_upper", char::is_uppercase);
    forward_char!("is_alpha", char::is_alphabetic);
    forward_char!("is_alnum", char::is_alphanumeric);
    forward_char!("is_digit", char::is_numeric); // sketchy
    forward_char!("is_space", char::is_whitespace);
    forward_char!("is_lower", char::is_lowercase);
    forward_char!("is_ascii", |c| char::is_ascii(&c));

    env.insert_builtin(TwoArgBuiltin {
        name: "join".to_string(),
        body: |mut a, b| match b {
            Obj::Seq(Seq::Bytes(b)) => {
                let mut acc: Vec<u8> = Vec::new();
                let mut started = false;
                for mut arg in mut_obj_into_iter(&mut a, "join (bytes)")? {
                    if started {
                        acc.extend(b.iter())
                    }
                    started = true;
                    acc.extend(
                        mut_obj_into_iter(&mut arg, "join (bytes) byte conversion")?
                            .map(|e| to_byte(e, "join (bytes) byte conversion"))
                            .collect::<NRes<Vec<u8>>>()?
                            .iter(),
                    );
                }
                Ok(Obj::Seq(Seq::Bytes(Rc::new(acc))))
            }
            _ => Ok(Obj::from(simple_join(a, format!("{}", b).as_str())?)),
        },
    });
    // TODO: split with limit
    env.insert_builtin(TwoArgBuiltin {
        name: "split".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => Ok(Obj::list(
                s.split(&*t).map(|w| Obj::from(w.to_string())).collect(),
            )),
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "starts_with".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => {
                Ok(Obj::from(s.starts_with(&*t)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "ends_with".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => Ok(Obj::from(s.ends_with(&*t))),
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "strip".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.trim())),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "trim".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.trim())),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "words".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::list(
                s.split_whitespace().map(|w| Obj::from(w)).collect(),
            )),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "lines".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::list(
                s.split_terminator('\n')
                    .map(|w| Obj::from(w.to_string()))
                    .collect(),
            )),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "unwords".to_string(),
        body: |a| Ok(Obj::from(simple_join(a, " ")?)),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "unlines".to_string(),
        body: |a| {
            let mut s = simple_join(a, "\n")?;
            s.push('\n');
            Ok(Obj::from(s))
        },
    });

    env.insert_builtin(TwoArgBuiltin {
        name: "search".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                let r = Regex::new(&b)
                    .map_err(|e| NErr::value_error(format!("invalid regex: {}", e)))?;
                if r.capture_locations().len() == 1 {
                    match r.find(&a) {
                        None => Ok(Obj::Null),
                        Some(c) => Ok(Obj::from(c.as_str())),
                    }
                } else {
                    match r.captures(&a) {
                        None => Ok(Obj::Null),
                        Some(c) => Ok(captures_to_obj(&r, &c)),
                    }
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "search_all".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                let r = Regex::new(&b)
                    .map_err(|e| NErr::value_error(format!("invalid regex: {}", e)))?;
                if r.capture_locations().len() == 1 {
                    Ok(Obj::list(
                        r.find_iter(&a).map(|c| Obj::from(c.as_str())).collect(),
                    ))
                } else {
                    Ok(Obj::list(
                        r.captures_iter(&a)
                            .map(|c| {
                                Obj::list(
                                    c.iter()
                                        .map(|cap| match cap {
                                            None => Obj::Null, // didn't participate
                                            Some(s) => Obj::from(s.as_str()),
                                        })
                                        .collect(),
                                )
                            })
                            .collect(),
                    ))
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(Replace);

    // Haskell-ism for partial application (when that works)
    env.insert_builtin(TwoArgBuiltin {
        name: "!!".to_string(),
        body: index,
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "!?".to_string(),
        body: safe_index,
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "!%".to_string(),
        body: obj_cyclic_index,
    });

    // Lists
    env.insert_builtin_with_alias(
        TwoArgBuiltin {
            name: "++".to_string(),
            body: |a, b| match (a, b) {
                (Obj::Seq(Seq::List(mut a)), Obj::Seq(Seq::List(mut b))) => {
                    Rc::make_mut(&mut a).append(Rc::make_mut(&mut b));
                    Ok(Obj::Seq(Seq::List(a)))
                }
                (Obj::Seq(Seq::Vector(mut a)), Obj::Seq(Seq::Vector(mut b))) => {
                    Rc::make_mut(&mut a).append(Rc::make_mut(&mut b));
                    Ok(Obj::Seq(Seq::Vector(a)))
                }
                (Obj::Seq(Seq::Bytes(mut a)), Obj::Seq(Seq::Bytes(mut b))) => {
                    Rc::make_mut(&mut a).append(Rc::make_mut(&mut b));
                    Ok(Obj::Seq(Seq::Bytes(a)))
                }
                (a, b) => Err(NErr::argument_error_2(&a, &b)),
            },
        },
        "⧺",
    );
    env.insert_rassoc_builtin(TwoArgBuiltin {
        name: ".+".to_string(),
        body: |a, b| match b {
            Obj::Seq(Seq::List(mut b)) => {
                Rc::make_mut(&mut b).insert(0, a);
                Ok(Obj::Seq(Seq::List(b)))
            }
            Obj::Seq(Seq::Vector(mut b)) => {
                Rc::make_mut(&mut b).insert(0, to_nnum(a, "prepend to vector")?);
                Ok(Obj::Seq(Seq::Vector(b)))
            }
            Obj::Seq(Seq::Bytes(mut b)) => {
                Rc::make_mut(&mut b).insert(0, to_byte(a, "prepend to bytes")?);
                Ok(Obj::Seq(Seq::Bytes(b)))
            }
            b => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin_with_alias(
        TwoArgBuiltin {
            name: "append".to_string(),
            body: |a, b| match a {
                Obj::Seq(Seq::List(mut a)) => {
                    Rc::make_mut(&mut a).push(b);
                    Ok(Obj::Seq(Seq::List(a)))
                }
                Obj::Seq(Seq::Vector(mut a)) => {
                    Rc::make_mut(&mut a).push(to_nnum(b, "append to vector")?);
                    Ok(Obj::Seq(Seq::Vector(a)))
                }
                Obj::Seq(Seq::Bytes(mut a)) => {
                    Rc::make_mut(&mut a).push(to_byte(b, "append to bytes")?);
                    Ok(Obj::Seq(Seq::Bytes(a)))
                }
                a => Err(NErr::argument_error_2(&a, &b)),
            },
        },
        "+.",
    );
    env.insert_builtin(TwoArgBuiltin {
        name: "..".to_string(),
        body: |a, b| Ok(Obj::list(vec![a, b])),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "=>".to_string(),
        body: |a, b| Ok(Obj::list(vec![a, b])),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "*.".to_string(),
        body: |a, b| Ok(Obj::list(vec![b; obj_clamp_to_usize_ok(&a)?])),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ".*".to_string(),
        body: |a, b| Ok(Obj::list(vec![a; obj_clamp_to_usize_ok(&b)?])),
    });
    env.insert_builtin_with_alias(CartesianProduct, "×");
    env.insert_builtin(TwoArgBuiltin {
        name: "^^".to_string(),
        body: |a, b| {
            let v = to_rc_vec_obj(a)?;
            match b {
                Obj::Num(n) => {
                    let u = n
                        .to_usize()
                        .ok_or(NErr::value_error("bad lazy pow".to_string()))?;
                    Ok(Obj::Seq(Seq::Stream(Rc::new(CartesianPower(
                        v,
                        Some(Rc::new(vec![0; u])),
                    )))))
                }
                b => Err(NErr::argument_error_second(&b)),
            }
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "id".to_string(),
        body: |a| Ok(a),
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "const".to_string(),
        body: |_, b| Ok(b),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "flip".to_string(),
        body: |a| match a {
            Obj::Func(f, _) => Ok(Obj::Func(Func::Flip(Box::new(f)), Precedence::zero())),
            _ => Err(NErr::type_error("not function".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "first".to_string(),
        body: |a| match a {
            Obj::Seq(s) => linear_index_isize(s, 0),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "second".to_string(),
        body: |a| match a {
            Obj::Seq(s) => linear_index_isize(s, 1),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "third".to_string(),
        body: |a| match a {
            Obj::Seq(s) => linear_index_isize(s, 2),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "last".to_string(),
        body: |a| match a {
            Obj::Seq(s) => linear_index_isize(s, -1),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "tail".to_string(),
        body: |a| slice(a, Some(Obj::one()), None),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "butlast".to_string(),
        body: |a| slice(a, None, Some(Obj::from(BigInt::from(-1)))),
    });
    env.insert_builtin(OneArgBuiltin {
        name: "uncons".to_string(),
        body: |a| match a {
            Obj::Seq(s) => match uncons(s) {
                None => Err(NErr::index_error("Can't uncons empty (or infinite) seq".to_string())),
                Some((e, s)) => Ok(Obj::list(vec![e, Obj::Seq(s)])),
            }
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "unsnoc".to_string(),
        body: |a| match a {
            Obj::Seq(s) => match unsnoc(s) {
                None => Err(NErr::index_error("Can't unsnoc empty (or infinite) seq".to_string())),
                Some((s, e)) => Ok(Obj::list(vec![Obj::Seq(s), e])),
            }
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "uncons?".to_string(),
        body: |a| match a {
            Obj::Seq(s) => match uncons(s) {
                None => Ok(Obj::Null),
                Some((e, s)) => Ok(Obj::list(vec![e, Obj::Seq(s)])),
            }
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "unsnoc?".to_string(),
        body: |a| match a {
            Obj::Seq(s) => match unsnoc(s) {
                None => Ok(Obj::Null),
                Some((s, e)) => Ok(Obj::list(vec![Obj::Seq(s), e])),
            }
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "take".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(s), Obj::Func(f, _)) => take_while(s, f, env),
            (a, b) => slice(a, None, Some(b)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "drop".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(s), Obj::Func(f, _)) => drop_while(s, f, env),
            (a, b) => slice(a, Some(b), None),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "find".to_string(),
        body: |env, mut a, b| match b {
            Obj::Func(f, _) => {
                let mut it = mut_obj_into_iter(&mut a, "find")?;
                while let Some(x) = it.next() {
                    if f.run(env, vec![x.clone()])?.truthy() {
                        return Ok(x);
                    }
                }
                Err(NErr::value_error("didn't find".to_string()))
            }
            b => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "find?".to_string(),
        body: |env, mut a, b| match b {
            Obj::Func(f, _) => {
                let mut it = mut_obj_into_iter(&mut a, "find?")?;
                while let Some(x) = it.next() {
                    if f.run(env, vec![x.clone()])?.truthy() {
                        return Ok(x);
                    }
                }
                Ok(Obj::Null)
            }
            b => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "index".to_string(),
        body: |env, a, b| match (a, b) {
            (mut a, Obj::Func(f, _)) => {
                let mut it = mut_obj_into_iter(&mut a, "index")?.enumerate();
                while let Some((i, x)) = it.next() {
                    if f.run(env, vec![x.clone()])?.truthy() {
                        return Ok(Obj::from(i));
                    }
                }
                Err(NErr::value_error("didn't find".to_string()))
            }
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                match a.find(&*b) {
                    // this is the byte index! shrug
                    Some(i) => Ok(Obj::from(i)),
                    None => Err(NErr::value_error("didn't find".to_string())),
                }
            }
            (mut a, b) => {
                let mut it = mut_obj_into_iter(&mut a, "index")?.enumerate();
                while let Some((i, x)) = it.next() {
                    if x == b {
                        return Ok(Obj::from(i));
                    }
                }
                Err(NErr::value_error("didn't find".to_string()))
            }
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "index?".to_string(),
        body: |env, a, b| match (a, b) {
            (mut a, Obj::Func(f, _)) => {
                let mut it = mut_obj_into_iter(&mut a, "index?")?.enumerate();
                while let Some((i, x)) = it.next() {
                    if f.run(env, vec![x.clone()])?.truthy() {
                        return Ok(Obj::from(i));
                    }
                }
                Ok(Obj::Null)
            }
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                match a.find(&*b) {
                    // this is the byte index! shrug
                    Some(i) => Ok(Obj::from(i)),
                    None => Ok(Obj::Null),
                }
            }
            (mut a, b) => {
                let mut it = mut_obj_into_iter(&mut a, "index?")?.enumerate();
                while let Some((i, x)) = it.next() {
                    if x == b {
                        return Ok(Obj::from(i));
                    }
                }
                Ok(Obj::Null)
            }
        },
    });
    env.insert_builtin(Sort);
    env.insert_builtin(OneArgBuiltin {
        name: "reverse".to_string(),
        body: |a| match a {
            Obj::Seq(s) => Ok(Obj::Seq(multi_reverse(s)?)),
            a => Err(NErr::argument_error_1(&a)),
        },
    });

    // Dicts
    env.insert_builtin(TwoArgBuiltin {
        name: "||".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::Dict(mut b, _))) => {
                Rc::make_mut(&mut a).extend(Rc::make_mut(&mut b).drain());
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "|.".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), b) => {
                Rc::make_mut(&mut a).insert(to_key(b)?, Obj::Null);
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "discard".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), b) => {
                Rc::make_mut(&mut a).remove(&to_key(b)?);
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "-.".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), b) => {
                Rc::make_mut(&mut a).remove(&to_key(b)?);
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "insert".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(mut s)) => {
                let mut it = mut_seq_into_iter(&mut s);
                match (it.next(), it.next(), it.next()) {
                    (Some(k), Some(v), None) => {
                        // TODO maybe fail if key exists? have |.. = "upsert"?
                        Rc::make_mut(&mut a).insert(to_key(k.clone())?, v.clone());
                        Ok(Obj::Seq(Seq::Dict(a, d)))
                    }
                    _ => Err(NErr::argument_error("RHS must be pair".to_string())),
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "|..".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(mut s)) => {
                let mut it = mut_seq_into_iter(&mut s);
                match (it.next(), it.next(), it.next()) {
                    (Some(k), Some(v), None) => {
                        Rc::make_mut(&mut a).insert(to_key(k.clone())?, v.clone());
                        Ok(Obj::Seq(Seq::Dict(a, d)))
                    }
                    _ => Err(NErr::argument_error("RHS must be pair".to_string())),
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "&&".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::Dict(b, _))) => {
                Rc::make_mut(&mut a).retain(|k, _| b.contains_key(k));
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "--".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::Dict(b, _))) => {
                Rc::make_mut(&mut a).retain(|k, _| !b.contains_key(k));
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "set".to_string(),
        body: |mut a| {
            Ok(Obj::dict(
                mut_obj_into_iter(&mut a, "set conversion")?
                    .map(|k| Ok((to_key(k)?, Obj::Null)))
                    .collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                None,
            ))
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "items".to_string(),
        body: |a| match a {
            Obj::Seq(mut s @ Seq::Dict(..)) => Ok(Obj::list(
                mut_seq_into_iter_pairs(&mut s)
                    .map(|(k, v)| Obj::list(vec![key_to_obj(k), v]))
                    .collect(),
            )),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "enumerate".to_string(),
        body: |mut a| {
            Ok(Obj::list(
                mut_obj_into_iter(&mut a, "enumerate conversion")?
                    .enumerate()
                    .map(|(k, v)| Obj::list(vec![Obj::from(k), v]))
                    .collect(),
            ))
        },
    });

    env.insert_builtin(EnvOneArgBuiltin {
        name: "eval".to_string(),
        body: |env, a| match a {
            Obj::Seq(Seq::String(r)) => match match parse(&r) {
                Ok(Some(code)) => evaluate(env, &code),
                Ok(None) => Err(NErr::value_error("eval: empty expression".to_string())),
                Err(s) => Err(NErr::value_error(s.render(&r))),
            } {
                Ok(x) => Ok(x),
                Err(mut e) => {
                    e.supply_source(Rc::new("<eval>".to_string()), r);
                    Err(e)
                }
            },
            s => Err(NErr::value_error(format!("can't eval {:?}", s))),
        },
    });

    env.insert_builtin(BasicBuiltin {
        name: "input".to_string(),
        body: |env, args| {
            if args.is_empty() {
                let mut input = String::new();
                match try_borrow_nres(env, "input", "")?
                    .mut_top_env(|t| t.input.read_line(&mut input))
                {
                    Ok(_) => Ok(Obj::from(input)),
                    Err(msg) => Err(NErr::value_error(format!("input failed: {}", msg))),
                }
            } else {
                Err(NErr::argument_error_args(&args))
            }
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "read".to_string(),
        body: |env, args| {
            if args.is_empty() {
                let mut input = String::new();
                // to EOF
                match try_borrow_nres(env, "read", "")?
                    .mut_top_env(|t| t.input.read_to_string(&mut input))
                {
                    Ok(_) => Ok(Obj::from(input)),
                    Err(msg) => Err(NErr::value_error(format!("input failed: {}", msg))),
                }
            } else {
                Err(NErr::argument_error_args(&args))
            }
        },
    });
    // Haskell-ism
    env.insert_builtin(EnvOneArgBuiltin {
        name: "interact".to_string(),
        body: |env, arg| {
            match arg {
                Obj::Func(f, _) => {
                    let mut input = String::new();
                    // to EOF
                    match try_borrow_nres(env, "interact", "")?
                        .mut_top_env(|t| t.input.read_to_string(&mut input))
                    {
                        Ok(_) => f.run(env, vec![Obj::from(input)]),
                        Err(msg) => Err(NErr::value_error(format!(
                            "interact: input failed: {}",
                            msg
                        ))),
                    }
                }
                _ => Err(NErr::type_error("not callable".to_string())),
            }
        },
    });

    // not TwoNums bc don't want to vectorize
    env.insert_builtin(TwoArgBuiltin {
        name: "str_radix".to_string(),
        body: |a, r| match (a, r) {
            (Obj::Num(NNum::Int(mut a)), Obj::Num(NNum::Int(r))) => {
                if let Some(base) = r.to_u32() {
                    if base >= 2 && base <= 36 {
                        let neg = a.is_negative();
                        if neg {
                            a = -a;
                        }
                        let mut ret = Vec::new();
                        while (&a).is_positive() {
                            ret.push(
                                char::from_digit(
                                    ((&a) % base).to_u32().expect("str_radix bad"),
                                    base,
                                )
                                .expect("str_radix bad"),
                            );
                            a /= base;
                        }
                        if neg {
                            ret.push('-');
                        }
                        ret.reverse();
                        Ok(Obj::from(ret.into_iter().collect::<String>()))
                    } else {
                        Err(NErr::value_error(format!("Base not in [2, 36]: {}", base)))
                    }
                } else {
                    Err(NErr::value_error(format!("Base way out of range: {}", r)))
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "int_radix".to_string(),
        body: |a, r| {
            if let Obj::Num(n) = r {
                if let Some(base) = n.to_bigint().and_then(BigInt::to_u32) {
                    if 2 <= base && base <= 36 {
                        let mut x = BigInt::from(0);
                        match a {
                            Obj::Seq(Seq::String(s)) => {
                                for c in s.chars() {
                                    match c.to_digit(base) {
                                        Some(cc) => {
                                            x = base * x + cc;
                                        }
                                        None => Err(NErr::value_error(format!(
                                            "Bad digit in base {}: {:?}",
                                            base, c
                                        )))?,
                                    }
                                }
                                return Ok(Obj::from(x));
                            }
                            Obj::Seq(Seq::Bytes(b)) => {
                                for c in b.iter() {
                                    match (*c as char).to_digit(base) {
                                        Some(cc) => {
                                            x = base * x + cc;
                                        }
                                        None => Err(NErr::value_error(format!(
                                            "Bad digit in base {}: {:?}",
                                            base, c
                                        )))?,
                                    }
                                }
                                Ok(Obj::from(x))
                            }
                            a => Err(NErr::argument_error_first(&a)),
                        }
                    } else {
                        Err(NErr::value_error(format!("Base not in [2, 36]: {}", base)))
                    }
                } else {
                    Err(NErr::value_error(format!("Base way out of range: {}", n)))
                }
            } else {
                Err(NErr::argument_error_2(&a, &r))
            }
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "utf8encode".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => Ok(Obj::Seq(Seq::Bytes(Rc::new(s.as_bytes().to_vec())))),
            _ => Err(NErr::type_error("must utf8encode string".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "utf8decode".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::Bytes(b)) => match String::from_utf8(unwrap_or_clone(b)) {
                Ok(s) => Ok(Obj::from(s)),
                Err(e) => Err(NErr::value_error(format!("utf8decode failed: {:?}", e))),
            },
            _ => Err(NErr::type_error("must utf8encode string".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "hex_encode".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::Bytes(b)) => Ok(Obj::from(
                b.iter().map(|x| format!("{:02x}", x)).collect::<String>(),
            )),
            _ => Err(NErr::type_error("must hex_encode bytes".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "hex_decode".to_string(),
        body: |arg| {
            fn val(c: u8) -> NRes<u8> {
                Ok(match c {
                    b'A'..=b'F' => c - b'A' + 10,
                    b'a'..=b'f' => c - b'a' + 10,
                    b'0'..=b'9' => c - b'0',
                    _ => return Err(NErr::value_error(format!("Invalid hex byte: {:?}", c))),
                })
            }
            match arg {
                Obj::Seq(Seq::String(s)) => {
                    if s.len() % 2 == 0 {
                        Ok(Obj::Seq(Seq::Bytes(Rc::new(
                            s.as_bytes()
                                .chunks(2)
                                .map(|ch| Ok(val(ch[0])? << 4 | val(ch[1])?))
                                .collect::<NRes<Vec<u8>>>()?,
                        ))))
                    } else {
                        Err(NErr::value_error(format!(
                            "Can't decode odd-length hex string"
                        )))
                    }
                }
                Obj::Seq(Seq::Bytes(s)) => {
                    if s.len() % 2 == 0 {
                        Ok(Obj::Seq(Seq::Bytes(Rc::new(
                            s.chunks(2)
                                .map(|ch| Ok(val(ch[0])? << 4 | val(ch[1])?))
                                .collect::<NRes<Vec<u8>>>()?,
                        ))))
                    } else {
                        Err(NErr::value_error(format!(
                            "Can't decode odd-length hex string"
                        )))
                    }
                }
                _ => Err(NErr::type_error(
                    "must hex_decode bytes or string".to_string(),
                )),
            }
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "base64encode".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::Bytes(b)) => Ok(Obj::from(base64::encode(&*b))),
            _ => Err(NErr::type_error("must hex_encode bytes".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "base64decode".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => match base64::decode(&*s) {
                Ok(b) => Ok(Obj::Seq(Seq::Bytes(Rc::new(b)))),
                Err(e) => Err(NErr::value_error(format!(
                    "failed to base64decode: {:?}",
                    e
                ))),
            },
            Obj::Seq(Seq::Bytes(s)) => match base64::decode(&*s) {
                Ok(b) => Ok(Obj::Seq(Seq::Bytes(Rc::new(b)))),
                Err(e) => Err(NErr::value_error(format!(
                    "failed to base64decode: {:?}",
                    e
                ))),
            },
            _ => Err(NErr::type_error("must hex_encode bytes".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "json_encode".to_string(),
        body: |arg| match serde_json::to_string(&json_encode(arg)?) {
            Ok(s) => Ok(Obj::from(s)),
            Err(t) => Err(NErr::value_error(format!("json encoding failed: {}", t))),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "json_decode".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => match serde_json::from_str(&*s) {
                Ok(k) => Ok(json_decode(k)),
                Err(t) => Err(NErr::value_error(format!("json decoding failed: {}", t))),
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });

    // TODO safety, wasm version
    env.insert_builtin(OneArgBuiltin {
        name: "read_file".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => match fs::read_to_string(&*s) {
                Ok(c) => Ok(Obj::from(c)),
                Err(e) => Err(NErr::io_error(format!("{}", e))),
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "read_file?".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => match fs::File::open(&*s) {
                Ok(mut f) => {
                    let mut contents = String::new();
                    match f.read_to_string(&mut contents) {
                        Ok(_) => Ok(Obj::from(contents)),
                        Err(e) => Err(NErr::io_error(format!("{}", e))),
                    }
                }
                Err(e) => {
                    if e.kind() == std::io::ErrorKind::NotFound {
                        Ok(Obj::Null)
                    } else {
                        Err(NErr::io_error(format!("{}", e)))
                    }
                }
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "write_file".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(f))) => {
                match fs::write(f.as_str(), s.as_bytes()) {
                    Ok(()) => Ok(Obj::Null),
                    Err(e) => Err(NErr::io_error(format!("{}", e))),
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });

    // this isn't a very good assert
    env.insert_builtin(OneArgBuiltin {
        name: "assert".to_string(),
        body: |a| {
            if a.truthy() {
                Ok(Obj::Null)
            } else {
                Err(NErr::assert_error(format!("{}", a)))
            }
        },
    });

    env.insert_builtin(BasicBuiltin {
        name: "time".to_string(),
        body: |_env, args| {
            if args.is_empty() {
                match SystemTime::now().duration_since(SystemTime::UNIX_EPOCH) {
                    Ok(d) => Ok(Obj::from(d.as_secs_f64())),
                    Err(e) => Ok(Obj::from(-e.duration().as_secs_f64())),
                }
            } else {
                Err(NErr::argument_error_args(&args))
            }
        },
    });

    env.insert_builtin(BasicBuiltin {
        name: "now".to_string(),
        body: |_env, args| match few(args) {
            Few::Zero => Ok(datetime_to_obj(Local::now())),
            Few::One(t) => match t {
                Obj::Num(n) => {
                    let now = Utc::now();
                    let off = FixedOffset::east((to_f64_ok(&n)? * 3600.0) as i32);
                    Ok(datetime_to_obj(now + off))
                }
                t => Err(NErr::argument_error_1(&t)),
            },
            Few::Many(a) => Err(NErr::argument_error_args(&a)),
        },
    });

    env.insert_builtin(BasicBuiltin {
        name: "random".to_string(),
        body: |_env, args| match few(args) {
            Few::Zero => Ok(Obj::from(rand::random::<f64>())),
            Few::One(a) => Err(NErr::argument_error_1(&a)),
            Few::Many(a) => Err(NErr::argument_error_args(&a)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "random_range".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Num(NNum::Int(a)), Obj::Num(NNum::Int(b))) => {
                Ok(Obj::from(rand::thread_rng().gen_bigint_range(&a, &b)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });

    // l m a o
    env.insert_builtin(BasicBuiltin {
        name: "import".to_string(),
        body: |env, args| {
            let mut ret = Obj::Null;
            for arg in args {
                ret = match arg {
                    Obj::Seq(Seq::String(f)) => match fs::read_to_string(&*f) {
                        Ok(c) => match match parse(&c) {
                            Ok(Some(code)) => evaluate(env, &code),
                            Ok(None) => Err(NErr::value_error("empty file".to_string())),
                            Err(s) => {
                                Err(NErr::value_error(format!("lex failed: {}", s.render(&c))))
                            }
                        } {
                            Ok(x) => Ok(x),
                            Err(mut e) => {
                                e.supply_source(f.clone(), Rc::new(c));
                                Err(e)
                            }
                        },
                        Err(e) => Err(NErr::io_error(format!("failed: {}", e))),
                    },
                    a => Err(NErr::type_error(format!("can't import: {}", a))),
                }?
            }
            Ok(ret)
        },
    });

    #[cfg(feature = "request")]
    env.insert_builtin(BasicBuiltin {
        name: "request".to_string(),
        body: |_env, args| {
            let resp = match few2(args) {
                Few2::One(Obj::Seq(Seq::String(url))) => reqwest::blocking::get(&*url)
                    .map_err(|e| NErr::io_error(format!("failed: {}", e))),
                Few2::Two(Obj::Seq(Seq::String(url)), Obj::Seq(Seq::Dict(opts, _))) => {
                    let client = reqwest::blocking::Client::new();
                    let method = match opts.get(&ObjKey::from("method")) {
                        Some(Obj::Seq(Seq::String(s))) => {
                            match reqwest::Method::from_bytes(s.as_bytes()) {
                                Ok(m) => m,
                                Err(e) => {
                                    return Err(NErr::value_error(format!("bad method: {}", e)))
                                }
                            }
                        }
                        Some(k) => return Err(NErr::type_error(format!("bad method: {}", k))),
                        None => reqwest::Method::GET,
                    };
                    let mut builder = client.request(method, &*url);
                    match opts.get(&ObjKey::from("headers")) {
                        Some(Obj::Seq(Seq::Dict(d, _))) => {
                            for (k, v) in d.iter() {
                                builder = builder.header(format!("{}", k), format!("{}", v))
                            }
                        }
                        Some(k) => {
                            return Err(NErr::type_error(format!(
                                "bad headers, should be dict: {}",
                                k
                            )))
                        }
                        None => {}
                    }
                    match opts.get(&ObjKey::from("query")) {
                        Some(Obj::Seq(Seq::Dict(d, _))) => {
                            builder = builder.query(
                                d.iter()
                                    .map(|(k, v)| (format!("{}", k), format!("{}", v)))
                                    .collect::<Vec<(String, String)>>()
                                    .as_slice(),
                            );
                        }
                        Some(k) => {
                            return Err(NErr::type_error(format!(
                                "bad query, should be dict: {}",
                                k
                            )))
                        }
                        None => {}
                    }
                    match opts.get(&ObjKey::from("form")) {
                        Some(Obj::Seq(Seq::Dict(d, _))) => {
                            builder = builder.form(
                                d.iter()
                                    .map(|(k, v)| (format!("{}", k), format!("{}", v)))
                                    .collect::<Vec<(String, String)>>()
                                    .as_slice(),
                            );
                        }
                        Some(k) => {
                            return Err(NErr::type_error(format!(
                                "bad form, should be dict: {}",
                                k
                            )))
                        }
                        None => {}
                    }
                    // builder = builder.header(key, value);
                    // builder = builder.query(&[(key, value)]);
                    // builder = builder.form(&[(key, value)]);
                    builder
                        .send()
                        .map_err(|e| NErr::io_error(format!("built request failed: {}", e)))
                }
                f => Err(NErr::argument_error_few2(&f)),
            }?;
            match resp.text() {
                Ok(s) => Ok(Obj::from(s)),
                Err(e) => Err(NErr::io_error(format!("failed: {}", e))),
            }
        },
    });

    #[cfg(feature = "crypto")]
    {
        env.insert_builtin(TwoArgBuiltin {
            name: "aes128_hazmat_encrypt_block".to_string(),
            body: |a, b| match (a, b) {
                (Obj::Seq(Seq::Bytes(k)), Obj::Seq(Seq::Bytes(mut m))) => {
                    if k.len() == 16 && m.len() == 16 {
                        aes::Aes128::new(generic_array::GenericArray::from_slice(&k))
                            .encrypt_block(generic_array::GenericArray::from_mut_slice(
                                Rc::make_mut(&mut m).as_mut(),
                            ));
                        Ok(Obj::Seq(Seq::Bytes(m)))
                    } else {
                        Err(NErr::value_error("aes: bad sizes".to_string()))
                    }
                }
                (a, b) => Err(NErr::argument_error_2(&a, &b)),
            },
        });
        env.insert_builtin(TwoArgBuiltin {
            name: "aes128_hazmat_decrypt_block".to_string(),
            body: |a, b| match (a, b) {
                (Obj::Seq(Seq::Bytes(k)), Obj::Seq(Seq::Bytes(mut m))) => {
                    if k.len() == 16 && m.len() == 16 {
                        aes::Aes128::new(generic_array::GenericArray::from_slice(&k))
                            .decrypt_block(generic_array::GenericArray::from_mut_slice(
                                Rc::make_mut(&mut m).as_mut(),
                            ));
                        Ok(Obj::Seq(Seq::Bytes(m)))
                    } else {
                        Err(NErr::value_error("aes: bad sizes".to_string()))
                    }
                }
                (a, b) => Err(NErr::argument_error_2(&a, &b)),
            },
        });
        env.insert_builtin(OneArgBuiltin {
            name: "md5".to_string(),
            body: |a| match a {
                Obj::Seq(Seq::Bytes(b)) => Ok(Obj::Seq(Seq::Bytes(Rc::new(
                    Md5::new().chain_update(&*b).finalize().to_vec(),
                )))),
                a => Err(NErr::argument_error_1(&a)),
            },
        });
        env.insert_builtin(OneArgBuiltin {
            name: "sha256".to_string(),
            body: |a| match a {
                Obj::Seq(Seq::Bytes(b)) => Ok(Obj::Seq(Seq::Bytes(Rc::new(
                    Sha256::new().chain_update(&*b).finalize().to_vec(),
                )))),
                a => Err(NErr::argument_error_1(&a)),
            },
        });
        env.insert_builtin(OneArgBuiltin {
            name: "blake3".to_string(),
            body: |a| match a {
                Obj::Seq(Seq::Bytes(b)) => {
                    let h: [u8; 32] = blake3::Hasher::new().update(&*b).finalize().into();
                    Ok(Obj::Seq(Seq::Bytes(Rc::new(h.to_vec()))))
                }
                a => Err(NErr::argument_error_1(&a)),
            },
        });
    }

    env.insert_builtin(OneArgBuiltin {
        name: "memoize".to_string(),
        body: |a| match a {
            Obj::Func(f, p) => Ok(Obj::Func(
                Func::Memoized(Box::new(f), Rc::new(RefCell::new(HashMap::new()))),
                p,
            )),
            a => Err(NErr::argument_error_1(&a)),
        },
    });

    env.insert_builtin(BasicBuiltin {
        name: "vars".to_string(),
        body: |env, _args| {
            Ok(Obj::Seq(Seq::Dict(
                Rc::new(
                    try_borrow_nres(env, "vars", "vars")?
                        .vars
                        .iter()
                        .map(|(k, (_t, v))| {
                            Ok((
                                ObjKey::String(Rc::new(k.clone())),
                                try_borrow_nres(v, "vars", k)?.clone(),
                            ))
                        })
                        .collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                ),
                None,
            )))
        },
    });
}

// copypasta
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub struct WasmOutputs {
    output: String,
    error: String,
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl WasmOutputs {
    pub fn get_output(&self) -> String {
        self.output.to_string()
    }
    pub fn get_error(&self) -> String {
        self.error.to_string()
    }
}

// stdout and error
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub fn encapsulated_eval(code: &str, input: &str) -> WasmOutputs {
    let mut env = Env::new(TopEnv {
        backrefs: Vec::new(),
        input: Box::new(io::Cursor::new(input.as_bytes().to_vec())),
        output: Box::new(Vec::new()),
    });
    initialize(&mut env);

    let e = Rc::new(RefCell::new(env));

    match parse(code) {
        Err(p) => WasmOutputs {
            output: String::new(),
            error: p.render(code),
        },
        Ok(None) => WasmOutputs {
            output: String::new(),
            error: String::new(),
        },
        Ok(Some(code)) => match evaluate(&e, &code) {
            Err(err) => WasmOutputs {
                output: e.borrow_mut().mut_top_env(|e| {
                    String::from_utf8_lossy(e.output.extract().unwrap()).into_owned()
                }),
                error: format!("{}", err),
            },
            Ok(res) => WasmOutputs {
                output: e.borrow_mut().mut_top_env(|e| {
                    String::from_utf8_lossy(e.output.extract().unwrap()).into_owned()
                }) + &format!("{}", res),
                error: String::new(),
            },
        },
    }
}
