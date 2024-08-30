#[macro_use]
extern crate lazy_static;

// TODO: isolate
use std::fs;
use std::io;
use std::io::{BufRead, Read, Write};

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;

use regex::Regex;

use num::bigint::{BigInt, RandBigInt};

use chrono::prelude::*;

use std::time::SystemTime;

use base64;
use rand;
use rand::prelude::SliceRandom;
use rand::{Rng, RngCore};

use flate2::read::{GzDecoder, GzEncoder};
use flate2::Compression;

#[cfg(feature = "request")]
use reqwest;

#[cfg(feature = "crypto")]
use aes;
#[cfg(feature = "crypto")]
use aes::cipher::{generic_array, BlockDecrypt, BlockEncrypt, KeyInit};
#[cfg(feature = "crypto")]
use aes_gcm;
#[cfg(feature = "crypto")]
use aes_gcm::aead::Aead;
#[cfg(feature = "crypto")]
use blake3;
#[cfg(feature = "crypto")]
use md5::{Digest, Md5};
#[cfg(feature = "crypto")]
use sha2::Sha256;

#[cfg(feature = "parallel")]
use rayon::iter::{ParallelBridge, ParallelIterator};

#[cfg(target_arch = "wasm32")]
use js_sys;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

mod core;
mod eval;
pub mod few;
mod gamma;
mod iter;
mod lex;
mod nint;
pub mod nnum;
mod rc;
mod streams;
// mod optim;
use crate::few::*;
use crate::iter::*;
use crate::streams::*;

pub use crate::core::*;
pub use crate::eval::*;
pub use crate::lex::Token;
use crate::nint::NInt;
use crate::nnum::NNum;
pub use crate::rc::*;

// can "destructure"
#[derive(Debug, Clone)]
struct Plus;

impl Builtin for Plus {
    // copypasta
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(a) => self.run1(_env, a),
            Few2::Two(a, b) => self.run2(_env, a, b),
            f => Err(NErr::argument_error(format!(
                "+ only accepts two numbers, got {}",
                f.len()
            ))),
        }
    }
    fn run1(&self, _env: &REnv, arg: Obj) -> NRes<Obj> {
        match arg {
            // partial application, spicy
            Obj::Num(_) | Obj::Seq(Seq::Vector(_)) => Ok(clone_and_part_app_2(self, arg)),
            a => Err(NErr::argument_error(format!(
                "+ only accepts numbers (or vectors), got {}",
                a
            ))),
        }
    }
    fn run2(&self, _env: &REnv, arg1: Obj, arg2: Obj) -> NRes<Obj> {
        expect_nums_and_vectorize_2_nums(|a, b| a + b, arg1, arg2, "+")
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
            Few2::One(s) => expect_nums_and_vectorize_1(|x| Ok(Obj::Num(-x)), s, "unary -"),
            Few2::Two(a, b) => expect_nums_and_vectorize_2_nums(|a, b| a - b, a, b, "binary -"),
            Few2::Many(a) => err_add_name(Err(NErr::argument_error_args(&a)), "-"),
        }
    }
    fn run1(&self, _env: &REnv, arg: Obj) -> NRes<Obj> {
        expect_nums_and_vectorize_1(|x| Ok(Obj::Num(-x)), arg, "unary -")
    }
    fn run2(&self, _env: &REnv, arg1: Obj, arg2: Obj) -> NRes<Obj> {
        expect_nums_and_vectorize_2_nums(|a, b| a - b, arg1, arg2, "binary -")
    }

    fn builtin_name(&self) -> &str {
        "-"
    }

    fn destructure(&self, rvalue: Obj, lhs: Vec<Option<Obj>>) -> NRes<Vec<Obj>> {
        if lhs.len() == 1 {
            Ok(vec![expect_nums_and_vectorize_1(
                |x| Ok(Obj::Num(-x)),
                rvalue,
                "destructuring -",
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
            Few2::Two(a, b) => expect_nums_and_vectorize_2_nums(|a, b| a * b, a, b, "*"),
            f => Err(NErr::argument_error(format!(
                "* only accepts two numbers, got {}",
                f.len()
            ))),
        }
    }
    // FIXME
    fn run2(&self, _env: &REnv, arg1: Obj, arg2: Obj) -> NRes<Obj> {
        expect_nums_and_vectorize_2_nums(|a, b| a * b, arg1, arg2, "*")
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
            Few2::Two(a, b) => expect_nums_and_vectorize_2_nums(|a, b| a / b, a, b, "/"),
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
            "Can't compare nums {} and {}",
            FmtObj::debug(aa),
            FmtObj::debug(bb)
        ))),
        (Obj::Seq(a), Obj::Seq(b)) => a.partial_cmp(b).ok_or(NErr::type_error(format!(
            "Can't compare seqs {} and {}",
            FmtObj::debug(aa),
            FmtObj::debug(bb)
        ))),
        _ => Err(NErr::type_error(format!(
            "Can't compare {} and {}",
            FmtObj::debug(aa),
            FmtObj::debug(bb)
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
                        self.chained[i].run2(env, args[i + 1].clone(), args[i + 2].clone())?;
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
            obj_to_cloning_iter(&rvalue, "comparison unpacking")?.collect::<NRes<Vec<Obj>>>()?
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

#[derive(Debug, Clone)]
struct First;

impl Builtin for First {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(Obj::Seq(s)) => linear_index_isize(s, 0),
            _ => Err(NErr::type_error("first: exactly 1 arg".to_string())),
        }
    }

    fn builtin_name(&self) -> &str {
        "first"
    }

    fn try_chain(&self, _other: &Func) -> Option<Func> {
        None
    }

    fn catamorphism(&self) -> Option<Box<dyn Catamorphism>> {
        Some(Box::new(CataFirst))
    }
}

#[derive(Debug, Clone)]
struct Last;

impl Builtin for Last {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(Obj::Seq(s)) => linear_index_isize(s, -1),
            _ => Err(NErr::type_error("last: exactly 1 arg".to_string())),
        }
    }

    fn builtin_name(&self) -> &str {
        "last"
    }

    fn try_chain(&self, _other: &Func) -> Option<Func> {
        None
    }

    fn catamorphism(&self) -> Option<Box<dyn Catamorphism>> {
        Some(Box::new(CataLast(None)))
    }
}

struct CataExtremum(Ordering, Option<Obj>);
impl Catamorphism for CataExtremum {
    fn give(&mut self, arg: Obj) -> NRes<()> {
        if match &self.1 {
            None => true,
            Some(r) => ncmp(&arg, r)? == self.0,
        } {
            self.1 = Some(arg)
        }
        Ok(())
    }
    fn finish(&mut self) -> NRes<Obj> {
        std::mem::take(&mut self.1).ok_or(NErr::empty_error(format!("cata-extremum: empty")))
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
                    let b = b?;
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
                            let b = b?;
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
                            let b = b?;
                            if match &ret {
                                None => true,
                                Some(r) => {
                                    ncmp(&f.run2(env, b.clone(), r.clone())?, &Obj::zero())?
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
                                    ncmp(&f.run2(env, b.clone(), r.clone())?, &Obj::zero())?
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

    fn catamorphism(&self) -> Option<Box<dyn Catamorphism>> {
        Some(Box::new(CataExtremum(self.bias, None)))
    }
}

struct CataCounter(usize);
impl Catamorphism for CataCounter {
    fn give(&mut self, arg: Obj) -> NRes<()> {
        if arg.truthy() {
            self.0 += 1;
        }
        Ok(())
    }
    fn finish(&mut self) -> NRes<Obj> {
        Ok(Obj::usize(self.0))
    }
}

// count. conditional partial application, cata
// not quite an id pred because there's "count equal".
#[derive(Debug, Clone)]
struct Count;
impl Builtin for Count {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::Zero => Err(NErr::type_error(format!("count: at least 1 arg"))),
            Few2::One(Obj::Seq(mut s)) => {
                let mut c = 0usize;
                for b in mut_seq_into_iter(&mut s) {
                    if b?.truthy() {
                        c += 1
                    }
                }
                Ok(Obj::usize(c))
            }
            Few2::One(a) => Ok(clone_and_part_app_last(self, a)),
            Few2::Two(mut a, b) => {
                let it = mut_obj_into_iter(&mut a, "count")?;
                let mut c = 0usize;
                match b {
                    Obj::Func(b, _) => {
                        for e in it {
                            if b.run1(env, e?)?.truthy() {
                                c += 1;
                            }
                        }
                    }
                    b => {
                        for e in it {
                            if e? == b {
                                c += 1;
                            }
                        }
                    }
                }
                Ok(Obj::usize(c))
            }
            Few2::Many(x) => err_add_name(Err(NErr::argument_error_args(&x)), "count"),
        }
    }

    fn builtin_name(&self) -> &str {
        "count"
    }

    fn try_chain(&self, _other: &Func) -> Option<Func> {
        None
    }

    fn catamorphism(&self) -> Option<Box<dyn Catamorphism>> {
        Some(Box::new(CataCounter(0)))
    }
}

struct CataSet(HashMap<ObjKey, Obj>);
impl Catamorphism for CataSet {
    fn give(&mut self, arg: Obj) -> NRes<()> {
        self.0.insert(to_key(arg)?, Obj::Null);
        Ok(())
    }
    fn finish(&mut self) -> NRes<Obj> {
        Ok(Obj::dict(std::mem::take(&mut self.0), None))
    }
}

// just for cata
#[derive(Debug, Clone)]
struct Set;
impl Builtin for Set {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(Obj::Seq(mut s)) => Ok(Obj::dict(
                mut_seq_into_iter(&mut s)
                    .map(|k| Ok((to_key(k?)?, Obj::Null)))
                    .collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                None,
            )),
            f => err_add_name(Err(NErr::argument_error_few(&f)), "set"),
        }
    }

    fn builtin_name(&self) -> &str {
        "set"
    }

    fn try_chain(&self, _other: &Func) -> Option<Func> {
        None
    }

    fn catamorphism(&self) -> Option<Box<dyn Catamorphism>> {
        Some(Box::new(CataSet(HashMap::new())))
    }
}

struct CataCountDistinct(HashSet<ObjKey>);
impl Catamorphism for CataCountDistinct {
    fn give(&mut self, arg: Obj) -> NRes<()> {
        self.0.insert(to_key(arg)?);
        Ok(())
    }
    fn finish(&mut self) -> NRes<Obj> {
        Ok(Obj::usize(self.0.len()))
    }
}

// just for cata
#[derive(Debug, Clone)]
struct CountDistinct;
impl Builtin for CountDistinct {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::One(Obj::Seq(mut s)) => Ok(Obj::usize(
                mut_seq_into_finite_iter(&mut s, "count_distinct conversion")?
                    .map(|e| to_key(e?))
                    .collect::<NRes<HashSet<ObjKey>>>()?
                    .len(),
            )),
            f => err_add_name(Err(NErr::argument_error_few(&f)), "count_distinct"),
        }
    }

    fn builtin_name(&self) -> &str {
        "count_distinct"
    }

    fn try_chain(&self, _other: &Func) -> Option<Func> {
        None
    }

    fn catamorphism(&self) -> Option<Box<dyn Catamorphism>> {
        Some(Box::new(CataCountDistinct(HashSet::new())))
    }
}

#[derive(Debug, Clone)]
struct TilBuiltin;

impl Builtin for TilBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few3::Two(Obj::Num(a), Obj::Num(b)) => {
                let n1 = into_nint_ok(a)?;
                let n2 = into_nint_ok(b)?;
                Ok(Obj::Seq(Seq::Stream(Rc::new(Range(
                    n1,
                    Some(n2),
                    NInt::Small(1),
                )))))
            }
            Few3::Two(Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                let mut ac = a.chars();
                let mut bc = b.chars();
                match (ac.next(), ac.next(), bc.next(), bc.next()) {
                    (Some(a), None, Some(b), None) => Ok(Obj::from(
                        // too lazy to make it lazy...
                        ((a as u32)..(b as u32))
                            .map(|c| {
                                std::char::from_u32(c).expect("string range incoherent roundtrip")
                            })
                            .collect::<String>(),
                    )),
                    _ => Err(NErr::argument_error(format!("til: Bad string args"))),
                }
            }
            Few3::Three(Obj::Num(a), Obj::Num(b), Obj::Num(c)) => {
                let n1 = into_nint_ok(a)?;
                let n2 = into_nint_ok(b)?;
                let n3 = into_nint_ok(c)?;
                Ok(Obj::Seq(Seq::Stream(Rc::new(Range(n1, Some(n2), n3)))))
            }
            c => err_add_name(Err(NErr::argument_error_few3(&c)), "til"),
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
            Few3::Two(a, b) => self.run2(_env, a, b),
            Few3::Three(Obj::Num(a), Obj::Num(b), Obj::Num(c)) => {
                let n1 = into_nint_ok(a)?;
                let n2 = into_nint_ok(b)?;
                let n3 = into_nint_ok(c)?;
                Ok(Obj::Seq(Seq::Stream(Rc::new(Range(
                    n1,
                    Some(if n3.is_negative() {
                        n2 - NInt::Small(1)
                    } else {
                        n2 + NInt::Small(1)
                    }),
                    n3,
                )))))
            }
            c => err_add_name(Err(NErr::argument_error_few3(&c)), "to"),
        }
    }
    fn run2(&self, _env: &REnv, a: Obj, b: Obj) -> NRes<Obj> {
        match (a, b) {
            (Obj::Num(a), Obj::Num(b)) => {
                let n1 = into_nint_ok(a)?;
                let n2 = into_nint_ok(b)?;
                Ok(Obj::Seq(Seq::Stream(Rc::new(Range(
                    n1,
                    Some(n2 + NInt::Small(1)),
                    NInt::Small(1),
                )))))
            }
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                let mut ac = a.chars();
                let mut bc = b.chars();
                match (ac.next(), ac.next(), bc.next(), bc.next()) {
                    (Some(a), None, Some(b), None) => Ok(Obj::from(
                        // too lazy to make it lazy...
                        ((a as u32)..=(b as u32))
                            .map(|c| {
                                std::char::from_u32(c).expect("string range incoherent roundtrip")
                            })
                            .collect::<String>(),
                    )),
                    _ => Err(NErr::argument_error(format!(
                        "to: Bad string args: lens {}, {}",
                        a.len(),
                        b.len()
                    ))),
                }
            }
            (a, Obj::Func(Func::Type(t), _)) => call_type1(&t, a), // sugar lmao
            (a, b) => err_add_name(Err(NErr::argument_error_2(&a, &b)), "to"),
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
                let mut any_finite = false;
                for arg in args.iter_mut() {
                    match (arg, &mut func) {
                        (Obj::Func(f, _), None) => {
                            func = Some(f.clone());
                        }
                        (Obj::Func(..), Some(_)) => Err(NErr::argument_error(
                            "zip: more than one function".to_string(),
                        ))?,
                        (Obj::Seq(s), _) => {
                            if s.len().is_some() {
                                any_finite = true;
                            }
                            iterators.push(mut_seq_into_iter(s))
                        }
                        (e, _) => {
                            return Err(NErr::argument_error(format!(
                                "zip: not iterable: {}",
                                FmtObj::debug(e)
                            )))
                        }
                    }
                }
                if iterators.is_empty() {
                    Err(NErr::argument_error("zip: zero iterables".to_string()))?
                }
                // It's possible you just want to zip an infinite sequence with a function as
                // "each" but IMO too unlikely.
                if !any_finite {
                    return Err(NErr::value_error(format!(
                        "zip: infinite, will not terminate"
                    )));
                }
                let mut ret = Vec::new();
                while let Some(batch) = iterators
                    .iter_mut()
                    .map(|a| a.next())
                    .collect::<Option<NRes<Vec<Obj>>>>()
                {
                    ret.push(match &func {
                        Some(f) => f.run(env, batch?)?,
                        None => Obj::list(batch?),
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
                        Some(x0) => {
                            let mut x = x0?;
                            match &func {
                                Some(f) => {
                                    for y in batch {
                                        x = f.run2(env, x, y?)?;
                                    }
                                    ret.push(x)
                                }
                                None => {
                                    let mut v = vec![x];
                                    for y in batch {
                                        v.push(y?);
                                    }
                                    ret.push(Obj::list(v))
                                }
                            }
                        }
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
struct LazyZip;

impl Builtin for LazyZip {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few(args) {
            Few::Zero => Err(NErr::argument_error("lazy_zip: no args".to_string())),
            Few::One(a) => Ok(clone_and_part_app_last(self, a)),
            Few::Many(args) => {
                let mut func = None;
                let mut streams: Vec<Box<dyn Stream>> = Vec::new();
                for arg in args.into_iter() {
                    match (arg, &mut func) {
                        (Obj::Func(f, _), None) => {
                            func = Some(f);
                        }
                        (Obj::Func(..), Some(_)) => Err(NErr::argument_error(
                            "lazy_zip: more than one function".to_string(),
                        ))?,
                        (Obj::Seq(Seq::Stream(s)), _) => streams.push(s.clone_box()),
                        (e, _) => {
                            return Err(NErr::argument_error(format!(
                                "lazy_zip: not stream: {}",
                                FmtObj::debug(&e)
                            )))
                        }
                    }
                }
                if streams.is_empty() {
                    Err(NErr::argument_error("lazy_zip: zero streams".to_string()))?
                }
                Ok(Obj::Seq(Seq::Stream(Rc::new(ZippedStream(Ok((
                    streams,
                    func,
                    Rc::clone(env),
                )))))))
            }
        }
    }

    fn builtin_name(&self) -> &str {
        "lazy_zip"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "lazy_zip" | "with" => Some(Func::Builtin(Rc::new(self.clone()))),
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
                acc.push(e?);
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
                                acc.push(e?);
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
                        Some(cur0) => {
                            let mut cur = cur0?;
                            // not sure if any standard fallible rust methods work...
                            for e in it {
                                cur = f.run2(env, cur, e?)?;
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
                            cur = f.run2(env, cur, e?)?;
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
                        Some(cur0) => {
                            let mut cur = cur0?;
                            let mut acc = vec![cur.clone()];
                            for e in it {
                                cur = f.run2(env, cur, e?)?;
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
                            cur = f.run2(env, cur, e?)?;
                            acc.push(cur.clone());
                        }
                        Ok(Obj::list(acc))
                    }
                    _ => Err(NErr::type_error("scan: not callable".to_string())),
                }
            }
            Few3::Many(x) => err_add_name(Err(NErr::argument_error_args(&x)), "scan"),
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
                                    *slot = f.run2(env, std::mem::take(slot), v)?;
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
            Few3::Two(a @ Obj::Seq(Seq::String(_)), b @ Obj::Seq(Seq::String(_))) => Ok(Obj::Func(
                Func::PartialAppLast(
                    Box::new(Func::PartialAppLast(
                        Box::new(Func::Builtin(Rc::new(self.clone()))),
                        Box::new(b),
                    )),
                    Box::new(a),
                ),
                Precedence::zero(),
            )),
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
                        match f.run1(env, captures_to_obj(&r, caps)) {
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
                "replace: must get three strings (or two for partial app)".to_string(),
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

#[derive(Debug, Clone)]
struct LiftedEquals;

impl Builtin for LiftedEquals {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        Ok(Obj::Func(
            Func::OnFanoutConst(
                Box::new(Func::Builtin(Rc::new(ComparisonOperator::of(
                    "==",
                    |a, b| Ok(a == b),
                )))),
                args,
            ),
            Precedence::zero(),
        ))
    }

    fn builtin_name(&self) -> &str {
        "equals"
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match other {
            Func::Builtin(b) => match b.builtin_name() {
                "equals" => Some(Func::Builtin(Rc::new(self.clone()))),
                _ => None,
            },
            _ => None,
        }
    }
}

// not actually chainable, but conditional partial application, and also I want aliases
#[derive(Debug, Clone)]
pub struct Group {
    strict: bool,
}

impl Builtin for Group {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(Obj::Seq(s)) => Ok(Obj::list(multi_group_by_eq(s)?)),
            Few2::One(a) => Ok(clone_and_part_app_2(self, a)),
            Few2::Two(Obj::Seq(s), Obj::Num(n)) => match to_usize_ok(&n)? {
                0 => Err(NErr::value_error("can't group into 0".to_string())),
                n => Ok(Obj::list(multi_group(s, n, self.strict)?)),
            },
            Few2::Two(Obj::Seq(s), Obj::Func(f, _)) => Ok(Obj::list(multi_group_by(env, f, s)?)),
            _ => Err(NErr::type_error("not number or func".to_string())),
        }
    }

    fn builtin_name(&self) -> &str {
        if self.strict {
            "group'"
        } else {
            "group"
        }
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

#[derive(Debug, Clone)]
struct Split;

impl Builtin for Split {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::One(t) => Ok(clone_and_part_app_2(self, t)),
            Few3::Two(Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => Ok(Obj::list(
                s.split(&*t).map(|w| Obj::from(w.to_string())).collect(),
            )),
            Few3::Three(Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t)), Obj::Num(n)) => {
                Ok(Obj::list(
                    s.splitn(clamp_to_usize_ok(&n)?, &*t)
                        .map(|w| Obj::from(w.to_string()))
                        .collect(),
                ))
            }
            c => err_add_name(Err(NErr::argument_error_few3(&c)), "split"),
        }
    }

    fn builtin_name(&self) -> &str {
        "split"
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
struct RSplit;

impl Builtin for RSplit {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::One(t) => Ok(clone_and_part_app_2(self, t)),
            Few3::Two(Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => Ok(Obj::list(
                s.rsplit(&*t).map(|w| Obj::from(w.to_string())).collect(),
            )),
            Few3::Three(Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t)), Obj::Num(n)) => {
                Ok(Obj::list(
                    s.rsplitn(clamp_to_usize_ok(&n)?, &*t)
                        .map(|w| Obj::from(w.to_string()))
                        .collect(),
                ))
            }
            c => err_add_name(Err(NErr::argument_error_few3(&c)), "rsplit"),
        }
    }

    fn builtin_name(&self) -> &str {
        "rsplit"
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
struct SplitRe;

impl Builtin for SplitRe {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few3(args) {
            Few3::One(t) => Ok(clone_and_part_app_2(self, t)),
            Few3::Two(Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t))) => Ok(Obj::list(
                Regex::new(t.as_str())
                    .map_err(|e| NErr::value_error(format!("regex error: {}", e)))?
                    .split(s.as_str())
                    .map(|w| Obj::from(w.to_string()))
                    .collect(),
            )),
            Few3::Three(Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(t)), Obj::Num(n)) => {
                Ok(Obj::list(
                    Regex::new(t.as_str())
                        .map_err(|e| NErr::value_error(format!("regex error: {}", e)))?
                        .splitn(s.as_str(), clamp_to_usize_ok(&n)?)
                        .map(|w| Obj::from(w.to_string()))
                        .collect(),
                ))
            }
            c => err_add_name(Err(NErr::argument_error_few3(&c)), "split_re"),
        }
    }

    fn builtin_name(&self) -> &str {
        "split_re"
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
        self.run1(_env, expect_one(args, &self.name)?)
    }
    fn run1(&self, _env: &REnv, arg: Obj) -> NRes<Obj> {
        let ty = type_of(&arg);
        err_add_name((self.body)(arg), &format!("{}({})", self.name, ty.name()))
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
            Few2::Two(a, b) => self.run2(_env, a, b),
            f => Err(NErr::argument_error(format!(
                "{} only accepts two arguments (or one for partial application), got {}",
                self.name,
                f.len()
            ))),
        }
    }
    fn run2(&self, _env: &REnv, a: Obj, b: Obj) -> NRes<Obj> {
        err_add_name((self.body)(a, b), &self.name)
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

struct CataMapped(Obj, fn(state: Obj, next: Obj) -> NRes<Obj>);
impl Catamorphism for CataMapped {
    fn give(&mut self, arg: Obj) -> NRes<()> {
        self.0 = (self.1)(std::mem::take(&mut self.0), arg)?;
        Ok(())
    }
    fn finish(&mut self) -> NRes<Obj> {
        Ok(std::mem::take(&mut self.0))
    }
}

// Folds a sequence with an optional mapping function. If given only a function, partially applies
// it. If given only a sequence, runs it with the identity function.
//
// Requires the fold to have a valid identity (max/min aren't this)
// Expects finite sequences only.
// body can return Break. But it can't break with null I think.

#[derive(Clone)]
pub struct SeqAndMappedFoldBuiltin {
    name: String,
    identity: Obj,
    body: fn(state: Obj, next: Obj) -> NRes<Obj>,
}
standard_three_part_debug!(SeqAndMappedFoldBuiltin);

impl Builtin for SeqAndMappedFoldBuiltin {
    fn run(&self, env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(a) => self.run1(env, a),
            Few2::Two(Obj::Seq(mut s), Obj::Func(f, _)) => {
                let mut state = self.identity.clone();
                for e in mut_seq_into_iter(&mut s) {
                    state = match (self.body)(state, f.run1(env, e?)?) {
                        Ok(r) => r,
                        Err(NErr::Break(0, r)) => return Ok(r.unwrap_or(Obj::Null)),
                        Err(NErr::Break(n, r)) => return Err(NErr::Break(n - 1, r)),
                        e @ Err(_) => return err_add_name(e, &self.name),
                    }
                }
                Ok(state)
            }
            a => err_add_name(Err(NErr::argument_error_few2(&a)), &self.name),
        }
    }
    fn run1(&self, _env: &REnv, arg: Obj) -> NRes<Obj> {
        match arg {
            Obj::Seq(mut s) => {
                let mut state = self.identity.clone();
                for e in mut_seq_into_iter(&mut s) {
                    state = match (self.body)(state, e?) {
                        Ok(r) => r,
                        Err(NErr::Break(0, r)) => return Ok(r.unwrap_or(Obj::Null)),
                        Err(NErr::Break(n, r)) => return Err(NErr::Break(n - 1, r)),
                        e @ Err(_) => return err_add_name(e, &self.name),
                    }
                }
                Ok(state)
            }
            f @ Obj::Func(..) => Ok(clone_and_part_app_2(self, f)),
            a => err_add_name(Err(NErr::argument_error_1(&a)), &self.name),
        }
    }
    fn run2(&self, env: &REnv, a: Obj, b: Obj) -> NRes<Obj> {
        match (a, b) {
            (Obj::Seq(mut s), Obj::Func(f, _)) => {
                let mut state = self.identity.clone();
                for e in mut_seq_into_iter(&mut s) {
                    state = match (self.body)(state, f.run1(env, e?)?) {
                        Ok(r) => r,
                        Err(NErr::Break(0, r)) => return Ok(r.unwrap_or(Obj::Null)),
                        Err(NErr::Break(n, r)) => return Err(NErr::Break(n - 1, r)),
                        e @ Err(_) => return err_add_name(e, &self.name),
                    }
                }
                Ok(state)
            }
            (a, b) => err_add_name(Err(NErr::argument_error_2(&a, &b)), &self.name),
        }
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }

    fn catamorphism(&self) -> Option<Box<dyn Catamorphism>> {
        Some(Box::new(CataMapped(self.identity.clone(), self.body)))
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
        let arg = expect_one(args, &self.name)?;
        self.run1(env, arg)
    }
    fn run1(&self, env: &REnv, arg: Obj) -> NRes<Obj> {
        err_add_name((self.body)(env, arg), &self.name)
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
            Few2::Two(a, b) => self.run2(env, a, b),
            f => Err(NErr::argument_error(format!(
                "{} only accepts two arguments (or one for partial application), got {}",
                self.name,
                f.len()
            ))),
        }
    }
    fn run2(&self, env: &REnv, arg1: Obj, arg2: Obj) -> NRes<Obj> {
        err_add_name((self.body)(env, arg1, arg2), &self.name)
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
}

impl Builtin for OneNumBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        self.run1(_env, expect_one(args, &self.name)?)
    }
    fn run1(&self, _env: &REnv, arg: Obj) -> NRes<Obj> {
        expect_nums_and_vectorize_1(self.body, arg, &self.name)
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
                            "only accepts numbers, got {}",
                            FmtObj::debug(&x)
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

// converting in and out of nums is a bit of a hot path sometimes??
#[derive(Debug, Clone)]
pub struct TwoNumsToNumsBuiltin {
    name: String,
    body: fn(a: NNum, b: NNum) -> NNum,
}

fn expect_nums_and_vectorize_2_nums(
    body: fn(NNum, NNum) -> NNum,
    a: Obj,
    b: Obj,
    name: &str,
) -> NRes<Obj> {
    match (a, b) {
        (Obj::Num(a), Obj::Num(b)) => Ok(Obj::Num(body(a, b))),
        (Obj::Num(a), Obj::Seq(Seq::Vector(mut b))) => Ok(Obj::Seq(Seq::Vector(Rc::new(
            RcVecIter::of(&mut b).map(|e| body(a.clone(), e)).collect(),
        )))),
        (Obj::Seq(Seq::Vector(mut a)), Obj::Num(b)) => Ok(Obj::Seq(Seq::Vector(Rc::new(
            RcVecIter::of(&mut a).map(|e| body(e, b.clone())).collect(),
        )))),
        (Obj::Seq(Seq::Vector(mut a)), Obj::Seq(Seq::Vector(mut b))) => {
            if a.len() == b.len() {
                Ok(Obj::Seq(Seq::Vector(Rc::new(
                    RcVecIter::of(&mut a)
                        .zip(RcVecIter::of(&mut b))
                        .map(|(a, b)| body(a, b))
                        .collect(),
                ))))
            } else {
                Err(NErr::value_error(format!(
                    "{}: couldn't vectorize, different lengths: {}, {}",
                    name,
                    a.len(),
                    b.len()
                )))
            }
        }
        (a, b) => Err(NErr::argument_error(format!(
            "{} only accepts numbers (or vectors), got {}, {}",
            name, a, b
        ))),
    }
}

impl Builtin for TwoNumsToNumsBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(a) => self.run1(_env, a),
            Few2::Two(a, b) => self.run2(_env, a, b),
            f => Err(NErr::argument_error(format!(
                "{} only accepts two numbers, got {}",
                self.name,
                f.len()
            ))),
        }
    }
    fn run1(&self, _env: &REnv, arg: Obj) -> NRes<Obj> {
        match arg {
            arg @ (Obj::Num(_) | Obj::Seq(Seq::Vector(_))) => Ok(clone_and_part_app_2(self, arg)),
            a => Err(NErr::argument_error(format!(
                "{} only accepts numbers (or vectors), got {}",
                self.name, a
            ))),
        }
    }
    fn run2(&self, _env: &REnv, a: Obj, b: Obj) -> NRes<Obj> {
        expect_nums_and_vectorize_2_nums(self.body, a, b, &self.name)
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

fn expect_nums_and_vectorize_2(
    body: fn(NNum, NNum) -> NRes<Obj>,
    a: Obj,
    b: Obj,
    name: &str,
) -> NRes<Obj> {
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
                    "{}: couldn't vectorize, different lengths: {}, {}",
                    name,
                    a.len(),
                    b.len()
                )))
            }
        }
        (a, b) => Err(NErr::argument_error(format!(
            "{} only accepts numbers (or vectors), got {}, {}",
            name, a, b
        ))),
    }
}

impl Builtin for TwoNumsBuiltin {
    fn run(&self, _env: &REnv, args: Vec<Obj>) -> NRes<Obj> {
        match few2(args) {
            Few2::One(a) => self.run1(_env, a),
            Few2::Two(a, b) => self.run2(_env, a, b),
            f => Err(NErr::argument_error(format!(
                "{} only accepts two numbers, got {}",
                self.name,
                f.len()
            ))),
        }
    }
    fn run1(&self, _env: &REnv, arg: Obj) -> NRes<Obj> {
        match arg {
            arg @ (Obj::Num(_) | Obj::Seq(Seq::Vector(_))) => Ok(clone_and_part_app_2(self, arg)),
            a => Err(NErr::argument_error(format!(
                "{} only accepts numbers (or vectors), got {}",
                self.name, a
            ))),
        }
    }
    fn run2(&self, _env: &REnv, a: Obj, b: Obj) -> NRes<Obj> {
        expect_nums_and_vectorize_2(self.body, a, b, &self.name)
    }

    fn builtin_name(&self) -> &str {
        &self.name
    }
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

fn linear_index_isize(xr: Seq, i: isize) -> NRes<Obj> {
    match xr {
        Seq::List(xx) => Ok(xx[pythonic_index_isize(&xx, i)?].clone()),
        Seq::Vector(x) => Ok(Obj::Num(x[pythonic_index_isize(&x, i)?].clone())),
        Seq::Bytes(x) => Ok(Obj::u8(x[pythonic_index_isize(&x, i)?])),
        Seq::String(s) => {
            let bs = s.as_bytes();
            let i = pythonic_index_isize(bs, i)?;
            Ok(soft_from_utf8(bs[i..i + 1].to_vec()))
        }
        Seq::Stream(v) => v.pythonic_index_isize(i),
        Seq::Dict(..) => Err(NErr::type_error(
            "dict is not a linear sequence".to_string(),
        )),
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
            Seq::Bytes(xx) => Ok(Obj::u8(xx[cyclic_index(xx, &ii)?])),
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

// *not* pythonic wraparound; I believe usually you want to use this so that -1 and n have sentinel
// behavior
fn safe_index_inner<T>(xs: &[T], i: &Obj) -> Option<usize> {
    match i {
        Obj::Num(ii) => match ii.to_usize() {
            Some(n) => {
                if n < xs.len() {
                    Some(n)
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}

fn safe_index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, &ir) {
        (Obj::Null, _) => Ok(Obj::Null),
        (Obj::Seq(s), ii) => match s {
            Seq::String(s) => {
                let bs = s.as_bytes();
                match safe_index_inner(bs, ii) {
                    Some(i) => Ok(weird_string_as_bytes_index(bs, i)),
                    None => Ok(Obj::Null),
                }
            }
            Seq::List(xx) => match safe_index_inner(xx, ii) {
                Some(i) => Ok(xx[i].clone()),
                None => Ok(Obj::Null),
            },
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
            Seq::Vector(v) => match safe_index_inner(v, ii) {
                Some(i) => Ok(Obj::Num(v[i].clone())),
                None => Ok(Obj::Null),
            },
            Seq::Bytes(v) => match safe_index_inner(v, ii) {
                Some(i) => Ok(Obj::u8(v[i])),
                None => Ok(Obj::Null),
            },
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

fn obj_in(a: Obj, b: Obj) -> NRes<bool> {
    match (a, b) {
        (a, Obj::Seq(Seq::Dict(v, _))) => Ok(v.contains_key(&to_key(a)?)),
        (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(v))) => Ok((*v).contains(&*s)),
        (a, Obj::Seq(mut s)) => {
            for e in mut_seq_into_iter(&mut s) {
                if e? == a {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
        _ => Err(NErr::type_error("in: not compatible".to_string())),
    }
}

pub fn warn(env: &Rc<RefCell<Env>>, expr: &LocExpr) -> LocExpr {
    let mut frenv = FreezeEnv {
        bound: HashSet::new(),
        env: Rc::clone(&env),
        warn: true,
    };
    match freeze(&mut frenv, &expr) {
        Ok(x) => x,
        Err(e) => {
            panic!("\x1b[1;31mERROR\x1b[0;33m: expr warn failed: {}\x1b[0m", e);
        }
    }
}

pub fn simple_eval(code: &str) -> Obj {
    let mut env = Env::empty();
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
        acc += format!("{}", arg?).as_str();
        started = true;
    }
    Ok(acc)
}

fn to_rc_vec_obj(a: Obj) -> NRes<Rc<Vec<Obj>>> {
    match a {
        Obj::Seq(Seq::List(v)) => Ok(v),
        mut a => {
            let ret = Ok(Rc::new(
                mut_obj_into_iter(&mut a, "to_rc_vec")?.collect::<NRes<Vec<Obj>>>()?,
            ));
            ret
        }
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
                let $name = $name.force()?;
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
        Seq::Stream(s) => s.reversed(),
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
        if f.run1(env, x.clone().into())?.truthy() != neg {
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
        match f.run2(env, a.clone().into(), b.clone().into()) {
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
fn sorted_on<T: Clone + Into<Obj>>(env: &REnv, f: Func, v: Vec<T>) -> NRes<Vec<T>> {
    let mut ret = Ok(());
    let mut w = v
        .into_iter()
        .map(|a| Ok((f.run1(env, a.clone().into())?, a)))
        .collect::<NRes<Vec<(Obj, T)>>>()?;
    w.sort_by(|(ak, _), (bk, _)| {
        if ret.is_err() {
            return Ordering::Equal;
        }
        match ncmp(&ak, &bk) {
            Ok(ord) => ord,
            Err(e) => {
                ret = Err(e);
                Ordering::Equal
            }
        }
    });
    ret?;
    Ok(w.into_iter().map(|(_, obj)| obj).collect())
}
fn multi_sort_on(env: &REnv, f: Func, v: Seq) -> NRes<Seq> {
    multi!(v, sorted_on(env, f, v))
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

fn grouped<T>(mut it: impl Iterator<Item = NRes<T>>, n: usize, strict: bool) -> NRes<Vec<Vec<T>>> {
    let mut acc = Vec::new();
    let mut group = Vec::new();
    loop {
        for _ in 0..n {
            match it.next() {
                Some(obj) => group.push(obj?),
                None => {
                    if !group.is_empty() {
                        if strict && group.len() != n {
                            return Err(NErr::argument_error(format!(
                                "strict group: {} left over",
                                group.len()
                            )));
                        }
                        acc.push(group);
                    }
                    return Ok(acc);
                }
            }
        }
        acc.push(std::mem::take(&mut group))
    }
}
fn grouped_by<T: Clone + Into<Obj>>(
    mut it: impl Iterator<Item = NRes<T>>,
    mut f: impl FnMut(Obj, Obj) -> NRes<bool>,
) -> NRes<Vec<Vec<T>>> {
    let mut acc = Vec::new();
    let mut group: Vec<T> = Vec::new();
    loop {
        match it.next() {
            Some(obj) => {
                let obj = obj?;
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

fn grouped_all_with<T: Clone + Into<Obj>>(
    it: impl Iterator<Item = NRes<T>>,
    mut f: impl FnMut(Obj) -> NRes<Obj>,
) -> NRes<Vec<Vec<T>>> {
    let mut map: HashMap<ObjKey, Vec<T>> = HashMap::new();
    for i in it {
        let i = i?;
        let key = to_key(f(i.clone().into())?)?;
        if map.contains_key(&key) {
            map.get_mut(&key).unwrap().push(i);
        } else {
            map.insert(key, vec![i]);
        }
    }
    Ok(map.into_values().collect())
}

fn windowed<T: Clone>(mut it: impl Iterator<Item = NRes<T>>, n: usize) -> NRes<Vec<Vec<T>>> {
    let mut window = VecDeque::new();
    window.reserve_exact(n);
    for _ in 0..n {
        match it.next() {
            Some(obj) => window.push_back(obj?),
            None => return Ok(Vec::new()),
        }
    }
    let mut acc = vec![window.iter().cloned().collect()];
    while let Some(next) = it.next() {
        window.pop_front();
        window.push_back(next?);
        acc.push(window.iter().cloned().collect());
    }
    Ok(acc)
}

fn take_while_inner<T: Clone + Into<Obj>>(
    mut it: impl Iterator<Item = T>,
    env: &REnv,
    f: Func,
) -> NRes<Vec<T>> {
    let mut acc = Vec::new();
    while let Some(x) = it.next() {
        if f.run1(env, x.clone().into())?.truthy() {
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
        Seq::Stream(s) => {
            let mut acc = Vec::new();
            let mut s = s.clone_box();
            while let Some(x) = s.next() {
                let x = x?;
                if f.run1(env, x.clone())?.truthy() {
                    acc.push(x)
                } else {
                    return Ok(Obj::list(acc));
                }
            }
            Ok(Obj::list(acc))
        }
    }
}

fn drop_while_inner<T: Clone + Into<Obj>>(
    it: impl Iterator<Item = T>,
    env: &REnv,
    f: Func,
) -> NRes<impl Iterator<Item = T>> {
    let mut it = it.peekable();
    while let Some(x) = it.peek() {
        if f.run1(env, x.clone().into())?.truthy() {
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
                let x = x?;
                if f.run1(env, x.clone())?.truthy() {
                    t.next();
                }
            }
            Ok(Obj::Seq(Seq::Stream(Rc::from(t))))
        }
    }
}

// also doesn't fit...
// want a soft "uncons?" so two layers
fn uncons(s: Seq) -> NRes<Option<(Obj, Seq)>> {
    match s {
        Seq::List(mut s) => {
            if s.is_empty() {
                Ok(None)
            } else {
                let head = Rc::make_mut(&mut s).remove(0);
                Ok(Some((head, Seq::List(s))))
            }
        }

        Seq::String(mut s) => {
            if s.is_empty() {
                Ok(None)
            } else {
                let head = Rc::make_mut(&mut s).remove(0);
                Ok(Some((Obj::from(head), Seq::String(s))))
            }
        }
        Seq::Dict(mut s, def) => match s.keys().next().cloned() {
            Some(k) => match Rc::make_mut(&mut s).remove_entry(&k) {
                Some((kk, v)) => Ok(Some((
                    Obj::list(vec![key_to_obj(kk), v]),
                    Seq::Dict(s, def),
                ))),
                None => panic!("no"),
            },
            None => Ok(None),
        },
        Seq::Vector(mut s) => {
            if s.is_empty() {
                Ok(None)
            } else {
                let head = Rc::make_mut(&mut s).remove(0);
                Ok(Some((Obj::from(head), Seq::Vector(s))))
            }
        }
        Seq::Bytes(mut s) => {
            if s.is_empty() {
                Ok(None)
            } else {
                let head = Rc::make_mut(&mut s).remove(0);
                Ok(Some((Obj::u8(head), Seq::Bytes(s))))
            }
        }
        Seq::Stream(s) => {
            let mut t = s.clone_box();
            match t.next() {
                None => Ok(None),
                Some(e) => Ok(Some((e?, Seq::Stream(Rc::from(t))))),
            }
        }
    }
}
fn unsnoc(s: Seq) -> NRes<Option<(Seq, Obj)>> {
    match s {
        Seq::List(mut s) => match Rc::make_mut(&mut s).pop() {
            None => Ok(None),
            Some(e) => Ok(Some((Seq::List(s), e))),
        },
        Seq::String(mut s) => match Rc::make_mut(&mut s).pop() {
            None => Ok(None),
            Some(e) => Ok(Some((Seq::String(s), Obj::from(e)))),
        },
        dd @ Seq::Dict(..) => Ok(uncons(dd)?.map(|(e, s)| (s, e))),
        Seq::Vector(mut s) => match Rc::make_mut(&mut s).pop() {
            None => Ok(None),
            Some(e) => Ok(Some((Seq::Vector(s), Obj::from(e)))),
        },
        Seq::Bytes(mut s) => match Rc::make_mut(&mut s).pop() {
            None => Ok(None),
            Some(e) => Ok(Some((Seq::Bytes(s), Obj::u8(e)))),
        },
        Seq::Stream(s) => unsnoc(Seq::List(Rc::new(s.force()?))),
    }
}

fn prefixes<T: Clone>(mut it: impl Iterator<Item = NRes<T>>) -> NRes<Vec<Vec<T>>> {
    let mut prefix = Vec::new();
    let mut acc = vec![Vec::new()];
    while let Some(obj) = it.next() {
        prefix.push(obj?);
        acc.push(prefix.clone());
    }
    Ok(acc)
}
fn reversed_prefixes<T: Clone>(mut it: impl Iterator<Item = NRes<T>>) -> NRes<Vec<Vec<T>>> {
    let mut prefix = Vec::new();
    let mut acc = vec![Vec::new()];
    while let Some(obj) = it.next() {
        prefix.push(obj?);
        let mut p = prefix.clone();
        p.reverse();
        acc.push(p);
    }
    Ok(acc)
}

// just return Vec<Obj>
macro_rules! multimulti {
    ($name:ident, $expr:expr) => {
        match $name {
            Seq::List($name) => {
                let $name = unwrap_or_clone($name).into_iter().map(Ok);
                Ok($expr?.into_iter().map(|x| Obj::list(x)).collect())
            }
            Seq::String($name) => {
                let mut $name = unwrap_or_clone($name);
                let $name = $name.drain(..).map(Ok);
                Ok($expr?
                    .into_iter()
                    .map(|x| Obj::from(x.into_iter().collect::<String>()))
                    .collect())
            }
            Seq::Dict($name, _def) => {
                let $name = unwrap_or_clone($name)
                    .into_keys()
                    .map(|k| Ok(key_to_obj(k)));
                Ok($expr?.into_iter().map(|x| Obj::list(x)).collect())
            }
            Seq::Vector($name) => {
                let $name = unwrap_or_clone($name).into_iter().map(Ok);
                Ok($expr?
                    .into_iter()
                    .map(|x| Obj::Seq(Seq::Vector(Rc::new(x))))
                    .collect())
            }
            Seq::Bytes($name) => {
                let $name = unwrap_or_clone($name).into_iter().map(Ok);
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

fn multi_group(v: Seq, n: usize, strict: bool) -> NRes<Vec<Obj>> {
    multimulti!(v, grouped(v, n, strict))
}
fn multi_group_by_eq(v: Seq) -> NRes<Vec<Obj>> {
    multimulti!(v, grouped_by(v, |a, b| Ok(a == b)))
}
fn multi_group_by(env: &REnv, f: Func, v: Seq) -> NRes<Vec<Obj>> {
    multimulti!(v, grouped_by(v, |a, b| Ok(f.run2(env, a, b)?.truthy())))
}
fn multi_group_all_with(env: &REnv, f: Func, v: Seq) -> NRes<Vec<Obj>> {
    multimulti!(v, grouped_all_with(v, |x| f.run1(env, x)))
}
fn multi_window(v: Seq, n: usize) -> NRes<Vec<Obj>> {
    multimulti!(v, windowed(v, n))
}
fn multi_prefixes(v: Seq) -> NRes<Vec<Obj>> {
    multimulti!(v, prefixes(v))
}
fn multi_suffixes(v: Seq) -> NRes<Vec<Obj>> {
    let v = multi_reverse(v)?;
    multimulti!(v, reversed_prefixes(v))
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
                    .map(|e| e.and_then(json_encode))
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
                    .map(|(k, v)| (ObjKey::from(k), json_decode(v)))
                    .collect::<HashMap<ObjKey, Obj>>(),
            ),
            None,
        )),
    }
}

#[cfg(feature = "request")]
fn request_response(args: Vec<Obj>) -> NRes<reqwest::blocking::Response> {
    match few2(args) {
        Few2::One(Obj::Seq(Seq::String(url))) => {
            reqwest::blocking::get(&*url).map_err(|e| NErr::io_error(format!("failed: {}", e)))
        }
        Few2::Two(Obj::Seq(Seq::String(url)), Obj::Seq(Seq::Dict(opts, _))) => {
            let client = reqwest::blocking::Client::new();
            let method = match opts.get(&ObjKey::from("method")) {
                Some(Obj::Seq(Seq::String(s))) => match reqwest::Method::from_bytes(s.as_bytes()) {
                    Ok(m) => m,
                    Err(e) => return Err(NErr::value_error(format!("bad method: {}", e))),
                },
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
                    return Err(NErr::type_error(format!("bad form, should be dict: {}", k)))
                }
                None => {}
            }
            match opts.get(&ObjKey::from("json")) {
                Some(map @ Obj::Seq(Seq::Dict(..))) => {
                    builder = builder.json(&json_encode(map.clone())?);
                }
                Some(k) => {
                    return Err(NErr::type_error(format!("bad json, should be dict: {}", k)))
                }
                None => {}
            }
            builder
                .send()
                .map_err(|e| NErr::io_error(format!("built request failed: {}", e)))
        }
        f => Err(NErr::argument_error_few2(&f)),
    }
}

fn read_input(env: &Rc<RefCell<Env>>) -> NRes<Obj> {
    let mut input = String::new();
    match try_borrow_nres(env, "input", "")?.mut_top_env(|t| t.input.read_line(&mut input)) {
        Ok(_) => Ok(Obj::from(input)),
        Err(msg) => Err(NErr::value_error(format!("input failed: {}", msg))),
    }
}

fn string_match(a: &Obj, b: &Obj) -> NRes<bool> {
    match (a, b) {
        (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
            let r =
                Regex::new(&b).map_err(|e| NErr::value_error(format!("invalid regex: {}", e)))?;
            Ok(r.find(&a).is_some())
        }
        (a, b) => Err(NErr::argument_error_2(&a, &b)),
    }
}

pub fn initialize(env: &mut Env) {
    env.insert("true".to_string(), ObjType::Int, Obj::one())
        .unwrap();
    env.insert("false".to_string(), ObjType::Int, Obj::zero())
        .unwrap();

    env.insert_builtin(BasicBuiltin {
        name: "L".to_string(),
        body: |_env, args| Ok(Obj::list(args)),
    });
    env.insert_builtin(BasicBuiltin {
        name: "V".to_string(),
        body: |_env, args| to_obj_vector(args.into_iter().map(Ok)),
    });
    env.insert_builtin(BasicBuiltin {
        name: "B".to_string(),
        body: |_env, args| {
            Ok(Obj::Seq(Seq::Bytes(Rc::new(
                args.into_iter()
                    .map(|e| to_byte(e, "bytes conversion"))
                    .collect::<NRes<Vec<u8>>>()?,
            ))))
        },
    });

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
            Few2::One(s) => expect_nums_and_vectorize_1(|x| Ok(Obj::Num(!x)), s, "unary ~"),
            Few2::Two(a, b) => expect_nums_and_vectorize_2_nums(|a, b| a ^ b, a, b, "binary ~"),
            Few2::Many(_) => Err(NErr::argument_error("received >2 args".to_string())),
        },
    });
    // for partial application
    env.insert_builtin(TwoNumsToNumsBuiltin {
        name: "subtract".to_string(),
        body: |a, b| a - b,
    });
    env.insert_builtin(TwoNumsToNumsBuiltin {
        name: "xor".to_string(),
        body: |a, b| a ^ b,
    });
    env.insert_builtin(TwoNumsToNumsBuiltin {
        name: "⊕".to_string(),
        body: |a, b| a ^ b,
    });
    env.insert_builtin(Times);
    env.insert_builtin(SeqAndMappedFoldBuiltin {
        name: "sum".to_string(),
        identity: Obj::zero(),
        body: |s, f| expect_nums_and_vectorize_2_nums(|a, b| a + b, s, f, "inner +"),
    });
    env.insert_builtin(SeqAndMappedFoldBuiltin {
        name: "product".to_string(),
        identity: Obj::one(),
        body: |s, f| expect_nums_and_vectorize_2_nums(|a, b| a * b, s, f, "inner *"),
    });
    env.insert_builtin(ComparisonOperator::of("==", |a, b| Ok(a == b)));
    env.insert_builtin(ComparisonOperator::of("!=", |a, b| Ok(a != b)));
    env.insert_builtin(ComparisonOperator::of("=~", string_match));
    env.insert_builtin(ComparisonOperator::of("!~", |a, b| {
        string_match(a, b).map(|r| !r)
    }));
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
    env.insert_builtin(TwoNumsToNumsBuiltin {
        name: "%".to_string(),
        body: |a, b| a % b,
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
        name: "/!".to_string(),
        body: |a, b| {
            if b.is_nonzero() {
                let r = a.mod_floor(&b);
                if r.is_nonzero() {
                    Err(NErr::value_error(format!(
                        "division had nonzero remainder {}",
                        r
                    )))
                } else {
                    Ok(Obj::Num(a.div_floor(&b)))
                }
            } else {
                Err(NErr::value_error("division by zero".to_string()))
            }
        },
    });
    env.insert_builtin(TwoNumsToNumsBuiltin {
        name: "gcd".to_string(),
        body: |a, b| a.gcd(&b),
    });
    env.insert_builtin(TwoNumsToNumsBuiltin {
        name: "lcm".to_string(),
        body: |a, b| a.lcm(&b),
    });
    env.insert_rassoc_builtin(TwoNumsToNumsBuiltin {
        name: "^".to_string(),
        body: |a, b| a.pow_num(&b),
    });
    env.insert_builtin(TwoNumsToNumsBuiltin {
        name: "&".to_string(),
        body: |a, b| a & b,
    });
    env.insert_builtin(TwoNumsToNumsBuiltin {
        name: "|".to_string(),
        body: |a, b| a | b,
    });
    /*
    env.insert_builtin(TwoNumsBuiltin {
        name: "@".to_string(),
        body: |a, b| Ok(Obj::Num(a ^ b)),
    });
    */
    env.insert_builtin_with_precedence(
        TwoNumsToNumsBuiltin {
            name: "<<".to_string(),
            body: |a, b| a << b,
        },
        Precedence(EXPONENT_PRECEDENCE, Assoc::Left),
    );
    env.insert_builtin_with_precedence(
        TwoNumsToNumsBuiltin {
            name: ">>".to_string(),
            body: |a, b| a >> b,
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
            Ok(f) => Ok(Obj::Seq(Seq::Vector(Rc::new(vec![
                NNum::from(f),
                NNum::from(0.0),
            ])))),
            Err(c) => Ok(Obj::Seq(Seq::Vector(Rc::new(vec![
                NNum::from(c.re),
                NNum::from(c.im),
            ])))),
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
        body: |a| Ok(Obj::Num(NNum::iverson(into_nint_ok(a)?.lazy_is_prime()))),
    });
    env.insert_builtin(OneNumBuiltin {
        name: "factorize".to_string(),
        body: |a| {
            Ok(Obj::list(
                nnum::lazy_factorize(into_bigint_ok(a)?)
                    .into_iter()
                    .map(|(a, e)| Obj::list(vec![Obj::from(a), Obj::usize(e)]))
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
                let mut c = s.chars();
                match (c.next(), c.next()) {
                    (Some(ch), None) => Ok(Obj::usize(ch as usize)),
                    (None, _) => Err(NErr::value_error("ord of empty string".to_string())),
                    (_, Some(_)) => {
                        Err(NErr::value_error("ord of string with len > 1".to_string()))
                    }
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
                Some(n) => Ok(Obj::usize(n)),
                None => Ok(Obj::from(f64::INFINITY)),
            },
            e => Err(NErr::type_error(format!(
                "sequence only, got {}",
                FmtObj::debug(&e)
            ))),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "only".to_string(),
        body: |arg| match arg {
            Obj::Seq(s) => match s.len() {
                Some(1) => linear_index_isize(s, 0),
                Some(n) => Err(NErr::index_error(format!("required len 1, got len {}", n))),
                None => Err(NErr::index_error(
                    "required len 1, got infinite len".to_string(),
                )),
            },
            e => Err(NErr::type_error(format!(
                "sequence only, got {}",
                FmtObj::debug(&e)
            ))),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "then".to_string(),
        body: |env, a, b| call1(env, b, a),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "apply".to_string(),
        body: |env, mut a, b| {
            call(
                env,
                b,
                mut_obj_into_iter(&mut a, "apply")?.collect::<NRes<Vec<Obj>>>()?,
            )
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "of".to_string(),
        body: |env, a, mut b| {
            call(
                env,
                a,
                mut_obj_into_iter(&mut b, "of")?.collect::<NRes<Vec<Obj>>>()?,
            )
        },
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
        body: |env, a, b| call1(env, b, a),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: ".>".to_string(),
        body: |env, a, b| call1(env, b, a),
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "<.".to_string(),
        body: |env, a, b| call1(env, a, b),
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
                NInt::Small(1),
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
            Obj::Func(f, _) => Ok(Obj::Seq(Seq::Stream(Rc::new(Iterate(Ok((
                a,
                f,
                env.clone(),
            ))))))),
            f => Err(NErr::argument_error_2(&a, &f)),
        },
    });
    // haxx!!!
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "lazy_map".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Stream(s)), Obj::Func(b, _)) => Ok(Obj::Seq(Seq::Stream(Rc::new(
                MappedStream(Ok((s.clone_box(), b, Rc::clone(env)))),
            )))),
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "lazy_filter".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Stream(s)), Obj::Func(b, _)) => Ok(Obj::Seq(Seq::Stream(Rc::new(
                FilteredStream(Ok((s.clone_box(), b, Rc::clone(env)))),
            )))),
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "each".to_string(),
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "each")?;
            match b {
                Obj::Func(b, _) => {
                    for e in it {
                        b.run1(env, e?)?;
                    }
                    Ok(Obj::Null)
                }
                _ => Err(NErr::type_error("not callable".to_string())),
            }
        },
    });
    #[cfg(feature = "parallel")]
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "par_each".to_string(),
        body: |env, mut a, b| {
            let it = mut_obj_into_iter(&mut a, "par_each")?;
            match b {
                Obj::Func(b, _) => {
                    it.par_bridge()
                        .map(|e| {
                            b.run1(env, e?)?;
                            Ok(())
                        })
                        .collect::<NRes<_>>()?;
                    Ok(Obj::Null)
                }
                _ => Err(NErr::type_error("not callable".to_string())),
            }
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "map".to_string(),
        body: |env, mut a, b| {
            let ret = {
                let it = mut_obj_into_iter(&mut a, "map")?;
                match b {
                    Obj::Func(b, _) => Ok(Obj::list(
                        it.map(|e| b.run1(env, e?)).collect::<NRes<Vec<Obj>>>()?,
                    )),
                    _ => Err(NErr::type_error("not callable".to_string())),
                }
            };
            ret
        },
    });
    #[cfg(feature = "parallel")]
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "par_map".to_string(),
        body: |env, mut a, b| {
            let ret = {
                let it = mut_obj_into_iter(&mut a, "par_map")?;
                match b {
                    Obj::Func(b, _) => Ok(Obj::list(
                        it.par_bridge()
                            .map(|e| b.run1(env, e?))
                            .collect::<NRes<Vec<Obj>>>()?,
                    )),
                    _ => Err(NErr::type_error("not callable".to_string())),
                }
            };
            ret
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "map_keys".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut d, def)), Obj::Func(b, _)) => Ok(Obj::dict(
                Rc::make_mut(&mut d)
                    .drain()
                    .map(|(k, v)| Ok((to_key(b.run1(env, key_to_obj(k))?)?, v)))
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
                    .map(|(k, v)| Ok((k, b.run1(env, v)?)))
                    .collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                match def {
                    Some(def) => Some(b.run1(env, *def)?),
                    None => None,
                },
            )),
            _ => Err(NErr::type_error("not dict or callable".to_string())),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "vector_map".to_string(),
        body: |env, mut a, b| {
            let ret = {
                let it = mut_obj_into_iter(&mut a, "vector_map")?;
                match b {
                    Obj::Func(b, _) => Ok(Obj::Seq(Seq::Vector(Rc::new(
                        it.map(|e| match b.run1(env, e?)? {
                            Obj::Num(n) => Ok(n),
                            e => Err(NErr::type_error(format!(
                                "vector_map result not num: {}",
                                e
                            ))),
                        })
                        .collect::<NRes<Vec<NNum>>>()?,
                    )))),
                    _ => Err(NErr::type_error("not callable".to_string())),
                }
            };
            ret
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "filter_keys".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(d, def)), Obj::Func(b, _)) => {
                // don't see an easy functional way to do this given fallible predicate
                let mut m = HashMap::new();
                for (k, v) in d.iter() {
                    if b.run1(env, key_to_obj(k.clone()))?.truthy() {
                        m.insert(k.clone(), v.clone());
                    }
                }
                Ok(Obj::dict(m, def.map(|x| *x)))
            }
            _ => Err(NErr::type_error("not dict or callable".to_string())),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "filter_values".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(d, def)), Obj::Func(b, _)) => {
                let mut m = HashMap::new();
                for (k, v) in d.iter() {
                    if b.run1(env, v.clone())?.truthy() {
                        m.insert(k.clone(), v.clone());
                    }
                }
                Ok(Obj::dict(m, def.map(|x| *x)))
            }
            _ => Err(NErr::type_error("not dict or callable".to_string())),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "filter_items".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(d, def)), Obj::Func(b, _)) => {
                // don't see an easy functional way to do this given fallible predicate
                let mut m = HashMap::new();
                for (k, v) in d.iter() {
                    if b.run2(env, key_to_obj(k.clone()), v.clone())?.truthy() {
                        m.insert(k.clone(), v.clone());
                    }
                }
                Ok(Obj::dict(m, def.map(|x| *x)))
            }
            _ => Err(NErr::type_error("not dict or callable".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "flatten".to_string(),
        body: |mut a| {
            let mut acc = Vec::new();
            for e in mut_obj_into_iter(&mut a, "flatten (outer)")? {
                for k in mut_obj_into_iter(&mut e?, "flatten (inner)")? {
                    acc.push(k?);
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
            for kv in mut_obj_into_iter_pairs(&mut a, "keys")? {
                acc.push(key_to_obj(kv?.0));
            }
            Ok(Obj::list(acc))
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "values".to_string(),
        body: |mut a| {
            let mut acc = Vec::new();
            for kv in mut_obj_into_iter_pairs(&mut a, "values")? {
                acc.push(kv?.1);
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
                        let mut r = b.run1(env, e?)?;
                        for k in mut_obj_into_iter(&mut r, "flat_map (inner)")? {
                            acc.push(k?);
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
                Obj::Func(b, _) => {
                    let mut prev = None;
                    let mut acc = Vec::new();
                    for a in it {
                        let a = a?;
                        match prev.take() {
                            Some(prev) => acc.push(b.run2(env, prev, a.clone())?),
                            None => (),
                        };
                        prev = Some(a);
                    }
                    Ok(Obj::list(acc))
                }
                _ => Err(NErr::type_error("not callable".to_string())),
            }
        },
    });
    env.insert_builtin(Zip);
    env.insert_builtin(ZipLongest);
    env.insert_builtin(LazyZip);
    env.insert_builtin(Parallel);
    env.insert_builtin(Fanout);
    env.insert_builtin(LiftedEquals);
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
                    .collect::<NRes<Vec<Obj>>>()?;
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
                Ok(Obj::Seq(multi_filter(env, f, s, true /* neg */)?))
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
                        let e = e?;
                        if b.run1(env, e.clone())?.truthy() {
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
    env.insert_builtin(SeqAndMappedFoldBuiltin {
        name: "any".to_string(),
        identity: Obj::from(false),
        body: |s, f| {
            if f.truthy() {
                Err(NErr::Break(0, Some(Obj::from(true))))
            } else {
                Ok(s)
            }
        },
    });
    env.insert_builtin(SeqAndMappedFoldBuiltin {
        name: "all".to_string(),
        identity: Obj::from(true),
        body: |s, f| {
            if !f.truthy() {
                Err(NErr::Break(0, Some(Obj::from(false))))
            } else {
                Ok(s)
            }
        },
    });
    env.insert_builtin(Count);
    env.insert_builtin(Group { strict: false });
    env.insert_builtin(Group { strict: true });
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
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "group_all".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(s), Obj::Func(f, _)) => Ok(Obj::list(multi_group_all_with(env, f, s)?)),
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
                *c.entry(to_key(e?)?).or_insert(0) += 1;
            }
            Ok(Obj::Seq(Seq::Dict(
                Rc::new(c.into_iter().map(|(k, v)| (k, Obj::usize(v))).collect()),
                Some(Box::new(Obj::zero())),
            )))
        },
    });
    env.insert_builtin(Fold);
    env.insert_builtin(Scan);
    env.insert_builtin(TwoArgBuiltin {
        name: "<=>".to_string(),
        body: |a, b| match ncmp(&a, &b) {
            Ok(Ordering::Less) => Ok(Obj::neg_one()),
            Ok(Ordering::Equal) => Ok(Obj::zero()),
            Ok(Ordering::Greater) => Ok(Obj::one()),
            Err(e) => Err(e),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: ">=<".to_string(),
        body: |a, b| match ncmp(&a, &b) {
            Ok(Ordering::Less) => Ok(Obj::one()),
            Ok(Ordering::Equal) => Ok(Obj::zero()),
            Ok(Ordering::Greater) => Ok(Obj::neg_one()),
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
        name: "flush".to_string(),
        body: |env, args| {
            if args.is_empty() {
                match try_borrow_nres(env, "flush", &format!("{}", args.len()))?
                    .mut_top_env(|t| t.output.flush())
                {
                    Ok(()) => Ok(Obj::Null),
                    Err(e) => Err(NErr::io_error(format!("flushing {}", e))),
                }
            } else {
                Err(NErr::argument_error_args(&args))?
            }
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
                    writeln!(t.output, "")?;
                    Ok(())
                })
                .map_err(|e| NErr::io_error(format!("writing {}", e)))?;
            Ok(Obj::Null)
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "__internal_debug".to_string(),
        body: |env, args| {
            try_borrow_nres(env, "debug", &format!("{}", args.len()))?
                .mut_top_env(|t| -> io::Result<()> {
                    let mut started = false;
                    for arg in args.iter() {
                        if started {
                            write!(t.output, " ")?;
                        }
                        started = true;
                        write!(t.output, "{:?}", arg)?;
                    }
                    writeln!(t.output, "")?;
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
    env.insert_builtin(OneArgBuiltin {
        name: "repr".to_string(),
        body: |arg| {
            let mut flags = MyFmtFlags::new();
            flags.repr = true;
            Ok(Obj::from(format!("{}", FmtObj(&arg, &flags))))
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
                for arg in mut_obj_into_iter(&mut a, "join (bytes)")? {
                    if started {
                        acc.extend(b.iter())
                    }
                    started = true;
                    acc.extend(
                        mut_obj_into_iter(&mut arg?, "join (bytes) byte conversion")?
                            .map(|e| to_byte(e?, "join (bytes) byte conversion"))
                            .collect::<NRes<Vec<u8>>>()?
                            .iter(),
                    );
                }
                Ok(Obj::Seq(Seq::Bytes(Rc::new(acc))))
            }
            _ => Ok(Obj::from(simple_join(a, format!("{}", b).as_str())?)),
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
    // I learned from Rust docs that terminologically "start" and "end" are better than "left" and
    // "right" since languages can be RTL
    env.insert_builtin(OneArgBuiltin {
        name: "strip_start".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.trim_start())),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "strip_end".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.trim_end())),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "trim_start".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.trim_start())),
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "trim_end".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => Ok(Obj::from(s.trim_end())),
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
    // or, with low precedence, for chaining
    env.insert_builtin(TwoArgBuiltin {
        name: "index".to_string(),
        body: index,
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "!?".to_string(),
        body: safe_index,
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "index?".to_string(),
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
    env.insert_builtin(First);
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
    env.insert_builtin(Last);
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
            Obj::Seq(s) => match uncons(s)? {
                None => Err(NErr::index_error(
                    "Can't uncons empty (or infinite) seq".to_string(),
                )),
                Some((e, s)) => Ok(Obj::list(vec![e, Obj::Seq(s)])),
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "unsnoc".to_string(),
        body: |a| match a {
            Obj::Seq(s) => match unsnoc(s)? {
                None => Err(NErr::index_error(
                    "Can't unsnoc empty (or infinite) seq".to_string(),
                )),
                Some((s, e)) => Ok(Obj::list(vec![Obj::Seq(s), e])),
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "uncons?".to_string(),
        body: |a| match a {
            Obj::Seq(s) => match uncons(s)? {
                None => Ok(Obj::Null),
                Some((e, s)) => Ok(Obj::list(vec![e, Obj::Seq(s)])),
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "unsnoc?".to_string(),
        body: |a| match a {
            Obj::Seq(s) => match unsnoc(s)? {
                None => Ok(Obj::Null),
                Some((s, e)) => Ok(Obj::list(vec![Obj::Seq(s), e])),
            },
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
                    let x = x?;
                    if f.run1(env, x.clone())?.truthy() {
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
                    let x = x?;
                    if f.run1(env, x.clone())?.truthy() {
                        return Ok(x);
                    }
                }
                Ok(Obj::Null)
            }
            b => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "locate".to_string(),
        body: |env, a, b| match (a, b) {
            (mut a, Obj::Func(f, _)) => {
                let mut it = mut_obj_into_iter(&mut a, "locate")?.enumerate();
                while let Some((i, x)) = it.next() {
                    if f.run1(env, x?.clone())?.truthy() {
                        return Ok(Obj::usize(i));
                    }
                }
                Err(NErr::value_error("didn't find".to_string()))
            }
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                match a.find(&*b) {
                    // this is the byte index! shrug
                    Some(i) => Ok(Obj::usize(i)),
                    None => Err(NErr::value_error("didn't find".to_string())),
                }
            }
            (mut a, b) => {
                let mut it = mut_obj_into_iter(&mut a, "locate")?.enumerate();
                while let Some((i, x)) = it.next() {
                    if x? == b {
                        return Ok(Obj::usize(i));
                    }
                }
                Err(NErr::value_error("didn't find".to_string()))
            }
        },
    });
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "locate?".to_string(),
        body: |env, a, b| match (a, b) {
            (mut a, Obj::Func(f, _)) => {
                let mut it = mut_obj_into_iter(&mut a, "locate?")?.enumerate();
                while let Some((i, x)) = it.next() {
                    if f.run1(env, x?.clone())?.truthy() {
                        return Ok(Obj::usize(i));
                    }
                }
                Ok(Obj::Null)
            }
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                match a.find(&*b) {
                    // this is the byte index! shrug
                    Some(i) => Ok(Obj::usize(i)),
                    None => Ok(Obj::Null),
                }
            }
            (mut a, b) => {
                let mut it = mut_obj_into_iter(&mut a, "locate?")?.enumerate();
                while let Some((i, x)) = it.next() {
                    if x? == b {
                        return Ok(Obj::usize(i));
                    }
                }
                Ok(Obj::Null)
            }
        },
    });
    env.insert_builtin(Sort);
    env.insert_builtin(Split);
    env.insert_builtin(RSplit);
    env.insert_builtin(SplitRe);
    env.insert_builtin(EnvTwoArgBuiltin {
        name: "sort_on".to_string(),
        body: |env, a, b| match (a, b) {
            (Obj::Seq(s), Obj::Func(f, _)) => Ok(Obj::Seq(multi_sort_on(env, f, s)?)),
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
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
        name: "||+".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::Dict(b, _))) => {
                let m = Rc::make_mut(&mut a);
                for (k, v) in unwrap_or_clone(b) {
                    match m.entry(k) {
                        std::collections::hash_map::Entry::Vacant(e) => {
                            e.insert(v);
                        }
                        std::collections::hash_map::Entry::Occupied(mut e) => {
                            let slot = e.get_mut();
                            *slot = expect_nums_and_vectorize_2_nums(
                                |a, b| a + b,
                                std::mem::take(slot),
                                v,
                                "||+",
                            )?
                        }
                    }
                }
                Ok(Obj::Seq(Seq::Dict(a, d)))
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "||-".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(Seq::Dict(b, _))) => {
                let m = Rc::make_mut(&mut a);
                for (k, v) in unwrap_or_clone(b) {
                    match m.entry(k) {
                        std::collections::hash_map::Entry::Vacant(e) => {
                            e.insert(expect_nums_and_vectorize_1(
                                |a| Ok(Obj::Num(-a)),
                                v,
                                "||- unary",
                            )?);
                        }
                        std::collections::hash_map::Entry::Occupied(mut e) => {
                            let slot = e.get_mut();
                            *slot = expect_nums_and_vectorize_2_nums(
                                |a, b| a - b,
                                std::mem::take(slot),
                                v,
                                "||-",
                            )?
                        }
                    }
                }
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
                        Rc::make_mut(&mut a).insert(to_key(k?.clone())?, v?.clone());
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
            (Obj::Seq(Seq::List(mut a)), Obj::Seq(mut s)) => {
                let mut it = mut_seq_into_iter(&mut s);
                match (it.next(), it.next(), it.next()) {
                    (Some(k), Some(v), None) => {
                        let i = pythonic_index(&a, &k?.clone())?;
                        Rc::make_mut(&mut a)[i] = v?.clone();
                        Ok(Obj::Seq(Seq::List(a)))
                    }
                    _ => Err(NErr::argument_error("RHS must be pair".to_string())),
                }
            }
            (Obj::Seq(Seq::Dict(mut a, d)), Obj::Seq(mut s)) => {
                let mut it = mut_seq_into_iter(&mut s);
                match (it.next(), it.next(), it.next()) {
                    (Some(k), Some(v), None) => {
                        Rc::make_mut(&mut a).insert(to_key(k?.clone())?, v?.clone());
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
    env.insert_builtin(Set);
    env.insert_builtin(CountDistinct);
    env.insert_builtin(OneArgBuiltin {
        name: "items".to_string(),
        body: |a| match a {
            Obj::Seq(mut s @ Seq::Dict(..)) => Ok(Obj::list(
                mut_seq_into_iter_pairs(&mut s)
                    .map(|kv| {
                        let (k, v) = kv?;
                        Ok(Obj::list(vec![key_to_obj(k), v]))
                    })
                    .collect::<NRes<Vec<Obj>>>()?,
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
                    .map(|(k, v)| Ok(Obj::list(vec![Obj::usize(k), v?])))
                    .collect::<NRes<Vec<Obj>>>()?,
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
            s => Err(NErr::value_error(format!(
                "can't eval {}",
                FmtObj::debug(&s)
            ))),
        },
    });

    env.insert_builtin(BasicBuiltin {
        name: "input".to_string(),
        body: |env, args| match few(args) {
            Few::Zero => read_input(env),
            Few::One(Obj::Seq(Seq::String(s))) => {
                try_borrow_nres(env, "input prompt", "")?
                    .mut_top_env(|t| {
                        write!(t.output, "{}", s)?;
                        t.output.flush()
                    })
                    .map_err(|e| NErr::io_error(format!("input prompt failed: {}", e)))?;
                read_input(env)
            }
            c => err_add_name(Err(NErr::argument_error_few(&c)), "input"),
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
    env.insert_builtin(BasicBuiltin {
        name: "read_bytes".to_string(),
        body: |env, args| {
            if args.is_empty() {
                let mut input = Vec::new();
                // to EOF
                match try_borrow_nres(env, "read_bytes", "")?
                    .mut_top_env(|t| t.input.read_to_end(&mut input))
                {
                    Ok(_) => Ok(Obj::Seq(Seq::Bytes(Rc::new(input)))),
                    Err(msg) => Err(NErr::value_error(format!("input failed: {}", msg))),
                }
            } else {
                Err(NErr::argument_error_args(&args))
            }
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "read_compressed".to_string(),
        body: |env, args| {
            if args.is_empty() {
                let mut input = String::new();
                // to EOF
                match try_borrow_nres(env, "read_compressed", "")?
                    .mut_top_env(|t| GzDecoder::new(&mut t.input).read_to_string(&mut input))
                {
                    Ok(_) => Ok(Obj::from(input)),
                    Err(msg) => Err(NErr::value_error(format!("input failed: {}", msg))),
                }
            } else {
                Err(NErr::argument_error_args(&args))
            }
        },
    });
    // generalized Haskell-ism
    env.insert_builtin(BasicBuiltin {
        name: "interact".to_string(),
        body: |env, args| {
            let mut input = String::new();
            // to EOF
            match try_borrow_nres(env, "interact", "")?
                .mut_top_env(|t| t.input.read_to_string(&mut input))
            {
                Ok(_) => {
                    let mut cur = Obj::from(input);
                    for arg in args {
                        match arg {
                            Obj::Func(f, _) => {
                                cur = f.run1(env, cur)?;
                            }
                            _ => return Err(NErr::type_error("not callable".to_string())),
                        }
                    }

                    try_borrow_nres(env, "interact print", "")?
                        .mut_top_env(|t| -> io::Result<()> {
                            write!(t.output, "{}", cur)?;
                            Ok(())
                        })
                        .map_err(|e| NErr::io_error(format!("writing {}", e)))?;
                    Ok(Obj::Null)
                }
                Err(msg) => Err(NErr::value_error(format!(
                    "interact: input failed: {}",
                    msg
                ))),
            }
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "interact_lines".to_string(),
        body: |env, args| {
            let mut input = String::new();
            // to EOF
            match try_borrow_nres(env, "interact", "")?
                .mut_top_env(|t| t.input.read_to_string(&mut input))
            {
                Ok(_) => {
                    let mut cur = Obj::list(
                        input
                            .split_terminator('\n')
                            .map(|w| Obj::from(w.to_string()))
                            .collect(),
                    );
                    for arg in args {
                        match arg {
                            Obj::Func(f, _) => {
                                cur = f.run1(env, cur)?;
                            }
                            _ => return Err(NErr::type_error("not callable".to_string())),
                        }
                    }

                    try_borrow_nres(env, "interact print", "")?.mut_top_env(|t| -> NRes<()> {
                        for out_line in mut_obj_into_iter(&mut cur, "interact lines print")? {
                            writeln!(t.output, "{}", out_line?)
                                .map_err(|e| NErr::io_error(format!("writing {}", e)))?;
                        }
                        Ok(())
                    })?;
                    Ok(Obj::Null)
                }
                Err(msg) => Err(NErr::value_error(format!(
                    "interact: input failed: {}",
                    msg
                ))),
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
                                char::from_digit((&a % &r).to_u32().expect("str_radix bad"), base)
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
                if let Some(base) = n.to_nint().and_then(NInt::to_u32) {
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
        name: "utf8_encode".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::String(s)) => Ok(Obj::Seq(Seq::Bytes(Rc::new(s.as_bytes().to_vec())))),
            _ => Err(NErr::type_error("must utf8encode string".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "utf8_decode".to_string(),
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
        name: "base64_encode".to_string(),
        body: |arg| match arg {
            Obj::Seq(Seq::Bytes(b)) => Ok(Obj::from(base64::encode(&*b))),
            _ => Err(NErr::type_error("must hex_encode bytes".to_string())),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "base64_decode".to_string(),
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

    env.insert_builtin(OneArgBuiltin {
        name: "compress".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::Bytes(b)) => {
                let mut gz = GzEncoder::new(&b[..], Compression::fast());
                let mut s = Vec::new();
                gz.read_to_end(&mut s).expect("what");
                Ok(Obj::Seq(Seq::Bytes(Rc::new(s))))
            }
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "decompress".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::Bytes(b)) => {
                let mut gz = GzDecoder::new(&b[..]);
                let mut s = Vec::new();
                gz.read_to_end(&mut s).expect("what");
                Ok(Obj::Seq(Seq::Bytes(Rc::new(s))))
            }
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
    env.insert_builtin(OneArgBuiltin {
        name: "read_file_bytes".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => match fs::read(&*s) {
                Ok(c) => Ok(Obj::Seq(Seq::Bytes(Rc::new(c)))),
                Err(e) => Err(NErr::io_error(format!("{}", e))),
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "read_file_bytes?".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => match fs::File::open(&*s) {
                Ok(mut f) => {
                    let mut contents = Vec::new();
                    match f.read(&mut contents) {
                        Ok(_) => Ok(Obj::Seq(Seq::Bytes(Rc::new(contents)))),
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
    env.insert_builtin(OneArgBuiltin {
        name: "list_files".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(s)) => match fs::read_dir(&*s) {
                Ok(c) => match c
                    .map(|d| d.map(|e| e.path()))
                    .collect::<Result<Vec<_>, io::Error>>()
                {
                    Ok(c) => Ok(Obj::list(
                        c.into_iter()
                            .map(|s| Obj::from(s.to_string_lossy().into_owned()))
                            .collect(),
                    )),
                    Err(e) => Err(NErr::io_error(format!("{}", e))),
                },
                Err(e) => Err(NErr::io_error(format!("{}", e))),
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "write_file".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Bytes(b)), Obj::Seq(Seq::String(f))) => {
                match fs::write(f.as_str(), &**b) {
                    Ok(()) => Ok(Obj::Null),
                    Err(e) => Err(NErr::io_error(format!("{}", e))),
                }
            }
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(f))) => {
                match fs::write(f.as_str(), s.as_bytes()) {
                    Ok(()) => Ok(Obj::Null),
                    Err(e) => Err(NErr::io_error(format!("{}", e))),
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "append_file".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::Bytes(b)), Obj::Seq(Seq::String(f))) => {
                match fs::OpenOptions::new()
                    .append(true)
                    .create(true)
                    .open(f.as_str())
                {
                    Ok(mut file) => match file.write(&**b) {
                        Ok(_size) => Ok(Obj::Null),
                        Err(e) => Err(NErr::io_error(format!("{}", e))),
                    },
                    Err(e) => Err(NErr::io_error(format!("{}", e))),
                }
            }
            (Obj::Seq(Seq::String(s)), Obj::Seq(Seq::String(f))) => {
                match fs::OpenOptions::new()
                    .append(true)
                    .create(true)
                    .open(f.as_str())
                {
                    Ok(mut file) => match file.write(s.as_bytes()) {
                        Ok(_size) => Ok(Obj::Null),
                        Err(e) => Err(NErr::io_error(format!("{}", e))),
                    },
                    Err(e) => Err(NErr::io_error(format!("{}", e))),
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(BasicBuiltin {
        name: "run_process".to_string(),
        body: |_env, args| match few3(args) {
            Few3::Two(Obj::Seq(Seq::String(s)), Obj::Seq(mut args)) => {
                match std::process::Command::new(&*s)
                    .args(
                        mut_seq_into_iter(&mut args)
                            .map(|s| Ok(format!("{}", s?)))
                            .collect::<NRes<Vec<String>>>()?,
                    )
                    .output()
                {
                    Ok(res) => {
                        if res.status.success() {
                            Ok(Obj::Seq(Seq::Bytes(Rc::new(res.stdout))))
                        } else {
                            Err(NErr::io_error(format!(
                                "subprocess exited with nonzero status {}",
                                res.status
                            )))
                        }
                    }
                    Err(e) => Err(NErr::io_error(format!("{}", e))),
                }
            }
            Few3::Three(Obj::Seq(Seq::String(s)), Obj::Seq(mut args), Obj::Seq(Seq::Bytes(b))) => {
                match std::process::Command::new(&*s)
                    .args(
                        mut_seq_into_iter(&mut args)
                            .map(|s| Ok(format!("{}", s?)))
                            .collect::<NRes<Vec<String>>>()?,
                    )
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn()
                {
                    Ok(mut child) => {
                        let mut stdin = child
                            .stdin
                            .take()
                            .ok_or(NErr::io_error(format!("Failed to open child stdin")))?;
                        let bc: Vec<u8> = (*b).clone();
                        let writer = std::thread::spawn(move || {
                            stdin.write_all(&bc).expect("couldn't write to stdin")
                        });

                        let res = child
                            .wait_with_output()
                            .map_err(|e| NErr::io_error(format!("{}", e)))?;
                        writer.join().map_err(|_| {
                            NErr::io_error(format!("Failed to join child stdin writer"))
                        })?;
                        if res.status.success() {
                            Ok(Obj::Seq(Seq::Bytes(Rc::new(res.stdout))))
                        } else {
                            Err(NErr::io_error(format!(
                                "subprocess exited with nonzero status {}",
                                res.status
                            )))
                        }
                    }
                    Err(e) => Err(NErr::io_error(format!("{}", e))),
                }
            }
            c => err_add_name(Err(NErr::argument_error_few3(&c)), "run_process"),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "path_parent".to_string(),
        body: |a| match a {
            Obj::Seq(Seq::String(a)) => match std::path::Path::new(&*a).parent() {
                Some(p) => Ok(Obj::from(p.to_string_lossy().into_owned())),
                None => Err(NErr::value_error(format!("No path parent: {}", a))),
            },
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "path_join".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Seq(Seq::String(a)), Obj::Seq(Seq::String(b))) => {
                let mut ap = std::path::PathBuf::from(&*a);
                ap.push(&*b);
                Ok(Obj::from(ap.to_string_lossy().into_owned()))
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
    env.insert_builtin(OneArgBuiltin {
        name: "sleep".to_string(),
        body: |a| match a {
            Obj::Num(a) => {
                if let Some(f) = a.to_f64() {
                    if f >= 0.0f64 && f.is_finite() {
                        // TODO: use try_from_secs_f64 when stable
                        std::thread::sleep(std::time::Duration::from_secs_f64(f));
                        return Ok(Obj::Null);
                    }
                }
                Err(NErr::type_error(format!("can't sleep: {}", a)))
            }
            a => Err(NErr::argument_error_1(&a)),
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
    env.insert_builtin(OneArgBuiltin {
        name: "random_bytes".to_string(),
        body: |a| match a {
            Obj::Num(a) => {
                let sz = to_usize_ok(&a)?;
                let mut bytes = vec![0; sz];
                rand::thread_rng().fill_bytes(&mut bytes);
                Ok(Obj::Seq(Seq::Bytes(Rc::new(bytes))))
            }
            a => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "random_range".to_string(),
        body: |a, b| match (a, b) {
            (Obj::Num(NNum::Int(a)), Obj::Num(NNum::Int(b))) => {
                if a >= b {
                    Err(NErr::value_error(
                        "random_range: lower >= upper".to_string(),
                    ))
                } else {
                    Ok(Obj::from(
                        rand::thread_rng().gen_bigint_range(&a.to_bigint(), &b.to_bigint()),
                    ))
                }
            }
            (a, b) => Err(NErr::argument_error_2(&a, &b)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "shuffle".to_string(),
        body: |a| match a {
            Obj::Seq(mut seq) => match seq {
                Seq::Bytes(ref mut l) => {
                    Rc::make_mut(l).shuffle(&mut rand::thread_rng());
                    Ok(Obj::Seq(seq))
                }
                Seq::Vector(ref mut l) => {
                    Rc::make_mut(l).shuffle(&mut rand::thread_rng());
                    Ok(Obj::Seq(seq))
                }
                Seq::List(ref mut l) => {
                    Rc::make_mut(l).shuffle(&mut rand::thread_rng());
                    Ok(Obj::Seq(seq))
                }
                Seq::String(s) => {
                    let mut chars: Vec<char> = s.chars().collect();
                    chars.shuffle(&mut rand::thread_rng());
                    Ok(Obj::Seq(Seq::String(Rc::new(chars.into_iter().collect()))))
                }
                s => Err(NErr::argument_error_1(&Obj::Seq(s))),
            },
            _ => Err(NErr::argument_error_1(&a)),
        },
    });
    env.insert_builtin(OneArgBuiltin {
        name: "choose".to_string(),
        body: |a| match a {
            Obj::Seq(seq) => {
                match seq {
                    Seq::Bytes(l) => l
                        .choose(&mut rand::thread_rng())
                        .map(|n| Obj::u8(*n))
                        .ok_or_else(|| {
                            NErr::value_error("Can't choose from empty bytes".to_string())
                        }),
                    Seq::Vector(l) => l
                        .choose(&mut rand::thread_rng())
                        .map(|n| Obj::from(n.clone()))
                        .ok_or_else(|| {
                            NErr::value_error("Can't choose from empty vector".to_string())
                        }),
                    Seq::List(l) => l.choose(&mut rand::thread_rng()).cloned().ok_or_else(|| {
                        NErr::value_error("Can't choose from empty list".to_string())
                    }),
                    Seq::String(s) => {
                        if s.len() == 0 {
                            Err(NErr::value_error("Can't choose from empty string".into()))
                        } else {
                            let rind = rand::thread_rng().gen_range(0..s.len());
                            Ok(Obj::Seq(Seq::String(Rc::new(
                                s.chars().nth(rind).map(String::from).unwrap(),
                            ))))
                        }
                    }
                    Seq::Dict(d, _) => {
                        if d.len() == 0 {
                            // TODO use default value when empty?
                            Err(NErr::value_error(
                                "Can't choose from empty dictionary".into(),
                            ))
                        } else {
                            let rind = rand::thread_rng().gen_range(0..d.len());
                            Ok(d.values().nth(rind).unwrap().clone())
                        }
                    }
                    s => Err(NErr::argument_error_1(&Obj::Seq(s))),
                }
            }
            _ => Err(NErr::argument_error_1(&a)),
        },
    });

    #[cfg(feature = "request")]
    env.insert_builtin(BasicBuiltin {
        name: "request".to_string(),
        body: |_env, args| {
            let resp = request_response(args)?;
            match resp.text() {
                Ok(s) => Ok(Obj::from(s)),
                Err(e) => Err(NErr::io_error(format!("failed: {}", e))),
            }
        },
    });

    #[cfg(feature = "request")]
    env.insert_builtin(BasicBuiltin {
        name: "request_bytes".to_string(),
        body: |_env, args| match request_response(args)?.bytes() {
            Ok(b) => Ok(Obj::Seq(Seq::Bytes(Rc::new(b.to_vec())))),
            Err(e) => Err(NErr::io_error(format!("failed: {}", e))),
        },
    });

    #[cfg(feature = "request")]
    env.insert_builtin(BasicBuiltin {
        name: "request_json".to_string(),
        body: |_env, args| match request_response(args)?.json() {
            Ok(j) => Ok(json_decode(j)),
            Err(e) => Err(NErr::io_error(format!("failed: {}", e))),
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
        env.insert_builtin(BasicBuiltin {
            name: "aes256_gcm_encrypt".to_string(),
            body: |_env, args| match few3(args) {
                Few3::Three(
                    Obj::Seq(Seq::Bytes(k)),
                    Obj::Seq(Seq::Bytes(n)),
                    Obj::Seq(Seq::Bytes(m)),
                ) => {
                    if k.len() == 32 && n.len() == 12 {
                        let cipher =
                            aes_gcm::Aes256Gcm::new(generic_array::GenericArray::from_slice(&k));
                        let nonce = aes_gcm::Nonce::from_slice(&n);
                        match cipher.encrypt(nonce, &**m) {
                            Ok(ct) => Ok(Obj::Seq(Seq::Bytes(Rc::new(ct)))),
                            Err(e) => Err(NErr::io_error(format!("{}", e))),
                        }
                    } else {
                        Err(NErr::value_error(
                            "aes256_gcm_encrypt: bad sizes".to_string(),
                        ))
                    }
                }
                _ => Err(NErr::argument_error(format!("Bad args for aes-gcm"))),
            },
        });
        env.insert_builtin(BasicBuiltin {
            name: "aes256_gcm_decrypt".to_string(),
            body: |_env, args| match few3(args) {
                Few3::Three(
                    Obj::Seq(Seq::Bytes(k)),
                    Obj::Seq(Seq::Bytes(n)),
                    Obj::Seq(Seq::Bytes(m)),
                ) => {
                    if k.len() == 32 && n.len() == 12 {
                        let cipher =
                            aes_gcm::Aes256Gcm::new(generic_array::GenericArray::from_slice(&k));
                        let nonce = aes_gcm::Nonce::from_slice(&n);
                        match cipher.decrypt(nonce, &**m) {
                            Ok(ct) => Ok(Obj::Seq(Seq::Bytes(Rc::new(ct)))),
                            Err(e) => Err(NErr::io_error(format!("{}", e))),
                        }
                    } else {
                        Err(NErr::value_error(
                            "aes256_gcm_encrypt: bad sizes".to_string(),
                        ))
                    }
                }
                c => err_add_name(Err(NErr::argument_error_few3(&c)), "aes-gcm"),
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
                                ObjKey::from(k.clone()),
                                try_borrow_nres(v, "vars", k)?.clone(),
                            ))
                        })
                        .collect::<NRes<HashMap<ObjKey, Obj>>>()?,
                ),
                None,
            )))
        },
    });

    env.insert_builtin(OneArgBuiltin {
        name: "is_big".to_string(),
        body: |a| match a {
            Obj::Num(NNum::Int(NInt::Big(_))) => Ok(Obj::one()),
            _ => Ok(Obj::zero()),
        },
    });
}

// #[cfg_attr(target_arch = "wasm32")]
#[cfg(target_arch = "wasm32")]
pub fn obj_to_js_value(obj: Obj) -> JsValue {
    match obj {
        Obj::Null => JsValue::NULL,
        Obj::Seq(Seq::List(ls)) => JsValue::from(
            ls.iter()
                .map(|obj| obj_to_js_value(obj.clone()))
                .collect::<js_sys::Array>(),
        ),
        Obj::Seq(Seq::Vector(ls)) => JsValue::from(
            ls.iter()
                .map(|obj| obj_to_js_value(Obj::from(obj.clone())))
                .collect::<js_sys::Array>(),
        ),
        Obj::Seq(Seq::Dict(d, def)) => {
            let a = d
                .iter()
                .map(|(k, v)| {
                    JsValue::from(js_sys::Array::of2(
                        &obj_to_js_value(key_to_obj(k.clone())),
                        &obj_to_js_value(v.clone()),
                    ))
                })
                .collect::<js_sys::Array>();
            match def {
                None => {}
                Some(def) => {
                    // FIXME Noulith doesn't have booleans so use JS false as
                    // a "default" sentinel (symbols can't pass the webworker serialization
                    // barrier) (I am lazy)
                    a.unshift(&JsValue::from(js_sys::Array::of2(
                        // &JsValue::symbol(Some("default")),
                        &JsValue::FALSE,
                        &obj_to_js_value(*def),
                    )));
                }
            };
            JsValue::from(a)
        }
        Obj::Instance(s, fields) => {
            // FIXME lol lmao
            let a = fields
                .iter()
                .map(|obj| obj_to_js_value(Obj::from(obj.clone())))
                .collect::<js_sys::Array>();
            a.unshift(&JsValue::from(&*s.name));
            a.unshift(&JsValue::TRUE);
            JsValue::from(a)
        }
        _ => JsValue::from(format!("{}", obj)),
    }
}

// Can't be bothered to write the code to create JavaScript objects with nice keys and everything
// (looks annoying, apparently use js_sys::Reflect)
// just return an [stdout, error, result] array
#[cfg(target_arch = "wasm32")]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub fn encapsulated_eval(code: &str, input: &[u8], fancy: bool) -> js_sys::Array {
    let mut env = Env::new(TopEnv {
        backrefs: Vec::new(),
        input: Box::new(io::Cursor::new(input.to_vec())),
        output: Box::new(Vec::new()),
    });
    initialize(&mut env);

    let tag_struct = Struct::new(
        Rc::new("HtmlTag".to_string()),
        Rc::new(vec![
            ("name".to_string(), None),
            ("children".to_string(), Some(Obj::list(vec![]))),
            (
                "attributes".to_string(),
                Some(Obj::dict(HashMap::new(), None)),
            ),
        ]),
    );
    env.insert(
        "HtmlTag".to_string(),
        ObjType::Func,
        Obj::Func(
            Func::Type(ObjType::Struct(tag_struct.clone())),
            Precedence::zero(),
        ),
    )
    .unwrap();
    env.insert(
        "html_tag_name".to_string(),
        ObjType::Func,
        Obj::Func(Func::StructField(tag_struct.clone(), 0), Precedence::zero()),
    )
    .unwrap();
    env.insert(
        "html_tag_children".to_string(),
        ObjType::Func,
        Obj::Func(Func::StructField(tag_struct.clone(), 1), Precedence::zero()),
    )
    .unwrap();
    env.insert(
        "html_tag_attributes".to_string(),
        ObjType::Func,
        Obj::Func(Func::StructField(tag_struct.clone(), 2), Precedence::zero()),
    )
    .unwrap();

    let e = Rc::new(RefCell::new(env));

    let mut output = JsValue::UNDEFINED;
    let mut error = JsValue::UNDEFINED;
    let mut result = JsValue::UNDEFINED;

    match parse(code) {
        Err(p) => {
            error = JsValue::from(p.render(code));
        }
        Ok(None) => {}
        Ok(Some(code)) => match evaluate(&e, &code) {
            Err(err) => {
                output = JsValue::from(e.borrow_mut().mut_top_env(|e| {
                    String::from_utf8_lossy(e.output.extract().unwrap()).into_owned()
                }));
                error = JsValue::from(format!("{}", err));
            }
            Ok(res) => {
                let output_s = e.borrow_mut().mut_top_env(|e| {
                    String::from_utf8_lossy(e.output.extract().unwrap()).into_owned()
                });
                if fancy {
                    output = JsValue::from(output_s);
                    result = obj_to_js_value(res);
                } else {
                    output = JsValue::from(output_s + &format!("{}", res));
                }
            }
        },
    }
    js_sys::Array::of3(&output, &error, &result)
}
