#[macro_use] extern crate lazy_static;

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

// TODO: drop Rc?
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

/*
fn to_bigint_ok(n: &NNum) -> NRes<BigInt> {
    Ok(n.to_bigint().ok_or(NErr::ValueError("bad number to int".to_string()))?.clone())
}
*/
fn into_bigint_ok(n: NNum) -> NRes<BigInt> {
    n.into_bigint().ok_or(NErr::ValueError("bad number to int".to_string()))
}

fn to_key(obj: Obj) -> NRes<ObjKey> {
    match obj {
        Obj::Null => Ok(ObjKey::Null),
        Obj::Num(x) => Ok(ObjKey::Num(NTotalNum(x))),
        Obj::String(x) => Ok(ObjKey::String(x)),
        mut x @ Obj::List(_) => Ok(ObjKey::List(Rc::new(
                    mut_obj_into_iter(&mut x)?.map(|e| to_key(e)).collect::<NRes<Vec<ObjKey>>>()?))),
        mut x @ Obj::Dict(..) => {
            let pairs = mut_obj_into_iter_pairs(&mut x)?.map(
                |(k,v)| Ok((k,to_key(v)?))).collect::<NRes<Vec<(ObjKey,ObjKey)>>>()?;
            Ok(ObjKey::Dict(Rc::new(pairs)))
        }
        Obj::Func(_) => Err(NErr::TypeError("Using a function as a dictionary key isn't supported".to_string())),
    }
}

fn key_to_obj(key: &ObjKey) -> Obj {
    match key {
        ObjKey::Null => Obj::Null,
        ObjKey::Num(NTotalNum(x)) => Obj::Num((*x).clone()),
        ObjKey::String(x) => Obj::String(Rc::clone(x)),
        ObjKey::List(x) => Obj::List(Rc::new(x.iter().map(|e| key_to_obj(&e.clone())).collect::<Vec<Obj>>())),
        ObjKey::Dict(x) => Obj::Dict(Rc::new(x.iter().map(|(k, v)| (k.clone(), key_to_obj(&v))).collect::<HashMap<ObjKey,Obj>>()), None),
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

// iterates over just keys of dictionaries
pub enum MutObjIntoIter<'a> {
    DrainList(std::vec::Drain<'a, Obj>),
    CloneList(std::slice::Iter<'a, Obj>),
    DrainDict(std::collections::hash_map::Drain<'a, ObjKey, Obj>),
    CloneDict(std::collections::hash_map::Iter<'a, ObjKey, Obj>),
}

// iterates over (index, value) or (key, value)
pub enum MutObjIntoIterPairs<'a> {
    DrainList(usize, std::vec::Drain<'a, Obj>),
    CloneList(usize, std::slice::Iter<'a, Obj>),
    DrainDict(std::collections::hash_map::Drain<'a, ObjKey, Obj>),
    CloneDict(std::collections::hash_map::Iter<'a, ObjKey, Obj>),
}

// Say the obj is a list. If the Rc<Vec> has refcount 1, we drain it, so we can lazily move out
// each element; but if the obj has refcount >1, we lazily clone each element. At least, that's the
// theory.
//
// Alternatively, consuming the object and either going IntoIter or handrolling a (Rc<Vec>, usize)
// would also work fine for lists, but dictionaries don't have an easy handrollable self-owning
// iterator, I think?
fn mut_obj_into_iter(obj: &mut Obj) -> NRes<MutObjIntoIter<'_>> {
    match obj {
        Obj::List(v) => {
            // Some non-lexical lifetime stuff going on here, matching Rc::get_mut(v) doesn't drop
            // it in the None branch and we can't access v again even though we should be able to.
            // If I switch to nightly I can probably use #![feature(nll)]
            if Rc::get_mut(v).is_some() {
                match Rc::get_mut(v) {
                    Some(v) => Ok(MutObjIntoIter::DrainList(v.drain(..))),
                    None => Err(NErr::TypeError("non-lexical lifetime issue".to_string())),
                }
            } else {
                Ok(MutObjIntoIter::CloneList(v.iter()))
            }
        }
        Obj::Dict(v, _) => {
            if Rc::get_mut(v).is_some() {
                match Rc::get_mut(v) {
                    Some(v) => Ok(MutObjIntoIter::DrainDict(v.drain())),
                    None => Err(NErr::TypeError("non-lexical lifetime issue".to_string())),
                }
            } else {
                Ok(MutObjIntoIter::CloneDict(v.iter()))
            }
        }
        _ => Err(NErr::TypeError("no".to_string())),
    }
}

impl Iterator for MutObjIntoIter<'_> {
    type Item = Obj;

    fn next(&mut self) -> Option<Obj> {
        match self {
            MutObjIntoIter::DrainList(it) => it.next(),
            MutObjIntoIter::CloneList(it) => it.next().cloned(),
            MutObjIntoIter::DrainDict(it) => Some(key_to_obj(&it.next()?.0)),
            MutObjIntoIter::CloneDict(it) => Some(key_to_obj(it.next()?.0)),
        }
    }
}

fn mut_obj_into_iter_pairs(obj: &mut Obj) -> NRes<MutObjIntoIterPairs<'_>> {
    match obj {
        Obj::List(v) => {
            // Some non-lexical lifetime stuff going on here, matching Rc::get_mut(v) doesn't drop
            // it in the None branch and we can't access v again even though we should be able to.
            // If I switch to nightly I can probably use #![feature(nll)]
            if Rc::get_mut(v).is_some() {
                match Rc::get_mut(v) {
                    Some(v) => Ok(MutObjIntoIterPairs::DrainList(0, v.drain(..))),
                    None => Err(NErr::TypeError("non-lexical lifetime issue".to_string())),
                }
            } else {
                Ok(MutObjIntoIterPairs::CloneList(0, v.iter()))
            }
        }
        Obj::Dict(v, _) => {
            if Rc::get_mut(v).is_some() {
                match Rc::get_mut(v) {
                    Some(v) => Ok(MutObjIntoIterPairs::DrainDict(v.drain())),
                    None => Err(NErr::TypeError("non-lexical lifetime issue".to_string())),
                }
            } else {
                Ok(MutObjIntoIterPairs::CloneDict(v.iter()))
            }
        }
        _ => Err(NErr::TypeError("no".to_string())),
    }
}

impl Iterator for MutObjIntoIterPairs<'_> {
    type Item = (ObjKey, Obj);

    fn next(&mut self) -> Option<(ObjKey, Obj)> {
        match self {
            MutObjIntoIterPairs::DrainList(i, it) => { let o = it.next()?; let j = *i; *i += 1; Some((ObjKey::from(j), o)) }
            MutObjIntoIterPairs::CloneList(i, it) => { let o = it.next()?; let j = *i; *i += 1; Some((ObjKey::from(j), o.clone())) }
            MutObjIntoIterPairs::DrainDict(it) => it.next(),
            MutObjIntoIterPairs::CloneDict(it) => { let (k, v) = it.next()?; Some((k.clone(), v.clone())) }
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

pub type NRes<T> = Result<T, NErr>;

#[derive(Debug, Clone)]
pub enum Func {
    Builtin(Rc<dyn Builtin>),
    Closure(Closure),

    // For now specifically partial application of a binary function to its second argument
    PartialApp(Box<Func>, Box<Obj>),
}

impl Func {
    fn run(&self, mut args: Vec<Obj>) -> NRes<Obj> {
        match self {
            Func::Builtin(b) => b.run(args),
            Func::Closure(c) => c.run(args),
            Func::PartialApp(f, x) => {
                if args.len() == 1 {
                    f.run(vec![args.pop().unwrap(), (**x).clone()])
                } else {
                    Err(NErr::ArgumentError("For now, partially applied functions can only be called with one more argument".to_string()))
                }
            }
        }
    }

    // Whether this might possibly look up a name in an environment
    fn can_refer(&self) -> bool {
        match self {
            Func::Builtin(b) => b.can_refer(),
            Func::Closure(_) => true,
            Func::PartialApp(f, _) => f.can_refer(),
        }
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match self {
            Func::Builtin(b) => b.try_chain(other),
            Func::Closure(_) => None,
            Func::PartialApp(..) => None,
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
    fn run(&self, mut args: Vec<Obj>) -> NRes<Obj> {
        if self.chained.is_empty() {
            match args.len() {
                0 => Err(NErr::ArgumentError(format!("Comparison operator {:?} needs 2+ args", self.name))),
                1 => Ok(Obj::Func(Func::PartialApp(
                    Box::new(Func::Builtin(Rc::new(self.clone()))),
                    Box::new(args.pop().unwrap())
                ))),
                _ => {
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
    fn run(&self, mut args: Vec<Obj>) -> NRes<Obj> {
        if args.len() == 1 {
            (self.body)(args.pop().unwrap())
        } else {
            Err(NErr::ArgumentError(format!("{} only accepts one argument, got {}", self.name, args.len())))
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
    fn run(&self, mut args: Vec<Obj>) -> NRes<Obj> {
        match args.pop() {
            None => Err(NErr::ArgumentError(format!("{} only accepts two arguments, got 0", self.name))),
            Some(b) => match args.pop() {
                None => {
                    // partial application, spicy
                    Ok(Obj::Func(Func::PartialApp(
                        Box::new(Func::Builtin(Rc::new(self.clone()))),
                        Box::new(b)
                    )))
                }
                Some(a) => if args.is_empty() {
                    (self.body)(a, b)
                } else {
                    Err(NErr::ArgumentError(format!("{} only accepts two arguments, got {}", self.name, args.len() + 2)))
                }
            }
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
    fn run(&self, mut args: Vec<Obj>) -> NRes<Obj> {
        if args.len() == 1 {
            match args.pop().unwrap() {
                Obj::Num(n) => (self.body)(n),
                x => Err(NErr::ArgumentError(format!("{} only accepts numbers, got {:?}", self.name, x))),
            }
        } else {
            Err(NErr::ArgumentError(format!("{} only accepts one argument, got {}", self.name, args.len())))
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
    fn run(&self, mut args: Vec<Obj>) -> NRes<Obj> {
        if args.len() == 2 {
            let b = args.pop().unwrap();
            let a = args.pop().unwrap();
            match (a, b) {
                (Obj::Num(aa), Obj::Num(bb)) => (self.body)(aa, bb),
                (aaa, bbb) => Err(NErr::ArgumentError(format!("{} only accepts numbers, got {:?} {:?}", self.name, aaa, bbb))),
            }
        } else {
            Err(NErr::ArgumentError(format!("{} only accepts two numbers, got {}", self.name, args.len())))
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
        let env = Env { vars: HashMap::new(), parent: Some(Rc::clone(&self.env)) };
        let ee = Rc::new(RefCell::new(env));
        let p = self.params.iter().map(|e| Ok(Box::new(eval_lvalue(&ee, e)?))).collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?;
        assign_all(&mut ee.borrow_mut(), &p, &args, true)?;
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
    // Newline,
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
    Assign(Box<Lvalue>, Box<Expr>),
    OpAssign(Box<Lvalue>, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    For(Box<Lvalue>, Box<Expr>, Box<Expr>),
    ForItem(Box<Lvalue>, Box<Expr>, Box<Expr>),
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
                    Ok(Expr::Splat(Box::new(self.atom()?)))
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
                    let pat0 = self.pattern()?;
                    let pat = to_lvalue(pat0)?;
                    let is_item = match self.peek() {
                        Some(Token::Colon) => false,
                        Some(Token::DoubleColon) => true,
                        p => return Err(format!("for: require : or ::, got {:?}", p)),
                    };
                    self.advance();
                    let iteratee = self.pattern()?;
                    self.require(Token::RightParen, "for iter end".to_string())?;
                    let body = self.assignment()?;
                    Ok(if is_item {
                        Expr::ForItem(Box::new(pat), Box::new(iteratee), Box::new(body))
                    } else {
                        Expr::For(Box::new(pat), Box::new(iteratee), Box::new(body))
                    })
                }
                _ => Err(format!("unexpected {:?}", token)),
            }
        } else {
            Err("atom: ran out of stuff to parse".to_string())
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

    // Comma-separated things. No semicolons or assigns allowed
    fn pattern(&mut self) -> Result<Expr, String> {
        let (mut exs, comma) = self.comma_separated()?;
        Ok(if exs.len() == 1 && !comma {
            *exs.swap_remove(0)
        } else {
            Expr::CommaSeq(exs)
        })
    }

    fn assignment(&mut self) -> Result<Expr, String> {
        let pat = self.pattern()?;

        if self.peek() == Some(Token::Assign) {
            self.i += 1;
            match pat {
                Expr::Call(lhs, mut op) => {
                    if op.len() == 1 {
                        Ok(Expr::OpAssign(
                            Box::new(to_lvalue(*lhs)?),
                            Box::new(*op.swap_remove(0)),
                            Box::new(self.pattern()?),
                        ))
                    } else {
                        Err("call w not 1 arg is not assignop".to_string())
                    }
                }
                _ => {
                    Ok(Expr::Assign(Box::new(to_lvalue(pat)?), Box::new(self.pattern()?)))
                }
            }
        } else {
            Ok(pat)
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
    fn get_var(self: &Env, s: &str) -> NRes<Obj> {
        match self.vars.get(s) {
            Some(v) => Ok(v.clone()),
            None => match &self.parent {
                Some(p) => p.borrow().get_var(s),
                None => Err(NErr::NameError(format!("No such variable: {}", s))),
            }
        }
    }

    fn modify_existing_var(self: &mut Env, key: &str, f: impl FnOnce(&mut Obj) -> ()) {
        match self.vars.get_mut(key) {
            Some(target) => f(target),
            None => match &self.parent {
                Some(p) => p.borrow_mut().modify_existing_var(key, f),
                None => (),
            }
        }
    }
    fn set(self: &mut Env, key: String, val: Obj) {
        let mut v = Some(val);
        self.modify_existing_var(&key, |target| {
            *target = v.take().unwrap();
        });
        match v {
            Some(vv) => self.insert(key, vv),
            None => (),
        }
    }
    fn insert(self: &mut Env, key: String, val: Obj) {
        self.vars.insert(key, val);
    }
    fn insert_builtin(self: &mut Env, b: impl Builtin + 'static) {
        self.insert(b.builtin_name().to_string(), Obj::Func(Func::Builtin(Rc::new(b))))
    }
}

fn assign_all_basic(env: &mut Env, lhs: &[Box<EvaluatedLvalue>], rhs: &[Obj], insert: bool) -> NRes<()> {
    if lhs.len() == rhs.len() {
        for (lhs1, rhs1) in lhs.iter().zip(rhs.iter()) {
            assign(env, lhs1, rhs1, insert)?;
        }
        Ok(())
    } else {
        Err(NErr::ValueError(format!("Can't unpack into mismatched length {:?} {} != {:?} {}", lhs, lhs.len(), rhs, rhs.len())))
    }
}

fn assign_all(env: &mut Env, lhs: &[Box<EvaluatedLvalue>], rhs: &[Obj], insert: bool) -> NRes<()> {
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
            assign_all_basic(env, &lhs[..si], &rhs[..si], insert)?;
            assign(env, inner, &Obj::List(Rc::new(rhs[si..rhs.len() - lhs.len() + si + 1].to_vec())), insert)?;
            assign_all_basic(env, &lhs[si + 1..], &rhs[rhs.len() - lhs.len() + si + 1..], insert)
        }
        None => assign_all_basic(env, lhs, rhs, insert),
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

fn assign(env: &mut Env, lhs: &EvaluatedLvalue, rhs: &Obj, insert: bool) -> NRes<Obj> {
    match lhs {
        EvaluatedLvalue::IndexedIdent(s, ixs) => {
            if insert {
                if ixs.is_empty() {
                    env.insert(s.to_string(), rhs.clone());
                } else {
                    return Err(NErr::TypeError(format!("Can't insert new value into index expression on nonexistent variable: {:?} {:?}", s, ixs)))
                }
            } else {
                if ixs.is_empty() {
                    env.set(s.to_string(), rhs.clone());
                } else {
                    let mut did_modify = Err(NErr::NameError(format!("Variable {:?} not found, couldn't set into index {:?}", s, ixs)));
                    env.modify_existing_var(s, |v| {
                        did_modify = set_index(v, ixs, rhs.clone());
                    });
                    did_modify?
                }
            }
            Ok(rhs.clone())
        }
        EvaluatedLvalue::CommaSeq(ss) => {
            match rhs {
                Obj::List(ls) => {
                    assign_all(env, ss, ls, insert)?;
                    Ok(rhs.clone())
                }
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
            Ok(self.operands.swap_remove(0).swap_remove(0))
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
            assign(&mut env.borrow_mut(), &p, &res, false)
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
                        assign(&mut env.borrow_mut(), &p, &Obj::Null, false)?;
                    }
                    let fres = ff.run(vec![pv, res])?;
                    assign(&mut env.borrow_mut(), &p, &fres, false)
                }
                _ => Err(NErr::TypeError(format!("Operator assignment: operator is not function {:?}", opv))),
            }
        }
        Expr::Call(f, args) => {
            let fr = evaluate(env, f)?;
            match fr {
                Obj::Func(ff) => {
                    let a = eval_seq(env, args)?;
                    ff.run(a)
                }
                _ => Err(NErr::TypeError(format!("Can't call non-function {:?}", fr))),
            }
        }
        Expr::CommaSeq(_) => Err(NErr::SyntaxError("Comma seqs only allowed directly on a side of an assignment (for now)".to_string())),
        Expr::Splat(_) => Err(NErr::SyntaxError("Splats only allowed on an assignment-related place".to_string())),
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
        Expr::For(pat, iteratee, body) => {
            let mut itr = evaluate(env, iteratee)?;
            let itrr = mut_obj_into_iter(&mut itr)?;
            for x in itrr {
                let p = eval_lvalue(env, pat)?;
                // should assign take x
                assign(&mut env.borrow_mut(), &p, &x, false)?;
                evaluate(env, body)?;
            }
            Ok(Obj::Null)
        }
        Expr::ForItem(pat, iteratee, body) => {
            let mut itr = evaluate(env, iteratee)?;
            let itrr = mut_obj_into_iter_pairs(&mut itr)?;
            for (k, v) in itrr {
                let p = eval_lvalue(env, pat)?;
                // should assign take x
                assign(&mut env.borrow_mut(), &p, &Obj::List(Rc::new(vec![key_to_obj(&k), v])), false)?;
                evaluate(env, body)?;
            }
            Ok(Obj::Null)
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
        body: |mut args| {
            if args.is_empty() {
                Err(NErr::ArgumentError("-: received 0 args".to_string()))
            } else {
                let mut s = args.remove(0);
                if args.is_empty() {
                    Ok(Obj::Num(-s))
                } else {
                    for arg in args {
                        s -= &arg;
                    }
                    Ok(Obj::Num(s))
                }
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
            _ => Err(NErr::TypeError("len: list or dict only".to_string()))
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
                _ => Err(NErr::TypeError("map: not iterable".to_string()))
            }
        }
    });
    env.insert_builtin(TwoArgBuiltin {
        name: "filter".to_string(),
        can_refer: true,
        body: |a, b| match (a, b) {
            (Obj::List(mut a), Obj::Func(b)) => {
                let mut ret = Ok(());
                Rc::make_mut(&mut a).retain(|e| {
                    if ret.is_err() {
                        false
                    } else {
                        match b.run(vec![e.clone()]) {
                            Ok(e) => e.truthy(),
                            Err(g) => { ret = Err(g); false }
                        }
                    }
                });
                Ok(Obj::List(a))
            }
            _ => Err(NErr::TypeError("map: list and func only".to_string()))
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
        name: "**".to_string(),
        can_refer: false,
        body: |a, b| match (a, b) {
            (Obj::List(v), Obj::Num(x)) => {
                Ok(Obj::List(Rc::new(std::iter::repeat(&**v).take(x.to_usize().ok_or(NErr::ValueError("can't repeat by non-usize".to_string()))?).flatten().cloned().collect())))
            }
            (Obj::Num(x), Obj::List(v)) => {
                Ok(Obj::List(Rc::new(std::iter::repeat(&**v).take(x.to_usize().ok_or(NErr::ValueError("can't repeat by non-usize".to_string()))?).flatten().cloned().collect())))
            }
            _ => Err(NErr::ArgumentError("**: unrecognized argument types".to_string()))
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
}
