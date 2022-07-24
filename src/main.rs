#[macro_use] extern crate lazy_static;

use std::cmp::Ordering;
use std::fmt;
use std::fmt::Display;
use std::fmt::Debug;
use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use std::cell::RefCell;

use num_iter;

#[derive(Debug, Clone)]
pub enum Obj {
    Null,
    Int(i64),
    // Float(f64),
    String(Rc<String>),
    List(Rc<Vec<Obj>>),
    Func(Rc<dyn Block>),
}

impl Obj {
    fn truthy(&self) -> bool {
        match self {
            Obj::Null => false,
            Obj::Int(x) => x != &0,
            Obj::String(x) => !x.is_empty(),
            Obj::List(x) => !x.is_empty(),
            Obj::Func(_) => true,
        }
    }
}

impl Display for Obj {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Obj::Null => write!(formatter, "null"),
            Obj::Int(n) => write!(formatter, "{}", n),
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
            Obj::Func(f) => write!(formatter, "{:?}", f),
        }
    }
}

#[derive(Debug)]
pub enum NErr {
    TypeError(String),
    NameError(String),
    ParseError(String),
}

pub type NRes<T> = Result<T, NErr>;

pub trait Block : Debug {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj>;

    // Should only be Some for builtins, used for them to identify each other
    fn builtin_name(&self) -> Option<&str> {
        None
    }

    fn try_chain(&self, _other: &Rc<dyn Block>) -> Option<Rc<dyn Block>> {
        None
    }
}

#[derive(Debug, Clone)]
struct ComparisonOperator {
    name: Option<String>,
    chained: Vec<Rc<dyn Block>>,
    accept: fn(Ordering) -> bool,
}

impl ComparisonOperator {
    fn of(name: &str, accept: fn(Ordering) -> bool) -> ComparisonOperator {
        ComparisonOperator {
            name: Some(name.to_string()),
            chained: Vec::new(),
            accept,
        }
    }
}

fn ncmp(aa: &Obj, bb: &Obj) -> NRes<Ordering> {
    match (aa, bb) {
        (Obj::Int(a), Obj::Int(b)) => Ok(a.cmp(b)),
        (Obj::String(a), Obj::String(b)) => Ok(a.cmp(b)),
        _ => Err(NErr::TypeError(format!("can't compare {:?} {:?}", aa, bb))),
    }
}

impl Block for ComparisonOperator {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        if self.chained.is_empty() {
            if args.len() >= 2 {
                for i in 0 .. args.len() - 1 {
                    if !(self.accept)(ncmp(&args[i], &args[i+1])?) {
                        return Ok(Obj::Int(0))
                    }
                }
                Ok(Obj::Int(1))
            } else {
                Err(NErr::TypeError(format!("comparison operator {:?} needs 2+ args", self.name)))
            }
        } else {
            if self.chained.len() + 2 == args.len() {
                if !(self.accept)(ncmp(&args[0], &args[1])?) {
                    return Ok(Obj::Int(0))
                }
                for i in 0 .. self.chained.len() {
                    let res = self.chained[i].run(vec![args[i+1].clone(), args[i+2].clone()])?;
                    if !res.truthy() {
                        return Ok(res)
                    }
                }
                Ok(Obj::Int(1))
            } else {
                Err(NErr::TypeError(format!("chained comparison operator wrong args")))
            }
        }
    }

    fn builtin_name(&self) -> Option<&str> {
        self.name.as_ref().map(|x| &**x)
    }

    fn try_chain(&self, other: &Rc<dyn Block>) -> Option<Rc<dyn Block>> {
        match other.builtin_name() {
            Some("==" | "!=" | "<" | ">" | "<=" | ">=") => Some(Rc::new(ComparisonOperator {
                name: None,
                chained: {
                    let mut k = self.chained.clone();
                    k.push(Rc::clone(other));
                    k
                },
                accept: self.accept,
            })),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Builtin {
    name: String,
    body: fn(args: Vec<Obj>) -> NRes<Obj>,
}

impl Block for Builtin {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        (self.body)(args)
    }

    fn builtin_name(&self) -> Option<&str> {
        Some(&self.name)
    }
}

#[derive(Debug, Clone)]
pub struct IntsBuiltin {
    name: String,
    body: fn(args: Vec<i64>) -> NRes<Obj>,
}

impl Block for IntsBuiltin {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        (self.body)(args.iter().map(|x| match x {
            Obj::Int(n) => Ok(*n),
            _ => Err(NErr::TypeError(format!("{} only accepts ints, got {:?}", self.name, x))),
        }).collect::<NRes<Vec<i64>>>()?)
    }

    fn builtin_name(&self) -> Option<&str> {
        Some(&self.name)
    }
}

struct Closure {
    params: Vec<Box<Expr>>,
    body: Expr,
    env: Rc<RefCell<Env>>,
}

// directly debug-printing env can easily recurse infinitely
impl Debug for Closure {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "Closure {{ params: {:?}, body: {:?}, env: ... }}", self.params, self.body)
    }
}

impl Block for Closure {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        let mut env = Env { vars: HashMap::new(), parent: Some(Rc::clone(&self.env)) };
        assign_all(&mut env, &self.params, &args, true)?;
        let e = Rc::new(RefCell::new(env));
        evaluate(&e, &self.body)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    IntLit(i64),
    // FloatLit(f64),
    StringLit(Rc<String>),
    Ident(String),
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
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
    // Newline,
}

#[derive(Debug, Clone)]
pub enum Expr {
    IntLit(i64),
    StringLit(Rc<String>),
    Ident(String),
    Call(Box<Expr>, Vec<Box<Expr>>),
    List(Vec<Box<Expr>>),
    // Slice(Box<Expr>, Vec<Box<Expr>>),
    Chain(Box<Expr>, Vec<(String, Box<Expr>)>),
    CommaSeq(Vec<Box<Expr>>),
    Assign(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    For(Box<Expr>, Box<Expr>, Box<Expr>),
    ForItem(Box<Expr>, Box<Expr>, Box<Expr>),
    Sequence(Vec<Box<Expr>>),
    Lambda(Vec<Box<Expr>>, Box<Expr>),
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
                if let Some(d) = c.to_digit(10) {
                    let mut acc = d as i64;

                    while let Some(cc) = chars.peek().and_then(|d| d.to_digit(10)) {
                        acc = 10 * acc + cc as i64;
                        chars.next();
                    }
                    tokens.push(Token::IntLit(acc as i64))
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
                        _ => Token::Ident(acc),
                    })
                } else if OPERATOR_SYMBOLS.contains(&c) {
                    let mut acc = c.to_string();

                    while let Some(cc) = chars.peek().filter(|c| OPERATOR_SYMBOLS.contains(c)) {
                        acc.push(*cc);
                        chars.next();
                    }
                    tokens.push(match acc.as_str() {
                        "=" => Token::Assign,
                        ":" => Token::Colon,
                        "::" => Token::DoubleColon,
                        "..." => Token::Ellipsis,
                        _ => Token::Ident(acc),
                    })
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
                Token::LeftParen => {
                    self.advance();
                    let e = self.expression()?;
                    self.require(Token::RightParen, "normal parenthesized expr".to_string())?;
                    Ok(e)
                }
                Token::LeftBracket => {
                    self.advance();
                    let (exs, _) = self.comma_separated_chains()?;
                    self.require(Token::RightBracket, "list expr".to_string())?;
                    Ok(Expr::List(exs))
                }
                Token::RightParen => Err("unexpected right paren".to_string()),
                Token::Lambda => {
                    self.advance();
                    let (params, _) = self.comma_separated_chains()?;
                    self.require(Token::Colon, "lambda start".to_string())?;
                    let body = self.chain()?;
                    Ok(Expr::Lambda(params, Box::new(body)))
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
                    let pat = self.pattern()?;
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

        while self.peek() == Some(Token::LeftParen) {
            self.i += 1;
            let (cs, _) = self.comma_separated_chains()?;
            self.require(Token::RightParen, "call expr".to_string())?;
            cur = Expr::Call(Box::new(cur), cs);
        }
        Ok(cur)
    }

    fn peek_csc_stopper(&self) -> bool {
        match self.peek() {
            Some(Token::RightParen) => true,
            Some(Token::RightBracket) => true,
            Some(Token::RightBrace) => true,
            Some(Token::Assign) => true,
            Some(Token::Colon) => true,
            Some(Token::Semicolon) => true,
            None => true,
            _ => false,
        }
    }

    fn chain(&mut self) -> Result<Expr, String> {
        let op1 = self.operand()?;
        // We'll specially allow some two-chains, (a b), as calls, so that negative number literals
        // and just writing an expression like "-x" works. But we will be aggressive-ish about
        // checking that the chain ends afterwards so we don't get runaway syntax errors.
        match self.peek() {
            Some(Token::IntLit(_) | Token::StringLit(_)) => {
                let ret = Expr::Call(Box::new(op1), vec![Box::new(self.atom()?)]);
                if !self.peek_csc_stopper() {
                    Err(format!("saw literal in operator position: these chains must be short, got {:?} after", self.peek()))
                } else {
                    Ok(ret)
                }
            }
            Some(Token::Ident(op)) => {
                self.advance();
                if self.peek_csc_stopper() {
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
            _ => Ok(op1),
        }
    }

    // No semicolons allowed, but can be empty. List literals; function declarations; LHSes of
    // assignments. Not for function calls, I think? f(x; y) might actually be ok...
    // bool is whether a comma was found, to distinguish (x) from (x,)
    fn comma_separated_chains(&mut self) -> Result<(Vec<Box<Expr>>, bool), String> {
        if self.peek_csc_stopper() {
            return Ok((Vec::new(), false));
        }

        let mut xs = vec![Box::new(self.chain()?)];
        let mut comma = false;
        while self.peek() == Some(Token::Comma) {
            self.i += 1;
            comma = true;
            if self.peek_csc_stopper() {
                return Ok((xs, comma))
            }
            xs.push(Box::new(self.chain()?));
        }
        return Ok((xs, comma))
    }

    // Comma-separated things. No semicolons or assigns allowed
    fn pattern(&mut self) -> Result<Expr, String> {
        let (mut exs, comma) = self.comma_separated_chains()?;
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
            Ok(Expr::Assign(Box::new(pat), Box::new(self.pattern()?)))
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
    fn new() -> Env {
        Env { vars: HashMap::new(), parent: None }
    }
    fn get_var(self: &Env, s: &str) -> NRes<Obj> {
        match self.vars.get(s) {
            Some(v) => Ok(v.clone()),
            None => match &self.parent {
                Some(p) => p.borrow().get_var(s),
                None => Err(NErr::NameError(s.to_string()))
            }
        }
    }

    // internal-ish; "return value" is whether it consumes val
    fn set_existing_var(self: &mut Env, key: &str, val: &mut Option<Obj>) {
        if val.is_some() {
            match self.vars.get_mut(key) {
                Some(target) => *target = val.take().unwrap(),
                None => match &self.parent {
                    Some(p) => p.borrow_mut().set_existing_var(key, val),
                    None => (),
                }
            }
        }
    }
    fn set(self: &mut Env, key: String, val: Obj) {
        let mut v = Some(val);
        self.set_existing_var(&key, &mut v);
        match v {
            Some(vv) => self.insert(key, vv),
            None => (),
        }
    }
    fn insert(self: &mut Env, key: String, val: Obj) {
        self.vars.insert(key, val);
    }
    fn insert_builtin(self: &mut Env, b: Builtin) {
        let name = b.name.to_string();
        self.insert(name, Obj::Func(Rc::new(b)))
    }
    fn insert_ints_builtin(self: &mut Env, b: IntsBuiltin) {
        let name = b.name.to_string();
        self.insert(name, Obj::Func(Rc::new(b)))
    }
    fn insert_comparison(self: &mut Env, b: ComparisonOperator) {
        let name = b.name.as_ref().unwrap().to_string();
        self.insert(name, Obj::Func(Rc::new(b)))
    }
}

fn assign_all(env: &mut Env, lhs: &Vec<Box<Expr>>, rhs: &Vec<Obj>, insert: bool) -> NRes<()> {
    if lhs.len() == rhs.len() {
        for (lhs1, rhs1) in lhs.iter().zip(rhs.iter()) {
            assign(env, lhs1, rhs1, insert)?;
        }
        Ok(())
    } else {
        Err(NErr::TypeError(format!("can't unpack into mismatched length {:?} {} != {:?} {}", lhs, lhs.len(), rhs, rhs.len())))
    }
}

fn assign(env: &mut Env, lhs: &Expr, rhs: &Obj, insert: bool) -> NRes<Obj> {
    match lhs {
        Expr::Ident(s) => {
            if insert {
                env.insert(s.to_string(), rhs.clone());
            } else {
                env.set(s.to_string(), rhs.clone());
            }
            Ok(rhs.clone())
        }
        Expr::CommaSeq(ss) => {
            match rhs {
                Obj::List(ls) => {
                    assign_all(env, ss, ls, insert)?;
                    Ok(rhs.clone())
                }
                _ => Err(NErr::TypeError(format!("can't unpack non-list {:?}", rhs))),
            }
        }
        _ => Err(NErr::TypeError(format!("can't assign to non-identifier {:?}", lhs))),
    }
}

fn precedence(name: &str) -> NRes<u8> {
    // stolen from Scala
    match name.chars().next() {
        None => Err(NErr::ParseError("empty name wtf".to_string())),
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
    operators: Vec<(Rc<dyn Block>, u8)>,
}

impl ChainEvaluator {
    fn new(operand: Obj) -> ChainEvaluator {
        ChainEvaluator { operands: vec![vec![operand]], operators: Vec::new() }
    }

    fn run_top_popped(&mut self, op: Rc<dyn Block>) -> NRes<()> {
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

    fn give(&mut self, operator: Rc<dyn Block>, precedence: u8, operand: Obj) -> NRes<()> {
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

pub fn evaluate(env: &Rc<RefCell<Env>>, expr: &Expr) -> NRes<Obj> {
    match expr {
        Expr::IntLit(n) => Ok(Obj::Int(*n)),
        Expr::StringLit(s) => Ok(Obj::String(Rc::clone(s))),
        Expr::Ident(s) => env.borrow_mut().get_var(s),
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
                    return Err(NErr::TypeError("no chaining nonblock".to_string()))
                }
            }
            ev.finish()
        }
        Expr::Assign(pat, rhs) => {
            let res = match &**rhs {
                Expr::CommaSeq(xs) => {
                    let mut acc = Vec::new();
                    for x in xs {
                        acc.push(evaluate(env, x)?);
                    }
                    Ok(Obj::List(Rc::new(acc)))
                }
                _ => evaluate(env, rhs)
            }?;
            assign(&mut env.borrow_mut(), pat, &res, false)
        }
        Expr::Call(f, args) => {
            let fr = evaluate(env, f)?;
            match fr {
                Obj::Func(ff) => {
                    let a = args.iter().map(|arg| evaluate(env, arg)).collect::<Result<Vec<Obj>, NErr>>()?;
                    ff.run(a)
                }
                _ => Err(NErr::TypeError(format!("can't call non-function {:?}", fr))),
            }
        }
        Expr::CommaSeq(_) => Err(NErr::ParseError("Comma seqs only allowed directly on a side of an assignment (for now)".to_string())),
        Expr::List(xs) => {
            let mut acc = Vec::new();
            for x in xs {
                acc.push(evaluate(env, x)?);
            }
            Ok(Obj::List(Rc::new(acc)))
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
            let itr = evaluate(env, iteratee)?;
            match itr {
                Obj::List(ls) => {
                    for x in ls.iter() {
                        assign(&mut env.borrow_mut(), pat, x, false)?;
                        evaluate(env, body)?;
                    }
                    Ok(Obj::Null)
                }
                _ => Err(NErr::TypeError(format!("can't iterate {:?}", itr)))
            }
        }
        Expr::ForItem(pat, iteratee, body) => {
            let itr = evaluate(env, iteratee)?;
            match itr {
                Obj::List(ls) => {
                    for (i, x) in ls.iter().enumerate() {
                        assign(&mut env.borrow_mut(), pat, &Obj::List(Rc::new(vec![Obj::Int(i as i64), x.clone()])), false)?;
                        evaluate(env, body)?;
                    }
                    Ok(Obj::Null)
                }
                _ => Err(NErr::TypeError(format!("can't iterate {:?}", itr)))
            }
        }
        Expr::Lambda(params, body) => {
            // TODO is this a good body clone?
            Ok(Obj::Func(Rc::new(Closure { params: params.clone(), body: (**body).clone(), env: Rc::clone(env) })))
        }
    }
}

fn main() {
    let mut env = Env::new();
    env.insert_ints_builtin(IntsBuiltin {
        name: "+".to_string(),
        body: |args| { Ok(Obj::Int(args.iter().sum())) },
    });
    env.insert_ints_builtin(IntsBuiltin {
        name: "-".to_string(),
        body: |args| match args.split_first() {
            None => Err(NErr::TypeError("- 0 args".to_string())),
            Some((s, rest)) => {
                if rest.is_empty() {
                    Ok(Obj::Int(-s))
                } else {
                    let mut ss = *s;
                    for arg in rest { ss -= arg; }
                    Ok(Obj::Int(ss))
                }
            }
        }
    });
    env.insert_ints_builtin(IntsBuiltin {
        name: "*".to_string(),
        body: |args| { Ok(Obj::Int(args.iter().product())) },
    });
    env.insert_comparison(ComparisonOperator::of("==", |ord| ord == Ordering::Equal));
    env.insert_comparison(ComparisonOperator::of("!=", |ord| ord != Ordering::Equal));
    env.insert_comparison(ComparisonOperator::of("<",  |ord| ord == Ordering::Less));
    env.insert_comparison(ComparisonOperator::of(">",  |ord| ord == Ordering::Greater));
    env.insert_comparison(ComparisonOperator::of("<=", |ord| ord != Ordering::Greater));
    env.insert_comparison(ComparisonOperator::of(">=", |ord| ord != Ordering::Less));
    env.insert_ints_builtin(IntsBuiltin {
        name: "/".to_string(),
        body: |args| match args.as_slice() {
            [a, b] => Ok(Obj::Int(a / b)),
            _ => Err(NErr::TypeError("/: 2 args only".to_string()))
        }
    });
    env.insert_ints_builtin(IntsBuiltin {
        name: "%".to_string(),
        body: |args| match args.as_slice() {
            [a, b] => Ok(Obj::Int(a % b)),
            _ => Err(NErr::TypeError("%: 2 args only".to_string()))
        }
    });
    env.insert_ints_builtin(IntsBuiltin {
        name: "%%".to_string(),
        body: |args| match args.as_slice() {
            [a, b] => Ok(Obj::Int(a.rem_euclid(*b))),
            _ => Err(NErr::TypeError("%%: 2 args only".to_string()))
        }
    });
    env.insert_ints_builtin(IntsBuiltin {
        name: "til".to_string(),
        body: |args| match args.as_slice() {
            // TODO: should be lazy
            [a, b] => Ok(Obj::List(Rc::new(num_iter::range(*a, *b).map(|x| Obj::Int(x)).collect()))),
            _ => Err(NErr::TypeError("til: 2 args only".to_string()))
        }
    });
    env.insert_ints_builtin(IntsBuiltin {
        name: "to".to_string(),
        body: |args| match args.as_slice() {
            // TODO: should be lazy
            [a, b] => Ok(Obj::List(Rc::new(num_iter::range_inclusive(*a, *b).map(|x| Obj::Int(x)).collect()))),
            _ => Err(NErr::TypeError("to: 2 args only".to_string()))
        }
    });
    env.insert_builtin(Builtin {
        name: "map".to_string(),
        body: |args| match args.as_slice() {
            [Obj::List(a), Obj::Func(b)] => {
                Ok(Obj::List(Rc::new(
                a.iter().map(|e| b.run(vec![e.clone()])).collect::<NRes<Vec<Obj>>>()?
                )))
            }
            _ => Err(NErr::TypeError("map: 2 args only".to_string()))
        }
    });
    env.insert_builtin(Builtin {
        name: "print".to_string(),
        body: |args| {
            println!("{}", args.iter().map(|arg| format!("{}", arg)).collect::<Vec<String>>().join(" "));
            Ok(Obj::Null)
        }
    });
    env.insert_builtin(Builtin {
        name: "debug".to_string(),
        body: |args| {
            println!("{}", args.iter().map(|arg| format!("{:?}", arg)).collect::<Vec<String>>().join(" "));
            Ok(Obj::Null)
        }
    });
    env.insert_builtin(Builtin {
        name: "++".to_string(),
        body: |args| {
            let mut acc = String::new();
            for arg in args {
                acc += format!("{}", arg).as_str();
            }
            Ok(Obj::String(Rc::new(acc)))
        }
    });

    let e = Rc::new(RefCell::new(env));

    // let s = "for (x : 1 to 100) (o = ''; for (f, s : [[3, 'Fizz'], [5, 'Buzz']]) if (x % f == 0) o = o ++ s; print(if (o == '') x else o))";
    // let s = "fact = \\n: if (n == 0) 1 else n * fact(n - 1); print 10; print(1 to 10 map fact)";
    // let s = "1 < 2 < 3";
    // let s = "==(1, 2, 3)";
    let s = "x = 1; y = 2; x, y = y, x; print('x:', x, 'y:', y)";
    println!("{:?}", lex(s));
    println!("{:?}", parse(s));
    println!("{:?}", evaluate(&e, &parse(s).unwrap()));
}
