#[macro_use] extern crate lazy_static;

use std::fmt;
use std::fmt::Display;
use std::fmt::Debug;
use std::rc::Rc;
use std::collections::{HashMap, HashSet};

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
    fn run(&self, env: &mut Env, args: Vec<Obj>) -> NRes<Obj>;
}

#[derive(Debug, Clone)]
pub struct Builtin {
    body: fn(args: Vec<Obj>) -> NRes<Obj>,
}

impl Block for Builtin {
    fn run(&self, _: &mut Env, args: Vec<Obj>) -> NRes<Obj> {
        (self.body)(args)
    }
}

#[derive(Debug, Clone)]
pub struct IntsBuiltin {
    name: String,
    body: fn(args: Vec<i64>) -> NRes<Obj>,
}

impl Block for IntsBuiltin {
    fn run(&self, _: &mut Env, args: Vec<Obj>) -> NRes<Obj> {
        (self.body)(args.iter().map(|x| match x {
            Obj::Int(n) => Ok(*n),
            _ => Err(NErr::TypeError(format!("{} only accepts ints, got {:?}", self.name, x))),
        }).collect::<NRes<Vec<i64>>>()?)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    IntLit(i64),
    // FloatLit(f64),
    StringLit(Rc<String>),
    Identifier(String),
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

#[derive(Debug)]
pub enum Expr {
    IntLit(i64),
    StringLit(Rc<String>),
    Identifier(String),
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
                        _ => Token::Identifier(acc),
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
                        _ => Token::Identifier(acc),
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
                Token::Identifier(s) => {
                    self.advance();
                    Ok(Expr::Identifier(s.to_string()))
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
                Token::Lambda => Err("lambda not implemented".to_string()),
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

    fn chain(&mut self) -> Result<Expr, String> {
        let op1 = self.operand()?;
        let mut ops = Vec::<(String, Box<Expr>)>::new();
        while let Some(Token::Identifier(op)) = self.peek() {
            self.i += 1;
            ops.push((op.to_string(), Box::new(self.operand()?)));
        }
        Ok(if ops.is_empty() {
            op1
        } else {
            Expr::Chain(Box::new(op1), ops)
        })
    }

    fn peek_csc_stopper(&self) -> bool {
        match self.peek() {
            Some(Token::RightParen) => true,
            Some(Token::RightBracket) => true,
            Some(Token::RightBrace) => true,
            Some(Token::Assign) => true,
            _ => false,
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

pub struct Env {
    vars: HashMap<String, Obj>
}
impl Env {
    fn new() -> Env {
        Env { vars: HashMap::new() }
    }
    fn get_var(self: &Env, s: &str) -> NRes<&Obj> {
        self.vars.get(s).ok_or(NErr::NameError(s.to_string()))
    }
    fn insert(self: &mut Env, key: String, val: Obj) {
        self.vars.insert(key, val);
    }
}
fn assign(env: &mut Env, lhs: &Expr, rhs: &Obj) -> NRes<Obj> {
    match lhs {
        Expr::Identifier(s) => {
            env.vars.insert(s.to_string(), rhs.clone());
            Ok(rhs.clone())
        }
        Expr::CommaSeq(ss) => {
            match rhs {
                Obj::List(ls) => {
                    if ss.len() == ls.len() {
                        for (lhs1, rhs1) in ss.iter().zip(ls.iter()) {
                            assign(env, lhs1, rhs1)?;
                        }
                        Ok(rhs.clone())
                    } else {
                        Err(NErr::TypeError(format!("can't unpack into mismatched length {:?} {} != {:?} {}", lhs, ss.len(), rhs, ls.len())))
                    }
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
    operands: Vec<Obj>,
    operators: Vec<(Rc<dyn Block>, u8)>,
}

impl ChainEvaluator {
    fn new(operand: Obj) -> ChainEvaluator {
        ChainEvaluator { operands: vec![operand], operators: Vec::new() }
    }

    fn run_top(&mut self, env: &mut Env) -> NRes<()> {
        let (op, _) = self.operators.pop().expect("sync");
        let rhs = self.operands.pop().expect("sync");
        let lhs = self.operands.pop().expect("sync");
        self.operands.push(op.run(env, vec![lhs, rhs])?);
        Ok(())
    }

    fn give(&mut self, env: &mut Env, operator: Rc<dyn Block>, precedence: u8, operand: Obj) -> NRes<()> {
        while self.operators.last().map_or(false, |t| t.1 >= precedence) {
            self.run_top(env)?;
        }

        self.operators.push((operator, precedence));
        self.operands.push(operand);
        Ok(())
    }

    fn finish(&mut self, env: &mut Env) -> NRes<Obj> {
        while !self.operators.is_empty() {
            self.run_top(env)?;
        }
        if self.operands.len() == 1 {
            Ok(self.operands.swap_remove(0))
        } else {
            panic!("chain eval out of sync")
        }
    }
}

pub fn evaluate(env: &mut Env, expr: &Expr) -> NRes<Obj> {
    match expr {
        Expr::IntLit(n) => Ok(Obj::Int(*n)),
        Expr::StringLit(s) => Ok(Obj::String(Rc::clone(s))),
        Expr::Identifier(s) => env.get_var(s).cloned(),
        Expr::Chain(op1, ops) => {
            let mut ev = ChainEvaluator::new(evaluate(env, op1)?);
            for (oper, opd) in ops {
                if let Obj::Func(b) = env.get_var(oper).cloned()? {
                    let prec = precedence(oper)?;
                    let oprd = evaluate(env, opd)?;
                    ev.give(env, b, prec, oprd)?;
                } else {
                    return Err(NErr::TypeError("no chaining nonblock".to_string()))
                }
            }
            ev.finish(env)
        }
        Expr::Assign(pat, rhs) => {
            let res = evaluate(env, rhs)?;
            assign(env, pat, &res)
        }
        Expr::Call(f, args) => {
            let fr = evaluate(env, f)?;
            match fr {
                Obj::Func(ff) => {
                    let a = args.iter().map(|arg| evaluate(env, arg)).collect::<Result<Vec<Obj>, NErr>>()?;
                    ff.run(env, a)
                }
                _ => Err(NErr::TypeError(format!("can't call non-function {:?}", fr))),
            }
        }
        Expr::CommaSeq(_) => Err(NErr::TypeError("comma seq not impl yet".to_string())),
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
                        assign(env, pat, x)?;
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
                        assign(env, pat, &Obj::List(Rc::new(vec![Obj::Int(i as i64), x.clone()])))?;
                        evaluate(env, body)?;
                    }
                    Ok(Obj::Null)
                }
                _ => Err(NErr::TypeError(format!("can't iterate {:?}", itr)))
            }
        }
    }
}

fn main() {
    let mut env = Env::new();
    env.insert("+".to_string(), Obj::Func(Rc::new(IntsBuiltin {
        name: "+".to_string(),
        body: |args| { Ok(Obj::Int(args.iter().sum())) },
    })));
    env.insert("-".to_string(), Obj::Func(Rc::new(IntsBuiltin {
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
    })));
    env.insert("*".to_string(), Obj::Func(Rc::new(IntsBuiltin {
        name: "*".to_string(),
        body: |args| { Ok(Obj::Int(args.iter().product())) },
    })));
    env.insert("==".to_string(), Obj::Func(Rc::new(Builtin { body: |args| {
        match args.as_slice() {
            [a, b] => match (a, b) {
                (Obj::Int(a), Obj::Int(b)) => Ok(Obj::Int(if a == b { 1 } else { 0 })),
                (Obj::String(a), Obj::String(b)) => Ok(Obj::Int(if a == b { 1 } else { 0 })),
                _ => Err(NErr::TypeError("== not yet impl".to_string()))
            }
            _ => Err(NErr::TypeError("== 2 args only".to_string()))
        }
    }})));
    env.insert("/".to_string(), Obj::Func(Rc::new(IntsBuiltin {
        name: "/".to_string(),
        body: |args| match args.as_slice() {
            [a, b] => Ok(Obj::Int(a / b)),
            _ => Err(NErr::TypeError("/: 2 args only".to_string()))
        }
    })));
    env.insert("%".to_string(), Obj::Func(Rc::new(IntsBuiltin {
        name: "%".to_string(),
        body: |args| match args.as_slice() {
            [a, b] => Ok(Obj::Int(a % b)),
            _ => Err(NErr::TypeError("%: 2 args only".to_string()))
        }
    })));
    env.insert("%%".to_string(), Obj::Func(Rc::new(IntsBuiltin {
        name: "%%".to_string(),
        body: |args| match args.as_slice() {
            [a, b] => Ok(Obj::Int(a.rem_euclid(*b))),
            _ => Err(NErr::TypeError("%%: 2 args only".to_string()))
        }
    })));
    env.insert("til".to_string(), Obj::Func(Rc::new(IntsBuiltin {
        name: "til".to_string(),
        body: |args| match args.as_slice() {
            // TODO: should be lazy
            [a, b] => Ok(Obj::List(Rc::new(num_iter::range(*a, *b).map(|x| Obj::Int(x)).collect()))),
            _ => Err(NErr::TypeError("til: 2 args only".to_string()))
        }
    })));
    env.insert("to".to_string(), Obj::Func(Rc::new(IntsBuiltin {
        name: "to".to_string(),
        body: |args| match args.as_slice() {
            // TODO: should be lazy
            [a, b] => Ok(Obj::List(Rc::new(num_iter::range_inclusive(*a, *b).map(|x| Obj::Int(x)).collect()))),
            _ => Err(NErr::TypeError("to: 2 args only".to_string()))
        }
    })));
    env.insert("print".to_string(), Obj::Func(Rc::new(Builtin { body: |args| {
        println!("{}", args.iter().map(|arg| format!("{}", arg)).collect::<Vec<String>>().join(" "));
        Ok(Obj::Null)
    }})));
    env.insert("debug".to_string(), Obj::Func(Rc::new(Builtin { body: |args| {
        println!("{}", args.iter().map(|arg| format!("{:?}", arg)).collect::<Vec<String>>().join(" "));
        Ok(Obj::Null)
    }})));
    env.insert("++".to_string(), Obj::Func(Rc::new(Builtin { body: |args| {
        let mut acc = String::new();
        for arg in args {
            acc += format!("{}", arg).as_str();
        }
        Ok(Obj::String(Rc::new(acc)))
    }})));

    let s = "for (x : 1 to 100) (o = ''; for (f, s : [[3, 'Fizz'], [5, 'Buzz']]) if (x % f == 0) o = o ++ s; print(if (o == '') x else o))";
    println!("{:?}", lex(s));
    println!("{:?}", parse(s));
    println!("{:?}", evaluate(&mut env, &parse(s).unwrap()));
}
