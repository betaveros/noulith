use num::bigint::BigInt;
use num::BigRational;
use std::collections::HashSet;
use std::rc::Rc;

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
    Into,
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
    Import,
    Literally,
    Underscore,

    InternalFrame,
    InternalPush,
    InternalPop,
    InternalPeek,
    InternalFor,

    // strip me before parsing
    Comment(String),
    // Newline,
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

pub struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    start: CodeLoc,

    // maintained at what chars.next() would give
    cur: CodeLoc,
    pub tokens: Vec<LocToken>,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
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
                        if let Some(d1) = self.next().and_then(|c| c.to_digit(16)) {
                            if let Some(d2) = self.next().and_then(|c| c.to_digit(16)) {
                                acc.push(char::from_u32(d1 * 16 + d2).unwrap())
                            } else {
                                self.emit(Token::Invalid(format!(
                                    "lexing: string literal: bad hex escape"
                                )));
                                break;
                            }
                        } else {
                            self.emit(Token::Invalid(format!(
                                "lexing: string literal: bad hex escape"
                            )));
                            break;
                        }
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

    pub fn lex(&mut self) {
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
                    if c.is_whitespace() {
                        // do nothing
                    } else if c.is_digit(10) {
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
                                "into" => Token::Into,
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
                                "import" => Token::Import,
                                "literally" => Token::Literally,
                                "_" => Token::Underscore,
                                "__internal_frame" => Token::InternalFrame,
                                "__internal_push" => Token::InternalPush,
                                "__internal_pop" => Token::InternalPop,
                                "__internal_peek" => Token::InternalPeek,
                                "__internal_for" => Token::InternalFor,
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
                    } else {
                        self.emit(Token::Invalid(format!("lexing: unrecognized char: {}", c)))
                    }
                }
            }
        }
    }
}
