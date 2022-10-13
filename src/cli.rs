use std::cell::RefCell;
use std::io;
use std::io::BufReader;
use std::rc::Rc;

use noulith::{evaluate, initialize, lex, parse, type_of, Env, Obj, Token, TopEnv};

use rustyline::error::ReadlineError;
use rustyline::Editor;
use rustyline_derive::{Helper, Hinter, Validator};

#[derive(Helper, Hinter, Validator)]
struct NoulithHelper(Rc<RefCell<Env>>);

impl rustyline::highlight::Highlighter for NoulithHelper {
    fn highlight<'a>(&self, line: &'a str, _pos: usize) -> std::borrow::Cow<'a, str> {
        let tokens = lex(line);
        let mut ret = String::new();
        let mut it = line.chars().enumerate().peekable();
        for token in tokens {
            while it.peek().map_or(false, |(i, _)| i < &token.start.index) {
                ret.push(it.next().unwrap().1);
            }
            let color = match token.token {
                Token::Invalid(_) => Some("\x1b[31m"),
                Token::Ident(s) => {
                    if self.0.borrow().vars.contains_key(&s) {
                        Some("\x1b[36m")
                    } else {
                        None
                    }
                }
                Token::IntLit(_)
                | Token::RatLit(_)
                | Token::FloatLit(_)
                | Token::ImaginaryFloatLit(_) => Some("\x1b[38;5;208m"),
                Token::StringLit(_) | Token::BytesLit(_) | Token::FormatString(_) => {
                    Some("\x1b[32m")
                }
                Token::Comment(_) => Some("\x1b[38;5;59m"),
                Token::And
                | Token::Or
                | Token::Coalesce
                | Token::While
                | Token::For
                | Token::Yield
                | Token::If
                | Token::Else
                | Token::Switch
                | Token::Case
                | Token::Try
                | Token::Catch
                | Token::Break
                | Token::Continue
                | Token::Return
                | Token::Throw
                | Token::Lambda
                | Token::Bang
                | Token::Colon
                | Token::DoubleColon
                | Token::Ellipsis
                | Token::Assign
                | Token::Consume
                | Token::Pop
                | Token::Remove
                | Token::Swap
                | Token::Every
                | Token::Struct
                | Token::Underscore => Some("\x1b[1;34m"),
                _ => None,
            };
            match color {
                Some(c) => ret += c,
                None => {}
            }
            while it.peek().map_or(false, |(i, _)| i < &token.end.index) {
                ret.push(it.next().unwrap().1);
            }
            match color {
                Some(_) => ret += "\x1b[0m",
                None => {}
            }
        }

        std::borrow::Cow::Owned(ret)
    }

    fn highlight_char(&self, _line: &str, _pos: usize) -> bool {
        true
    }
}

pub struct Pair {
    /// Text to display when listing alternatives.
    pub display: String,
    /// Text to insert in line.
    pub replacement: String,
}

impl rustyline::completion::Candidate for Pair {
    fn display(&self) -> &str {
        self.display.as_str()
    }

    fn replacement(&self) -> &str {
        self.replacement.as_str()
    }
}

impl rustyline::completion::Completer for NoulithHelper {
    type Candidate = Pair;
    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &rustyline::Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        for token in lex(line) {
            if token.end.index >= pos {
                if token.start.index >= pos {
                    break;
                }
                match token.token {
                    Token::Ident(x) => {
                        let v = self
                            .0
                            .borrow()
                            .vars
                            .keys()
                            .filter(|s| s.starts_with(&x))
                            .map(|s| Pair {
                                display: s.to_string(),
                                replacement: s.to_string(),
                            })
                            .collect::<Vec<Pair>>();
                        return Ok((token.start.index, v));
                    }
                    _ => break,
                }
            }
        }
        Ok((0, Vec::new()))
    }
}

pub fn repl() {
    let mut env = Env::new(TopEnv {
        backrefs: Vec::new(),
        input: Box::new(BufReader::new(io::stdin())),
        output: Box::new(io::stdout()),
    });
    initialize(&mut env);
    let e = Rc::new(RefCell::new(env));

    let mut rl = Editor::<NoulithHelper>::new().expect("readline failed");
    rl.set_helper(Some(NoulithHelper(Rc::clone(&e))));
    loop {
        let readline = rl.readline("\x1b[38;5;67mnoulith>\x1b[0m ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                match parse(&line) {
                    Ok(Some(expr)) => match evaluate(&e, &expr) {
                        Ok(Obj::Null) => {}
                        Ok(x) => {
                            let refs_len = e.borrow_mut().mut_top_env(|v| {
                                v.backrefs.push(x.clone());
                                v.backrefs.len()
                            });
                            let name = type_of(&x).name();
                            println!(
                                "\x1b[34m\\{}: \x1b[0m{}\x1b[38;5;59m: {}\x1b[0m",
                                refs_len,
                                noulith::FmtObj(&x, &noulith::MyFmtFlags::budgeted_repr(64)),
                                name
                            );
                        }
                        Err(e) => {
                            println!("ERROR: {}", e);
                        }
                    },
                    Ok(None) => {}
                    Err(e) => {
                        println!("PARSE ERROR: {}", e);
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                continue;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
}
