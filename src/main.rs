use std::fs::File;
use std::io;
use std::io::{Read, Write, BufReader};
use std::rc::Rc;
use std::cell::RefCell;
use noulith::{Obj, Env, TopEnv, initialize, parse, evaluate};

fn prompt(input: &mut String) -> bool {
    input.clear();
    print!("noulith> ");
    if io::stdout().flush().is_err() { return false }

    match io::stdin().read_line(input) {
        Ok(0) => false,
        Ok(_) => true,
        Err(_) => false,
    }
}

fn repl() {
    let mut env = Env::new(TopEnv { backrefs: Vec::new(), input: Box::new(BufReader::new(io::stdin())), output: Box::new(io::stdout()) });
    initialize(&mut env);
    let e = Rc::new(RefCell::new(env));

    let mut input = String::new();
    while prompt(&mut input) {
        match parse(&input) {
            Ok(Some(expr)) => match evaluate(&e, &expr) {
                Ok(Obj::Null) => {}
                Ok(x) => {
                    let refs_len = e.borrow_mut().mut_top_env(|v| {
                        v.backrefs.push(x.clone());
                        v.backrefs.len()
                    });
                    println!("\\{}: {}",
                             refs_len,
                             noulith::FlaggedObj(x, noulith::MyFmtFlags::budgeted_repr(64)));
                }
                Err(e) => { println!("ERROR: {}", e); }
            }
            Ok(None) => {}
            Err(e) => { println!("PARSE ERROR: {}", e); }
        }
    }
}

fn main() {
    match std::env::args().collect::<Vec<String>>().as_slice() {
        [] | [_] => { repl(); }
        [_, s] => match File::open(s) {
            Ok(mut file) => {
                let mut code = String::new();
                file.read_to_string(&mut code).expect("reading code file failed");

                let mut env = Env::new(TopEnv { backrefs: Vec::new(), input: Box::new(BufReader::new(io::stdin())), output: Box::new(io::stdout()) });
                initialize(&mut env);
                let e = Rc::new(RefCell::new(env));

                match parse(&code) {
                    Ok(Some(expr)) => match evaluate(&e, &expr) {
                        Ok(Obj::Null) => {}
                        Ok(e) => { println!("{}", e); }
                        Err(e) => { println!("ERROR: {}", e); }
                    }
                    Ok(None) => {}
                    Err(e) => { println!("PARSE ERROR: {}", e); }
                }
            }
            Err(_) => {
                panic!("opening code file failed");
            }
        }
        _ => { panic!("too many arguments"); }
    }
}
