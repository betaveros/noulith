use std::io;
use std::io::Write;
use std::rc::Rc;
use std::cell::RefCell;
use noulith::{Obj, Env, initialize, parse, evaluate};

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

fn main() {
    let mut env = Env::new();
    initialize(&mut env);
    let e = Rc::new(RefCell::new(env));

    let mut input = String::new();
    while prompt(&mut input) {
        match parse(&input) {
            Ok(Some(expr)) => match evaluate(&e, &expr) {
                Ok(Obj::Null) => {}
                Ok(e) => { println!("{}", e); }
                Err(e) => { println!("ERROR: {}", e); }
            }
            Ok(None) => {}
            Err(e) => { println!("PARSE ERROR: {}", e); }
        }
    }
}
