use noulith::{evaluate, initialize, parse, warn, Env, Obj, ObjType, TopEnv};
use std::cell::RefCell;
use std::fs::File;
use std::io;
use std::io::{BufReader, Read};
use std::rc::Rc;

#[cfg(feature = "cli")]
mod cli;
#[cfg(not(feature = "cli"))]
use std::io::Write;
#[cfg(not(feature = "cli"))]
fn prompt(input: &mut String) -> bool {
    input.clear();
    print!("noulith> ");
    if io::stdout().flush().is_err() {
        return false;
    }

    match io::stdin().read_line(input) {
        Ok(0) => false,
        Ok(_) => true,
        Err(_) => false,
    }
}
#[cfg(not(feature = "cli"))]
fn repl() {
    let mut env = Env::new(TopEnv {
        backrefs: Vec::new(),
        input: Box::new(BufReader::new(io::stdin())),
        output: Box::new(io::stdout()),
    });
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
                    println!(
                        "\\{}: {}",
                        refs_len,
                        noulith::FmtObj(&x, &noulith::MyFmtFlags::budgeted_repr(64))
                    );
                }
                Err(e) => {
                    println!("ERROR: {}", e.render(&input));
                }
            },
            Ok(None) => {}
            Err(e) => {
                println!("PARSE ERROR: {}", e.render(&input));
            }
        }
    }
}

fn run_code(code: &str, args: Vec<String>, filename: String) {
    let mut env = Env::new(TopEnv {
        backrefs: Vec::new(),
        input: Box::new(BufReader::new(io::stdin())),
        output: Box::new(io::stdout()),
    });
    initialize(&mut env);
    match env.insert(
        "argv".to_string(),
        ObjType::Any,
        Obj::list(args.into_iter().map(|arg| Obj::from(arg)).collect()),
    ) {
        Ok(()) => (),
        Err(e) => panic!("inserting argv failed: {}", e),
    }
    match env.insert("__file__".to_string(), ObjType::Any, Obj::from(filename)) {
        Ok(()) => (),
        Err(e) => panic!("inserting __file__ failed: {}", e),
    }
    let e = Rc::new(RefCell::new(env));

    match parse(&code) {
        Ok(Some(expr)) => {
            warn(&e, &expr);
            match evaluate(&e, &expr) {
                Ok(Obj::Null) => {}
                Ok(e) => {
                    println!("{}", e);
                }
                Err(e) => {
                    println!("ERROR: {}", e.render(&code));
                }
            }
        }
        Ok(None) => {}
        Err(e) => {
            println!("PARSE ERROR: {}", e.render(&code));
        }
    }
}

fn main() {
    let mut args = std::env::args().collect::<Vec<String>>();
    if args.len() <= 1 {
        #[cfg(feature = "cli")]
        cli::repl();
        #[cfg(not(feature = "cli"))]
        repl();
    } else {
        args.remove(0);
        let (code, filename) = if args[0] == "-e" {
            args.remove(0);
            if args.is_empty() {
                panic!("got -e option but nothing after");
            }
            (args.remove(0), "<repl>".to_string())
        } else {
            let mut code = String::new();
            let arg_filename = args.remove(0);
            let filename = std::fs::canonicalize(&arg_filename)
                .expect(&format!("canonicalizing file {} failed", arg_filename));
            match File::open(&filename) {
                Ok(mut file) => match file.read_to_string(&mut code) {
                    Ok(_) => (code, filename.to_string_lossy().into_owned()),
                    Err(e) => panic!("reading code file {} failed: {}", arg_filename, e),
                },
                Err(e) => {
                    panic!("opening code file {} failed: {}", arg_filename, e);
                }
            }
        };
        run_code(&code, args, filename);
    }
}
