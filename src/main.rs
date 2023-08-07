use noulith::{evaluate, initialize, parse, warn, Env, Expr, LocExpr, Obj, ObjType, TopEnv};
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

fn run_code(code: &str, args: Vec<String>, invoke_wrapper: Option<&'static str>, filename: String) {
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
            let wrapped_expr = match invoke_wrapper {
                Some(wrap_id) => {
                    let wrapper = Env::try_borrow_get_var(&e, wrap_id)
                        .expect("BUG: env didn't have specified invocation wrapper");
                    LocExpr {
                        start: expr.start,
                        end: expr.end,
                        expr: Expr::Call(
                            Box::new(LocExpr {
                                start: expr.start,
                                end: expr.start,
                                expr: Expr::Frozen(wrapper),
                            }),
                            vec![Box::new(expr)],
                            noulith::CallSyntax::Parentheses,
                        ),
                    }
                }
                None => expr,
            };
            match evaluate(&e, &wrapped_expr) {
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

fn get_wrapper(arg: &str) -> Option<Option<&'static str>> {
    match arg {
        "-e" => Some(None),
        "-i" => Some(Some("interact")),
        "-l" => Some(Some("interact_lines")),
        _ => None,
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
        let (code, filename, wrap_id) = match get_wrapper(&args[0]) {
            Some(wrap_id) => {
                args.remove(0);
                if args.is_empty() {
                    panic!("got {} option but nothing after", args[0]);
                }
                (args.remove(0), "<repl>".to_string(), wrap_id)
            }
            _ => {
                let mut code = String::new();
                let arg_filename = args.remove(0);
                let filename = std::fs::canonicalize(&arg_filename)
                    .expect(&format!("canonicalizing file {} failed", arg_filename));
                match File::open(&filename) {
                    Ok(mut file) => match file.read_to_string(&mut code) {
                        Ok(_) => (code, filename.to_string_lossy().into_owned(), None),
                        Err(e) => panic!("reading code file {} failed: {}", arg_filename, e),
                    },
                    Err(e) => {
                        panic!("opening code file {} failed: {}", arg_filename, e);
                    }
                }
            }
        };
        run_code(&code, args, wrap_id, filename);
    }
}
