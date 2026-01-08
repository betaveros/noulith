use crate::core::*;
use crate::lex::CodeLoc;
use std::collections::HashMap;

struct OptimState {
    stack: HashMap<String, usize>,
    stack_size: usize,
}

fn optimize_for(
    state: &mut OptimState,
    mut its: Vec<ForIteration>,
    outer_start: CodeLoc,
    outer_end: CodeLoc,
    body: LocExpr,
) -> LocExpr {
    if its.is_empty() {
        optimize(state, body)
    } else {
        match its.remove(0) {
            ForIteration::Iteration(ForIterationType::Normal, lvalue, expr) => match *lvalue {
                Lvalue::IndexedIdent(Ident::Ident(ident), ioses) => {
                    if ioses.is_empty() {
                        let opt_expr = optimize(state, *expr);

                        // not necessarily problematic, just shadows; but i'm lazy
                        assert!(!state.stack.contains_key(&ident));
                        state.stack.insert(ident.clone(), state.stack_size);
                        state.stack_size += 1;

                        let opt_rest = optimize_for(state, its, outer_start, outer_end, body);

                        state.stack.remove(&ident);
                        state.stack_size -= 1;

                        LocExpr {
                            start: outer_start,
                            end: outer_end,
                            expr: Expr::InternalFor(Box::new(opt_expr), Box::new(opt_rest)),
                        }
                    } else {
                        panic!("For iteration: No indexing")
                    }
                }
                _ => panic!("Unsupported for lvalue"),
            },
            _ => panic!("Unsupported for iteration"),
        }
    }
}

fn optimize(state: &mut OptimState, e: LocExpr) -> LocExpr {
    match e.expr {
        Expr::Sequence(seq, swallow) => LocExpr {
            start: e.start,
            end: e.end,
            expr: Expr::Sequence(
                seq.into_iter()
                    .map(|e| Box::new(optimize(state, *e)))
                    .collect(),
                swallow,
            ),
        },
        Expr::Ident(ident) => {
            let expr = match state.stack.get(&ident) {
                Some(stack_index) => Expr::InternalPeek(state.stack_size - stack_index - 1),
                None => Expr::Ident(ident),
            };
            LocExpr {
                start: e.start,
                end: e.end,
                expr,
            }
        }
        Expr::Assign(false, lvalue, expr) => {
            match *lvalue {
                Lvalue::Annotation(ann_lvalue, None) => match *ann_lvalue {
                    Lvalue::IndexedIdent(Ident::Ident(ident), ioses) => {
                        if ioses.is_empty() {
                            let opt_expr = optimize(state, *expr);

                            // Check if this is a new variable or reassignment
                            match state.stack.get(&ident) {
                                None => {
                                    // New variable - push onto stack
                                    state.stack.insert(ident.clone(), state.stack_size);
                                    state.stack_size += 1;
                                    LocExpr {
                                        start: e.start,
                                        end: e.end,
                                        expr: Expr::InternalPush(Box::new(opt_expr)),
                                    }
                                }
                                Some(stack_index) => {
                                    // Reassignment to existing stack variable
                                    let peek_index = state.stack_size - stack_index - 1;
                                    LocExpr {
                                        start: e.start,
                                        end: e.end,
                                        expr: Expr::Assign(
                                            false,
                                            Box::new(Lvalue::IndexedIdent(
                                                Ident::InternalPeek(peek_index),
                                                Vec::new(),
                                            )),
                                            Box::new(opt_expr),
                                        ),
                                    }
                                }
                            }
                        } else {
                            panic!("Assign: No indexing supported")
                        }
                    }
                    _ => panic!("Unsupported assign lvalue annotation"),
                },
                Lvalue::IndexedIdent(Ident::Ident(ident), ioses) => {
                    if ioses.is_empty() {
                        let opt_expr = optimize(state, *expr);

                        // Check if this is a new variable or reassignment
                        match state.stack.get(&ident) {
                            None => {
                                // New variable - push onto stack
                                state.stack.insert(ident.clone(), state.stack_size);
                                state.stack_size += 1;
                                LocExpr {
                                    start: e.start,
                                    end: e.end,
                                    expr: Expr::InternalPush(Box::new(opt_expr)),
                                }
                            }
                            Some(stack_index) => {
                                // Reassignment to existing stack variable
                                let peek_index = state.stack_size - stack_index - 1;
                                LocExpr {
                                    start: e.start,
                                    end: e.end,
                                    expr: Expr::Assign(
                                        false,
                                        Box::new(Lvalue::IndexedIdent(
                                            Ident::InternalPeek(peek_index),
                                            Vec::new(),
                                        )),
                                        Box::new(opt_expr),
                                    ),
                                }
                            }
                        }
                    } else {
                        panic!("Assign: No indexing supported")
                    }
                }
                _ => panic!("Unsupported assign lvalue"),
            }
        }
        Expr::OpAssign(false, lvalue, op, rhs) => match *lvalue {
            Lvalue::IndexedIdent(Ident::Ident(ident), ioses) => {
                if ioses.is_empty() {
                    match state.stack.get(&ident) {
                        Some(stack_index) => {
                            let peek_index = state.stack_size - stack_index - 1;
                            let opt_op = optimize(state, *op);
                            let opt_rhs = optimize(state, *rhs);
                            LocExpr {
                                start: e.start,
                                end: e.end,
                                expr: Expr::OpAssign(
                                    false,
                                    Box::new(Lvalue::IndexedIdent(
                                        Ident::InternalPeek(peek_index),
                                        Vec::new(),
                                    )),
                                    Box::new(opt_op),
                                    Box::new(opt_rhs),
                                ),
                            }
                        }
                        None => panic!("OpAssign to undeclared variable: {}", ident),
                    }
                } else {
                    panic!("OpAssign: No indexing supported")
                }
            }
            _ => panic!("Unsupported OpAssign lvalue"),
        },
        Expr::For(its, body) => match *body {
            ForBody::Execute(inner) => optimize_for(state, its, e.start, e.end, inner),
            _ => panic!("Unsupported for"),
        },
        Expr::Chain(base, calls) => {
            let opt_base = optimize(state, *base);
            let opt_calls = calls
                .into_iter()
                .map(|(op, arg)| {
                    (
                        Box::new(optimize(state, *op)),
                        Box::new(optimize(state, *arg)),
                    )
                })
                .collect();
            LocExpr {
                start: e.start,
                end: e.end,
                expr: Expr::Chain(Box::new(opt_base), opt_calls),
            }
        }
        Expr::Call(func, args, syntax) => {
            let opt_func = optimize(state, *func);
            let opt_args = args
                .into_iter()
                .map(|arg| Box::new(optimize(state, *arg)))
                .collect();
            LocExpr {
                start: e.start,
                end: e.end,
                expr: Expr::Call(Box::new(opt_func), opt_args, syntax),
            }
        }
        Expr::Frozen(obj) => LocExpr {
            start: e.start,
            end: e.end,
            expr: Expr::Frozen(obj),
        },
        expr @ (Expr::Null
        | Expr::IntLit64(_)
        | Expr::IntLit(_)
        | Expr::RatLit(_)
        | Expr::FloatLit(_)
        | Expr::ImaginaryFloatLit(_)
        | Expr::StringLit(_)
        | Expr::BytesLit(_)
        | Expr::Underscore
        | Expr::Backref(_)) => LocExpr {
            start: e.start,
            end: e.end,
            expr,
        },
        expr => panic!("can't optimize {:?}", expr),
    }
}

pub fn optimize_expr(e: LocExpr) -> LocExpr {
    let mut state = OptimState {
        stack: HashMap::new(),
        stack_size: 0,
    };
    optimize(&mut state, e)
}
