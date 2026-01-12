use crate::core::*;
use crate::lex::CodeLoc;
use crate::rc::Rc;
use std::collections::HashMap;

struct OptimState {
    stack: HashMap<String, usize>,
    stack_size: usize,
}

fn extract_simple_ident_from_lvalue(lv: &Lvalue) -> Option<String> {
    match lv {
        Lvalue::IndexedIdent(Ident::Ident(name), indices) if indices.is_empty() => {
            Some(name.clone())
        }
        Lvalue::Annotation(inner, _) => extract_simple_ident_from_lvalue(inner),
        _ => None,
    }
}

fn optimize_indices(state: &mut OptimState, indices: Vec<IndexOrSlice>) -> Vec<IndexOrSlice> {
    indices
        .into_iter()
        .map(|ios| match ios {
            IndexOrSlice::Index(expr) => IndexOrSlice::Index(Box::new(optimize(state, *expr))),
            IndexOrSlice::Slice(start, end) => IndexOrSlice::Slice(
                start.map(|e| Box::new(optimize(state, *e))),
                end.map(|e| Box::new(optimize(state, *e))),
            ),
            IndexOrSlice::Symbol(s) => IndexOrSlice::Symbol(s),
        })
        .collect()
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
                        let opt_expr = optimize(state, *expr);

                        if ioses.is_empty() {
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
                            // Has indexing - optimize indices and replace ident if on stack
                            let opt_indices = optimize_indices(state, ioses);
                            let new_ident = match state.stack.get(&ident) {
                                Some(stack_index) => {
                                    let peek_index = state.stack_size - stack_index - 1;
                                    Ident::InternalPeek(peek_index)
                                }
                                None => Ident::Ident(ident),
                            };
                            LocExpr {
                                start: e.start,
                                end: e.end,
                                expr: Expr::Assign(
                                    false,
                                    Box::new(Lvalue::IndexedIdent(new_ident, opt_indices)),
                                    Box::new(opt_expr),
                                ),
                            }
                        }
                    }
                    _ => panic!("Unsupported assign lvalue annotation"),
                },
                Lvalue::IndexedIdent(Ident::Ident(ident), ioses) => {
                    let opt_expr = optimize(state, *expr);

                    if ioses.is_empty() {
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
                        // Has indexing - optimize indices and replace ident if on stack
                        let opt_indices = optimize_indices(state, ioses);
                        let new_ident = match state.stack.get(&ident) {
                            Some(stack_index) => {
                                let peek_index = state.stack_size - stack_index - 1;
                                Ident::InternalPeek(peek_index)
                            }
                            None => Ident::Ident(ident),
                        };
                        LocExpr {
                            start: e.start,
                            end: e.end,
                            expr: Expr::Assign(
                                false,
                                Box::new(Lvalue::IndexedIdent(new_ident, opt_indices)),
                                Box::new(opt_expr),
                            ),
                        }
                    }
                }
                _ => panic!("Unsupported assign lvalue"),
            }
        }
        Expr::OpAssign(false, lvalue, op, rhs) => match *lvalue {
            Lvalue::IndexedIdent(Ident::Ident(ident), ioses) => {
                let opt_op = optimize(state, *op);
                let opt_rhs = optimize(state, *rhs);
                let opt_indices = optimize_indices(state, ioses);

                let new_ident = match state.stack.get(&ident) {
                    Some(stack_index) => {
                        let peek_index = state.stack_size - stack_index - 1;
                        Ident::InternalPeek(peek_index)
                    }
                    None => Ident::Ident(ident),
                };

                LocExpr {
                    start: e.start,
                    end: e.end,
                    expr: Expr::OpAssign(
                        false,
                        Box::new(Lvalue::IndexedIdent(new_ident, opt_indices)),
                        Box::new(opt_op),
                        Box::new(opt_rhs),
                    ),
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
        Expr::Index(base, ios) => {
            let opt_base = optimize(state, *base);
            let opt_ios = match ios {
                IndexOrSlice::Index(expr) => IndexOrSlice::Index(Box::new(optimize(state, *expr))),
                IndexOrSlice::Slice(start, end) => IndexOrSlice::Slice(
                    start.map(|e| Box::new(optimize(state, *e))),
                    end.map(|e| Box::new(optimize(state, *e))),
                ),
                IndexOrSlice::Symbol(s) => IndexOrSlice::Symbol(s),
            };
            LocExpr {
                start: e.start,
                end: e.end,
                expr: Expr::Index(Box::new(opt_base), opt_ios),
            }
        }
        Expr::Lambda(params, body, _slot_vars) => {
            // TODO slot_vars totally broke this. maybe give up

            // capture expressions for all current stack variables
            // (this optimization is totally wrong whenever we mutate them; we need to do like
            // upvalues or something.)
            let mut captures = Vec::new();
            let mut stack_vars: Vec<_> = state.stack.iter().collect();
            stack_vars.sort_by_key(|(_, idx)| **idx);

            for &(_, stack_idx) in &stack_vars {
                let peek_offset = state.stack_size - stack_idx - 1;
                captures.push(Box::new(LocExpr {
                    start: e.start,
                    end: e.start,
                    expr: Expr::InternalPeek(peek_offset),
                }));
            }

            let saved_stack = state.stack.clone();
            let saved_size = state.stack_size;

            // add lambda parameters to the stack (on top of captures)
            let mut param_count = 0;
            for param in params.iter() {
                match extract_simple_ident_from_lvalue(param) {
                    Some(name) => {
                        state.stack.insert(name, state.stack_size);
                        state.stack_size += 1;
                        param_count += 1;
                    }
                    None => panic!("Lambda: Only simple parameter names supported"),
                }
            }

            let body_owned = Rc::try_unwrap(body).unwrap_or_else(|_rc| {
                panic!("Lambda optimization: body Rc has multiple strong references")
            });
            let opt_body = optimize(state, body_owned);

            state.stack = saved_stack;
            state.stack_size = saved_size;

            LocExpr {
                start: e.start,
                end: e.end,
                expr: Expr::InternalLambda(Rc::new(captures), Some(param_count), Rc::new(opt_body)),
            }
        }
        Expr::List(elements) => {
            let opt_elements = elements
                .into_iter()
                .map(|elem| Box::new(optimize(state, *elem)))
                .collect();
            LocExpr {
                start: e.start,
                end: e.end,
                expr: Expr::List(opt_elements),
            }
        }
        Expr::Freeze(inner) => {
            let opt_inner = optimize(state, *inner);
            LocExpr {
                start: e.start,
                end: e.end,
                expr: Expr::Freeze(Box::new(opt_inner)),
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
