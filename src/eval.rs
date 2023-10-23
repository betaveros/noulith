use crate::core::*;
use crate::few::*;
use crate::iter::*;
use crate::lex::*;
use crate::nnum::NNum;
use num::complex::Complex64;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Display;
use std::fs;
use std::rc::Rc;

#[derive(Debug)]
pub enum EvaluatedIndexOrSlice {
    Index(Obj),
    Slice(Option<Obj>, Option<Obj>),
}

#[derive(Debug)]
pub enum EvaluatedLvalue {
    Underscore,
    IndexedIdent(String, Vec<EvaluatedIndexOrSlice>),
    Annotation(Box<EvaluatedLvalue>, Option<Obj>),
    CommaSeq(Vec<Box<EvaluatedLvalue>>),
    Splat(Box<EvaluatedLvalue>),
    Or(Box<EvaluatedLvalue>, Box<EvaluatedLvalue>),
    Literal(Obj),
    Destructure(Rc<dyn Builtin>, Vec<Box<EvaluatedLvalue>>),
    DestructureStruct(Struct, Vec<Box<EvaluatedLvalue>>),
}

impl Display for EvaluatedLvalue {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EvaluatedLvalue::Underscore => write!(formatter, "_"),
            EvaluatedLvalue::IndexedIdent(s, ixs) => {
                write!(formatter, "{}", s)?;
                for ix in ixs {
                    // FIXME
                    write!(formatter, "[{:?}]", ix)?;
                }
                Ok(())
            }
            EvaluatedLvalue::Annotation(s, Some(anno)) => {
                write!(formatter, "{}: {}", s, anno)
            }
            EvaluatedLvalue::Annotation(s, None) => {
                write!(formatter, "({}:)", s)
            }
            EvaluatedLvalue::CommaSeq(vs) => {
                write!(formatter, "(")?;
                for v in vs {
                    write!(formatter, "{},", v)?;
                }
                write!(formatter, ")")
            }
            EvaluatedLvalue::Splat(s) => {
                write!(formatter, "(...{})", s)
            }
            EvaluatedLvalue::Or(a, b) => {
                write!(formatter, "({} or {})", a, b)
            }
            EvaluatedLvalue::Literal(a) => {
                write!(formatter, "literal({})", a)
            }
            EvaluatedLvalue::Destructure(f, vs) => {
                write!(formatter, "{}(", f.builtin_name())?;
                for v in vs {
                    write!(formatter, "{},", v)?;
                }
                write!(formatter, ")")
            }
            EvaluatedLvalue::DestructureStruct(s, vs) => {
                write!(formatter, "{}(", s.name)?;
                for v in vs {
                    write!(formatter, "{},", v)?;
                }
                write!(formatter, ")")
            }
        }
    }
}

pub struct ChainEvaluator {
    // represents all pending operators and operands that we can't yet be certain have high enough
    // precedence to evaluate. in steady state, the operators are interspersed between the operands
    // in order, so operands.len() == 1 + operators.len(). but elements of operands can be multiple
    // Objs long when we're chaining operators. e.g. after seeing 1 < 2 <= 3, operands should be
    // [1, 2], [3] and operators should just have one element that's a (<, <=) merger
    operands: Vec<Vec<Obj>>,
    operators: Vec<(Func, Precedence, CodeLoc, CodeLoc)>,
}

impl ChainEvaluator {
    pub fn new(operand: Obj) -> ChainEvaluator {
        ChainEvaluator {
            operands: vec![vec![operand]],
            operators: Vec::new(),
        }
    }

    pub fn run_top_popped(
        &mut self,
        env: &REnv,
        op: Func,
        start: CodeLoc,
        end: CodeLoc,
    ) -> NRes<()> {
        let rhs = self.operands.pop().expect("sync");
        let mut lhs = self.operands.pop().expect("sync");
        lhs.extend(rhs);
        self.operands.push(vec![add_trace(
            op.run(env, lhs),
            || format!("chain {}", op),
            start,
            end,
        )?]);
        Ok(())
    }

    pub fn run_top(&mut self, env: &REnv) -> NRes<()> {
        let (op, _, start, end) = self.operators.pop().expect("sync");
        self.run_top_popped(env, op, start, end)
    }

    pub fn give(
        &mut self,
        env: &REnv,
        operator: Func,
        precedence: Precedence,
        operand: Obj,
        start: CodeLoc,
        end: CodeLoc,
    ) -> NRes<()> {
        // is the top operator on the stack higher precedence than the new operator?
        while self
            .operators
            .last()
            .map_or(false, |t| t.1.tighter_than_when_before(&precedence))
        {
            // if so, run it, and repeat.
            let (top, prec, start, end) = self.operators.pop().expect("sync");
            match top.try_chain(&operator) {
                Some(new_op) => {
                    // except that if it chains with the new operator, that takes precedence; merge
                    // the operators and the last two operands.
                    self.operators.push((new_op, prec, start, end));

                    let last = self.operands.pop().expect("sync");
                    self.operands.last_mut().expect("sync").extend(last);
                    self.operands.push(vec![operand]);

                    return Ok(());
                }
                None => {
                    self.run_top_popped(env, top, start, end)?;
                }
            }
        }

        self.operators.push((operator, precedence, start, end));
        self.operands.push(vec![operand]);
        Ok(())
    }

    pub fn finish(&mut self, env: &REnv) -> NRes<Obj> {
        while !self.operators.is_empty() {
            self.run_top(env)?;
        }
        if self.operands.len() == 1 {
            Ok(self.operands.remove(0).remove(0))
        } else {
            panic!("chain eval out of sync")
        }
    }
}

struct LvalueChainEvaluator {
    operands: Vec<Vec<Box<EvaluatedLvalue>>>,
    operators: Vec<(Func, Precedence)>,
}

impl LvalueChainEvaluator {
    fn new(operand: EvaluatedLvalue) -> LvalueChainEvaluator {
        LvalueChainEvaluator {
            operands: vec![vec![Box::new(operand)]],
            operators: Vec::new(),
        }
    }

    fn run_top_popped(&mut self, op: Func) -> NRes<()> {
        let rhs = self.operands.pop().expect("sync");
        let mut lhs = self.operands.pop().expect("sync");
        match op {
            Func::Builtin(b) => {
                lhs.extend(rhs);
                self.operands
                    .push(vec![Box::new(EvaluatedLvalue::Destructure(b, lhs))]);
                Ok(())
            }
            nop => Err(NErr::type_error(format!(
                "can't destructure with non-builtin {:?}",
                nop
            ))),
        }
    }

    fn run_top(&mut self) -> NRes<()> {
        let (op, _) = self.operators.pop().expect("sync");
        self.run_top_popped(op)
    }

    fn give(
        &mut self,
        operator: Func,
        precedence: Precedence,
        operand: EvaluatedLvalue,
    ) -> NRes<()> {
        while self
            .operators
            .last()
            .map_or(false, |t| t.1.tighter_than_when_before(&precedence))
        {
            let (top, prec) = self.operators.pop().expect("sync");
            match top.try_chain(&operator) {
                Some(new_op) => {
                    self.operators.push((new_op, prec));

                    let last = self.operands.pop().expect("sync");
                    self.operands.last_mut().expect("sync").extend(last);
                    self.operands.push(vec![Box::new(operand)]);

                    return Ok(());
                }
                None => {
                    self.run_top_popped(top)?;
                }
            }
        }

        self.operators.push((operator, precedence));
        self.operands.push(vec![Box::new(operand)]);
        Ok(())
    }

    fn finish(&mut self) -> NRes<EvaluatedLvalue> {
        while !self.operators.is_empty() {
            self.run_top()?;
        }
        if self.operands.len() == 1 {
            Ok(*self.operands.remove(0).remove(0))
        } else {
            panic!("chain eval out of sync")
        }
    }
}

// allow splats
pub fn eval_seq(env: &Rc<RefCell<Env>>, exprs: &Vec<Box<LocExpr>>) -> NRes<Vec<Obj>> {
    let mut acc = Vec::new();
    for x in exprs {
        match &((**x).expr) {
            Expr::Splat(inner) => {
                let mut res = evaluate(env, inner)?;
                for o in mut_obj_into_iter(&mut res, "splat")? {
                    acc.push(o?);
                }
            }
            _ => acc.push(evaluate(env, x)?),
        }
    }
    Ok(acc)
}

pub fn eval_index_or_slice(
    env: &Rc<RefCell<Env>>,
    expr: &IndexOrSlice,
) -> NRes<EvaluatedIndexOrSlice> {
    match expr {
        IndexOrSlice::Index(v) => Ok(EvaluatedIndexOrSlice::Index(evaluate(env, v)?)),
        IndexOrSlice::Slice(a, b) => Ok(EvaluatedIndexOrSlice::Slice(
            match a {
                Some(a) => Some(evaluate(env, a)?),
                None => None,
            },
            match b {
                Some(b) => Some(evaluate(env, b)?),
                None => None,
            },
        )),
    }
}

pub fn eval_lvalue(env: &Rc<RefCell<Env>>, expr: &Lvalue) -> NRes<EvaluatedLvalue> {
    match expr {
        Lvalue::Underscore => Ok(EvaluatedLvalue::Underscore),
        Lvalue::IndexedIdent(s, v) => Ok(EvaluatedLvalue::IndexedIdent(
            s.to_string(),
            v.iter()
                .map(|e| Ok(eval_index_or_slice(env, e)?))
                .collect::<NRes<Vec<EvaluatedIndexOrSlice>>>()?,
        )),
        Lvalue::Annotation(s, t) => Ok(EvaluatedLvalue::Annotation(
            Box::new(eval_lvalue(env, s)?),
            match t {
                Some(e) => Some(evaluate(env, e)?),
                None => None,
            },
        )),
        Lvalue::CommaSeq(v) => Ok(EvaluatedLvalue::CommaSeq(
            v.iter()
                .map(|e| Ok(Box::new(eval_lvalue(env, e)?)))
                .collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?,
        )),
        Lvalue::Splat(v) => Ok(EvaluatedLvalue::Splat(Box::new(eval_lvalue(env, v)?))),
        Lvalue::Or(a, b) => Ok(EvaluatedLvalue::Or(
            Box::new(eval_lvalue(env, a)?),
            Box::new(eval_lvalue(env, b)?),
        )),
        Lvalue::Literal(obj) => Ok(EvaluatedLvalue::Literal(obj.clone())),
        Lvalue::Destructure(f, args) => match evaluate(env, f)? {
            Obj::Func(Func::Builtin(b), _) => Ok(EvaluatedLvalue::Destructure(
                b,
                args.iter()
                    .map(|e| Ok(Box::new(eval_lvalue(env, e)?)))
                    .collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?,
            )),
            Obj::Func(Func::Type(ObjType::Struct(s)), _) => Ok(EvaluatedLvalue::DestructureStruct(
                s,
                args.iter()
                    .map(|e| Ok(Box::new(eval_lvalue(env, e)?)))
                    .collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?,
            )),
            ef => Err(NErr::type_error(format!(
                "destructure callee was not builtin or struct, got {}",
                ef
            ))),
        },
        Lvalue::ChainDestructure(lv, vs) => {
            let mut ce = LvalueChainEvaluator::new(eval_lvalue(env, lv)?);
            for (oper, opd) in vs {
                let oprr = evaluate(env, oper)?;
                if let Obj::Func(b, prec) = oprr {
                    let oprd = eval_lvalue(env, opd)?;
                    ce.give(b, prec, oprd)?;
                } else {
                    return Err(NErr::type_error(format!(
                        "Destructure chain cannot use nonblock in operand position: {}",
                        FmtObj::debug(&oprr)
                    )));
                }
            }
            ce.finish()
        }
        Lvalue::Literally(e) => Ok(EvaluatedLvalue::Literal(evaluate(env, e)?)),
    }
}

// Important: callers are responsible for absorbing NErr::Break!
fn evaluate_for(
    env: &Rc<RefCell<Env>>,
    its: &[ForIteration],
    callback: &mut impl FnMut(&Rc<RefCell<Env>>) -> NRes<()>,
) -> NRes<()> {
    match its {
        [] => match callback(env) {
            Ok(()) => Ok(()),
            // don't catch break, thonking
            Err(NErr::Continue) => Ok(()),
            Err(e) => Err(e),
        },
        [ForIteration::Iteration(ty, lvalue, expr), rest @ ..] => {
            let mut itr = evaluate(env, expr)?;
            match ty {
                ForIterationType::Normal => {
                    for x in mut_obj_into_iter(&mut itr, "for iteration")? {
                        let ee = Env::with_parent(env);
                        let p = eval_lvalue(&ee, lvalue)?;

                        // should assign take x
                        assign(&ee, &p, Some(&ObjType::Any), x?)?;
                        evaluate_for(&ee, rest, callback)?;
                    }
                }
                ForIterationType::Item => {
                    for kv in mut_obj_into_iter_pairs(&mut itr, "for (item) iteration")? {
                        let (k, v) = kv?;
                        let ee = Env::with_parent(env);
                        let p = eval_lvalue(&ee, lvalue)?;

                        // should assign take x
                        assign(
                            &ee,
                            &p,
                            Some(&ObjType::Any),
                            Obj::list(vec![key_to_obj(k), v]),
                        )?;
                        evaluate_for(&ee, rest, callback)?;
                    }
                }
                ForIterationType::Declare => {
                    let ee = Env::with_parent(env);
                    let p = eval_lvalue(&ee, lvalue)?;
                    assign(&ee, &p, Some(&ObjType::Any), itr)?;

                    evaluate_for(&ee, rest, callback)?;
                }
            }
            Ok(())
        }
        [ForIteration::Guard(guard), rest @ ..] => {
            let r = evaluate(env, guard)?;
            if r.truthy() {
                evaluate_for(env, rest, callback)
            } else {
                Ok(())
            }
        }
    }
}

fn splat_section_eval(
    env: &Rc<RefCell<Env>>,
    args: &Vec<Box<LocExpr>>,
) -> NRes<Result<Vec<Obj>, Vec<Result<Obj, bool>>>> {
    // check for underscores indicating a call section
    // splats are expanded, underscores are Err(false), splatted underscores are Err(true)
    let mut acc: Result<Vec<Obj>, Vec<Result<Obj, bool>>> = Ok(Vec::new());
    for x in args {
        let curx = match &**x {
            LocExpr {
                expr: Expr::Splat(e),
                ..
            } => match &**e {
                LocExpr {
                    expr: Expr::Underscore,
                    ..
                } => (true, None),
                e => (true, Some(evaluate(env, &e)?)),
            },
            LocExpr {
                expr: Expr::Underscore,
                ..
            } => (false, None),
            e => (false, Some(evaluate(env, &e)?)),
        };
        acc = match (curx, acc) {
            ((is_splat, None), Ok(v)) => {
                let mut r = v.into_iter().map(Ok).collect::<Vec<Result<Obj, bool>>>();
                r.push(Err(is_splat));
                Err(r)
            }
            ((false, Some(e)), Ok(mut v)) => {
                v.push(e);
                Ok(v)
            }
            ((true, Some(mut e)), Ok(mut v)) => {
                for x in mut_obj_into_iter(&mut e, "call splat")? {
                    v.push(x?);
                }
                Ok(v)
            }
            ((false, Some(e)), Err(mut v)) => {
                v.push(Ok(e));
                Err(v)
            }
            ((true, Some(mut e)), Err(mut v)) => {
                for x in mut_obj_into_iter(&mut e, "call splat")? {
                    v.push(Ok(x?))
                }
                Err(v)
            }
            ((is_splat, None), Err(mut v)) => {
                v.push(Err(is_splat));
                Err(v)
            }
        }
    }
    Ok(acc)
}

pub fn evaluate(env: &Rc<RefCell<Env>>, expr: &LocExpr) -> NRes<Obj> {
    match &expr.expr {
        Expr::Null => Ok(Obj::Null),
        Expr::IntLit(n) => Ok(Obj::from(n.clone())),
        Expr::RatLit(n) => Ok(Obj::from(NNum::from(n.clone()))),
        Expr::FloatLit(n) => Ok(Obj::from(*n)),
        Expr::ImaginaryFloatLit(n) => Ok(Obj::Num(NNum::Complex(Complex64::new(0.0, *n)))),
        Expr::StringLit(s) => Ok(Obj::Seq(Seq::String(Rc::clone(s)))),
        Expr::BytesLit(s) => Ok(Obj::Seq(Seq::Bytes(Rc::clone(s)))),
        Expr::Frozen(x) => Ok(x.clone()),
        Expr::FormatString(s) => {
            let mut acc = String::new();
            for x in s.iter() {
                match x {
                    Ok(c) => acc.push(*c),
                    Err((expr, flags)) => {
                        evaluate(env, &expr)?
                            .fmt_with(&mut acc, flags.clone())
                            .map_err(|e| NErr::io_error(format!("format string issue: {}", e)))?
                    }
                }
            }
            Ok(Obj::from(acc))
        }
        Expr::Ident(s) => add_trace(
            Env::try_borrow_get_var(env, s),
            || format!("ident"),
            expr.start,
            expr.end,
        ),
        Expr::Underscore => Err(NErr::syntax_error_loc(
            "Can't evaluate underscore".to_string(),
            "_".to_string(),
            expr.start,
            expr.end,
        )),
        Expr::Index(x, i) => match (&**x, i) {
            (
                LocExpr {
                    expr: Expr::Underscore,
                    ..
                },
                IndexOrSlice::Index(i),
            ) => match &**i {
                LocExpr {
                    expr: Expr::Underscore,
                    ..
                } => Ok(Obj::Func(
                    Func::IndexSection(None, None),
                    Precedence::zero(),
                )),
                i => Ok(Obj::Func(
                    Func::IndexSection(None, Some(Box::new(evaluate(env, i)?))),
                    Precedence::zero(),
                )),
            },
            (
                LocExpr {
                    expr: Expr::Underscore,
                    ..
                },
                IndexOrSlice::Slice(i, j),
            ) => {
                let ii = match i.as_deref() {
                    None => None, // actually nothing
                    Some(LocExpr {
                        expr: Expr::Underscore,
                        ..
                    }) => Some(Box::new(None)), // section slot
                    Some(e) => Some(Box::new(Some(evaluate(env, e)?))),
                };
                let jj = match j.as_deref() {
                    None => None, // actually nothing
                    Some(LocExpr {
                        expr: Expr::Underscore,
                        ..
                    }) => Some(Box::new(None)), // section slot
                    Some(e) => Some(Box::new(Some(evaluate(env, e)?))),
                };
                Ok(Obj::Func(
                    Func::SliceSection(None, ii, jj),
                    Precedence::zero(),
                ))
            }
            // TODO: foo[_] (maybe lower priority though, this is a rarer partial app)
            (x, i) => {
                let xr = evaluate(env, x)?;
                let ir = eval_index_or_slice(env, i)?;
                add_trace(
                    index_or_slice(xr, &ir),
                    || format!("index/slice"),
                    expr.start,
                    expr.end,
                )
            }
        },
        Expr::Chain(op1, ops) => {
            if match &((**op1).expr) {
                Expr::Underscore => true,
                _ => false,
            } || ops.iter().any(|(_op, e)| match &((**e).expr) {
                Expr::Underscore => true,
                _ => false,
            }) {
                let v1 = match &((**op1).expr) {
                    Expr::Underscore => None,
                    _ => Some(Box::new(evaluate(env, op1)?)),
                };
                let mut acc = Vec::new();
                for (i, (oper, opd)) in ops.iter().enumerate() {
                    let oprr = evaluate(env, oper)?;
                    if let Obj::Func(b, prec) = oprr {
                        match &((**opd).expr) {
                            Expr::Underscore => {
                                acc.push((oper.start, oper.end, Box::new(b), prec, None));
                            }
                            _ => {
                                let oprd = evaluate(env, opd)?;
                                acc.push((
                                    oper.start,
                                    oper.end,
                                    Box::new(b),
                                    prec,
                                    Some(Box::new(oprd)),
                                ));
                            }
                        }
                    } else {
                        return Err(NErr::type_error_loc(
                            format!(
                                "Chain section cannot use nonblock in operator position: {}",
                                FmtObj::debug(&oprr)
                            ),
                            format!("op {}/{}", i + 1, ops.len()),
                            oper.start,
                            oper.end,
                        ));
                    }
                }
                Ok(Obj::Func(Func::ChainSection(v1, acc), Precedence::zero()))
            } else if ops.len() == 1 {
                // micro-optimization, but this path is extremely common
                let lhs = evaluate(env, op1)?;
                let (oper, opd) = &ops[0];
                let oprr = evaluate(env, oper)?;
                if let Obj::Func(b, _prec) = &oprr {
                    let oprd = evaluate(env, opd)?;
                    add_trace(
                        b.run2(env, lhs, oprd),
                        || format!("chain {}", oprr),
                        oper.start,
                        oper.end,
                    )
                } else {
                    Err(NErr::type_error_loc(
                        format!(
                            "Chain cannot use nonblock in operator position: {}",
                            FmtObj::debug(&oprr)
                        ),
                        "op 1/1".to_string(),
                        oper.start,
                        oper.end,
                    ))
                }
            } else {
                let mut ev = ChainEvaluator::new(evaluate(env, op1)?);
                for (i, (oper, opd)) in ops.iter().enumerate() {
                    let oprr = evaluate(env, oper)?;
                    if let Obj::Func(b, prec) = oprr {
                        let oprd = evaluate(env, opd)?;
                        ev.give(env, b, prec, oprd, oper.start, oper.end)?;
                    } else {
                        return Err(NErr::type_error_loc(
                            format!(
                                "Chain cannot use nonblock in operator position: {}",
                                FmtObj::debug(&oprr)
                            ),
                            format!("op {}/{}", i + 1, ops.len()),
                            oper.start,
                            oper.end,
                        ));
                    }
                }
                ev.finish(env)
            }
        }
        Expr::And(lhs, rhs) => {
            let lr = evaluate(env, lhs)?;
            if lr.truthy() {
                evaluate(env, rhs)
            } else {
                Ok(lr)
            }
        }
        Expr::Or(lhs, rhs) => {
            let lr = evaluate(env, lhs)?;
            if lr.truthy() {
                Ok(lr)
            } else {
                evaluate(env, rhs)
            }
        }
        Expr::Coalesce(lhs, rhs) => {
            let lr = evaluate(env, lhs)?;
            if lr != Obj::Null {
                Ok(lr)
            } else {
                evaluate(env, rhs)
            }
        }
        Expr::Assign(every, pat, rhs) => {
            let p = add_trace(
                eval_lvalue(env, pat),
                || format!("assign lvalue"),
                expr.start,
                expr.end,
            )?;
            let res = match &**rhs {
                LocExpr {
                    expr: Expr::CommaSeq(xs),
                    ..
                } => Ok(Obj::list(eval_seq(env, xs)?)),
                _ => evaluate(env, rhs),
            }?;

            let ret = if *every {
                assign_every(&env, &p, None, res)
            } else {
                assign(&env, &p, None, res)
            };
            add_trace(ret, || format!("assign"), expr.start, expr.end)?;
            Ok(Obj::Null)
        }
        Expr::Annotation(s, _) => evaluate(env, s),
        Expr::Consume(pat) => match eval_lvalue(env, pat)? {
            EvaluatedLvalue::IndexedIdent(s, ixs) => try_borrow_nres(env, "env for pop", &s)?
                .modify_existing_var(&s, |(_type, vv)| {
                    modify_existing_index(
                        &mut *try_borrow_mut_nres(vv, "var for consume", &s)?,
                        &ixs,
                        |x| Ok(std::mem::take(x)),
                    )
                })
                .ok_or(NErr::type_error("failed to consume??".to_string()))?,
            _ => Err(NErr::type_error("can't consume, weird pattern".to_string())),
        },
        Expr::Pop(pat) => add_trace(
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => try_borrow_nres(env, "env for pop", &s)?
                    .modify_existing_var(&s, |(_type, vv)| {
                        modify_existing_index(
                            &mut *try_borrow_mut_nres(vv, "var for pop", &s)?,
                            &ixs,
                            |x| match x {
                                Obj::Seq(Seq::List(xs)) => Rc::make_mut(xs)
                                    .pop()
                                    .ok_or(NErr::empty_error("can't pop empty".to_string())),
                                _ => Err(NErr::type_error("can't pop".to_string())),
                            },
                        )
                    })
                    .unwrap_or(Err(NErr::type_error("failed to pop??".to_string()))),
                _ => Err(NErr::type_error_loc(
                    "can't pop, weird pattern".to_string(),
                    "pop".to_string(),
                    expr.start,
                    expr.end,
                )),
            },
            || "pop".to_string(),
            expr.start,
            expr.end,
        ),
        Expr::Remove(pat) => add_trace(
            match eval_lvalue(env, pat)? {
                EvaluatedLvalue::IndexedIdent(s, ixs) => match ixs.as_slice() {
                    [] => Err(NErr::value_error(
                        "can't remove flat identifier".to_string(),
                    )),
                    [rest @ .., last_i] => {
                        try_borrow_nres(env, "env for remove", &s)?
                            .modify_existing_var(&s, |(_type, vv)| {
                                modify_existing_index(
                                    &mut *try_borrow_mut_nres(vv, "var for remove", &s)?,
                                    &rest,
                                    |x| {
                                        match (x, last_i) {
                                            (
                                                Obj::Seq(Seq::List(xs)),
                                                EvaluatedIndexOrSlice::Index(i),
                                            ) => {
                                                let ii = pythonic_index(xs, i)?;
                                                Ok(Rc::make_mut(xs).remove(ii))
                                            }
                                            (
                                                Obj::Seq(Seq::List(xs)),
                                                EvaluatedIndexOrSlice::Slice(i, j),
                                            ) => {
                                                let (lo, hi) =
                                                    pythonic_slice_obj(xs, i.as_ref(), j.as_ref())?;
                                                Ok(Obj::list(
                                                    Rc::make_mut(xs).drain(lo..hi).collect(),
                                                ))
                                            }
                                            (
                                                Obj::Seq(Seq::Dict(xs, _)),
                                                EvaluatedIndexOrSlice::Index(i),
                                            ) => Rc::make_mut(xs)
                                                .remove(&to_key(i.clone())?)
                                                .ok_or(NErr::key_error(
                                                    "key not found in dict".to_string(),
                                                )),
                                            // TODO: remove parts of strings...
                                            // TODO: vecs, bytes...
                                            _ => Err(NErr::type_error("can't remove".to_string())),
                                        }
                                    },
                                )
                            })
                            .unwrap_or(Err(NErr::name_error("var not found to remove".to_string())))
                    }
                },
                _ => Err(NErr::type_error("can't pop, weird pattern".to_string())),
            },
            || format!("remove"),
            expr.start,
            expr.end,
        ),
        Expr::Swap(a, b) => {
            let al = eval_lvalue(env, a)?;
            let bl = eval_lvalue(env, b)?;
            let ao = eval_lvalue_as_obj(env, &al)?;
            let bo = eval_lvalue_as_obj(env, &bl)?;
            assign(&env, &al, None, bo)?;
            assign(&env, &bl, None, ao)?;
            Ok(Obj::Null)
        }
        Expr::OpAssign(every, pat, op, rhs) => {
            if *every {
                let p = eval_lvalue(env, pat)?;
                match evaluate(env, op)? {
                    Obj::Func(ff, _) => {
                        let res = match &**rhs {
                            LocExpr {
                                expr: Expr::CommaSeq(xs),
                                ..
                            } => Ok(Obj::list(eval_seq(env, xs)?)),
                            _ => evaluate(env, rhs),
                        }?;
                        add_trace(
                            modify_every(env, &p, &mut |x| ff.run(env, vec![x, res.clone()])),
                            || format!("op({})-assign", ff),
                            expr.start,
                            expr.end,
                        )?;
                        Ok(Obj::Null)
                    }
                    opv => Err(NErr::type_error(format!(
                        "Operator assignment: operator is not function {:?}",
                        opv
                    ))),
                }
            } else {
                let p = eval_lvalue(env, pat)?;
                let pv = eval_lvalue_as_obj(env, &p)?;
                match evaluate(env, op)? {
                    Obj::Func(ff, _) => {
                        let res = match &**rhs {
                            LocExpr {
                                expr: Expr::CommaSeq(xs),
                                ..
                            } => Ok(Obj::list(eval_seq(env, xs)?)),
                            _ => evaluate(env, rhs),
                        }?;
                        // Drop the Rc from the lvalue so that functions can try to consume it. We
                        // used to only do this when the function was pure, but that required a
                        // stupid amount of code to bookkeep and prevents users from writing
                        // consuming modifiers. Instead it's now enshrined into the semantics.
                        add_trace(
                            drop_lhs(&env, &p),
                            || format!("null-assign"),
                            expr.start,
                            expr.end,
                        )?;
                        let fres = ff.run(env, vec![pv, res])?;
                        add_trace(
                            assign(&env, &p, None, fres),
                            || format!("op({})-assign", ff),
                            expr.start,
                            expr.end,
                        )?;
                        Ok(Obj::Null)
                    }
                    opv => Err(NErr::type_error(format!(
                        "Operator assignment: operator is not function {:?}",
                        opv
                    ))),
                }
            }
        }
        Expr::Call(f, args, _syntax) => {
            let fr = match &**f {
                LocExpr {
                    expr: Expr::Underscore,
                    ..
                } => None,
                f => Some(evaluate(env, f)?),
            };
            // let a = eval_seq(env, args)?;
            let acc = splat_section_eval(env, args)?;

            match (fr, acc) {
                // no section
                (Some(f), Ok(v)) => {
                    // FIXME hmm, eager format not great...
                    let f_for_error = f.clone();
                    add_trace(
                        call_or_part_apply(env, f, v),
                        || format!("call to {}", f_for_error),
                        expr.start,
                        expr.end,
                    )
                }

                // some section
                (None, Ok(v)) => Ok(Obj::Func(
                    Func::CallSection(
                        None,
                        v.into_iter().map(Ok).collect::<Vec<Result<Obj, bool>>>(),
                    ),
                    Precedence::zero(),
                )),
                (f, Err(v)) => Ok(Obj::Func(
                    Func::CallSection(f.map(Box::new), v),
                    Precedence::zero(),
                )),
            }
        }
        Expr::CommaSeq(_) => Err(NErr::syntax_error_loc(
            "Comma seqs only allowed directly on a side of an assignment (for now)".to_string(),
            "seq".to_string(),
            expr.start,
            expr.end,
        )),
        Expr::Splat(_) => Err(NErr::syntax_error_loc(
            "Splats only allowed on an assignment-related place or in call or list (?)".to_string(),
            "splat".to_string(),
            expr.start,
            expr.end,
        )),
        Expr::List(xs) => match splat_section_eval(env, xs)? {
            Ok(v) => Ok(Obj::list(v)),
            Err(e) => Ok(Obj::Func(Func::ListSection(e), Precedence::zero())),
        },
        Expr::Vector(xs) => to_obj_vector(eval_seq(env, xs)?.into_iter().map(Ok)),
        Expr::Dict(def, xs) => {
            let dv = match def {
                Some(de) => Some(evaluate(env, de)?),
                None => None,
            };
            let mut acc = HashMap::new();
            for (ke, ve) in xs {
                match (&((**ke).expr), ve) {
                    (Expr::Splat(inner), None) => {
                        let mut res = evaluate(env, inner)?;
                        for kv in mut_obj_into_iter_pairs(&mut res, "dictionary splat")? {
                            let (k, v) = kv?;
                            acc.insert(k, v);
                        }
                    }
                    (Expr::Splat(_), Some(_)) => {
                        Err(NErr::type_error_loc(format!("Dictionary: Can only splat other dictionary without value; instead got {:?} {:?}", ke, ve),
                        format!("dict lit"),
                        ke.start,
                        ke.end))?
                    }
                    _ => {
                        let k = evaluate(env, ke)?;
                        let kk = to_key(k)?;
                        let v = match ve {
                            Some(vve) => evaluate(env, vve)?,
                            None => Obj::Null,
                        };
                        acc.insert(kk, v);
                    }
                }
            }
            Ok(Obj::dict(acc, dv))
        }
        Expr::Sequence(xs, ending_semicolon) => {
            for (i, x) in xs[..xs.len() - 1].iter().enumerate() {
                add_trace(
                    evaluate(env, x),
                    || format!(";-sequence({}/{})", i + 1, xs.len()),
                    expr.start,
                    expr.end,
                )?;
            }
            let ret = add_trace(
                evaluate(env, xs.last().unwrap()),
                || format!(";-sequence({}/{})", xs.len(), xs.len()),
                expr.start,
                expr.end,
            )?;
            if *ending_semicolon {
                Ok(Obj::Null)
            } else {
                Ok(ret)
            }
        }
        Expr::If(cond, if_body, else_body) => {
            let cr = add_trace(
                evaluate(env, cond),
                || "if-cond".to_string(),
                expr.start,
                expr.end,
            )?;
            if cr.truthy() {
                add_trace(
                    evaluate(env, if_body),
                    || "if-branch".to_string(),
                    expr.start,
                    expr.end,
                )
            } else {
                match else_body {
                    Some(b) => add_trace(
                        evaluate(env, b),
                        || "else-branch".to_string(),
                        expr.start,
                        expr.end,
                    ),
                    None => Ok(Obj::Null),
                }
            }
        }
        Expr::For(iteratees, body) => {
            add_trace(
                match &**body {
                    // something HRTB something forces us to write the closures inline
                    ForBody::Execute(body) => {
                        match evaluate_for(env, iteratees.as_slice(), &mut |e| {
                            evaluate(e, body)?;
                            Ok(())
                        }) {
                            Ok(()) => Ok(Obj::Null),
                            Err(NErr::Break(e)) => Ok(e.unwrap_or(Obj::Null)),
                            Err(e) => Err(e),
                        }
                    }
                    ForBody::Yield(body, into) => {
                        let (cata, into_res) = match into {
                            Some(into_body) => {
                                let f = evaluate(env, into_body)?;
                                match &f {
                                    Obj::Func(Func::Builtin(ref b), _) => {
                                        let cat = b.catamorphism();
                                        (cat, Some(f))
                                    }
                                    _ => (None, Some(f)),
                                }
                            }
                            None => (None, None),
                        };
                        match cata {
                            Some(mut cata) => {
                                let inner = evaluate_for(env, iteratees.as_slice(), &mut |e| {
                                    cata.give(evaluate(e, body)?)
                                });
                                match inner {
                                    Ok(()) | Err(NErr::Break(None)) => cata.finish(),
                                    Err(NErr::Break(Some(e))) => Ok(e),
                                    Err(e) => Err(e),
                                }
                            }
                            None => {
                                let mut acc = Vec::new();
                                let inner = evaluate_for(env, iteratees.as_slice(), &mut |e| {
                                    acc.push(evaluate(e, body)?);
                                    Ok(())
                                });
                                let res = match inner {
                                    Ok(()) | Err(NErr::Break(None)) => Ok(Obj::list(acc)),
                                    Err(NErr::Break(Some(e))) => Ok(e),
                                    Err(e) => Err(e),
                                }?;
                                match into_res {
                                    Some(f) => call_or_part_apply(env, f, vec![res]),
                                    None => Ok(res),
                                }
                            }
                        }
                    }
                    ForBody::YieldItem(key_body, value_body) => {
                        let mut acc = HashMap::new();
                        match evaluate_for(env, iteratees.as_slice(), &mut |e| {
                            acc.insert(to_key(evaluate(e, key_body)?)?, evaluate(e, value_body)?);
                            Ok(())
                        }) {
                            Ok(()) | Err(NErr::Break(None)) => Ok(Obj::dict(acc, None)),
                            Err(NErr::Break(Some(e))) => Ok(e),
                            Err(e) => Err(e),
                        }
                    }
                },
                || "for loop".to_string(),
                expr.start,
                expr.end,
            )
        }
        Expr::While(cond, body) => {
            // FIXME :(
            loop {
                let ee = Env::with_parent(env);
                if !(add_trace(
                    evaluate(&ee, cond),
                    || "while-cond".to_string(),
                    expr.start,
                    expr.end,
                )?
                .truthy())
                {
                    return Ok(Obj::Null);
                }
                match add_trace(
                    evaluate(&ee, body),
                    || "while-body".to_string(),
                    expr.start,
                    expr.end,
                ) {
                    Ok(_) => (),
                    Err(NErr::Break(e)) => return Ok(e.unwrap_or(Obj::Null)),
                    Err(NErr::Continue) => continue,
                    Err(e) => return Err(e),
                }
            }
        }
        Expr::Switch(scrutinee, arms) => {
            let s = add_trace(
                evaluate(env, scrutinee),
                || "switchee".to_string(),
                expr.start,
                expr.end,
            )?;
            for (pat, body) in arms {
                let ee = Env::with_parent(env);
                let p = eval_lvalue(&ee, pat)?;
                // drop asap
                // TODO this clone isn't great but isn't trivial to eliminate. maybe pattern match
                // errors should return the assigned object back or something?? idk
                // TODO: only catch pattern match errors tbh
                let ret = assign(&ee, &p, Some(&ObjType::Any), s.clone());
                match ret {
                    Ok(()) => {
                        std::mem::drop(s);
                        return add_trace(
                            evaluate(&ee, body),
                            || "switch-case".to_string(),
                            expr.start,
                            expr.end,
                        );
                    }
                    Err(_) => continue,
                };
            }
            add_trace(
                Err(NErr::value_error(format!(
                    "no case matched switch scrutinee: {}",
                    s
                ))),
                || "switch".to_string(),
                expr.start,
                expr.end,
            )
        }
        Expr::Try(body, pat, catcher) => {
            match evaluate(env, body) {
                x @ (Ok(_) | Err(NErr::Break(_) | NErr::Continue | NErr::Return(_))) => x,
                Err(NErr::Throw(e, trace)) => {
                    let ee = Env::with_parent(env);
                    let p = eval_lvalue(&ee, pat)?;
                    // drop asap
                    // TODO as above, this clone isn't great but isn't trivial to eliminate
                    let ret = assign(&ee, &p, Some(&ObjType::Any), e.clone());
                    match ret {
                        Ok(()) => {
                            std::mem::drop(e);
                            return evaluate(&ee, catcher);
                        }
                        Err(_) => Err(NErr::Throw(e, trace)),
                    }
                }
            }
        }
        Expr::Throw(body) => Err(NErr::Throw(
            evaluate(&env, body)?,
            vec![("throw".to_string(), expr.start, expr.end, None)],
        )),
        Expr::Lambda(params, body) => Ok(Obj::Func(
            Func::Closure(Closure {
                params: Rc::clone(params),
                body: Rc::clone(body),
                env: Rc::clone(env),
            }),
            Precedence::zero(),
        )),
        Expr::Backref(i) => {
            try_borrow_nres(env, "backref", &format!("{}", i))?.mut_top_env(|top| {
                match if *i == 0 {
                    top.backrefs.last()
                } else {
                    top.backrefs.get(i - 1)
                } {
                    Some(x) => Ok(x.clone()),
                    None => Err(NErr::index_error("no such backref".to_string())),
                }
            })
        }
        Expr::Struct(name, field_names) => {
            let s = Struct::new(field_names.len(), name.clone());
            assign(
                &env,
                &EvaluatedLvalue::IndexedIdent((&**name).clone(), Vec::new()),
                Some(&ObjType::Func),
                Obj::Func(Func::Type(ObjType::Struct(s.clone())), Precedence::zero()),
            )?;
            for (i, field) in field_names.iter().enumerate() {
                assign(
                    &env,
                    &EvaluatedLvalue::IndexedIdent((&**field).clone(), Vec::new()),
                    Some(&ObjType::Func),
                    Obj::Func(Func::StructField(s.clone(), i), Precedence::zero()),
                )?;
            }
            Ok(Obj::Null)
        }
        Expr::Freeze(expr) => {
            let mut frenv = FreezeEnv {
                bound: HashSet::new(),
                env: Rc::clone(env),
                warn: false,
            };
            evaluate(env, &freeze(&mut frenv, expr)?)
        }
        Expr::Import(arg) => {
            // l m a o
            // we'd really like to try importing relative to the current file's path. but then for that to
            // be sensible we probably need to nest envs so whe we import a file we stick its path in its
            // env. so either the imported file has to explicitly export stuff outside, or the import
            // statement has to pull things out. might procrastinate after christmas... FIXME
            add_trace(
                match evaluate(&env, arg)? {
                    // FIXME refactor out with freeze
                    Obj::Seq(Seq::String(f)) => match fs::read_to_string(&*f) {
                        Ok(c) => match match parse(&c) {
                            Ok(Some(code)) => evaluate(env, &code),
                            Ok(None) => Err(NErr::value_error("empty file".to_string())),
                            Err(s) => {
                                Err(NErr::value_error(format!("lex failed: {}", s.render(&c))))
                            }
                        } {
                            Ok(x) => Ok(x),
                            Err(mut e) => {
                                e.supply_source(f.clone(), Rc::new(c));
                                Err(e)
                            }
                        },
                        Err(e) => Err(NErr::io_error(format!("failed: {}", e))),
                    },
                    a => Err(NErr::type_error(format!("can't import: {}", a))),
                },
                || "import".to_string(),
                expr.start,
                expr.end,
            )
        }
        Expr::Literally(_) => Err(NErr::syntax_error_loc(
            "'literally' can only be in lvalues / patterns".to_string(),
            "literally".to_string(),
            expr.start,
            expr.end,
        )),
        Expr::Break(Some(e)) => Err(NErr::Break(Some(evaluate(env, e)?))),
        Expr::Break(None) => Err(NErr::Break(None)),
        Expr::Continue => Err(NErr::Continue),
        Expr::Return(Some(e)) => Err(NErr::Return(evaluate(env, e)?)),
        Expr::Return(None) => Err(NErr::Return(Obj::Null)),
    }
}

impl Closure {
    fn run(&self, args: Vec<Obj>) -> NRes<Obj> {
        let ee = Env::with_parent(&self.env);
        let p = self
            .params
            .iter()
            .map(|e| Ok(Box::new(eval_lvalue(&ee, e)?)))
            .collect::<NRes<Vec<Box<EvaluatedLvalue>>>>()?;
        add_trace(
            assign_all(
                &ee,
                &p,
                Some(&ObjType::Any),
                args.len(),
                || Ok(args),
                "Wrong number of arguments",
            ),
            || "argument receiving".to_string(),
            self.body.start,
            self.body.end,
        )?;
        match evaluate(&ee, &self.body) {
            Err(NErr::Return(k)) => Ok(k),
            x => add_trace(
                x,
                || "closure call".to_string(),
                self.body.start,
                self.body.end,
            ),
        }
    }
}

pub fn soft_from_utf8(bs: Vec<u8>) -> Obj {
    match String::from_utf8(bs) {
        Ok(s) => Obj::from(s),
        Err(e) => Obj::Seq(Seq::Bytes(Rc::new(e.into_bytes()))),
    }
}

// caller has done as_bytes and any pythonic index calculations
// weird semantics but fine I guess
pub fn weird_string_as_bytes_index(s: &[u8], i: usize) -> Obj {
    soft_from_utf8(s[i..i + 1].to_vec())
}

pub fn slice_seq(xr: Seq, lo: Option<Obj>, hi: Option<Obj>) -> NRes<Obj> {
    match (&xr, lo, hi) {
        (Seq::List(xx), lo, hi) => {
            let (lo, hi) = pythonic_slice_obj(xx, lo.as_ref(), hi.as_ref())?;
            Ok(Obj::list(xx[lo..hi].to_vec()))
        }
        (Seq::String(s), lo, hi) => {
            let bs = s.as_bytes();
            let (lo, hi) = pythonic_slice_obj(bs, lo.as_ref(), hi.as_ref())?;
            Ok(soft_from_utf8(bs[lo..hi].to_vec()))
        }
        (Seq::Vector(s), lo, hi) => {
            let (lo, hi) = pythonic_slice_obj(s, lo.as_ref(), hi.as_ref())?;
            Ok(Obj::Seq(Seq::Vector(Rc::new(s[lo..hi].to_vec()))))
        }
        (Seq::Bytes(s), lo, hi) => {
            let (lo, hi) = pythonic_slice_obj(s, lo.as_ref(), hi.as_ref())?;
            Ok(Obj::Seq(Seq::Bytes(Rc::new(s[lo..hi].to_vec()))))
        }
        (Seq::Stream(s), lo, hi) => {
            let lo = obj_to_isize_slice_index(lo.as_ref())?;
            let hi = obj_to_isize_slice_index(hi.as_ref())?;
            Ok(Obj::Seq(s.pythonic_slice(lo, hi)?))
        }
        (Seq::Dict(..), _, _) => Err(NErr::type_error("can't slice dictionary".to_string())),
    }
}

pub fn slice(xr: Obj, lo: Option<Obj>, hi: Option<Obj>) -> NRes<Obj> {
    match xr {
        Obj::Seq(s) => slice_seq(s, lo, hi),
        xr => Err(NErr::type_error(format!(
            "can't slice {} {:?} {:?}",
            FmtObj::debug(&xr),
            lo,
            hi
        ))),
    }
}

pub fn index(xr: Obj, ir: Obj) -> NRes<Obj> {
    match (&xr, ir) {
        (Obj::Seq(s), ii) => match s {
            Seq::List(xx) => Ok(xx[pythonic_index(xx, &ii)?].clone()),
            Seq::String(s) => {
                let bs = s.as_bytes();
                let i = pythonic_index(bs, &ii)?;
                Ok(weird_string_as_bytes_index(bs, i))
            }
            Seq::Dict(xx, def) => {
                let k = to_key(ii)?;
                match xx.get(&k) {
                    Some(e) => Ok(e.clone()),
                    None => match def {
                        Some(d) => Ok((&**d).clone()),
                        None => Err(NErr::key_error(format!(
                            "Dictionary lookup: nothing at key {}[{}]",
                            FmtDictPairs(xx.iter(), &MyFmtFlags::budgeted_repr(6)),
                            k
                        ))),
                    },
                }
            }
            Seq::Vector(v) => Ok(Obj::Num(v[pythonic_index(v, &ii)?].clone())),
            Seq::Bytes(v) => Ok(Obj::from(v[pythonic_index(v, &ii)?] as usize)),
            Seq::Stream(v) => match ii {
                Obj::Num(ii) => match ii.to_isize() {
                    Some(n) => v.pythonic_index_isize(n),
                    _ => Err(NErr::index_error(format!(
                        "Index out of bounds of isize or non-integer: {:?}",
                        ii
                    ))),
                },
                _ => Err(NErr::index_error(format!(
                    "Invalid (non-numeric) index: {}",
                    FmtObj::debug(&ii)
                ))),
            },
        },
        (Obj::Func(_, Precedence(p, _)), Obj::Seq(Seq::String(k))) => match &**k {
            "precedence" => Ok(Obj::from(*p as f64)),
            _ => Err(NErr::type_error(format!("can't index into func {:?}", k))),
        },
        (Obj::Instance(struc, fields), Obj::Func(Func::StructField(istruc, field_index), _)) => {
            if struc == &istruc {
                Ok(fields[field_index].clone())
            } else {
                Err(NErr::index_error(format!("wrong struct type",)))
            }
        }
        (xr, ir) => Err(NErr::type_error(format!(
            "can't index {}[{}]",
            FmtObj::debug(&xr),
            FmtObj::debug(&ir)
        ))),
    }
}

pub fn index_or_slice(xr: Obj, ir: &EvaluatedIndexOrSlice) -> NRes<Obj> {
    match ir {
        // FIXME can or should we push these clones down
        EvaluatedIndexOrSlice::Index(i) => index(xr, i.clone()),
        EvaluatedIndexOrSlice::Slice(i, j) => slice(xr, i.clone(), j.clone()),
    }
}

pub fn apply_section(
    sec_args: Vec<Result<Obj, bool>>,
    mut arg_iter: impl Iterator<Item = Obj>,
) -> NRes<Vec<Obj>> {
    let mut out = Vec::new();
    for s in sec_args {
        match s {
            Ok(e) => out.push(e),
            Err(is_splat) => match arg_iter.next() {
                Some(mut a) => {
                    if is_splat {
                        for o in mut_obj_into_iter(&mut a, "section splat")? {
                            out.push(o?)
                        }
                    } else {
                        out.push(a)
                    }
                }
                None => Err(NErr::argument_error(
                    "section: too many arguments".to_string(),
                ))?,
            },
        }
    }
    Ok(out)
}

pub fn eval_lvalue_as_obj(env: &REnv, expr: &EvaluatedLvalue) -> NRes<Obj> {
    match expr {
        EvaluatedLvalue::Underscore => Err(NErr::syntax_error(
            "Can't evaluate underscore on LHS of assignment??".to_string(),
        )),
        EvaluatedLvalue::IndexedIdent(s, v) => {
            let mut sr = Env::try_borrow_get_var(env, s)?;
            for ix in v {
                sr = index_or_slice(sr, ix)?.clone();
            }
            Ok(sr)
        }
        EvaluatedLvalue::Annotation(s, _) => eval_lvalue_as_obj(env, s),
        EvaluatedLvalue::CommaSeq(v) => Ok(Obj::list(
            v.iter()
                .map(|e| Ok(eval_lvalue_as_obj(env, e)?))
                .collect::<NRes<Vec<Obj>>>()?,
        )),
        // maybe if commaseq eagerly looks for splats...
        EvaluatedLvalue::Splat(_) => Err(NErr::syntax_error(
            "Can't evaluate splat on LHS of assignment??".to_string(),
        )),
        EvaluatedLvalue::Or(..) => Err(NErr::syntax_error(
            "Can't evaluate or on LHS of assignment??".to_string(),
        )),
        // seems questionable
        EvaluatedLvalue::Literal(x) => Ok(x.clone()),
        // very cursed, but there's only one reasonable definition
        EvaluatedLvalue::Destructure(f, vs) => f.run(
            env,
            vs.iter()
                .map(|v| eval_lvalue_as_obj(env, v))
                .collect::<NRes<Vec<Obj>>>()?,
        ),
        EvaluatedLvalue::DestructureStruct(s, vs) => {
            let v: Vec<Obj> = vs
                .iter()
                .map(|v| eval_lvalue_as_obj(env, v))
                .collect::<NRes<Vec<Obj>>>()?;
            if v.len() == s.size {
                Ok(Obj::Instance(s.clone(), v))
            } else {
                Err(NErr::argument_error(format!(
                    "struct construction: wrong number of arguments: {}, wanted {}",
                    v.len(),
                    s.size
                )))
            }
        }
    }
}

pub fn call(env: &REnv, f: Obj, args: Vec<Obj>) -> NRes<Obj> {
    match f {
        Obj::Func(ff, _) => ff.run(env, args),
        _ => Err(NErr::type_error(format!(
            "Can't call non-function {}",
            FmtObj::debug(&f)
        ))),
    }
}

pub fn call_or_part_apply(env: &REnv, f: Obj, args: Vec<Obj>) -> NRes<Obj> {
    match f {
        Obj::Func(ff, _) => ff.run(env, args),
        f => match few(args) {
            Few::One(Obj::Func(f2, _)) => Ok(Obj::Func(
                Func::PartialApp1(Box::new(f2), Box::new(f)),
                Precedence::zero(),
            )),
            Few::One(f2) => Err(NErr::type_error(format!(
                "Can't call non-function {} (and argument {} not callable)",
                FmtObj::debug(&f),
                FmtObj::debug(&f2)
            ))),
            _ => Err(NErr::type_error(format!(
                "Can't call non-function {} (and more than one argument)",
                FmtObj::debug(&f)
            ))),
        },
    }
}

// the ObjType is provided iff it's a declaration
pub fn assign_all_basic(
    env: &REnv,
    lhs: &[Box<EvaluatedLvalue>],
    rt: Option<&ObjType>,
    rhs: Vec<Obj>,
    err_msg: &str,
) -> NRes<()> {
    if lhs.len() == rhs.len() {
        for (lhs1, rhs1) in lhs.iter().zip(rhs.into_iter()) {
            assign(env, lhs1, rt, rhs1)?;
        }
        Ok(())
    } else {
        Err(NErr::value_error(format!(
            "{}: expected {} ({}), got {} ({})",
            err_msg,
            lhs.len(),
            CommaSeparated(lhs),
            rhs.len(),
            CommaSeparatedDebug(&rhs)
        )))
    }
}

// Delay computing the rhs if possible because it might be a big vector for which cloning is
// expensive and our pattern might blatantly not match (this is pretty ad hoc lol)
pub fn assign_all(
    env: &REnv,
    lhs: &[Box<EvaluatedLvalue>],
    rt: Option<&ObjType>,
    rhs_len: usize,
    lazy_rhs: impl FnOnce() -> NRes<Vec<Obj>>,
    err_msg: &str,
) -> NRes<()> {
    let mut splat = None;
    for (i, lhs1) in lhs.iter().enumerate() {
        match &**lhs1 {
            EvaluatedLvalue::Splat(inner) => match splat {
                Some(_) => {
                    return Err(NErr::syntax_error(format!(
                        "Can't have two splats in same sequence on left-hand side of assignment"
                    )))
                }
                None => {
                    splat = Some((i, Ok(inner)));
                }
            },
            // FIXME? probably another consequence of forcing annotations into CommaSeq
            EvaluatedLvalue::Annotation(mid, anno) => match &**mid {
                EvaluatedLvalue::Splat(inner) => match splat {
                    Some(_) => {
                        return Err(NErr::syntax_error(format!(
                            "Can't have two splats in same sequence on left-hand side of assignment"
                        )))
                    }
                    None => {
                        splat = Some((i, Err((inner, anno))));
                    }
                },
                _ => {}
            },
            _ => {}
        }
    }
    match splat {
        Some((si, inner)) => {
            // mmm we could compare against rhs len eagerly to not call it, but the bad cases don't
            // involve a splat
            let mut rhs = lazy_rhs()?;
            let rrhs = rhs.drain(rhs.len() - lhs.len() + si + 1..).collect();
            let srhs = rhs.drain(si..).collect();
            assign_all_basic(env, &lhs[..si], rt, rhs, err_msg)?;
            match inner {
                Ok(inner) => assign(env, inner, rt, Obj::list(srhs))?,
                Err((inner, anno)) => {
                    let t = match anno {
                        None => Some(ObjType::Any),
                        Some(t) => Some(to_type(t, "splat anno")?),
                    };
                    assign(env, inner, t.as_ref(), Obj::list(srhs))?
                }
            };
            assign_all_basic(env, &lhs[si + 1..], rt, rrhs, err_msg)
        }
        None => {
            if lhs.len() == rhs_len {
                assign_all_basic(env, lhs, rt, lazy_rhs()?, err_msg)
            } else if rhs_len <= 8 {
                Err(NErr::value_error(format!(
                    "{}: expected {} ({}), got {} ({})",
                    err_msg,
                    lhs.len(),
                    CommaSeparated(lhs),
                    rhs_len,
                    CommaSeparatedDebug(&lazy_rhs()?)
                )))
            } else {
                Err(NErr::value_error(format!(
                    "{}: expected {} ({}), got {}",
                    err_msg,
                    lhs.len(),
                    CommaSeparated(lhs),
                    rhs_len
                )))
            }
        }
    }
}

// Modifying parts of a &mut Obj
// =============================

pub fn set_index(
    lhs: &mut Obj,
    indexes: &[EvaluatedIndexOrSlice],
    value: Option<Obj>, // None for LHS-dropping. In homogeneous seq, OK to nop
    every: bool,
) -> NRes<()> {
    // hack
    match (&*lhs, indexes) {
        (Obj::Seq(Seq::Stream(m)), [_, ..]) => {
            let mm = m.clone_box();
            *lhs = Obj::list(mm.force()?)
        }
        _ => {}
    }
    match (lhs, indexes) {
        (lhs, []) => {
            *lhs = value.unwrap_or(Obj::Null);
            Ok(())
        }
        (Obj::Seq(s), [fi, rest @ ..]) => match (s, fi) {
            (Seq::List(v), EvaluatedIndexOrSlice::Index(i)) => {
                set_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, value, every)
            }
            (Seq::List(v), EvaluatedIndexOrSlice::Slice(i, j)) => {
                if every {
                    let v = Rc::make_mut(v);
                    let (lo, hi) = pythonic_slice_obj(v, i.as_ref(), j.as_ref())?;
                    for i in lo..hi {
                        set_index(&mut v[i], rest, value.clone(), true)?;
                    }
                    Ok(())
                } else {
                    todo!("assgn to slice")
                    // set_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, value)
                }
            }
            (Seq::String(s), EvaluatedIndexOrSlice::Index(i)) if rest.is_empty() => match value {
                Some(Obj::Seq(Seq::String(v))) => {
                    let mut_s = Rc::make_mut(s);
                    if v.as_bytes().len() == 1 {
                        // FIXME lmao
                        let mut owned = std::mem::take(mut_s).into_bytes();
                        let i = match pythonic_index(&owned, i) {
                            Ok(i) => i,
                            Err(e) => {
                                // put it baaaack!!
                                *mut_s = String::from_utf8(owned).unwrap();
                                return Err(e);
                            }
                        };
                        owned[i..i + 1].copy_from_slice(v.as_bytes());
                        match String::from_utf8(owned) {
                            Ok(r) => {
                                *mut_s = r;
                                Ok(())
                            }
                            Err(err) => {
                                *mut_s = String::from_utf8_lossy(err.as_bytes()).into_owned();
                                Err(NErr::value_error(format!(
                                    "assigning to string result not utf-8 (string corrupted)"
                                )))
                            }
                        }
                    } else {
                        Err(NErr::value_error(format!(
                            "assigning to string index, not a byte"
                        )))
                    }
                }
                Some(_) => Err(NErr::value_error(format!(
                    "assigning to string index, not a string"
                ))),
                None => Ok(()),
            },
            (Seq::String(_), _) => Err(NErr::type_error(format!("string bad slice"))),
            (Seq::Dict(v, _), EvaluatedIndexOrSlice::Index(kk)) => {
                let k = to_key(kk.clone())?;
                let mut_d = Rc::make_mut(v);
                // We might create a new map entry, but only at the end, which is a bit of a
                // mismatch for Rust's map API if we want to recurse all the way
                if rest.is_empty() {
                    mut_d.insert(k, value.unwrap_or(Obj::Null));
                    Ok(())
                } else {
                    set_index(
                        match mut_d.get_mut(&k) {
                            Some(vvv) => vvv,
                            None => Err(NErr::type_error(format!(
                                "setting dictionary: nothing at key {}[{}]",
                                FmtDictPairs(mut_d.iter(), &DEBUG_FMT),
                                k
                            )))?,
                        },
                        rest,
                        value,
                        every,
                    )
                }
            }
            (Seq::Dict(v, _), EvaluatedIndexOrSlice::Slice(None, None)) if rest.is_empty() => {
                let mut_d = Rc::make_mut(v);
                if every {
                    for (_, vv) in mut_d.iter_mut() {
                        set_index(vv, rest, value.clone(), true)?;
                    }
                    Ok(())
                } else {
                    Err(NErr::type_error(format!(
                        "can't slice dictionaries except with every"
                    )))
                }
            }
            (Seq::Dict(..), _) => Err(NErr::type_error(format!("dict bad slice"))),
            (Seq::Vector(v), EvaluatedIndexOrSlice::Index(i)) if rest.is_empty() => match value {
                Some(Obj::Num(n)) => {
                    let i = pythonic_index(v, i)?;
                    Rc::make_mut(v)[i] = n;
                    Ok(())
                }
                Some(e) => Err(NErr::type_error(format!(
                    "vec bad value assign: {}",
                    FmtObj::debug(&e)
                ))),
                None => Ok(()),
            },
            (Seq::Vector(_), _) => Err(NErr::type_error(format!("vec bad slice / not impl"))),
            (Seq::Bytes(v), EvaluatedIndexOrSlice::Index(i)) if rest.is_empty() => match value {
                Some(Obj::Num(ref n)) => {
                    let i = pythonic_index(v, i)?;
                    Rc::make_mut(v)[i] = n
                        .to_u8()
                        .ok_or(NErr::value_error(format!("can't to byte: {}", n)))?;
                    Ok(())
                }
                Some(e) => Err(NErr::type_error(format!(
                    "bytes bad value assign: {}",
                    FmtObj::debug(&e)
                ))),
                None => Ok(()),
            },
            (Seq::Bytes(_), _) => Err(NErr::type_error(format!("vec bad slice / not impl"))),
            (Seq::Stream(_), _) => panic!("stream handled above"),
        },
        (
            Obj::Func(_, Precedence(p, _)),
            [EvaluatedIndexOrSlice::Index(Obj::Seq(Seq::String(r)))],
        ) => match &***r {
            "precedence" => match value {
                Some(Obj::Num(f)) => match f.to_f64() {
                    Some(f) => {
                        *p = f;
                        Ok(())
                    }
                    None => Err(NErr::value_error(format!(
                        "precedence must be convertible to float: {}",
                        f
                    ))),
                },
                Some(f) => Err(NErr::type_error(format!(
                    "precedence must be number, got {}",
                    f
                ))),
                None => Ok(()),
            },
            k => Err(NErr::key_error(format!(
                "function key must be 'precedence', got {}",
                k
            ))),
        },
        (
            Obj::Instance(struc, fields),
            [EvaluatedIndexOrSlice::Index(Obj::Func(Func::StructField(istruc, field_index), _)), rest @ ..],
        ) => {
            if struc == istruc {
                set_index(&mut fields[*field_index], rest, value, every)
            } else {
                Err(NErr::index_error(format!("wrong struct type",)))
            }
        }
        (lhs, ii) => Err(NErr::index_error(format!(
            "can't set index {:?} {:?}",
            lhs, ii
        ))),
    }
}

// be careful not to call this with both lhs holding a mutable reference into a RefCell and rhs
// trying to take such a reference!
pub fn modify_existing_index(
    lhs: &mut Obj,
    indexes: &[EvaluatedIndexOrSlice],
    f: impl FnOnce(&mut Obj) -> NRes<Obj>,
) -> NRes<Obj> {
    // hack
    match (&*lhs, indexes) {
        (Obj::Seq(Seq::Stream(m)), [_, ..]) => {
            let mm = m.clone_box();
            *lhs = Obj::list(mm.force()?)
        }
        _ => {}
    }
    match indexes.split_first() {
        None => f(lhs),
        Some((i, rest)) => {
            match (lhs, i) {
                (Obj::Seq(Seq::List(v)), EvaluatedIndexOrSlice::Index(i)) => {
                    modify_existing_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, f)
                }
                (Obj::Seq(Seq::Dict(v, def)), EvaluatedIndexOrSlice::Index(kk)) => {
                    let k = to_key(kk.clone())?;
                    let mut_d = Rc::make_mut(v);
                    match mut_d.entry(k) {
                        std::collections::hash_map::Entry::Occupied(mut e) => {
                            modify_existing_index(e.get_mut(), rest, f)
                        }
                        std::collections::hash_map::Entry::Vacant(e) => match def {
                            Some(d) => modify_existing_index(e.insert((&**d).clone()), rest, f),
                            None => {
                                return Err(NErr::key_error(format!(
                                    "nothing at key {}[{}]",
                                    FmtDictPairs(mut_d.iter(), &DEBUG_FMT),
                                    kk
                                )))
                            }
                        },
                    }
                }
                (
                    Obj::Instance(struc, fields),
                    EvaluatedIndexOrSlice::Index(Obj::Func(
                        Func::StructField(istruc, field_index),
                        _,
                    )),
                ) => {
                    if struc == istruc {
                        modify_existing_index(&mut fields[*field_index], rest, f)
                    } else {
                        Err(NErr::index_error(format!("wrong struct type",)))
                    }
                }
                // TODO everything
                (lhs2, ii) => Err(NErr::type_error(format!(
                    "can't modify index {:?} {:?}",
                    lhs2, ii
                ))),
            }
        }
    }
}

// same here...
pub fn modify_every_existing_index(
    lhs: &mut Obj,
    indexes: &[EvaluatedIndexOrSlice],
    f: &mut impl FnMut(&mut Obj) -> NRes<()>,
) -> NRes<()> {
    // hack
    match (&*lhs, indexes) {
        (Obj::Seq(Seq::Stream(m)), [_, ..]) => {
            let mm = m.clone_box();
            *lhs = Obj::list(mm.force()?)
        }
        _ => {}
    }
    match indexes.split_first() {
        None => f(lhs),
        Some((i, rest)) => {
            match (lhs, i) {
                (Obj::Seq(Seq::List(v)), EvaluatedIndexOrSlice::Index(i)) => {
                    modify_every_existing_index(pythonic_mut(&mut Rc::make_mut(v), i)?, rest, f)
                }
                (Obj::Seq(Seq::List(v)), EvaluatedIndexOrSlice::Slice(lo, hi)) => {
                    let (lo, hi) = pythonic_slice_obj(v, lo.as_ref(), hi.as_ref())?;
                    for m in &mut Rc::make_mut(v)[lo..hi] {
                        modify_every_existing_index(m, rest, f)?;
                    }
                    Ok(())
                }
                (Obj::Seq(Seq::Dict(v, def)), EvaluatedIndexOrSlice::Index(kk)) => {
                    let k = to_key(kk.clone())?;
                    let mut_d = Rc::make_mut(v);
                    match mut_d.entry(k) {
                        std::collections::hash_map::Entry::Occupied(mut e) => {
                            modify_every_existing_index(e.get_mut(), rest, f)
                        }
                        std::collections::hash_map::Entry::Vacant(e) => match def {
                            Some(d) => {
                                modify_every_existing_index(e.insert((&**d).clone()), rest, f)
                            }
                            None => {
                                return Err(NErr::key_error(format!(
                                    "nothing at key {}[{}]",
                                    FmtDictPairs(mut_d.iter(), &DEBUG_FMT),
                                    kk
                                )))
                            }
                        },
                    }
                }
                (
                    Obj::Instance(struc, fields),
                    EvaluatedIndexOrSlice::Index(Obj::Func(
                        Func::StructField(istruc, field_index),
                        _,
                    )),
                ) => {
                    if struc == istruc {
                        modify_every_existing_index(&mut fields[*field_index], rest, f)
                    } else {
                        Err(NErr::index_error(format!("wrong struct type",)))
                    }
                }
                // TODO everything
                (lhs2, ii) => Err(NErr::type_error(format!(
                    "can't modify every index {:?} {:?}",
                    lhs2, ii
                ))),
            }
        }
    }
}

pub fn insert_declare(env: &REnv, s: &str, ty: ObjType, rhs: Obj) -> NRes<()> {
    if !is_type(&ty, &rhs) {
        Err(NErr::name_error(format!(
            "Declaring, type mismatch: {} is not of type {}",
            rhs,
            ty.name()
        )))
    } else {
        try_borrow_mut_nres(env, "variable declaration", s)?.insert(s.to_string(), ty, rhs)
    }
}

pub fn assign_respecting_type(
    env: &REnv,
    s: &str,
    ixs: &[EvaluatedIndexOrSlice],
    rhs: Obj,
    every: bool,
) -> NRes<()> {
    try_borrow_nres(env, "env for assigning", s)?.modify_existing_var(s, |(ty, v)| {
        // Eagerly check type only if ixs is empty, otherwise we can't really do
        // that (at least not in full generality)
        // FIXME is there possibly a double borrow here? maybe not because we only use immutable
        // borrows, so we'd only conflict with mutable borrows, and the type couldn't have been
        // constructed to mutably borrow the variable it's for?
        if ixs.is_empty() && !is_type(ty, &rhs) {
            Err(NErr::type_error(format!("Assignment to {} type check failed: {} not {}", s, FmtObj::debug(&rhs), ty.name())))?
        }
        set_index(&mut *try_borrow_mut_nres(v, "var for assigning", s)?, ixs, Some(rhs), every)?;
        // Check type after the fact. TODO if we ever do subscripted types: this
        // will be super inefficient lmao, we can be smart tho
        if !ixs.is_empty() && !is_type(ty, &*try_borrow_nres(v, "assignment late type check", s)?) {
            Err(NErr::type_error(format!("Assignment to {} LATE type check failed (the assignment still happened): not {}", s, ty.name())))
        } else {
            Ok(())
        }
    }).ok_or_else(|| NErr::name_error(if ixs.is_empty() {
         format!("Variable {:?} not found (use := to declare)", s)
    } else {
         format!("Variable {:?} not found, couldn't set into index {:?}", s, ixs)
    }))?
}

pub fn assign(env: &REnv, lhs: &EvaluatedLvalue, rt: Option<&ObjType>, rhs: Obj) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::Underscore => {
            match rt {
                Some(ty) => {
                    if !is_type(&ty, &rhs) {
                        return Err(NErr::type_error(format!(
                            "Assigning to underscore type mismatch: {} is not of type {}",
                            rhs,
                            ty.name()
                        )));
                    }
                }
                None => (),
            }
            Ok(())
        }
        EvaluatedLvalue::IndexedIdent(s, ixs) => match rt {
            Some(ty) => {
                // declaration
                if ixs.is_empty() {
                    insert_declare(env, s, ty.clone(), rhs.clone())
                } else {
                    return Err(NErr::name_error(format!(
                        "Can't declare new value into index expression: {:?} {:?}",
                        s, ixs
                    )));
                }
            }
            None => assign_respecting_type(env, s, ixs, rhs, /* every */ false),
        },
        EvaluatedLvalue::CommaSeq(ss) => match rhs {
            Obj::Seq(Seq::List(ls)) => assign_all(
                env,
                ss,
                rt,
                ls.len(),
                || Ok(unwrap_or_clone(ls)),
                "Can't unpack into mismatched length",
            ),
            Obj::Seq(seq) => match seq.len() {
                Some(len) => assign_all(
                    env,
                    ss,
                    rt,
                    len,
                    || seq_to_cloning_iter(&seq).collect::<NRes<Vec<Obj>>>(),
                    "Can't unpack into mismatched length",
                ),
                None => Err(NErr::type_error(
                    "Can't unpack from infinite sequence".to_string(),
                )),
            },
            _ => Err(NErr::type_error(
                "Unpacking failed: not iterable".to_string(),
            )),
        },
        EvaluatedLvalue::Annotation(s, ann) => match ann {
            None => assign(env, s, Some(&ObjType::Any), rhs),
            Some(t) => assign(env, s, Some(&to_type(t, "annotation")?), rhs),
        },
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!(
            "Can't assign to raw splat {:?}",
            lhs
        ))),
        EvaluatedLvalue::Or(a, b) => match assign(env, a, rt, rhs.clone()) {
            Ok(()) => Ok(()),
            Err(_) => assign(env, b, rt, rhs),
        },
        EvaluatedLvalue::Literal(obj) => {
            if obj == &rhs {
                Ok(())
            } else {
                Err(NErr::type_error(format!(
                    "Literal pattern didn't match: {} {}",
                    FmtObj::debug(obj),
                    FmtObj::debug(&rhs)
                )))
            }
        }
        EvaluatedLvalue::Destructure(f, args) => {
            let known = args
                .iter()
                .map(|e| match &**e {
                    EvaluatedLvalue::Literal(obj) => Some(obj.clone()),
                    _ => None,
                })
                .collect::<Vec<Option<Obj>>>();
            let res = f.destructure(rhs.clone(), known)?;
            if res.len() == args.len() {
                assign_all(
                    env,
                    args,
                    rt,
                    res.len(),
                    || Ok(res),
                    "Can't destructure into mismatched length",
                )
            } else {
                Err(NErr::type_error(format!(
                    "{} destructure length didn't match: {:?} {:?}",
                    f.builtin_name(),
                    res,
                    args
                )))
            }
        }
        EvaluatedLvalue::DestructureStruct(s, args) => match rhs {
            Obj::Instance(s2, vs) if s.id == s2.id => assign_all(
                env,
                args,
                rt,
                vs.len(),
                || Ok(vs),
                "(Shouldn't be possible) Can't destructure into mismatched length struct",
            ),
            _ => Err(NErr::type_error(
                "Destructuring structure failed: not type".to_string(),
            )),
        },
    }
}

pub fn drop_lhs_all(env: &REnv, lhs: &[Box<EvaluatedLvalue>]) -> NRes<()> {
    for lhs1 in lhs.iter() {
        match &**lhs1 {
            EvaluatedLvalue::Splat(inner) => drop_lhs(env, inner)?,
            lhs1 => drop_lhs(env, lhs1)?,
        }
    }
    Ok(())
}

pub fn drop_lhs(env: &REnv, lhs: &EvaluatedLvalue) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::Underscore => Ok(()),
        EvaluatedLvalue::IndexedIdent(s, ixs) => try_borrow_nres(env, "env for dropping lhs", s)?
            .modify_existing_var(s, |(_ty, v)| {
                // overriding type!!
                set_index(
                    &mut *try_borrow_mut_nres(v, "var for dropping lhs", s)?,
                    ixs,
                    None,
                    true,
                )?;
                Ok(())
            })
            .ok_or_else(|| {
                NErr::name_error(if ixs.is_empty() {
                    format!("Variable {:?} not found (use := to declare)", s)
                } else {
                    format!(
                        "Variable {:?} not found, couldn't set into index {:?}",
                        s, ixs
                    )
                })
            })?,
        EvaluatedLvalue::CommaSeq(ss) => drop_lhs_all(env, ss),
        EvaluatedLvalue::Annotation(..) => Err(NErr::syntax_error(
            "can't drop LHS with annotations in it for op-assign??".to_string(),
        )),
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!(
            "Can't assign to raw splat {:?}",
            lhs
        ))),
        EvaluatedLvalue::Or(..) => Err(NErr::syntax_error(
            "can't drop LHS with or for op-assign??".to_string(),
        )),
        EvaluatedLvalue::Literal(_) => Ok(()), // assigning to it probably will fail later...
        EvaluatedLvalue::Destructure(_, vs) => drop_lhs_all(env, vs),
        EvaluatedLvalue::DestructureStruct(_, vs) => drop_lhs_all(env, vs),
    }
}

pub fn assign_every(env: &REnv, lhs: &EvaluatedLvalue, rt: Option<&ObjType>, rhs: Obj) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::Underscore => Ok(()),
        EvaluatedLvalue::IndexedIdent(s, ixs) => match rt {
            Some(ty) => {
                // declaration
                if ixs.is_empty() {
                    insert_declare(env, s, ty.clone(), rhs.clone())
                } else {
                    Err(NErr::name_error(format!(
                        "Can't declare new value into index expression: {:?} {:?}",
                        s, ixs
                    )))
                }
            }
            None => assign_respecting_type(env, s, ixs, rhs, /* every */ true),
        },
        EvaluatedLvalue::CommaSeq(ss) => {
            for v in ss {
                assign_every(env, v, rt, rhs.clone())?;
            }
            Ok(())
        }
        EvaluatedLvalue::Annotation(s, ann) => match ann {
            None => assign_every(env, s, Some(&ObjType::Any), rhs),
            Some(t) => assign_every(env, s, Some(&to_type(t, "annotation")?), rhs),
        },
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!(
            "Can't assign-every to raw splat {:?}",
            lhs
        ))),
        EvaluatedLvalue::Or(..) => Err(NErr::type_error(format!(
            "Can't assign-every to or {:?}",
            lhs
        ))),
        EvaluatedLvalue::Literal(obj) => {
            if obj == &rhs {
                Ok(())
            } else {
                Err(NErr::type_error(format!(
                    "Literal pattern didn't match: {} {}",
                    obj, rhs
                )))
            }
        }
        EvaluatedLvalue::Destructure(f, args) => {
            let known = args
                .iter()
                .map(|e| match &**e {
                    EvaluatedLvalue::Literal(obj) => Some(obj.clone()),
                    _ => None,
                })
                .collect::<Vec<Option<Obj>>>();
            let res = f.destructure(rhs.clone(), known)?;
            if res.len() == args.len() {
                assign_all(
                    env,
                    args,
                    rt,
                    res.len(),
                    || Ok(res),
                    "Can't destructure into mismatched length",
                )
            } else {
                Err(NErr::type_error(format!(
                    "{} destructure length didn't match: {:?} {:?}",
                    f.builtin_name(),
                    res,
                    args
                )))
            }
        }
        EvaluatedLvalue::DestructureStruct(..) => Err(NErr::type_error(format!(
            "Can't assign-every to struct {:?}",
            lhs
        ))),
    }
}

// different: doesn't hold a mutable borrow to the environment when calling rhs; doesn't accept
// declarations
pub fn modify_every(
    env: &Rc<RefCell<Env>>,
    lhs: &EvaluatedLvalue,
    rhs: &mut impl FnMut(Obj) -> NRes<Obj>,
) -> NRes<()> {
    match lhs {
        EvaluatedLvalue::Underscore => Err(NErr::type_error(format!("Can't modify underscore"))),
        EvaluatedLvalue::IndexedIdent(s, ixs) => {
            // drop borrow immediately
            let mut old: Obj = Env::try_borrow_get_var(env, s)?;

            if ixs.is_empty() {
                let new = rhs(old)?;
                try_borrow_nres(env, "env for modify every", s)?
                    .modify_existing_var(s, |(ty, old)| {
                        // FIXME is there possibly another double borrow here?
                        if is_type(ty, &new) {
                            *try_borrow_mut_nres(old, "var for modify every", s)? = new.clone();
                            Ok(())
                        } else {
                            Err(NErr::name_error(format!(
                                "Modify every: assignment to {} type check failed: {} not {}",
                                s,
                                new,
                                ty.name()
                            )))
                        }
                    })
                    .ok_or_else(|| {
                        NErr::name_error(format!("Variable {:?} not found in modify every", s))
                    })?
            } else {
                modify_every_existing_index(&mut old, ixs, &mut |x: &mut Obj| {
                    *x = rhs(std::mem::take(x))?;
                    Ok(())
                })?;
                assign_respecting_type(env, s, &[], old, false /* every */)
            }
        }
        EvaluatedLvalue::CommaSeq(ss) => {
            for v in ss {
                modify_every(env, v, rhs)?;
            }
            Ok(())
        }
        EvaluatedLvalue::Annotation(..) => Err(NErr::type_error(format!(
            "No annotations in modify every: {:?}",
            lhs
        ))),
        EvaluatedLvalue::Splat(_) => Err(NErr::type_error(format!(
            "Can't modify raw splat {:?}",
            lhs
        ))),
        EvaluatedLvalue::Or(..) => Err(NErr::type_error(format!("Can't modify or {:?}", lhs))),
        EvaluatedLvalue::Literal(x) => Err(NErr::type_error(format!(
            "Can't modify literal {}",
            FmtObj::debug(x)
        ))),
        EvaluatedLvalue::Destructure(..) => Err(NErr::type_error(format!(
            "Can't modify destructure {:?}",
            lhs
        ))),
        EvaluatedLvalue::DestructureStruct(..) => Err(NErr::type_error(format!(
            "Can't modify destructure struct {:?}",
            lhs
        ))),
    }
}

impl Func {
    pub fn run(&self, env: &REnv, mut args: Vec<Obj>) -> NRes<Obj> {
        match self {
            Func::Builtin(b) => b.run(env, args),
            Func::Closure(c) => c.run(args),
            Func::PartialApp1(f, x) => match few(args) {
                Few::One(arg) => f.run(env, vec![(**x).clone(), arg]),
                a => Err(NErr::argument_error(format!("partially applied functions can only be called with one more argument, but {} {} got {}", f, FmtObj::debug(x), a)))
            }
            Func::PartialApp2(f, x) => match few(args) {
                Few::One(arg) => f.run(env, vec![arg, (**x).clone()]),
                a => Err(NErr::argument_error(format!("partially applied functions can only be called with one more argument, but {} {} got {}", f, FmtObj::debug(x), a)))
            }
            Func::PartialAppLast(f, x) => {
                args.push(*x.clone());
                f.run(env, args)
            }
            Func::Composition(f, g) => f.run(env, vec![g.run(env, args)?]),
            Func::OnComposition(f, g) => {
                let mut mapped_args = Vec::new();
                for e in args {
                    mapped_args.push(g.run(env, vec![e])?);
                }
                f.run(env, mapped_args)
            }
            Func::Parallel(fs) => {
                let mut res = Vec::new();
                match few(args) {
                    Few::One(Obj::Seq(mut seq)) => {
                        match seq.len() {
                            Some(n) if n == fs.len() => {
                                for (f, a) in fs.iter().zip(mut_seq_into_iter(&mut seq)) {
                                    res.push(f.run(env, vec![a?])?);
                                }
                            }
                            Some(n) => return Err(NErr::type_error(format!("Parallel argument seq has wrong length {}: {:?}", n, seq))),
                            None => return Err(NErr::type_error(format!("Parallel argument seq has infinite length?: {:?}", seq)))
                        }
                    }
                    Few::Zero => {
                        return Err(NErr::argument_error(format!("can't call Parallel with no args")))
                    }
                    Few::One(x) => {
                        return Err(NErr::type_error(format!("can't call Parallel with one non-seq {}", FmtObj::debug(&x))))
                    }
                    Few::Many(args) => {
                        for (f, a) in fs.iter().zip(args) {
                            res.push(f.run(env, vec![a])?);
                        }
                    }
                }
                Ok(Obj::list(res))
            }
            Func::Fanout(fs) => {
                let mut res = Vec::new();
                for f in fs {
                    res.push(f.run(env, args.clone())?);
                }
                Ok(Obj::list(res))
            }
            Func::Flip(f) => match few2(args) {
                // weird lol
                Few2::One(a) => Ok(Obj::Func(Func::PartialApp1(f.clone(), Box::new(a)), Precedence::zero())),
                Few2::Two(a, b) => f.run(env, vec![b, a]),
                _ => Err(NErr::argument_error("Flipped function can only be called on two arguments".to_string()))
            }
            Func::ListSection(x) => {
                Ok(Obj::list(apply_section(x.clone(), args.into_iter())?))
            }
            Func::ChainSection(seed, ops) => {
                let mut it = args.into_iter();
                let mut ce = ChainEvaluator::new(match seed {
                    Some(x) => *x.clone(),
                    None => match it.next() {
                        Some(e) => e,
                        None => return Err(NErr::argument_error("chain section: too few arguments".to_string())),
                    }
                });
                for (start, end, op, prec, opd) in ops {
                    ce.give(env, *op.clone(), *prec, match opd {
                        Some(x) => *x.clone(),
                        None => match it.next() {
                            Some(e) => e,
                            None => return Err(NErr::argument_error("chain section: too few arguments".to_string())),
                        }
                    }, *start, *end)?;
                }
                match it.next() {
                    None => ce.finish(env),
                    Some(_) => Err(NErr::argument_error("chain section: too many arguments".to_string())),
                }
            }
            Func::CallSection(callee, sec_args) => {
                let mut it = args.into_iter();
                let callee = match callee {
                    Some(x) => *x.clone(),
                    None => match it.next() {
                        Some(e) => e,
                        None => return Err(NErr::argument_error("call section: too few arguments".to_string())),
                    }
                };
                let real_args = apply_section(sec_args.clone(), it)?;
                call(env, callee, real_args)
            }
            Func::IndexSection(x, i) => {
                let mut it = args.into_iter();
                let x = match x {
                    Some(e) => (**e).clone(),
                    None => it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?,
                };
                let i = match i {
                    Some(e) => (**e).clone(),
                    None => it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?,
                };
                index(x, i)
            }
            Func::SliceSection(x, lo, hi) => {
                let mut it = args.into_iter();
                let x = match x {
                    Some(e) => (**e).clone(),
                    None => it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?,
                };
                let lo = match lo {
                    None => None,
                    Some(inner) => match &**inner {
                        None => Some(it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?),
                        Some(e) => Some((*e).clone()),
                    }
                };
                let hi = match hi {
                    None => None,
                    Some(inner) => match &**inner {
                        None => Some(it.next().ok_or(NErr::argument_error("index section: too few arguments".to_string()))?),
                        Some(e) => Some((*e).clone()),
                    }
                };
                slice(x, lo, hi)
            }
            Func::Type(t) => call_type(t, args),
            Func::StructField(struc, field_index) => match few(args) {
                Few::One(Obj::Instance(s, fields)) => {
                    if *struc == s {
                        Ok(fields[*field_index].clone())
                    } else {
                        Err(NErr::argument_error(format!("field of {} got wrong kind of struct", &*struc.name)))
                    }
                }
                f => err_add_name(Err(NErr::argument_error_few(&f)), &format!("field of {}", &*struc.name))
            }
            Func::Memoized(f, memo) => {
                let kargs = args.into_iter().map(to_key).collect::<NRes<Vec<ObjKey>>>()?;
                match memo.try_borrow() {
                    Ok(memo) => match memo.get(&kargs) {
                        Some(res) => return Ok(res.clone()),
                        None => {}
                    }
                    Err(e) => Err(NErr::io_error(format!("memo: borrow failed: {}", e)))?
                };
                let res = f.run(env, kargs.iter().cloned().map(key_to_obj).collect())?;
                match memo.try_borrow_mut() {
                    Ok(mut memo) => memo.insert(kargs, res.clone()),
                    Err(e) => Err(NErr::io_error(format!("memo: borrow failed: {}", e)))?
                };
                Ok(res)
            }
        }
    }
    pub fn run1(&self, env: &REnv, arg: Obj) -> NRes<Obj> {
        match self {
            Func::Builtin(b) => b.run1(env, arg),
            _ => self.run(env, vec![arg]),
        }
    }
    pub fn run2(&self, env: &REnv, arg1: Obj, arg2: Obj) -> NRes<Obj> {
        match self {
            Func::Builtin(b) => b.run2(env, arg1, arg2),
            _ => self.run(env, vec![arg1, arg2]),
        }
    }

    fn try_chain(&self, other: &Func) -> Option<Func> {
        match self {
            Func::Builtin(b) => b.try_chain(other),
            Func::Closure(_) => None,
            Func::PartialApp1(..) => None,
            Func::PartialApp2(..) => None,
            Func::PartialAppLast(..) => None,
            Func::Composition(..) => None,
            Func::OnComposition(..) => None,
            Func::Parallel(_) => None,
            Func::Fanout(_) => None,
            Func::Flip(..) => None,
            Func::ListSection(_) => None,
            Func::ChainSection(..) => None,
            Func::CallSection(..) => None,
            Func::IndexSection(..) => None,
            Func::SliceSection(..) => None,
            Func::Type(_) => None,
            Func::StructField(..) => None,
            Func::Memoized(..) => None,
        }
    }
}

pub fn is_type(ty: &ObjType, arg: &Obj) -> bool {
    match (ty, arg) {
        (ObjType::Null, Obj::Null) => true,
        (ObjType::Int, Obj::Num(NNum::Int(_))) => true,
        (ObjType::Float, Obj::Num(NNum::Float(_))) => true,
        (ObjType::Complex, Obj::Num(NNum::Complex(_))) => true,
        (ObjType::Number, Obj::Num(_)) => true,
        (ObjType::List, Obj::Seq(Seq::List(_))) => true,
        (ObjType::String, Obj::Seq(Seq::String(_))) => true,
        (ObjType::Dict, Obj::Seq(Seq::Dict(..))) => true,
        (ObjType::Vector, Obj::Seq(Seq::Vector(..))) => true,
        (ObjType::Bytes, Obj::Seq(Seq::Bytes(..))) => true,
        (ObjType::Stream, Obj::Seq(Seq::Stream(..))) => true,
        (ObjType::Func, Obj::Func(..)) => true,
        (ObjType::Type, Obj::Func(Func::Type(_), _)) => true,
        (ObjType::Any, _) => true,
        (ObjType::Struct(s1), Obj::Instance(s2, _)) => s1.id == s2.id,
        (ObjType::Satisfying(renv, func), x) => match func.run(renv, vec![x.clone()]) {
            Ok(res) => res.truthy(),
            Err(e) => {
                eprintln!("INTERNAL ERROR: running the predicate for a 'satisfying'-type-check failed with; {}! trudging on...", e);
                false // FIXME yikes
            }
        },
        _ => false,
    }
}

/*
// note we must (?) not hold a mutable borrow of env while calling f since f might (will probably?)
// also get one
fn modify_every_lvalue(env: &Rc<RefCell<Env>>, expr: &Lvalue, f: &Func) -> NRes<()> {
    match expr {
        Lvalue::IndexedIdent(s, v) => {
            let mut sr = env.borrow_mut().get_var(s)?;
            for ix in v {
                sr = index_or_slice(sr, eval_index_or_slice(env, ix)?)?.clone();
            }
            Ok(sr)
        },
        Lvalue::Annotation(s, _) => eval_lvalue_as_obj(env, s),
        Lvalue::CommaSeq(v) => Ok(Obj::List(Rc::new(
            v.iter().map(|e| Ok(eval_lvalue_as_obj(env, e)?)).collect::<NRes<Vec<Obj>>>()?
        ))),
        // maybe if commaseq eagerly looks for splats...
        Lvalue::Splat(_) => Err(NErr::syntax_error("Can't evaluate splat on LHS of assignment??".to_string())),
    }
}
*/
