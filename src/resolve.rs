// Resolve variables to (how many Envs up, which slot), so evaluating them doesn't hash the name in
// every Env on the way up. This happens right before evaluating, against the Env the code will be
// evaluated in (see parse_and_resolve_in), so every variable can be resolved, including the top
// level's and builtins.
//
// Scoping is strict: a name declared anywhere in a scope means that scope's variable throughout
// it, and using it before the declaration has run is an error. We reject that here when it's
// visible in the source order (outside a lambda, which might be called later), and at runtime
// otherwise (e.g. conditional declarations). Envs inside the code have fixed layouts, so this has
// to find every declaration in a scope.
//
// The outermost scope is the live Env the code is evaluated in (or for eval, a new scope inside
// it). If that's the root Env, we make empty slots in it for everything the code declares at its
// top level. Using a name that isn't declared anywhere (in the code or the Envs it's evaluated in)
// is an error, even in a REPL, where a later line might have declared it.
//
// The other thing that has to stay in sync with eval.rs is which nodes create Envs, and which of
// their parts are evaluated in them:
//
// - Lambda: the params and body, in a new Env per call
// - For: each iteration's pattern, later iterations and guards, and the body, in a new Env per
//   element; the first iteratee and the `into` are outside
// - While: the condition and body, in a new Env per iteration
// - Switch: each case's pattern and body, in a new Env per case tried; the scrutinee is outside
// - Try: the catch pattern and body, in a new Env; the try body is outside
//
// Within an Env, code outside lambdas runs in source order, except that an assignment's RHS runs
// before its declarations take effect. That's what the "declared so far" check relies on.

use std::collections::{HashMap, HashSet};

use crate::core::*;
use crate::lex::CodeLoc;
use crate::rc::*;

struct Scope {
    // what the code declares in this scope -> its slot. For a scope inside the code, whose Envs
    // don't exist yet, this is the layout they'll get when created.
    slots: HashMap<String, usize>,
    // whether this is the live scope: the outermost scope we track, which is the existing Env the
    // code is being resolved for (beyond it, outside() looks through that Env's parents). That Env
    // can also have variables the code doesn't declare (builtins, earlier REPL lines), and some of
    // the code's own can already be filled (a REPL line redeclaring one).
    live: bool,
    // what's been declared so far in the rewriting pass, which goes in source order, for rejecting
    // uses before declarations
    declared: HashSet<String>,
    // whether this is a lambda's scope, whose code can run after its outer scopes' later code
    lambda: bool,
}

// What a scope declares, in order of first declaration; slots[name] is name's index in names.
#[derive(Default)]
struct Collected {
    names: Vec<String>,
    slots: HashMap<String, usize>,
}

impl Collected {
    fn add(&mut self, name: &str) {
        if !self.slots.contains_key(name) {
            self.slots.insert(name.to_string(), self.names.len());
            self.names.push(name.to_string());
        }
    }
}

struct Resolver {
    env: REnv,
    // scopes we're inside, innermost last
    scopes: Vec<Scope>,
    // Each scope gets two passes: collecting everything it declares, then rewriting names into
    // SlotRefs. This is Some during the collecting pass, holding what's been collected.
    collecting: Option<Collected>,
    // declarations in the current statement, which take effect after its RHS
    pending: Vec<String>,
    // where we are, for errors
    loc: (CodeLoc, CodeLoc),
    error: Option<ParseError>,
}

impl Resolver {
    fn new(env: &REnv, expr: &LocExpr) -> Resolver {
        Resolver {
            env: Rc::clone(env),
            scopes: Vec::new(),
            collecting: None,
            pending: Vec::new(),
            loc: (expr.start, expr.end),
            error: None,
        }
    }

    // Err if anything so far has failed
    fn check(&mut self) -> Result<(), ParseError> {
        match self.error.take() {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }
}

// Resolve code to be evaluated directly in env.
pub fn resolve(env: &REnv, expr: &mut LocExpr) -> Result<(), ParseError> {
    let mut r = Resolver::new(env, expr);
    // collecting pass over the top level, like scope() but for the live Env
    r.collecting = Some(Collected::default());
    r.expr(expr);
    let declares = r.collecting.take().unwrap().names;
    r.check()?;
    let slots = r.make_room(&declares);
    r.check()?;
    // rewriting pass, now that the live Env has slots for everything the top level declares
    r.scopes.push(Scope {
        slots,
        live: true,
        declared: HashSet::new(),
        lambda: false,
    });
    r.expr(expr);
    r.check()
}

// Resolve code to be evaluated in a new Env whose parent is env (which is what eval does, so
// what it declares stays inside it), and return that Env's layout.
pub fn resolve_in_new_scope(env: &REnv, expr: &mut LocExpr) -> Result<SlotLayout, ParseError> {
    let mut r = Resolver::new(env, expr);
    r.scopes.push(Scope {
        slots: HashMap::new(),
        live: true,
        declared: HashSet::new(),
        lambda: false,
    });
    let layout = r.scope(false, |r| r.expr(expr));
    r.check()?;
    Ok(layout.unwrap())
}

impl Resolver {
    fn fail(&mut self, msg: String) {
        if self.error.is_none() {
            self.error = Some(ParseError::expr(msg, self.loc.0, self.loc.1));
        }
    }

    // make sure the live Env has slots for what the top level declares, and return them
    fn make_room(&mut self, names: &[String]) -> HashMap<String, usize> {
        let mut slots = HashMap::new();
        let live = Rc::clone(&self.env);
        let mut env = match cell_try_borrow_mut(&live) {
            Ok(e) => e,
            Err(_) => {
                self.fail(format!("BUG: resolving while the Env is borrowed"));
                return slots;
            }
        };
        for name in names {
            let slot = if env.parent.is_err() {
                env.reserve_root_slot(name)
            } else {
                match env.vars.get(name) {
                    Some(slot) => slot,
                    None => {
                        std::mem::drop(env);
                        self.fail(format!(
                            "Can't declare {:?} here: this scope's variables were fixed when it \
                             was parsed",
                            name
                        ));
                        return slots;
                    }
                }
            };
            slots.insert(name.clone(), slot);
        }
        slots
    }

    // the live Env's slot for name, and whether it's been declared
    fn live_slot(&mut self, name: &str) -> Option<(usize, bool)> {
        let live = Rc::clone(&self.env);
        match cell_try_borrow(&live) {
            Ok(env) => env.vars.get(name).map(|i| (i, env.slots[i].is_some())),
            Err(_) => {
                self.fail(format!("BUG: resolving while the Env is borrowed"));
                None
            }
        }
    }

    // " Did you mean ...?" with the closest name in scope, for a name that isn't
    fn suggestion(&self, name: &str) -> String {
        let mut names: Vec<String> = Vec::new();
        for s in &self.scopes {
            names.extend(s.slots.keys().cloned());
        }
        let mut env = Some(Rc::clone(&self.env));
        while let Some(e) = env {
            env = match cell_try_borrow(&e) {
                Ok(e) => {
                    names.extend(e.vars.names().map(str::to_string));
                    e.parent.as_ref().ok().map(Rc::clone)
                }
                Err(_) => None,
            };
        }
        match names
            .iter()
            .min_by_key(|k| fast_edit_distance(k.as_bytes(), name.as_bytes()))
        {
            Some(k) => format!(" Did you mean: {:?}?", k),
            None => String::new(),
        }
    }

    // name isn't in any scope in the code, so look in the Envs above the live one, and if it's
    // not anywhere, it's an error
    fn outside(&mut self, name: &str) -> Option<SlotRef> {
        let mut depth = self.scopes.len() - 1;
        let mut env = Rc::clone(&self.env);
        loop {
            let parent = match cell_try_borrow(&env) {
                Ok(e) => {
                    if let Some(slot) = e.vars.get(name) {
                        return Some(SlotRef {
                            name: Rc::new(name.to_string()),
                            depth,
                            slot,
                        });
                    }
                    match &e.parent {
                        Ok(p) => Rc::clone(p),
                        Err(_) => break,
                    }
                }
                Err(_) => {
                    self.fail(format!("BUG: resolving while an Env is borrowed"));
                    return None;
                }
            };
            env = parent;
            depth += 1;
        }
        let msg = format!("No such variable: {:?}.{}", name, self.suggestion(name));
        self.fail(msg);
        None
    }

    fn reference(&mut self, name: &str) -> Option<SlotRef> {
        if self.collecting.is_some() {
            return None;
        }
        let n = self.scopes.len();
        for i in (0..n).rev() {
            // the slot, and whether it's this scope's own variable that hasn't been declared yet
            let scope = &self.scopes[i];
            let (own, live) = (scope.slots.get(name).copied(), scope.live);
            let undeclared_so_far = !scope.declared.contains(name);
            let (slot, undeclared) = match own {
                // in the live Env, it might be filled already
                Some(slot) if live => (
                    slot,
                    undeclared_so_far && !self.live_slot(name).map_or(false, |(_, filled)| filled),
                ),
                Some(slot) => (slot, undeclared_so_far),
                None if live => match self.live_slot(name) {
                    Some((slot, _)) => (slot, false),
                    None => continue,
                },
                None => continue,
            };
            if undeclared && !self.scopes[i + 1..].iter().any(|s| s.lambda) {
                self.fail(format!(
                    "{} is used before it's declared (later in the same scope)",
                    name
                ));
            }
            return Some(SlotRef {
                name: Rc::new(name.to_string()),
                depth: n - 1 - i,
                slot,
            });
        }
        self.outside(name)
    }

    fn declaration(&mut self, name: &str) -> Option<SlotRef> {
        if let Some(c) = &mut self.collecting {
            c.add(name);
            return None;
        }
        let slot = *self.scopes.last()?.slots.get(name)?;
        self.pending.push(name.to_string());
        Some(SlotRef {
            name: Rc::new(name.to_string()),
            depth: 0,
            slot,
        })
    }

    // the declarations so far take effect
    fn commit(&mut self) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.declared.extend(self.pending.drain(..));
        } else {
            self.pending.clear();
        }
    }

    // Resolve the parts of a node that run in a new Env. Takes two passes: collecting everything
    // the scope declares (including later in it, so e.g. a closure can call a function declared
    // after it), then rewriting. Does nothing in an outer scope's collecting pass, since
    // declarations in here don't go there.
    fn scope(&mut self, lambda: bool, mut f: impl FnMut(&mut Self)) -> Option<SlotLayout> {
        if self.collecting.is_some() {
            return None;
        }
        self.collecting = Some(Collected::default());
        f(self);
        let slots = self.collecting.take().unwrap().slots;
        let outer_pending = std::mem::take(&mut self.pending);
        self.scopes.push(Scope {
            slots,
            live: false,
            declared: HashSet::new(),
            lambda,
        });
        f(self);
        self.pending = outer_pending;
        Some(SlotLayout::new(self.scopes.pop().unwrap().slots))
    }

    fn ident(&mut self, id: &mut Ident, declaring: bool) {
        if let Ident::Ident(name) = id {
            let resolved = if declaring {
                self.declaration(name)
            } else {
                self.reference(name)
            };
            if let Some(r) = resolved {
                *id = Ident::Slot(r);
            }
        }
    }

    // Resolve the code in an Rc, which has to be the only reference to it: resolving can depend on
    // where the code is, so the parser never shares these, and nothing else can have them yet.
    fn rc<'a, T>(&mut self, e: &'a mut Rc<T>) -> Option<&'a mut T> {
        let r = Rc::get_mut(e);
        if r.is_none() {
            self.fail(format!("BUG: resolving code that's shared"));
        }
        r
    }

    fn opt(&mut self, e: &mut Option<Box<LocExpr>>) {
        if let Some(e) = e {
            self.expr(e)
        }
    }

    fn ios(&mut self, ios: &mut IndexOrSlice) {
        match ios {
            IndexOrSlice::Index(i) => self.expr(i),
            IndexOrSlice::Slice(a, b) => {
                self.opt(a);
                self.opt(b);
            }
            IndexOrSlice::Symbol(_) => {}
        }
    }

    // declaring mirrors whether eval.rs's assign gets Some(type): true in patterns, and inside
    // annotations (which is what := is)
    fn lvalue(&mut self, lv: &mut Lvalue, declaring: bool) {
        match lv {
            Lvalue::Underscore | Lvalue::Literal(_) => {}
            Lvalue::IndexedIdent(id, ioses) => {
                for ios in ioses {
                    self.ios(ios);
                }
                self.ident(id, declaring);
            }
            Lvalue::Annotation(x, t) => {
                self.lvalue(x, true);
                if let Some(t) = t.as_mut().and_then(|t| self.rc(t)) {
                    self.expr(t);
                }
            }
            Lvalue::WithDefault(x, d) => {
                self.lvalue(x, declaring);
                if let Some(d) = self.rc(d) {
                    self.expr(d);
                }
            }
            Lvalue::CommaSeq(xs, _) => {
                for x in xs {
                    self.lvalue(x, declaring);
                }
            }
            Lvalue::Splat(x) => self.lvalue(x, declaring),
            Lvalue::Or(a, b) | Lvalue::And(a, b) => {
                self.lvalue(a, declaring);
                self.lvalue(b, declaring);
            }
            Lvalue::Destructure(f, args) => {
                self.expr(f);
                for x in args {
                    self.lvalue(x, declaring);
                }
            }
            Lvalue::ChainDestructure(x, ops) => {
                self.lvalue(x, declaring);
                for (op, x) in ops {
                    self.expr(op);
                    self.lvalue(x, declaring);
                }
            }
            Lvalue::Literally(e) => self.expr(e),
        }
    }

    // each iteration's Env contains all the later iterations and the body
    fn for_iterations(&mut self, its: &mut [ForIteration], body: &mut dyn FnMut(&mut Self)) {
        match its.split_first_mut() {
            None => body(self),
            Some((ForIteration::Guard(g), rest)) => {
                self.expr(g);
                self.for_iterations(rest, body);
            }
            Some((ForIteration::Iteration(_, pat, iteratee, layout), rest)) => {
                self.expr(iteratee);
                if let Some(l) = self.scope(false, |r| {
                    r.lvalue(pat, true);
                    r.commit();
                    r.for_iterations(rest, body);
                }) {
                    *layout = l;
                }
            }
        }
    }

    fn for_body(&mut self, its: &mut [ForIteration], body: &mut ForBody) {
        match body {
            ForBody::Execute(b) => self.for_iterations(its, &mut |r| r.expr(b)),
            ForBody::Yield(b, into) => {
                if let Some(into) = into {
                    self.expr(into);
                }
                self.for_iterations(its, &mut |r| r.expr(b));
            }
            ForBody::YieldItem(k, v, into) => {
                if let Some(into) = into {
                    self.expr(into);
                }
                self.for_iterations(its, &mut |r| {
                    r.expr(k);
                    r.expr(v);
                });
            }
        }
    }

    fn expr(&mut self, e: &mut LocExpr) {
        let outer_loc = std::mem::replace(&mut self.loc, (e.start, e.end));
        self.expr_inner(e);
        self.loc = outer_loc;
    }

    fn expr_inner(&mut self, e: &mut LocExpr) {
        match &mut e.expr {
            Expr::Ident(name) => {
                if let Some(r) = self.reference(name) {
                    e.expr = Expr::Slot(r);
                }
            }
            Expr::Null
            | Expr::IntLit64(_)
            | Expr::IntLit(_)
            | Expr::RatLit(_)
            | Expr::FloatLit(_)
            | Expr::ImaginaryFloatLit(_)
            | Expr::StringLit(_)
            | Expr::BytesLit(_)
            | Expr::Slot(_)
            | Expr::Symbol(_)
            | Expr::Backref(_)
            | Expr::Frozen(_)
            | Expr::Underscore
            | Expr::Continue(_) => {}
            Expr::FormatString(parts) => {
                for part in parts {
                    if let Err((e, _)) = part {
                        self.expr(e);
                    }
                }
            }
            Expr::Call(f, args, _) => {
                self.expr(f);
                for a in args {
                    self.expr(a);
                }
            }
            Expr::SymbolAccess(e, _) => self.expr(e),
            Expr::List(xs) => {
                for x in xs {
                    self.expr(x);
                }
            }
            Expr::CommaSeq(xs) => {
                for x in xs {
                    self.expr(x);
                }
            }
            Expr::Dict(def, pairs) => {
                self.opt(def);
                for (k, v) in pairs {
                    self.expr(k);
                    self.opt(v);
                }
            }
            Expr::Index(x, ios) => {
                self.expr(x);
                self.ios(ios);
            }
            Expr::Update(x, pairs) => {
                self.expr(x);
                for (k, v) in pairs {
                    self.expr(k);
                    self.expr(v);
                }
            }
            Expr::Chain(x, ops) => {
                self.expr(x);
                for (op, y) in ops {
                    self.expr(op);
                    self.expr(y);
                }
            }
            Expr::And(a, b) | Expr::Or(a, b) | Expr::Coalesce(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            Expr::Annotation(x, t) => {
                self.expr(x);
                if let Some(t) = t.as_mut().and_then(|t| self.rc(t)) {
                    self.expr(t);
                }
            }
            Expr::Consume(lv) | Expr::Pop(lv) | Expr::Remove(lv) => {
                self.lvalue(lv, false);
                self.commit();
            }
            Expr::Swap(a, b) => {
                self.lvalue(a, false);
                self.lvalue(b, false);
                self.commit();
            }
            Expr::Assign(_, lv, rhs) => {
                self.lvalue(lv, false);
                self.expr(rhs);
                self.commit();
            }
            Expr::OpAssign(_, lv, op, rhs) => {
                self.lvalue(lv, false);
                self.expr(op);
                self.expr(rhs);
                self.commit();
            }
            Expr::If(c, a, b) => {
                self.expr(c);
                self.expr(a);
                self.opt(b);
            }
            Expr::For(its, body) => {
                self.for_body(its, body);
            }
            Expr::While(cond, body, layout) => {
                if let Some(l) = self.scope(false, |r| {
                    r.expr(cond);
                    r.expr(body);
                }) {
                    *layout = l;
                }
            }
            Expr::Switch(scrutinee, cases) => {
                self.expr(scrutinee);
                for (pat, body, layout) in cases {
                    if let Some(l) = self.scope(false, |r| {
                        r.lvalue(pat, true);
                        r.commit();
                        r.expr(body);
                    }) {
                        *layout = l;
                    }
                }
            }
            Expr::Try(body, pat, catcher, layout) => {
                self.expr(body);
                if let Some(l) = self.scope(false, |r| {
                    r.lvalue(pat, true);
                    r.commit();
                    r.expr(catcher);
                }) {
                    *layout = l;
                }
            }
            Expr::Break(_, e) | Expr::Return(e) => self.opt(e),
            Expr::Throw(e) | Expr::Freeze(e) | Expr::Literally(e) | Expr::Import(e) => self.expr(e),
            Expr::Splat(e) => self.expr(e),
            Expr::Sequence(xs, _) => {
                for x in xs {
                    self.expr(x);
                }
            }
            Expr::Struct(_, fields, ids) => {
                // the defaults are evaluated first
                for (_, def) in fields.iter_mut() {
                    self.opt(def);
                }
                for id in ids {
                    self.ident(id, true);
                }
                self.commit();
            }
            Expr::Lambda(params, body) => {
                let (Some(LambdaParams { lvalues, layout }), Some(body)) =
                    (self.rc(params), self.rc(body))
                else {
                    return;
                };
                if let Some(l) = self.scope(true, |r| {
                    for p in lvalues.iter_mut() {
                        r.lvalue(p, true);
                    }
                    r.commit();
                    r.expr(body);
                }) {
                    *layout = l;
                }
            }
            // 🐉 syntax for the internal stack. These evaluate everything in the current Env...
            Expr::InternalPop | Expr::InternalPeek(_) => {}
            Expr::InternalFrame(e) | Expr::InternalPush(e) | Expr::InternalCall(_, e) => {
                self.expr(e)
            }
            Expr::InternalWhile(a, b) | Expr::InternalFor(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            // ...including an InternalLambda's body, which really runs in whatever Env calls it, but
            // we resolve it as if it were written inline. So it only works when called from the
            // Env it's written in, and anywhere else it'll find the wrong variables (or a BUG
            // error).
            Expr::InternalLambda(caps, _, body) => {
                if let Some(caps) = self.rc(caps) {
                    for c in caps {
                        self.expr(c);
                    }
                }
                if let Some(body) = self.rc(body) {
                    self.expr(body);
                }
            }
        }
    }
}
