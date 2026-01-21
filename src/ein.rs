use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

pub use crate::core::*;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    LParen,
    RParen,
    Arrow,
}

type EinsumExpr = (Vec<Vec<String>>, Vec<Vec<String>>);

fn lex(input: &str) -> NRes<Vec<Token>> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\n' | '\r' => {
                chars.next();
            }
            '(' => {
                tokens.push(Token::LParen);
                chars.next();
            }
            ')' => {
                tokens.push(Token::RParen);
                chars.next();
            }
            '-' => {
                chars.next();
                if chars.next_if_eq(&'>').is_some() {
                    tokens.push(Token::Arrow);
                } else {
                    return Err(NErr::throw("expected '>' after '-'".into()));
                }
            }
            _ if c.is_ascii_alphabetic() || c == '_' => {
                let mut ident = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_ascii_alphanumeric() || c == '_' {
                        ident.push(c);
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token::Ident(ident));
            }
            _ => return Err(NErr::throw(format!("unexpected character '{}'", c))),
        }
    }
    Ok(tokens)
}

fn parse_elements(tokens: &[Token]) -> NRes<Vec<Vec<String>>> {
    let mut elements = Vec::new();
    let mut i = 0;

    while i < tokens.len() {
        match &tokens[i] {
            Token::Ident(name) => {
                elements.push(vec![name.clone()]);
                i += 1;
            }
            Token::LParen => {
                i += 1;
                let mut group = Vec::new();
                loop {
                    match tokens.get(i) {
                        None => return Err(NErr::throw("unclosed '('".into())),
                        Some(Token::Ident(name)) => {
                            group.push(name.clone());
                            i += 1;
                        }
                        Some(Token::RParen) => {
                            if group.is_empty() {
                                return Err(NErr::throw("empty group".into()));
                            }
                            i += 1;
                            break;
                        }
                        Some(Token::LParen) => {
                            return Err(NErr::throw("nested '(' not allowed".into()));
                        }
                        Some(Token::Arrow) => return Err(NErr::throw("'->' inside group".into())),
                    }
                }
                elements.push(group);
            }
            Token::RParen => return Err(NErr::throw("unexpected ')'".into())),
            Token::Arrow => return Err(NErr::throw("unexpected '->'".into())),
        }
    }
    Ok(elements)
}

fn parse_einsum(input: &str) -> NRes<EinsumExpr> {
    let tokens = lex(input)?;

    let arrow_count = tokens.iter().filter(|t| **t == Token::Arrow).count();
    if arrow_count == 0 {
        return Err(NErr::throw("missing '->'".into()));
    }
    if arrow_count > 1 {
        return Err(NErr::throw("multiple '->'".into()));
    }

    let arrow_idx = tokens.iter().position(|t| *t == Token::Arrow).unwrap();
    let lhs = parse_elements(&tokens[..arrow_idx])?;
    let rhs = parse_elements(&tokens[arrow_idx + 1..])?;

    Ok((lhs, rhs))
}

fn compile_einsum(
    expr: &EinsumExpr,
    sizes: &HashMap<String, usize>,
) -> NRes<(Vec<Vec<usize>>, Vec<usize>, Vec<bool>)> {
    let (lhs, rhs) = expr;

    // Build lhs_dims, using 0 for missing identifiers
    let lhs_dims: Vec<Vec<usize>> = lhs
        .iter()
        .map(|group| {
            group
                .iter()
                .map(|id| sizes.get(id).copied().unwrap_or(0))
                .collect()
        })
        .collect();

    // Flatten lhs and rhs
    let lhs_flat: Vec<&String> = lhs.iter().flat_map(|g| g.iter()).collect();
    let rhs_flat: Vec<&String> = rhs.iter().flat_map(|g| g.iter()).collect();

    // Check uniqueness
    let lhs_set: HashSet<_> = lhs_flat.iter().collect();
    let rhs_set: HashSet<_> = rhs_flat.iter().collect();
    if lhs_set.len() != lhs_flat.len() {
        return Err(NErr::throw("duplicate identifier in lhs".into()));
    }
    if rhs_set.len() != rhs_flat.len() {
        return Err(NErr::throw("duplicate identifier in rhs".into()));
    }
    if lhs_set != rhs_set {
        return Err(NErr::throw("lhs and rhs have different identifiers".into()));
    }

    // Build index map: id -> index in flattened lhs
    let id_to_idx: HashMap<&String, usize> = lhs_flat
        .iter()
        .enumerate()
        .map(|(i, id)| (*id, i))
        .collect();

    // Build rhs result
    let rhs_inds: Vec<usize> = rhs
        .iter()
        .flat_map(|group| group.iter().map(|i| id_to_idx[i]))
        .collect();

    let rhs_merges: Vec<bool> = rhs
        .iter()
        .flat_map(|group| {
            let n = group.len();
            let mut v = vec![true; n];
            v[n - 1] = false;
            v
        })
        .collect();

    Ok((lhs_dims, rhs_inds, rhs_merges))
}

fn iterate(
    acc: &mut Vec<(Vec<usize>, Obj)>,
    inds: &mut Vec<usize>,
    rest_dims: &[Vec<usize>],
    mut obj: Obj,
) -> NRes<()> {
    match rest_dims.split_first() {
        None => {
            acc.push((inds.clone(), obj));
        }
        Some((first, rest)) => {
            let v =
                mut_obj_into_iter(&mut obj, "rearrange iterate")?.collect::<NRes<Vec<Obj>>>()?;
            let n = v.len();
            let zeros = first.iter().filter(|e| **e == 0).count();
            let prod: usize = first
                .iter()
                .fold(1, |acc, e| acc.saturating_mul((*e).max(1)));
            if prod == usize::MAX {
                return Err(NErr::throw("rearrange: too big".to_string()));
            }
            let filled_dims = match zeros {
                0 => {
                    if n == prod {
                        Cow::Borrowed(first)
                    } else {
                        return Err(NErr::throw(format!(
                            "rearrange: exact dim mismatch, need {} got {}",
                            prod, n
                        )));
                    }
                }
                1 => {
                    if n % prod == 0 {
                        Cow::Owned(
                            first
                                .iter()
                                .map(|e| if *e == 0 { n / prod } else { *e })
                                .collect(),
                        )
                    } else {
                        return Err(NErr::throw(format!(
                            "rearrange: divisible dim mismatch, need {} got {}",
                            prod, n
                        )));
                    }
                }
                z => {
                    return Err(NErr::throw(format!(
                        "rearrange: underconstrained, {} unspecified",
                        z
                    )));
                }
            };
            let nn = filled_dims.len();
            for _ in filled_dims.iter() {
                inds.push(0);
            }
            let inn = inds.len();
            for e in v.into_iter() {
                iterate(acc, inds, rest, e)?;

                inds[inn - 1] += 1;
                let mut p = 0;
                while p < nn && inds[inn - 1 - p] >= filled_dims[filled_dims.len() - 1 - p] {
                    inds[inn - 1 - p] = 0;
                    p += 1;
                    if p < nn {
                        inds[inn - 1 - p] += 1;
                    }
                }
            }
            for _ in filled_dims.iter() {
                if inds.pop() != Some(0) {
                    panic!("rearrange sucks")
                }
            }
        }
    }
    Ok(())
}

enum Vecs {
    Atom(Obj),
    Vec(Vec<Vecs>),
}

fn flatten_some(v: Vecs, flag: &[bool]) -> Vecs {
    match (v, flag.split_first()) {
        (Vecs::Atom(obj), None) => Vecs::Atom(obj),
        (Vecs::Vec(vecs), Some((merge, rest))) => {
            let vs = vecs.into_iter().map(|v| flatten_some(v, rest));
            if *merge {
                Vecs::Vec(
                    vs.flat_map(|v| match v {
                        Vecs::Vec(vv) => vv,
                        Vecs::Atom(_) => panic!("inconsistent"),
                    })
                    .collect(),
                )
            } else {
                Vecs::Vec(vs.collect())
            }
        }
        _ => panic!("inconsistent"),
    }
}

fn expand(v: Vecs) -> Obj {
    match v {
        Vecs::Atom(obj) => obj,
        Vecs::Vec(vs) => Obj::list(vs.into_iter().map(expand).collect()),
    }
}

pub fn rearrange(v: Obj, spec: &str, constraints: HashMap<String, usize>) -> NRes<Obj> {
    let ein = parse_einsum(spec)?;
    let (lhs_dims, rhs_inds, rhs_merges) = compile_einsum(&ein, &constraints)?;

    // 1. iterate
    let mut elements: Vec<(Vec<usize>, Obj)> = Vec::new();
    {
        let mut inds: Vec<usize> = Vec::new();
        iterate(&mut elements, &mut inds, &lhs_dims, v)?;
    }

    // 2. object
    let mut exp: Vec<Vecs> = Vec::new();

    for (inds, elt) in elements {
        let mut ptr = &mut exp;
        if rhs_inds.is_empty() {
            return Err(NErr::throw("rearrange: empty rhs".to_string()));
        }
        for rii in &rhs_inds[..rhs_inds.len() - 1] {
            let ri = inds[*rii];
            while ptr.len() <= ri {
                ptr.push(Vecs::Vec(Vec::new()));
            }
            match &mut ptr[ri] {
                Vecs::Vec(v) => {
                    ptr = v;
                }
                _ => panic!("inconsistent ret"),
            }
        }
        ptr.push(Vecs::Atom(elt));
    }

    // 3. flatten
    Ok(expand(flatten_some(Vecs::Vec(exp), &rhs_merges)))
}
