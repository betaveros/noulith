use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;

use num::bigint::Sign;

use crate::core::*;
use crate::nint::NInt;
use crate::rc::Rc;

#[derive(Debug, Clone)]
pub struct Repeat(pub Obj);
impl Iterator for Repeat {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        Some(Ok(self.0.clone()))
    }
}
impl Display for Repeat {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "repeat({})", self.0)
    }
}
impl Stream for Repeat {
    fn peek(&self) -> Option<NRes<Obj>> {
        Some(Ok(self.0.clone()))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        None
    }
    fn force(&self) -> NRes<Vec<Obj>> {
        Err(NErr::value_error(
            "Cannot force repeat because it's infinite".to_string(),
        ))
    }
    fn pythonic_index_isize(&self, _: isize) -> NRes<Obj> {
        Ok(self.0.clone())
    }
    fn pythonic_slice(&self, lo: Option<isize>, hi: Option<isize>) -> NRes<Seq> {
        let lo = match lo {
            Some(x) => {
                if x < 0 {
                    x - 1
                } else {
                    x
                }
            }
            None => 0,
        };
        let hi = match hi {
            Some(x) => {
                if x < 0 {
                    x - 1
                } else {
                    x
                }
            }
            None => -1,
        };
        Ok(match (lo < 0, hi < 0) {
            (true, true) | (false, false) => {
                Seq::List(Rc::new(vec![self.0.clone(); (hi - lo).max(0) as usize]))
            }
            (true, false) => Seq::List(Rc::new(Vec::new())),
            (false, true) => Seq::Stream(Rc::new(self.clone())),
        })
    }
    fn reversed(&self) -> NRes<Seq> {
        Ok(Seq::Stream(Rc::new(self.clone())))
    }
}
#[derive(Debug, Clone)]
// just gonna say this has to be nonempty
pub struct Cycle(pub Rc<Vec<Obj>>, pub usize);
impl Iterator for Cycle {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        let ret = self.0[self.1].clone();
        self.1 = (self.1 + 1) % self.0.len();
        Some(Ok(ret))
    }
}
impl Display for Cycle {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "cycle({})", CommaSeparated(&**self.0))
    }
}
impl Stream for Cycle {
    fn peek(&self) -> Option<NRes<Obj>> {
        Some(Ok(self.0[self.1].clone()))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        None
    }
    fn force(&self) -> NRes<Vec<Obj>> {
        Err(NErr::value_error(
            "Cannot force cycle because it's infinite".to_string(),
        ))
    }
    fn pythonic_index_isize(&self, i: isize) -> NRes<Obj> {
        Ok(self.0[(self.1 as isize + i).rem_euclid(self.0.len() as isize) as usize].clone())
    }
    fn reversed(&self) -> NRes<Seq> {
        let mut v: Vec<Obj> = (*self.0).clone();
        v.reverse();
        // 0 -> 0, 1 -> n - 1...
        let i = (v.len() - self.1) % v.len();
        Ok(Seq::Stream(Rc::new(Cycle(Rc::new(v), i))))
    }
}
#[derive(Debug, Clone)]
pub struct Range(pub NInt, pub Option<NInt>, pub NInt);
impl Range {
    fn empty(&self) -> bool {
        let Range(start, end, step) = self;
        match (step.sign(), end) {
            (_, None) => false,
            (Sign::Minus, Some(end)) => start <= end,
            (Sign::NoSign | Sign::Plus, Some(end)) => start >= end,
        }
    }
}
impl Iterator for Range {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        if self.empty() {
            None
        } else {
            let Range(start, _end, step) = self;
            let ret = start.clone();
            *start += &*step;
            Some(Ok(Obj::from(ret)))
        }
    }
}
impl Display for Range {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(end) => write!(formatter, "{} til {} by {}", self.0, end, self.2),
            None => write!(formatter, "{} til ... by {}", self.0, self.2),
        }
    }
}
impl Stream for Range {
    fn peek(&self) -> Option<NRes<Obj>> {
        if self.empty() {
            None
        } else {
            Some(Ok(Obj::from(self.0.clone())))
        }
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        let Range(start, end, step) = self;
        let end = end.as_ref()?;
        match step.sign() {
            // weird
            Sign::NoSign => {
                if start < end {
                    None
                } else {
                    Some(0)
                }
            }
            Sign::Minus => {
                ((end - start - step + NInt::Small(1)).max(NInt::Small(0)) / (-step)).to_usize()
            }
            Sign::Plus => {
                ((end - start + step - NInt::Small(1)).max(NInt::Small(0)) / step).to_usize()
            }
        }
    }
}

// Order: lexicographic indexes
#[derive(Debug, Clone)]
pub struct Permutations(pub Rc<Vec<Obj>>, pub Option<Rc<Vec<usize>>>);
impl Iterator for Permutations {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        let v = Rc::make_mut(self.1.as_mut()?);
        let ret = Obj::list(v.iter().map(|i| self.0[*i].clone()).collect());

        // 1 6 4 2 -> 2 1 4 6
        // last increase, and the largest index of something larger than it
        let mut up = None;
        for i in 0..(v.len() - 1) {
            if v[i] < v[i + 1] {
                up = Some((i, i + 1));
            } else {
                match &mut up {
                    Some((inc, linc)) => {
                        if v[i + 1] > v[*inc] {
                            *linc = i + 1;
                        }
                    }
                    None => {}
                }
            }
        }
        match up {
            Some((inc, linc)) => {
                v.swap(inc, linc);
                v[inc + 1..].reverse();
            }
            None => {
                self.1 = None;
            }
        }
        Some(Ok(ret))
    }
}
impl Display for Permutations {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(x) => {
                write!(
                    formatter,
                    "permutations({} @ {})",
                    CommaSeparated(&**self.0),
                    CommaSeparated(&**x)
                )
            }
            None => write!(formatter, "permutations(done)"),
        }
    }
}
impl Stream for Permutations {
    fn peek(&self) -> Option<NRes<Obj>> {
        Some(Ok(Obj::list(
            self.1
                .as_ref()?
                .iter()
                .map(|i| self.0[*i].clone())
                .collect(),
        )))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        match &self.1 {
            None => Some(0),
            Some(v) => {
                let mut cur = 1usize;
                Some(
                    (1..v.len())
                        .map(|i| {
                            // Each way we could replace v[len - 1 - i] with a later number that's larger
                            // gives us cur.
                            // i = 0, cur = undef
                            // i = 1, cur = 1
                            // i = 2, cur = 2
                            // i = 3, cur = 6
                            cur *= i;
                            cur * (v.len() - i..v.len())
                                .filter(|j| v[*j] > v[v.len() - 1 - i])
                                .count()
                        })
                        .sum::<usize>()
                        + 1usize,
                )
            }
        }
    }
}

// Order: lexicographic indexes
#[derive(Debug, Clone)]
pub struct Combinations(pub Rc<Vec<Obj>>, pub Option<Rc<Vec<usize>>>);
impl Iterator for Combinations {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        let v = Rc::make_mut(self.1.as_mut()?);
        if v.len() > self.0.len() {
            return None;
        }
        let ret = Obj::list(v.iter().map(|i| self.0[*i].clone()).collect());

        let mut last = self.0.len();
        for i in (0..v.len()).rev() {
            if v[i] + 1 < last {
                // found the next
                v[i] += 1;
                for j in i + 1..v.len() {
                    v[j] = v[j - 1] + 1;
                }
                return Some(Ok(ret));
            }
            last -= 1;
        }
        self.1 = None;
        Some(Ok(ret))
    }
}
impl Display for Combinations {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(x) => {
                write!(
                    formatter,
                    "combinations({} @ {})",
                    CommaSeparated(&**self.0),
                    CommaSeparated(&**x)
                )
            }
            None => write!(formatter, "combinations(done)"),
        }
    }
}
impl Stream for Combinations {
    fn peek(&self) -> Option<NRes<Obj>> {
        Some(Ok(Obj::list(
            self.1
                .as_ref()?
                .iter()
                .map(|i| self.0[*i].clone())
                .collect(),
        )))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    // FIXME this math is hard
    /*
    fn len(&self) -> Option<usize> {
        match &self.1 {
            None => Some(0),
            Some(v) => {
                Some((0..v.len()).rev().map(|i| {
                    // ...
                }).sum::<usize>() + 1usize)
            }
        }
    }
    */
}

// Order: big-endian binary
#[derive(Debug, Clone)]
pub struct Subsequences(pub Rc<Vec<Obj>>, pub Option<Rc<Vec<bool>>>);
impl Iterator for Subsequences {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        let v = Rc::make_mut(self.1.as_mut()?);
        let ret = Obj::list(
            v.iter()
                .zip(self.0.iter())
                .filter_map(|(b, x)| if *b { Some(x.clone()) } else { None })
                .collect(),
        );

        for i in (0..v.len()).rev() {
            if !v[i] {
                v[i] = true;
                for j in i + 1..v.len() {
                    v[j] = false;
                }
                return Some(Ok(ret));
            }
        }
        self.1 = None;
        Some(Ok(ret))
    }
}
impl Display for Subsequences {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(x) => {
                write!(
                    formatter,
                    "subsequences({} @ {})",
                    CommaSeparated(&**self.0),
                    CommaSeparated(&**x)
                )
            }
            None => write!(formatter, "subsequences(done)"),
        }
    }
}
impl Stream for Subsequences {
    fn peek(&self) -> Option<NRes<Obj>> {
        Some(Ok(Obj::list(
            self.1
                .as_ref()?
                .iter()
                .zip(self.0.iter())
                .filter_map(|(b, x)| if *b { Some(x.clone()) } else { None })
                .collect(),
        )))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        match &self.1 {
            None => Some(0),
            Some(v) => {
                let mut cur = 1usize;
                Some(
                    (0..v.len())
                        .rev()
                        .map(|i| {
                            let s = if !v[i] {
                                // If we keep everything before this and set this to true:
                                cur
                            } else {
                                0
                            };
                            cur *= 2;
                            s
                        })
                        .sum::<usize>()
                        + 1usize,
                )
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct CartesianPower(pub Rc<Vec<Obj>>, pub Option<Rc<Vec<usize>>>);
impl Iterator for CartesianPower {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        let v = Rc::make_mut(self.1.as_mut()?);
        let ret = Obj::list(v.iter().map(|i| self.0[*i].clone()).collect());

        // let mut last = self.0.len();
        for i in (0..v.len()).rev() {
            v[i] += 1;
            if v[i] == self.0.len() {
                v[i] = 0;
            } else {
                return Some(Ok(ret));
            }
        }
        self.1 = None;
        Some(Ok(ret))
    }
}
impl Display for CartesianPower {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.1 {
            Some(x) => {
                write!(
                    formatter,
                    "CartesianPower({} @ {})",
                    CommaSeparated(&**self.0),
                    CommaSeparated(&**x)
                )
            }
            None => write!(formatter, "CartesianPower(done)"),
        }
    }
}
impl Stream for CartesianPower {
    fn peek(&self) -> Option<NRes<Obj>> {
        Some(Ok(Obj::list(
            self.1
                .as_ref()?
                .iter()
                .map(|i| self.0[*i].clone())
                .collect(),
        )))
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        match &self.1 {
            None => Some(0),
            Some(v) => {
                let mut cur = 1usize;
                Some(
                    (0..v.len())
                        .rev()
                        .map(|i| {
                            // If we keep everything before this and increase this:
                            let s = (self.0.len() - 1 - v[i]) * cur;
                            cur *= self.0.len();
                            s
                        })
                        .sum::<usize>()
                        + 1usize,
                )
            }
        }
    }
}

// moderately illegal
// we'll treat NErr::Break as graceful termination
#[derive(Clone)]
pub struct Iterate(pub NRes<(Obj, Func, REnv)>);
// directly debug-printing env can easily recurse infinitely
impl Debug for Iterate {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self.0 {
            Ok((obj, func, _)) => write!(fmt, "Iterate({:?}, {:?}, ...)", obj, func),
            Err(NErr::Break(0, None)) => write!(fmt, "Iterate(stopped)"),
            Err(e) => write!(fmt, "Iterate(ERROR: {:?})", e),
        }
    }
}
impl Iterator for Iterate {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        match &mut self.0 {
            Ok((obj, func, renv)) => {
                let ret = obj.clone();
                let cur = std::mem::take(obj);
                match func.run1(&renv, cur) {
                    Ok(nxt) => {
                        *obj = nxt;
                    }
                    Err(e) => {
                        self.0 = Err(e);
                    }
                }
                Some(Ok(ret))
            }
            Err(NErr::Break(0, None)) => None,
            Err(e) => Some(Err(e.clone())),
        }
    }
}
impl Display for Iterate {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.0 {
            Ok((obj, func, _)) => write!(formatter, "Iterate({}, {}, ...)", obj, func),
            Err(NErr::Break(0, None)) => write!(formatter, "Iterate(stopped)"),
            Err(e) => write!(formatter, "Iterate(ERROR: {})", e),
        }
    }
}
impl Stream for Iterate {
    fn peek(&self) -> Option<NRes<Obj>> {
        match &self.0 {
            Ok((obj, _, _)) => Some(Ok(obj.clone())),
            Err(NErr::Break(0, None)) => None,
            Err(e) => Some(Err(e.clone())),
        }
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    fn len(&self) -> Option<usize> {
        None
    }
}

// maybe even more illegal? not sure
// again we'll treat NErr::Break as graceful termination
pub struct MappedStream(pub NRes<(Box<dyn Stream>, Func, REnv)>);
impl Clone for MappedStream {
    fn clone(&self) -> MappedStream {
        match &self.0 {
            Err(e) => MappedStream(Err(e.clone())),
            Ok((inner, func, renv)) => {
                MappedStream(Ok((inner.clone_box(), func.clone(), renv.clone())))
            }
        }
    }
}
// directly debug-printing env can easily recurse infinitely
impl Debug for MappedStream {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self.0 {
            Err(NErr::Break(0, None)) => write!(fmt, "MappedStream(stopped)"),
            Err(e) => write!(fmt, "MappedStream(ERROR: {:?})", e),
            Ok((inner, func, _)) => write!(fmt, "MappedStream({:?}, {:?}, ...)", inner, func),
        }
    }
}
impl Iterator for MappedStream {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        let (inner, func, renv) = self.0.as_mut().ok()?;
        match inner.next() {
            Some(Err(e)) => {
                self.0 = Err(e.clone());
                Some(Err(e))
            }
            Some(Ok(cur)) => match func.run1(&renv, cur) {
                Ok(nxt) => Some(Ok(nxt)),
                Err(e) => {
                    self.0 = Err(e.clone());
                    Some(Err(e))
                }
            },
            None => {
                self.0 = Err(NErr::Break(0, None));
                None
            }
        }
    }
}
impl Display for MappedStream {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.0 {
            Ok((inner, func, _)) => write!(formatter, "MappedStream({}, {}, ...)", inner, func),
            Err(e) => write!(formatter, "MappedStream(ERROR: {})", e),
        }
    }
}
impl Stream for MappedStream {
    fn peek(&self) -> Option<NRes<Obj>> {
        let (inner, func, renv) = self.0.as_ref().ok()?;
        match inner.peek()? {
            Ok(inxt) => match func.run1(&renv, inxt) {
                Ok(nxt) => Some(Ok(nxt)),
                Err(e) => Some(Err(e.clone())),
            },
            Err(NErr::Break(0, None)) => None,
            Err(e) => Some(Err(e)),
        }
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
    /*
    fn len(&self) -> Option<usize> {
        match &self.0 {
            Ok((inner, _, _)) => inner.len(),
            Err(_) => Some(0),
        }
    }
    */
}

// i think just equally illegal
// again we'll treat NErr::Break as graceful termination
pub struct FilteredStream(pub NRes<(Box<dyn Stream>, Func, REnv)>);
impl Clone for FilteredStream {
    fn clone(&self) -> FilteredStream {
        match &self.0 {
            Err(e) => FilteredStream(Err(e.clone())),
            Ok((inner, func, renv)) => {
                FilteredStream(Ok((inner.clone_box(), func.clone(), renv.clone())))
            }
        }
    }
}
// directly debug-printing env can easily recurse infinitely
impl Debug for FilteredStream {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self.0 {
            Err(NErr::Break(0, None)) => write!(fmt, "FilteredStream(stopped)"),
            Err(e) => write!(fmt, "FilteredStream(ERROR: {:?})", e),
            Ok((inner, func, _)) => write!(fmt, "FilteredStream({:?}, {:?}, ...)", inner, func),
        }
    }
}
impl Iterator for FilteredStream {
    type Item = NRes<Obj>;
    fn next(&mut self) -> Option<NRes<Obj>> {
        let (inner, func, renv) = self.0.as_mut().ok()?;
        loop {
            match inner.next() {
                Some(Err(e)) => {
                    self.0 = Err(e.clone());
                    return Some(Err(e));
                }
                Some(Ok(cur)) => match func.run1(&renv, cur.clone()) {
                    Ok(nxt) => {
                        if nxt.truthy() {
                            return Some(Ok(cur));
                        }
                    }
                    Err(e) => {
                        self.0 = Err(e.clone());
                        return Some(Err(e));
                    }
                },
                None => {
                    self.0 = Err(NErr::Break(0, None));
                    return None;
                }
            }
        }
    }
}
impl Display for FilteredStream {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.0 {
            Ok((inner, func, _)) => write!(formatter, "FilteredStream({}, {}, ...)", inner, func),
            Err(e) => write!(formatter, "FilteredStream(ERROR: {})", e),
        }
    }
}
impl Stream for FilteredStream {
    fn peek(&self) -> Option<NRes<Obj>> {
        // lol this can be arbitrarily slow:
        self.clone().next()
    }
    fn clone_box(&self) -> Box<dyn Stream> {
        Box::new(self.clone())
    }
}
