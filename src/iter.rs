use crate::rc::Rc;
use std::collections::HashMap;

pub fn unwrap_or_clone<T: Clone>(x: Rc<T>) -> T {
    match Rc::try_unwrap(x) {
        Ok(x) => x,
        Err(x) => (*x).clone(),
    }
}

// Say we have an Rc<Vec>. If it has refcount 1, we can drain it, so we can lazily move out each
// element; but if it has refcount >1, we lazily clone each element. At least, that's the theory.
//
// Alternatively, consuming the object and either going IntoIter or handrolling a (Rc<Vec>, usize)
// would also work fine for lists; but dictionaries don't have an easy handrollable self-owning
// iterator, I think?
pub enum RcVecIter<'a, T> {
    Draining(std::vec::Drain<'a, T>),
    Cloning(std::slice::Iter<'a, T>),
}

impl<T> RcVecIter<'_, T> {
    pub fn of(v: &mut Rc<Vec<T>>) -> RcVecIter<'_, T> {
        if Rc::strong_count(v) == 1 && Rc::weak_count(v) == 0 {
            RcVecIter::Draining(Rc::get_mut(v).unwrap().drain(..))
        } else {
            RcVecIter::Cloning(v.iter())
        }
    }
}

impl<T: Clone> Iterator for RcVecIter<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        match self {
            RcVecIter::Draining(it) => it.next(),
            RcVecIter::Cloning(it) => it.next().cloned(),
        }
    }
}

pub enum RcHashMapIter<'a, K, V> {
    Draining(std::collections::hash_map::Drain<'a, K, V>),
    Cloning(std::collections::hash_map::Iter<'a, K, V>),
}

impl<K, V> RcHashMapIter<'_, K, V> {
    pub fn of(v: &mut Rc<HashMap<K, V>>) -> RcHashMapIter<'_, K, V> {
        // Same non-lexical lifetime stuff
        if Rc::get_mut(v).is_some() {
            match Rc::get_mut(v) {
                Some(v) => RcHashMapIter::Draining(v.drain()),
                None => panic!("non-lexical lifetime issue"),
            }
        } else {
            RcHashMapIter::Cloning(v.iter())
        }
    }
}

impl<K: Clone, V: Clone> Iterator for RcHashMapIter<'_, K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        match self {
            RcHashMapIter::Draining(it) => it.next(),
            RcHashMapIter::Cloning(it) => it.next().map(|(k, v)| (k.clone(), v.clone())),
        }
    }
}

pub enum RcStringIter<'a> {
    Draining(std::string::Drain<'a>),
    Cloning(std::str::Chars<'a>),
}

impl RcStringIter<'_> {
    pub fn of(v: &mut Rc<String>) -> RcStringIter<'_> {
        if Rc::get_mut(v).is_some() {
            match Rc::get_mut(v) {
                Some(v) => RcStringIter::Draining(v.drain(..)),
                None => panic!("non-lexical lifetime issue"),
            }
        } else {
            RcStringIter::Cloning(v.chars())
        }
    }
}

impl Iterator for RcStringIter<'_> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        match self {
            RcStringIter::Draining(it) => it.next(),
            RcStringIter::Cloning(it) => it.next(),
        }
    }
}
