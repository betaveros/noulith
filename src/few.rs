use std::fmt;
use std::fmt::Display;
// Silly helpers to pattern-match on a Vec<T> while moving things out

#[derive(Debug)]
pub enum Few<T> {
    Zero,
    One(T),
    Many(Vec<T>),
}
pub fn few<T>(mut xs: Vec<T>) -> Few<T> {
    match xs.len() {
        0 => Few::Zero,
        1 => Few::One(xs.remove(0)),
        _ => Few::Many(xs),
    }
}
impl<T> Few<T> {
    pub fn len(&self) -> usize {
        match self {
            Few::Zero => 0,
            Few::One(..) => 1,
            Few::Many(x) => x.len(),
        }
    }
}
impl<T: Display> Display for Few<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Few::Zero => write!(formatter, "(0)"),
            Few::One(x) => write!(formatter, "(1: {})", x),
            Few::Many(xs) => {
                write!(formatter, "(many: ")?;
                let mut started = false;
                for x in xs {
                    if started {
                        write!(formatter, ", ")?;
                    }
                    started = true;
                    write!(formatter, "{}", x)?;
                }
                write!(formatter, ")")
            }
        }
    }
}
#[derive(Debug)]
pub enum Few2<T> {
    Zero,
    One(T),
    Two(T, T),
    Many(Vec<T>),
}
pub fn few2<T>(mut xs: Vec<T>) -> Few2<T> {
    match xs.len() {
        0 => Few2::Zero,
        1 => Few2::One(xs.remove(0)),
        2 => Few2::Two(xs.remove(0), xs.pop().unwrap()),
        _ => Few2::Many(xs),
    }
}
impl<T> Few2<T> {
    pub fn len(&self) -> usize {
        match self {
            Few2::Zero => 0,
            Few2::One(..) => 1,
            Few2::Two(..) => 2,
            Few2::Many(x) => x.len(),
        }
    }
}
impl<T: Display> Display for Few2<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Few2::Zero => write!(formatter, "(0)"),
            Few2::One(x) => write!(formatter, "(1: {})", x),
            Few2::Two(x, y) => write!(formatter, "(2: {}, {})", x, y),
            Few2::Many(xs) => {
                write!(formatter, "(many: ")?;
                let mut started = false;
                for x in xs {
                    if started {
                        write!(formatter, ", ")?;
                    }
                    started = true;
                    write!(formatter, "{}", x)?;
                }
                write!(formatter, ")")
            }
        }
    }
}

#[derive(Debug)]
pub enum Few3<T> {
    Zero,
    One(T),
    Two(T, T),
    Three(T, T, T),
    Many(Vec<T>),
}
pub fn few3<T>(mut xs: Vec<T>) -> Few3<T> {
    match xs.len() {
        0 => Few3::Zero,
        1 => Few3::One(xs.remove(0)),
        2 => Few3::Two(xs.remove(0), xs.pop().unwrap()),
        3 => Few3::Three(xs.remove(0), xs.remove(0), xs.pop().unwrap()),
        _ => Few3::Many(xs),
    }
}
impl<T> Few3<T> {
    pub fn len(&self) -> usize {
        match self {
            Few3::Zero => 0,
            Few3::One(..) => 1,
            Few3::Two(..) => 2,
            Few3::Three(..) => 3,
            Few3::Many(x) => x.len(),
        }
    }
}
impl<T: Display> Display for Few3<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Few3::Zero => write!(formatter, "(0)"),
            Few3::One(x) => write!(formatter, "(1: {})", x),
            Few3::Two(x, y) => write!(formatter, "(2: {}, {})", x, y),
            Few3::Three(x, y, z) => write!(formatter, "(3: {}, {}, {})", x, y, z),
            Few3::Many(xs) => {
                write!(formatter, "(many: ")?;
                let mut started = false;
                for x in xs {
                    if started {
                        write!(formatter, ", ")?;
                    }
                    started = true;
                    write!(formatter, "{}", x)?;
                }
                write!(formatter, ")")
            }
        }
    }
}
