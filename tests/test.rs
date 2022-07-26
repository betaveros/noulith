extern crate noulith;
use std::rc::Rc;
use noulith::Obj;
use noulith::simple_eval;

#[test]
fn basic() {
    // let s = "for (x : 1 to 100) (o = ''; for (f, s : [[3, 'Fizz'], [5, 'Buzz']]) if (x % f == 0) o = o ++ s; print(if (o == '') x else o))";
    assert_eq!(simple_eval("fact = \\n: if (n == 0) 1 else n * fact(n - 1); fact 10"), Obj::from(3628800));
    assert_eq!(simple_eval("1 < 2 < 3"), Obj::from(1));
    assert_eq!(simple_eval("3 > 2 > 1"), Obj::from(1));
    assert_eq!(simple_eval("1 < 2 < 2"), Obj::from(0));
    assert_eq!(simple_eval("==(1, 1, 1)"), Obj::from(1));
    assert_eq!(simple_eval("==(0, 0, 1)"), Obj::from(0));
    assert_eq!(simple_eval("x = {:2, 3, 4: 5}; 1 to 5 map \\k: x[k]"),
       Obj::List(Rc::new(vec![Obj::from(2), Obj::from(2), Obj::from(1), Obj::from(5), Obj::from(2)])));
    assert_eq!(simple_eval("x = 3; x += 4; y = x; x min= 2; [y, x]"),
       Obj::List(Rc::new(vec![Obj::from(7), Obj::from(2)])));
    assert_eq!(simple_eval("[3 or x, 0 and x, len([4, 5, 6])]"),
       Obj::List(Rc::new(vec![Obj::from(3), Obj::from(0), Obj::from(3)])));
    assert_eq!(simple_eval("x = [3]; for (i : 1 to 10000) x append= i; x; y = []; for (i : 1 to 10000) y append= pop x; len(y)"), Obj::from(10000));
}
