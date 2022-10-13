extern crate noulith;
// use std::rc::Rc;
use noulith::simple_eval;
use noulith::Obj;

fn i(n: i32) -> Obj {
    Obj::i32(n)
}

#[test]
fn demos() {
    assert_eq!(
        simple_eval("fact := \\n: if (n == 0) 1 else n * fact(n - 1); fact 10"),
        i(3628800)
    );
    assert_eq!(
        simple_eval("(for (x : 1 to 15) yield (o := ''; for (f, s : [[3, 'Fizz'], [5, 'Buzz']]) if (x % f == 0) o $= s; if (o == '') x else o)) join ';'"),
        Obj::from("1;2;Fizz;4;Buzz;Fizz;7;8;Fizz;Buzz;11;Fizz;13;14;FizzBuzz")
    );
}

#[test]
fn quick_operators() {
    assert_eq!(simple_eval("2 + 3"), i(5));
    assert_eq!(simple_eval("+(2, 3)"), i(5));
    assert_eq!(simple_eval("plus := +; 2 plus 3"), i(5));
    assert_eq!(simple_eval("plus := \\x, y: x + y; 2 plus 3"), i(5));
}

#[test]
fn modifications() {
    assert_eq!(simple_eval("x := 2; x += 3; x"), i(5));
    assert_eq!(simple_eval("x := 2; x max= 3; x"), i(3));
    assert_eq!(simple_eval("x := 2; x .= +3; x"), i(5));
}

#[test]
fn weird_assignments() {
    assert_eq!(simple_eval("every x, y := 2; x + y"), i(4));
    assert_eq!(simple_eval("x := 1 to 10; every x[2:4] = -1; sum x"), i(46));
    assert_eq!(simple_eval("x := 1 to 10; every x[2:4] -= 1; sum x"), i(53));
}

#[test]
fn ranges() {
    assert_eq!(simple_eval("1 til 3 join ','"), Obj::from("1,2"));
    assert_eq!(simple_eval("1 to 3 join ','"), Obj::from("1,2,3"));
    assert_eq!(simple_eval("1 til 7 by 3 join ','"), Obj::from("1,4"));
    assert_eq!(simple_eval("1 to 7 by 3 join ','"), Obj::from("1,4,7"));
}

#[test]
fn evil_operators() {
    assert_eq!(simple_eval("2 + 5 * 3"), i(17));
    assert_eq!(simple_eval("+, * = *, +; 2 + 5 * 3"), i(13));
    assert_eq!(
        simple_eval(
            "+['precedence'], *['precedence'] = *['precedence'], +['precedence']; 2 + 5 * 3"
        ),
        i(21)
    );
    assert_eq!(simple_eval("+, * = *, +; +['precedence'], *['precedence'] = *['precedence'], +['precedence']; 2 + 5 * 3"), i(16));
}

#[test]
fn math() {
    assert_eq!(simple_eval("7 + 4"), i(11));
    assert_eq!(simple_eval("7 - 4"), i(3));
    assert_eq!(simple_eval("7 * 4"), i(28));
    assert_eq!(simple_eval("7 / 4"), Obj::from(1.75));
    assert_eq!(simple_eval("7 % 4"), i(3));
    assert_eq!(simple_eval("7 // 4"), i(1));
    assert_eq!(simple_eval("7 %% 4"), i(3));
}

#[test]
fn fractions() {
    assert_eq!(simple_eval("numerator! 35 / 28"), i(5));
    assert_eq!(simple_eval("denominator! 35 / 28"), i(4));
    assert_eq!(simple_eval("x / y := 35 / 28; x * y"), i(20));
}

#[test]
fn bitwise() {
    assert_eq!(simple_eval("7 & 4"), i(4));
    assert_eq!(simple_eval("7 | 4"), i(7));
    assert_eq!(simple_eval("7 ~ 4"), i(3));
    assert_eq!(simple_eval("7 ⊕ 4"), i(3));
    assert_eq!(simple_eval("~4"), i(-5));
    assert_eq!(simple_eval("7 << 4"), i(112));
    assert_eq!(simple_eval("7 >> 4"), i(0));
}

#[test]
fn len() {
    assert_eq!(simple_eval("len([2, 5, 3])"), i(3));
    assert_eq!(simple_eval("len(1 to 10)"), i(10));
}

#[test]
fn lists() {
    assert_eq!(simple_eval("[1, 2] ++ [3, 4] join ''"), Obj::from("1234"));
    assert_eq!(simple_eval("[1, 2, 3] +. 4 join ''"), Obj::from("1234"));
    assert_eq!(simple_eval("1 .+ [2, 3, 4] join ''"), Obj::from("1234"));
    assert_eq!(simple_eval("[1, 2] ** 3 join ''"), Obj::from("121212"));
    assert_eq!(simple_eval("1 .* 3 join ''"), Obj::from("111"));
    assert_eq!(simple_eval("1 .. 2 join ''"), Obj::from("12"));
    assert_eq!(
        simple_eval("[1, 2] ** [3, 4] then flatten join ''"),
        Obj::from("13142324")
    );
    assert_eq!(
        simple_eval("[1, 2] ^^ 3 then flatten join ''"),
        Obj::from("111112121122211212221222")
    );
    assert_eq!(simple_eval("sort([2, 5, 3]) join ''"), Obj::from("235"));
    assert_eq!(simple_eval("reverse([2, 5, 3]) join ''"), Obj::from("352"));
}

#[test]
fn indexing() {
    assert_eq!(simple_eval("(1 to 10)[2]"), i(3));
    assert_eq!(simple_eval("(1 to 10)[-2]"), i(9));
    assert_eq!(simple_eval("(1 to 10)[2:4] join ''"), Obj::from("34"));
    assert_eq!(simple_eval("x := 1 to 10; x[2] = 4; x[2]"), i(4));
    assert_eq!(
        simple_eval("x := [[0] ** 10] ** 10; x[1][2] = 3; x[2][2] = 4; x[1][2] $ x[2][2]"),
        Obj::from("34")
    );
}

#[test]
fn dicts() {
    assert_eq!(simple_eval("len({1, 2} || {3, 4})"), i(4));
    assert_eq!(simple_eval("len({1, 2} || {3, 2})"), i(3));
    assert_eq!(simple_eval("len({1, 2} && {3, 4})"), i(0));
    assert_eq!(simple_eval("len({1, 2} && {3, 2})"), i(1));
    assert_eq!(simple_eval("len({1, 2} -- {3, 4})"), i(2));
    assert_eq!(simple_eval("len({1, 2} -- {3, 2})"), i(1));
    assert_eq!(simple_eval("len({1, 2} -. 2)"), i(1));
    assert_eq!(simple_eval("len({1, 2} -. 3)"), i(2));
    assert_eq!(simple_eval("len({1, 2} |. 3)"), i(3));
    assert_eq!(simple_eval("len({1, 2} |. 2)"), i(2));
    assert_eq!(simple_eval("{1: 2, 3: 4}[1]"), i(2));
    assert_eq!(simple_eval("{:5, 1: 2, 3: 4}[1]"), i(2));
    assert_eq!(simple_eval("{:5, 1: 2, 3: 4}[2]"), i(5));
    assert_eq!(simple_eval("({1: 2, 3: 4} |.. [5, 6])[5]"), i(6));
    assert_eq!(simple_eval("({1: 2, 3: 4} |.. [5, 6])[1]"), i(2));
    assert_eq!(simple_eval("({1: 2, 3: 4} |.. [1, 7])[1]"), i(7));
    assert_eq!(simple_eval("({1: 2, 3: 4} |.. [1, 7])[3]"), i(4));
    assert_eq!(simple_eval("{1: 2, 3: 4} !? 4"), Obj::Null);
    assert_eq!(simple_eval("1 ∈ {1: 2}"), i(1));
    assert_eq!(simple_eval("1 ∉ {1: 2}"), i(0));
    assert_eq!(simple_eval("2 ∈ {1: 2}"), i(0));
    assert_eq!(simple_eval("2 ∉ {1: 2}"), i(1));
}

#[test]
fn fast_append_pop() {
    assert_eq!(
        simple_eval(
            "x := []; for (i : 1 to 10000) x append= i; y := 0; for (i : 1 to 10000) y += pop x; y"
        ),
        i(50005000)
    );
}

#[test]
fn short_circuit() {
    assert_eq!(simple_eval("3 or x"), i(3));
    assert_eq!(simple_eval("0 and x"), i(0));
    assert_eq!(simple_eval("3 ∨ x"), i(3));
    assert_eq!(simple_eval("0 ∧ x"), i(0));
    assert_eq!(simple_eval("0 or 4"), i(4));
    assert_eq!(simple_eval("3 and 4"), i(4));
}

#[test]
fn comparisons() {
    assert_eq!(simple_eval("1 < 2"), i(1));
    assert_eq!(simple_eval("1 > 2"), i(0));
    assert_eq!(simple_eval("1 == 2"), i(0));
    assert_eq!(simple_eval("1 != 2"), i(1));
    assert_eq!(simple_eval("1 <= 2"), i(1));
    assert_eq!(simple_eval("1 >= 2"), i(0));
    assert_eq!(simple_eval("1 ≤ 2"), i(1));
    assert_eq!(simple_eval("1 ≥ 2"), i(0));
    assert_eq!(simple_eval("1 < 1.1"), i(1));
    assert_eq!(simple_eval("1.1 < 1"), i(0));
    assert_eq!(simple_eval("1 == 1.0"), i(1));
    assert_eq!(simple_eval("1 > 0.9"), i(1));
    assert_eq!(simple_eval("1 == 1 == 1"), i(1));
    assert_eq!(simple_eval("0 == 0 == 1"), i(0));
    assert_eq!(simple_eval("1 == 1 < 2 ≤ 3 <= 3 < 4 == 4"), i(1));
    assert_eq!(
        simple_eval("1 == 1 > 0 ≥ (-1) >= (-2) > (-3) == (-3)"),
        i(1)
    );
    assert_eq!(simple_eval("1 < 2 == 2"), i(1));
    assert_eq!(simple_eval("1 < (2 == 2)"), i(0));
    assert_eq!(simple_eval("(1 < 2) == 2"), i(0));
    assert_eq!(simple_eval("1 < 2 < 3"), i(1));
    assert_eq!(simple_eval("3 > 2 > 1"), i(1));
    assert_eq!(simple_eval("(-1) < 2 < 2"), i(0));
    assert_eq!(simple_eval("((-1) < 2) < 2"), i(1));
    assert_eq!(simple_eval("(-1) < (2 < 2)"), i(1));
}
#[test]
fn minmax() {
    assert_eq!(simple_eval("3 min 4"), i(3));
    assert_eq!(simple_eval("3 max 4"), i(4));
    assert_eq!(simple_eval("min(3 to 5)"), i(3));
    assert_eq!(simple_eval("max(3 to 5)"), i(5));
}

#[test]
fn opassigns() {
    assert_eq!(simple_eval("x := 3; x += 4; x"), i(7));
    assert_eq!(simple_eval("x := 3; x min= 2; x"), i(2));
    assert_eq!(
        simple_eval("x: list = [4, 6]; x map= (+1); product x"),
        i(35)
    );
}

#[test]
fn for_loops() {
    assert_eq!(simple_eval("x := 0; for (y : 1 to 5) x += y + 1; x"), i(20));
    assert_eq!(simple_eval("sum (for (y : 1 to 5) yield y + 1)"), i(20));
    assert_eq!(
        simple_eval("x := 0; for (i, y :: 1 to 5) x += i * y; x"),
        i(40)
    );
    assert_eq!(simple_eval("sum (for (i, x :: 1 to 5) yield i * x)"), i(40));
    assert_eq!(simple_eval("x := 0; for (y := 5) x += y + 1; x"), i(6));
}

#[test]
fn function_stuff() {
    assert_eq!(
        simple_eval("1 to 3 map (*3) >>> (2).subtract >>> (%5) >>> (+1) join '' then ($*2)"),
        Obj::from("253253")
    );
}

#[test]
fn bases() {
    assert_eq!(simple_eval("int_radix('105', 8)"), i(69));
    assert_eq!(simple_eval("str_radix(105, 16)"), Obj::from("69"));
    assert_eq!(simple_eval("base64encode B'aaa'"), Obj::from("YWFh"));
    assert_eq!(
        simple_eval("utf8decode! base64decode 'YWFh'"),
        Obj::from("aaa")
    );
    assert_eq!(simple_eval("hex_encode B'lox'"), Obj::from("6c6f78"));
    assert_eq!(
        simple_eval("utf8decode! hex_decode '6c6f78'"),
        Obj::from("lox")
    );
}

#[test]
fn random() {
    assert_eq!(simple_eval("0 <= random() < 1"), i(1));
    assert_eq!(simple_eval("random() != random()"), i(1));
    assert_eq!(simple_eval("5 <= random_range(5, 10) < 10"), i(1));
}
