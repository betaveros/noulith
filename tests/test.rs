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
        simple_eval("fact := \\n -> if (n == 0) 1 else n * fact(n - 1); fact 10"),
        i(3628800)
    );
    assert_eq!(
        simple_eval("(for (x <- 1 to 15) yield (o := ''; for (f, s <- [[3, 'Fizz'], [5, 'Buzz']]) if (x % f == 0) o $= s; if (o == '') x else o)) join ';'"),
        Obj::from("1;2;Fizz;4;Buzz;Fizz;7;8;Fizz;Buzz;11;Fizz;13;14;FizzBuzz")
    );
}

#[test]
fn quick_operators() {
    assert_eq!(simple_eval("2 + 3"), i(5));
    assert_eq!(simple_eval("+(2, 3)"), i(5));
    assert_eq!(simple_eval("plus := +; 2 plus 3"), i(5));
    assert_eq!(simple_eval("plus := \\x, y -> x + y; 2 plus 3"), i(5));
}

#[test]
fn splat_call() {
    assert_eq!(simple_eval("f := \\...x -> len(x); f()"), i(0));
    assert_eq!(simple_eval("f := \\...x -> len(x); f(1)"), i(1));
    assert_eq!(simple_eval("f := \\...x -> len(x); f(1, 2)"), i(2));
    assert_eq!(simple_eval("f := \\...x -> len(x); f(...[1, 2])"), i(2));
    assert_eq!(simple_eval("f := \\...x -> len(x); f(1, ...[2])"), i(2));
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
    assert_eq!(
        simple_eval("a, b, ...x, c := 1 to 6; [a, b, x join '', c] join ','"),
        Obj::from("1,2,345,6")
    );
    assert_eq!(simple_eval("[x] := [2]; x"), i(2));
    assert_eq!(simple_eval("x, := 2,; x"), i(2));
    assert_eq!(simple_eval("x, := [2]; x"), i(2));
    assert_eq!(simple_eval("[x] := 2,; x"), i(2));
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
    assert_eq!(simple_eval("sort([2, 5, 3]) join ''"), Obj::from("235"));
    assert_eq!(simple_eval("reverse([2, 5, 3]) join ''"), Obj::from("352"));
    assert_eq!(
        simple_eval("uncons([2, 5, 3]) join ''"),
        Obj::from("2[5, 3]")
    );
    assert_eq!(
        simple_eval("unsnoc([2, 5, 3]) join ''"),
        Obj::from("[2, 5]3")
    );
    assert_eq!(
        simple_eval("uncons?([2, 5, 3]) join ''"),
        Obj::from("2[5, 3]")
    );
    assert_eq!(
        simple_eval("unsnoc?([2, 5, 3]) join ''"),
        Obj::from("[2, 5]3")
    );
    assert_eq!(simple_eval("uncons?([])"), Obj::Null);
    assert_eq!(simple_eval("unsnoc?([])"), Obj::Null);
}

#[test]
fn more_lists() {
    assert_eq!(
        simple_eval("[1,2,3,4,5,6,7] group 3 map (join '') join ','"),
        Obj::from("123,456,7")
    );
    assert_eq!(
        simple_eval("[1,2,3,4,5].prefixes map (join '') join ','"),
        Obj::from(",1,12,123,1234,12345")
    );
    assert_eq!(
        simple_eval("[1,2,3,4,5].suffixes map (join '') join ','"),
        Obj::from(",5,45,345,2345,12345")
    );
    assert_eq!(
        simple_eval("[1,3,5,7,2,4,6] sort >=< join ''"),
        Obj::from("7654321")
    );
    assert_eq!(
        simple_eval("[1,2,3,4,5,6,7] window 3 map (join '') join ','"),
        Obj::from("123,234,345,456,567")
    );
}

#[test]
fn strings() {
    assert_eq!(simple_eval("'1234'[2]"), Obj::from("3"));
    assert_eq!(simple_eval("ord('β')"), i(946));
    assert_eq!(simple_eval("chr(946)"), Obj::from("β"));
}

#[test]
fn streams() {
    assert_eq!(
        simple_eval("[1, 2] ^^ 3 map (join '') join ','"),
        Obj::from("111,112,121,122,211,212,221,222")
    );
    assert_eq!(
        simple_eval("permutations([1, 2, 3]) map (join '') join ','"),
        Obj::from("123,132,213,231,312,321")
    );
    assert_eq!(
        simple_eval("combinations([1, 2, 3, 4, 5], 2) map (join '') join ','"),
        Obj::from("12,13,14,15,23,24,25,34,35,45")
    );
    assert_eq!(
        simple_eval("subsequences([1, 2, 3]) map (join '') join ','"),
        Obj::from(",3,2,23,1,13,12,123")
    );
    assert_eq!(simple_eval("len! (1 to 6) ^^ 7 drop 12345"), i(267591));
    assert_eq!(
        simple_eval("len! permutations(1 to 10) drop 12345"),
        i(3616455)
    );
    assert_eq!(
        simple_eval("len! combinations(1 to 10, 5) drop 100"),
        i(152)
    );
    assert_eq!(simple_eval("len! subsequences(1 to 10) drop 100"), i(924));
}

#[test]
fn indexing() {
    assert_eq!(simple_eval("(1 to 10)[2]"), i(3));
    assert_eq!(simple_eval("(1 to 10)[-2]"), i(9));
    assert_eq!(simple_eval("(1 to 10)[2:4] join ''"), Obj::from("34"));
    assert_eq!(simple_eval("(1 to 10)[-4:-2] join ''"), Obj::from("78"));
    assert_eq!(simple_eval("(1 to 10)[4:2] join ''"), Obj::from(""));
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
            "x := []; for (i <- 1 to 10000) x append= i; y := 0; for (i <- 1 to 10000) y += pop x; y"
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
    assert_eq!(
        simple_eval("x: str = 'foo'; x[0] .= upper; x"),
        Obj::from("Foo")
    );
    assert_eq!(
        simple_eval("x: vector = V(4, 6); x .= (+1) >>> vector; product x"),
        i(35)
    );
    assert_eq!(
        simple_eval("x: vector = V(4, 6); x[0] += 1; product x"),
        i(30)
    );
}

#[test]
fn sections_etc() {
    assert_eq!(simple_eval("(+4) 7"), i(11));
    assert_eq!(simple_eval("(7-) 4"), i(3));
    assert_eq!(simple_eval("(_[1])([2, 5, 3])"), i(5));
    assert_eq!(simple_eval("(_[1:3])([2, 5, 3, 9, 9, 9]).sum"), i(8));
    assert_eq!(
        simple_eval("[4, 5] map [_, 3] map (apply ^) then sum"),
        i(189)
    );
}

#[test]
fn for_loops() {
    assert_eq!(
        simple_eval("x := 0; for (y <- 1 to 5) x += y + 1; x"),
        i(20)
    );
    assert_eq!(simple_eval("sum (for (y <- 1 to 5) yield y + 1)"), i(20));
    assert_eq!(
        simple_eval("x := 0; for (i, y <<- 1 to 5) x += i * y; x"),
        i(40)
    );
    assert_eq!(
        simple_eval("sum (for (i, x <<- 1 to 5) yield i * x)"),
        i(40)
    );
    assert_eq!(
        simple_eval("for (i, x <<- 1 to 5) yield i * x into sum"),
        i(40)
    );
    assert_eq!(
        simple_eval("for (i, x <<- 1 to 5) yield i * x into \\s -> sum s"),
        i(40)
    );
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
fn basic_hofs() {
    assert_eq!(
        simple_eval("1 to 10 map - join ''"),
        Obj::from("-1-2-3-4-5-6-7-8-9-10")
    );
    assert_eq!(
        simple_eval("1 to 10 filter even join ''"),
        Obj::from("246810")
    );
}

#[test]
fn folds() {
    assert_eq!(simple_eval("1 to 10 fold +"), i(55));
    assert_eq!(simple_eval("1 to 10 fold + from 1000"), i(1055));
    assert_eq!(simple_eval("1 to 10 then sum"), i(55));
    assert_eq!(simple_eval("1 to 10 sum (+1)"), i(65));
    assert_eq!(simple_eval("1 to 10 then product"), i(3628800));
    assert_eq!(simple_eval("1 to 10 product (+1)"), i(39916800));
    assert_eq!(simple_eval("1 to 5 count even"), i(2));
    assert_eq!(simple_eval("1 to 5 any even"), i(1));
    assert_eq!(simple_eval("1 to 5 all even"), i(0));
    assert_eq!(simple_eval("1 to 10 by 2 any even"), i(0));
    assert_eq!(simple_eval("1 to 10 by 2 any odd"), i(1));
    assert_eq!(simple_eval("1 to 10 by 2 all even"), i(0));
    assert_eq!(simple_eval("1 to 10 by 2 all odd"), i(1));

    assert_eq!(
        simple_eval("for (i <- 1 to 10) yield even(i) into count"),
        i(5)
    );
    assert_eq!(simple_eval("for (i <- 1 to 10) yield i into sum"), i(55));
    assert_eq!(
        simple_eval("for (i <- 1 to 10) yield i into product"),
        i(3628800)
    );
}

#[test]
fn short_circuiting_folds() {
    assert_eq!(
        simple_eval("its := 0; [1 to 10 all \\i -> (its += 1; i < 3), its] join ','"),
        Obj::from("0,3")
    );
    assert_eq!(
        simple_eval("its := 0; [1 to 10 any \\i -> (its += 1; i >= 3), its] join ','"),
        Obj::from("1,3")
    );
    assert_eq!(
        simple_eval(
            "its := 0; [for (i <- 1 to 10) yield (its += 1; i < 3) into all, its] join ','"
        ),
        Obj::from("0,3")
    );
    assert_eq!(
        simple_eval(
            "its := 0; [for (i <- 1 to 10) yield (its += 1; i >= 3) into any, its] join ','"
        ),
        Obj::from("1,3")
    );
    assert_eq!(
        simple_eval(
            "its := 0; [for (i <- 1 to 10) yield (its += 1; i < 3) into count, its] join ','"
        ),
        Obj::from("2,10")
    );
}

#[test]
fn bases() {
    assert_eq!(simple_eval("int_radix('105', 8)"), i(69));
    assert_eq!(simple_eval("str_radix(105, 16)"), Obj::from("69"));
    assert_eq!(simple_eval("base64_encode B'aaa'"), Obj::from("YWFh"));
    assert_eq!(
        simple_eval("utf8_decode! base64_decode 'YWFh'"),
        Obj::from("aaa")
    );
    assert_eq!(simple_eval("hex_encode B'lox'"), Obj::from("6c6f78"));
    assert_eq!(
        simple_eval("utf8_decode! hex_decode '6c6f78'"),
        Obj::from("lox")
    );
}

#[test]
fn random() {
    assert_eq!(simple_eval("0 <= random() < 1"), i(1));
    assert_eq!(simple_eval("random() != random()"), i(1));
    assert_eq!(simple_eval("5 <= random_range(5, 10) < 10"), i(1));
}

#[test]
fn try_() {
    assert_eq!(simple_eval("try throw 3 catch x -> x + 4"), i(7));
    assert_eq!(simple_eval("try throw 3 catch x: int -> x + 4"), i(7));
    assert_eq!(simple_eval("try throw [4, 5] catch x, y -> x + y"), i(9));
}

#[test]
fn switch() {
    assert_eq!(simple_eval("switch (2) case 2 -> 8"), i(8));
    assert_eq!(
        simple_eval("switch (2) case 5 -> 3 case _ -> null"),
        Obj::Null
    );
    assert_eq!(simple_eval("switch (2) case 4 -> 6 case 2 -> 1"), i(1));
    assert_eq!(simple_eval("switch (2) case _ < 3 -> 8"), i(8));
    assert_eq!(
        simple_eval("switch (3) case _ < 3 -> 8 case _ -> null"),
        Obj::Null
    );
    assert_eq!(
        simple_eval("switch (2) case _: str -> 1 case _: vector -> 3 case x: int -> x * 2"),
        i(4)
    );
    assert_eq!(simple_eval("switch ([1, 2, 3]) case a, b -> 1 case a, 1, b -> 2 case a, 2, 2 -> 3 case a, 2, b -> a + b"), i(4));
}
