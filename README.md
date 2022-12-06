An attempt to give myself a new Pareto-optional choice for quick-and-dirty scripts, particularly when I'm not on a dev computer, and to practice writing a more realistic programming language instead of the [overengineered stack-based nonsense](https://github.com/betaveros/paradoc) I spend too much time on. ([Crafting Interpreters](https://craftinginterpreters.com/) is such a good book, I have no excuses.)

## Elevator pitches (and anti-pitches)

- Immutable data structures (but not variables) means you can write `matrix = [[0] ** 10] ** 10; matrix[1][2] = 3` and not worry about it, instead of the `[[0] * 10 for _ in range(10)]` you always have to do in Python. You can also freely use things as keys in dictionaries. But, thanks to mutate-or-copy-on-write shenanigans behind the scenes (powered by Rust's overpowered reference-counting pointers), you don't have to sacrifice the performance you'd get from mutating lists. (There are almost certainly space leaks from cavalier use of `Rc` but shhhhh.)
- Everything is an infix operator; nearly everything can be partially applied. If you thought Scala had a lot of syntax sugar, wait till you see what we've got.

  ```
  noulith> 1 to 10 filter even map (3*)
  [6, 12, 18, 24, 30]
  ```

- Ever wanted to write `x max= y` while searching for some maximum value in some complicated loop? You can do that here. You can do it with literally any function.
- You know how Python has this edge case where you can write things like `{1}` and `{1, 2}` to get sets, but `{}` is a dictionary because dictionaries came first? We don't have that problem because we don't distinguish sets and dictionaries.
- Operator precedence is customizable and resolved at runtime.

  ```
  noulith> f := \-> 2 + 5 * 3
  noulith> f()
  17
  noulith> swap +, *
  noulith> f() # (2 times 5) plus 3
  13
  noulith> swap +["precedence"], *["precedence"]
  noulith> f() # 2 times (5 plus 3)
  16
  noulith> swap +, *
  noulith> f() # (2 plus 5) times 3
  21
  ```

  Imagine all the [operator parsing](https://adventofcode.com/2020/day/18) code you won't need to write. When you need like arbitrarily many levels of operator precedence, and are happy to `eval` inputs.

## How do you run this thing?

It's a standard Rust project, so, in brief:

- [Install Rust](https://www.rust-lang.org/tools/install) and set it up
- Clone this repository, `cd` to it
- `cargo run --release --features cli,request,crypto`

This will drop you into a REPL, or you can pass a filename to run it. If you just want to build an executable so you can alias it or add it to `$PATH`, just run `cargo build --release --features cli,request,crypto` and look inside `target/release`.

None of the command-line options to `cargo run` or `cargo build` are required; they just give you better run-time performance and features for a slower compile time and larger binary size. (Without `--release`, stack frames are so large that one of the tests overflows the stack...)

## Features (and anti-features) (and claims that will become false as I keep hacking on this)

- Dynamically typed.
- Not whitespace- or indentation-sensitive (except for delimiting tokens, of course, but that does matter more than is common: operator symbols can be strung together freely like Haskell or Scala). In particular, newlines don't mean anything; semicolons everywhere. (I can foresee myself regretting this choice so we might revisit it later.)
- Declare variables with `:=`. (I never would have considered this on my own, but then I read the [Crafting Interpreters design note](https://craftinginterpreters.com/statements-and-state.html#design-note) and was just totally convinced.)
- List concatenation is `++`. String concatenation is `$`. Maybe? Not sure yet.
- Things that introduce scopes: functions, loops, `switch`, `try`, apparently.
- Everything is an expression.
- No classes or members or whatever, it's just global functions all the way down. Or up.
- I already said this, but operator precedence is resolved at runtime.
- At the highest level, statements are C/Java/Scala-style `if (condition) body else body`, `for (thing) body` (not the modern `if cond { body }`). The `if ... else` is the ternary expression.
- Lists and dictionaries should look familiar from Python. Lists are brackets: `[a, b, c]`. Dictionaries are curly braces: `{a, b, c}`. We don't bother with a separate set type, but dictionaries often behave quite like their sets of keys.
- For loops use left arrows: `for (x <- xs) ...`. Use a double-headed arrow for index-value or key-value pairs: `for (i, x <<- xs) ...`.
- Prefix operators are wonky. When in doubt, parenthesize the operand: `a + -(b)`; `x and not(y)`.
- Lambdas look like `\x, y -> x + y`.

## Example

Somewhat imperative:

```
for (x <- 1 to 100) (
  o := '';
  for (f, s <- [[3, 'Fizz'], [5, 'Buzz']])
    if (x % f == 0)
      o $= s;
  print(if (o == '') x else o)
)
```

Somewhat functional:

```
for (x <- 1 to 100) print([[3, 'Fizz'], [5, 'Buzz']] map (\(f, s) -> if (x % f == 0) s else "") join "" or x)
```

## More in-depth tour

NOTE: I will probably keep changing the language and may not keep all this totally up to date.

Numbers, arithmetic operators, and comparisons mostly work as you'd expect, including C-style bitwise operators, except that:

- `^` is exponentiation. Instead, `~` as a binary operator is xor (but can still be unary as bitwise complement). Or you can just use `xor`.
- `/` does perfect rational division like in Common Lisp or something. `%` does C-style signed modulo. `//` does integer division rounding down, and `%%` does the paired modulo (roughly).
- The precedence is something somewhat reasonable and simpler, inspired by Go's precedence, rather than following C's legacy:

```
Tighter ^ << >>
        * / % &
        + - ~
        |
Looser  == != < > <= >=
```

We support arbitrary radixes up to 36 with syntax `36r1000 == 36^3`, plus specifically the slightly weird base-64 `64rBAAA == 64^3` (because in base-64 `A` is 0, `B` is 1, etc.)

Like in Python and mathematics, comparison operators can be chained like `1 < 2 < 3`; we explain how this works later. We also have `min`, `max`, and the three-valued comparison operator `<=>` and its reverse `>=<`.

End-of-line comments: `#` (not immediately followed by `(`). Range comments: `#( ... )`. Those count parentheses so can be nested.

Strings: `"` or `'`. (What will we use the backtick for one day, I wonder.) Also like in Python, we don't have a separate character type; iterating over a string just gives single-character strings.

Data types:

- Null
- Numbers: big integers, rationals, floats, and complex numbers, which coerce from left to right in that list as needed. Note that there are no booleans, we just use 0 and 1.
- Lists (heterogeneous): `[a, b]`. Pythonic indexing and slicing, both in syntax and semantics of negative integers. Assigning to slices is indefinitely unimplemented.
- Dictionaries (heterogeneous): `{a: b, c: d}`. (Valid JSON is valid Noulith, maybe modulo the same kind of weird whitespace issues that make valid JSON not valid JavaScript.) Values can be omitted, in which case they're just `null`, and are used like sets. Index `my_dict[key]`, test `key in my_dict`. If you add a `{:a}`, that's the default value.
- Strings: just what Rust has, always valid UTF-8 sequences of bytes
- Bytes
- Vectors: lists of numbers, notable in that most operations on these automatically vectorize/broadcast, e.g. `V(2, 3) + V(4, 5) == V(6, 8)`; `V(2, 3) + 4 == V(6, 7)`. (Note that comparison operators don't vectorize!)
- Streams: lazy lists, only generated in a few specific situations for now. Most higher-order functions are eager.
- Functions, which carry with them a precedence. Fun!
- Structs!

### Expressions

Everything is a global function and can be used as an operator! For example `a + b` is really just `+(a, b)`; `a max b` is `max(a, b)`. As a special case, `a b` (when fenced by other syntax that prevents treating either as binary operator) is `a(b)` (this is mainly to allow unary minus), but four or more evenly-many identifiers and similar things in a row like `(a b c d)` is illegal. (Also, beware that `a[b]` parses as indexing `b` into `a`, not `a([b])` like you might sometimes hope if you start relying on this too much.) Also:

- Many functions/operators that normally accept two arguments also accept just one and partially-apply it as their second, e.g. `+(3)` (which, as above, can be written `+3` in the right context) is a function that adds 3. (This is not special syntax, just opt-in from many functions; `+` is defined to take one or two arguments and if it takes one it partially applies itself.) Since `-` and `~` have unary overloads, we provide alternatives `subtract` and `xor` that do partially apply when called with one argument, just like in Haskell.
- If you call `a(b)` where `a` isn't a function but `b` is, `b` partially applies `a` as its first argument! It's just like Haskell sections. For a slightly more verbose / less mystical way to do this, you can use Scala-style `_`, see below.

(Sort of considering removing some of the partial application stuff now that `_`s work... hmm...)

Operator precedence is determined at runtime! This is mainly to support chained comparisons: `1 < 2 < 3` works like in Python. Functions can decide at runtime when they chain (though there's no way for user-defined functions to do this yet), and we use this to make a few other functions nicer. For example, `zip` and `**` (cartesian product) chain with themselves; `a ** b ** c` and `a zip b zip c` will give you a list of triplets, instead of a bunch of `[[x, y], z]`-shaped things.

Identifiers can consist of a letter or `_` followed by any number of alphanumerics, `'`, or `?`; or any consecutive number of valid symbols for use in operators, including `?`. (So e.g. `a*-1` won't work because `*-` will be parsed as a single token. `a* -1` won't work either, but for a different reason — it parses like it begins with calling `*` with `a` and `-` as arguments. `a*(-1)` or `a* -(1)` would work.) Compared to similar languages, note that `:` is not a legal character to use in operators, while `$` is. In addition, a bunch of keywords are forbidden, as are all single-letter uppercase letters and tokens beginning with single-letter uppercase letters immediately followed by a single quote (though these are just reserved and the language doesn't recognize all of them yet); `=`, `!`, `...`, `<-`, `->`, and `<<-`. Also, with the exception of `==` `!=` `<=` and `>=`, operators ending in `=` will be parsed as the operator followed by an `=`, so in general operators cannot end with `=`.

Almost all builtin functions' precedences are determined by this Scala-inspired rule: Look up each character in the function's name in this table, then take the *loosest* precedence of any individual character. But note that this isn't a rule in the syntax, it's just a strategy I decided to follow when selecting builtin functions' precedences. For example, `+`, `++`, `.+`, and `+.` all have the same precedence. As of time of writing, the only exceptions to this rule are `<<` and `>>`, which have precedence like `^`.

```
Tighter . (every other symbol, mainly @ which I haven't allocated yet)
        !?
        ^
        */%&
        +-~
        |
        $
        =<>
Looser  (alphanumerics)
```

`.` is not special syntax, it's actually just an operator that does tightly-binding reverse function application! `a.b = b(a)`. `then` is loosely-binding reverse function application.

`!` is syntax that's spiritually sort of like what Haskell's `$` lets you write. It's as tight as an opening parenthesis on its left, but performs a function call that lets you can omit the closing one up to the next semicolon or so. `f! a, b` is `f(a, b)`.

`_` is special; assigning to it discards (but type checks still happen; see below). Some expressions produce Scala-style anonymous functions, e.g. `1 < _ < 3`, `[_, 2]`, `_[3]`. I might implement more later.

Types double as conversion functions: `str(3)` `int(3)` `dict([[1, 2], [3, 4]])` etc. Bending internal consistency for pure syntax sweetness, `to` is overloaded to takes a type as its second argument to call the same conversion. Test types explicitly with `is`: `3 is int`, `int is type`. The type of `null` is `nulltype`. Strings are `str` and functions are `func`. The "top" type is `anything`.

We got `eval`, a dumb dynamic guy; `import`, a stupid transclusion right now; `vars` for examining local variables; `assert`, which is currently a silly function and will probably become a keyword so it can inspect the expression being asserted.

`freeze` is a wonky keyword that goes through an expression and eagerly resolves each free variable to what it points to outside. It can slightly optimize some functions, surface some name errors earlier, and more elegantly(??) handle some binding acrobatics that you might have to write IIFEs for in other languages.

### Variables and assignments

Declare with `:=`, assign with `=`. (Statements must be separated by semicolons.)

```
x := 0; x = 1
```

Actually `:=` is just a declaration with an empty type. You can declare typed variables like:

```
x : int = 3
```

Pythonically, sequences can be unpacked with commas, including a single trailing comma for a single-element unpack. Type annotations are looser than commas, so below, `x` and `y` are both ints. Prefix `...` to pack/unpack multiple things, and likewise in function calls.

```
x, y : int
```

You can declare in an assignment with a parenthesized annotation.

```
a := 0
a, (c:) = 1, 2
a, (d:int) = 3, 4
```

These are checked at runtime! Assigning non-`int`s to x will throw an error. Hopefully. This is useful in other scenarios.

You can also do operator-assignments like you'd expect, with *any* operator! `a f= b` is basically just `a = f(a, b)`. Note that the left side is parsed just like a call `a(f)`, so the operator can even be parenthesized: after

```
x := [1, 2]; x (zip+)= [3, 4]
```

`x` is `[4, 6]`. In particular when you want to write `a = f(a)` you can just write `a .= f` because `.` is function application.

One corner case in the semantics here: While the operator is being called, the LHS variable will be null. That is, the following code will print `null`:

```
x := 0
f := \a: (print x; a)
x .= f
```

This allows us to not have to keep an extra copy of the LHS variable in common cases where we "modify" it, so code like `x append= y` is actually efficient (see discussion of immutability below).

The weird keyword `every` lets you assign to or operate on multiple variables or elements of a slice at once. This initializes three variables to `1`. This doesn't work with operator-assignments, though it might in the future.

```
every a, b, c := 1
```

After this, `x == [0, 0, 1, 1, 0]`.

```
x := [0] ** 5; every x[2:4] = 1
```

Important note about assignment: **All data structures are immutable.** When we mutate indexes, we make a fresh copy to mutate if anything else points to the same data structure. So for example, after

```
x := [1, 2, 3];
y := x;
x[0] = 4
```

`y` will still be `[1, 2, 3]`. You may wish to think of `x[0] = 4` as syntax sugar for `x = [4] ++ x[1:]`, although when nothing else refers to the same list, it's actually as fast as a mutation.

As a consequence, calling a function on a data structure cannot mutate it. There are a few special keywords that mutate whatever they're given. There's `swap` like `swap x, y` for swapping two values; there's `pop` and `remove` for mutating sequences; and the crudest instrument of all, `consume` gives you the value after replacing it in where it came from with `null`. After

```
x := [1, 2, 3, 4, 5];
y := pop x;
z := remove x[0]
```

`y` will be `5`, `z` will be `a`, and `x` will be `[2, 3, 4]`. There's no way to implement `pop` as a function yourself; the best you could do is take a list and separately return the last element and everything before it.

You can implement your own "mutable data cells" easily (?) with a closure:

```
make_cell := \init: (x := init; [\: x, \y: (x = y)])
get_a, set_a := make_cell(0)
```

### Control Flow

As above: statements must be separated by semicolons.

Everything is an expression, so the "ternary expression" and if/else statement are one and the same: `if (a) b else c`. Loops: `for (var <- list) body`; `while (cond) body`. For loops can have many iteration clauses: `for (a <- b; c <- d)`. Several other clauses are supported: `for (p <<- m)` iterates over index-value or key-value pairs, `for (x := y)` declares a variable in the middle, and `for (if x)` is a guard. Finally `for` loops can `yield` (only the entire body, not inside a more complicated expression) to turn into a list comprehension, like Scala: `for (x <- xs) yield x + 1`.

There are no "blocks"; just use more parentheses: `if (a) (b; c; d)`.

We have short-circuiting, quite-low-precedence `and` and `or`. We also have `coalesce`, which is similar to `or`, but it only takes its RHS if its LHS is precisely `null`, not other falsy things. Note `not` is just a normal function.

Switch:

```
switch (x)
case 1 -> b
case 2 -> d
```

Run-time type checking does some work here:

```
switch (x)
case _: int -> print("it's an int")
case _ -> print("not sure")
```

Stupid complicated runtime types with `satisfying`:

```
switch (x)
case _: satisfying! 1 < _ < 9 -> print("it's between 1 and 9")
case _ -> print("not sure")
```

Don't do weird things in the argument to `satisfying`, it's illegal. (Also actually you can just write this because the comparison operators `<` have yet another layer of magic — `1 < _ < 9` is *not* a lambda here; you could have actually replaced `_` with a named variable to bind it.)

```
switch (x)
case 1 < _ < 9 -> print("it's between 1 and 9")
case _ -> print("not sure")
```

Try-catch: `try a catch x -> y`.

`break` `continue` `return` work.

Only lambdas exist, declare all functions this way: `\a, b -> c`. You can annotate parameters and otherwise pattern match in functions as you'd expect: `\a: int, (b, c) -> d`.

### Structs

Super bare-bones product types right now. No methods or namespaces or anything. (Haskell survived without them for a few decades, we can procrastinate.) You can't even give fields types or default values.

```
struct Foo (bar, baz);
```

Then you can construct an all-null instance `Foo()` or all values with `Foo(a, b)`. `bar` and `baz` are now member access functions, or if you have a `foo` of type `Foo`, you can access, assign, or modify the fields as `foo[bar]` and `foo[baz]`. To be clear, these names really are not namespaced at all; `bar` and `baz` are new variables holding functions in whatever scope you declared this struct in, and can be passed around as functions in their own right, assigned to variables, etc. (but won't work on any other struct).

### Sequence operators

`len` for length.

Most operators for working with lists/dictionaries/other sequences are two characters, doubled or involving a `.` on the side of an individual element:

- List concatenation is `++`. You can combine individual elements with lists with `+.`, `.+`, and `..`, e.g. `[1, 2] +. 3 == [1, 2, 3]`
- Replicate is `.*`, e.g. `2 .* 3 == [2, 2, 2]`. List multiplication or (n-ary) cartesian product is `**`. Cartesian exponentiation (?) is `^^`.
- Dictionary union, intersection, and subtraction are `||`, `&&`, and `--`; `|.` and `|..` and `-.`.
- Indexing, alternatives to `a[b]` syntax: `!!` and `!?` for or-null (these are Haskell-isms roughly); `!%` for mod the length.
- `tail` `first` `second` `third` `last` `take` `drop`
- Get keys, values: `keys`, `values`. Get index/key-value pairs: `enumerate`, `items`.
- String concatenation is `$`. It has quite low precedence and coerces things to strings. String multiplication `$*` / `*$`.
- Ranges: `a til b` is exclusive, `a to b` is inclusive. Both use chaining to allow `a til b by c`. `iota a` counts from `a` up. These are all lazy.
- `sort`, `reverse`, `unique`. `set` "converts to a set". `transpose`. `prefixes` `suffixes` `frequencies`
- `upper`, `lower`; `is_upper`, ...
- strings: `split`, `join`, `strip`, `starts_with`, `ends_with`. Split always takes two arguments, a string and a separator, common splits and joins are like in Haskell, `words`/`unwords`/`lines`/`unlines`.

Some functions to make streams: `repeat` `cycle` `permutations` `combinations` `subsequences`

`start iterate func` swallows, plus you can cause weird borrow errors if the function is weird. Don't do this:

```
x := iterate! 0, \t -> x const t
x[0] = 0
```

### Functional programming

All the usuals and some weird ones: `each`, `map`, `flat_map`, `filter`, `reject`, `any`, `all`, `find`/`find?`, `locate`/`locate?` (finds the index of something), `count`, `take`, `drop`, `zip`, `sort`, `group`. These take the function as the second argument / on the right! Also they're eager!

`zip`, `group`, `window` have overloads that don't take functions.

`zip` is n-ary and can take a function to zip with too (which gets all arguments); you can also use `with`. `merge` is similar but for like-keyed entries of dictionaries. `ziplongest` is like `zip`, but, well, the longest; and when there's a function it's used to reduce all the remaining elements, two at a time, instead of called with all of them at once.

`fold`/`reduce` (which are the same) require a nonempty sequence with two arguments, but also chain with an optional `from` starting value, e.g. `x fold * from 1`.

`sort` takes a three-valued comparator, which you can get by `<=> on` some key function. Or `>=<` for backwards. Sorry, no built-in Schwartzian transform yet.

```
[[1], [2, 3, 4], [5, 6]] sort_by (<=> on len)
\1: [[1], [5, 6], [2, 3, 4]]
```

Other goodies: `id`, `const` (returns its second argument!), `flip`. Some Haskell-Arrow-esque operators exist: `&&&`, `***`, `>>>`, `<<<`. The first two are n-ary like `zip`.

### I/O and interfacing with the world

- `print`: space-separated newline-terminated
- `echo`: space-separated
- `write`: just concatenated
- `debug`: debug

- `input`: read line
- `read`: read all

- `read_file` `read_file?` `read_file_bytes` `read_file_bytes?`
- `write_file` `append_file` These take the file as the second argument to better support partial application, but I feel like I'll regret this soon.
- (current implementation completely disrespects cross-OS unicode things) `path_join` `path_parent`

- `time` `now`

If compiled with `request`:

- `request("https://httpbin.org/", {"method": "POST", "headers": {"Foo": "Bar"}})`
