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
  noulith> f := \: 2 + 5 * 3
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

## Features (and anti-features) (and claims that will become false as I keep hacking on this)

- Dynamically typed.
- Not whitespace- or indentation-sensitive (except for delimiting tokens, of course, but that does matter more than is common: operator symbols can be strung together freely like Haskell or Scala). In particular, newlines don't mean anything; semicolons everywhere. (I can foresee myself regretting this choice so we might revisit it later.)
- Declare variables with `:=`. (I never would have considered this on my own, but then I read the [Crafting Interpreters design note](https://craftinginterpreters.com/statements-and-state.html#design-note) and was just totally convinced.)
- List concatenation is `++`. String concatenation is `$`. Maybe? Not sure yet.
- Functions and `for` loops introduce scopes, apparently.
- Probably will be pretty TIMTOWDI because I don't want to remember if I chose `&&` or `and` for boolean operators. Just support both, whatever.
- Everything is an expression.
- No classes or members or whatever, it's just global functions all the way down. Or up.
- I already said this, but operator precedence is resolved at runtime.
- At the highest level, statements are C/Java/Scala-style `if (condition) body else body`, `for (thing) body` (not the modern `if cond { body }`). The `if ... else` is the ternary expression.
- Lists and dictionaries should look familiar from Python. Lists are brackets: `[a, b, c]`. Dictionaries are curly braces: `{a, b, c}`. We don't bother with a separate set type, but dictionaries often behave quite like their sets of keys.
- For loops use colons: `for (x : xs) ...`. Use a double-colon for index-value (or key-value) pairs: `for (i, x :: xs) ...`. (Do I actually want this feature? Not sure yet...)
- Prefix operators are wonky. When in doubt, parenthesize the operand: `a + -(b)`; `x and not(y)`.
- Lambdas look like `\x, y: x + y`.

## Example

Somewhat imperative:

```
for (x : 1 to 100) (
  o := '';
  for (f, s : [[3, 'Fizz'], [5, 'Buzz']])
    if (x % f == 0)
      o $= s;
  print(if (o == '') x else o)
)
```

Somewhat functional:

```
for (x : 1 to 100) print([[3, 'Fizz'], [5, 'Buzz']] map (\(f, s): if (x % f == 0) s else "") join "" or x)
```
