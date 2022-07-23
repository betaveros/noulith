An attempt to give myself a new Pareto-optional choice for quick-and-dirty scripts, particularly when I'm not on a dev computer, and to practice writing a more realistic programming language instead of the [overengineered stack-based nonsense](https://github.com/betaveros/paradoc) I spend too much time on. ([Crafting Interpreters](https://craftinginterpreters.com/) is such a good book, I have no excuses.)

## Features (and anti-features)

- Dynamically typed.
- Not whitespace- or indentation-sensitive (except for delimiting tokens, of course, but that does matter more than is common: operator symbols can be strung together freely like Haskell or Scala). In particular, newlines don't mean anything; semicolons everywhere. (I can foresee myself regretting this choice so we might revisit it later.)
- String concatenation is `++`. Or maybe `~` or something? Not sure yet.
- Only functions introduce scopes. Well, when they get implemented.
- Probably will be pretty TIMTOWDI because I don't want to remember if I chose `&&` or `and` for boolean operators. Just support both, whatever.
- Everything is an expression.
- No classes or members or whatever, it's just global functions all the way down. Or up.
- Operator precedence is resolved at runtime.
- At the highest level, statements are C/Java/Scala-style `if (condition) body else body`, `for (thing) body` (not the modern `if cond { body }`). The `if ... else` is the ternary expression.
- Lists just use brackets: `[a, b, c]`.
- For loops use colons: `for (x : xs) ...`. Use a double-colon for index-value (or key-value) pairs: `for (i, x :: xs) ...`. (Do I actually want this feature? Not sure yet...)
- Prefix operators are wonky. When in doubt, parenthesize the operand: `a + -(b)`; `x and not(y)`.
- Lambda will look like `\x, y: x + y` when they exist. Probably.

## Example

```
for (x : 1 to 100) (
  o = '';
  for (f, s : [[3, 'Fizz'], [5, 'Buzz']])
    if (x % f == 0)
      o = o ++ s;
  print(if (o == '') x else o)
)
```

Possibly supported one day:

```
for (x : 1 to 100) print([[3, 'Fizz'], [5, 'Buzz']] map (\(f, s): if (x % f == 0) s else "") join "" or x)
```
