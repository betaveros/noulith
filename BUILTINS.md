# Noulith Builtins

## Arithmetic

### Binary Operators

All functions take two arguments and partially apply on the right if called with one argument, except for `-` and `~`. All functions vectorize on vectors.

| Function | Definition |
| - | - |
| `+` | Add
| `-` | Subtract, or negate with one argument
| `subtract` | Subtract
| `*` | Multiply
| `/` | Divide (produces exact fractions on two integers)
| `%` | Remainder (sign of dividend)
| `//` | Integer division with incompletely defined semantics, but if the divisor is positive the result floors, and pairs with `%%`
| `%%` | Modulo with incompletely defined semantics, but if the divisor is positive the result is nonegative, and pairs with `//`
| `/!` | Exact division; errors if there's a remainder
| `^` | Exponentiation
| `gcd` | Greatest common divisor
| `lcm` | Least common multiple
| `&` | Bitwise AND
| `\|` | Bitwise OR
| `~` | Bitwise XOR, or bitwise NOT with one argument
| `xor` | Bitwise XOR
| `<<` | Bitwise left shift
| `>>` | Bitwise right shift

### Unary Operators

- `abs` `floor` `ceil` `round`
- `signum`: -1, 0, or 1 depending on sign. Generalizes to complex numbers by returning the number on the unit circle with the same direction on nonzero complex numbers.
- `is_prime`, `even`, `odd`: 1 if satisfies the predicate, 0 else.
- `numerator`, `denominator`: retrieve an integer from a fraction
- `real_part`, `imag_part`: retrieve a float component from a complex number
- `complex_parts`: retrieve both float components from a complex number

All of these basically just naively lift the `f64 -> f64` function of the same name from Rust: `sin` `sinh` `cos` `cosh` `tan` `tanh` `asin` `asinh` `acos` `acosh` `atan` `atanh` `sqrt` `cbrt` `exp` `ln` `log10` `log2`

- `factorize`

We have `atan2` though it's not technically unary.

### Comparisons

`==` `!=` `<` `>` `<=` `>=` `max` `min`

These functions don't vectorize. Sequences are compared lexicographically.

`<=>` returns -1 if the left argument is less, 0 if they're equal, 1 if the left argument is greater. `>=<` does the opposite.

### Randomness

- `random`: [0.0, 1.0)
- `random_bytes(n)`: `n` random bytes
- `random_range(a, b)`: integer in [a, b)
- `shuffle`
- `choose`: random element

## Sequences

| Function | Args | Definition |
| - | - | - |
| `to` | 2 or 3 | Inclusive range. Third argument, which can be specified by chaining with `by`, specifies a step.
| `til` | 2 or 3 | Half-open range (inclusive of first argument, exclusive of second). Third argument, which can be specified by chaining with `by`, specifies a step.
| `len` | 1 | Length of a sequence.
| `only` | 1 | The only element in a sequence; errors if there are 0 or at least 2.
| `in`, `∈` | 2 | Test for presence of key in dictionary, or just element in sequence.
| `not_in`, `∉` | 2 | Test for absence of key in dictionary, or just element in sequence.
| `contains`, `∋` | 2 | Reversed test for presence of key in dictionary, or just element in sequence.
| `∌` | 2 | Reversed test for absence of key in dictionary, or just element in sequence.
| `transpose` | 2 | Transpose a sequence of sequences
| `set` | 1 | Convert to a "set" (dictionary with elements as keys, `null` as every value)
| `dict` | 1 | Convert sequence of key-value pairs to a dictionary
| `count_distinct` | 1 | Count distinct elements. It's just `len(set(...))` really.
| `items` | 1 | Sequence of key-value pairs in a dictionary.
| `keys` | 1 | Sequence of keys in a dictionary.
| `values` | 1 | Sequence of values in a dictionary.
| `enumerate` | 1 | Indexes counting from 0 zipped with a sequence.
| `unique` | 1 | Sequence of same type with duplicates removed; elements are ordered by their first appearance. (Some other languages call this `nub`.)
| `window` | 2 | List of same-type slices of a particular length in order, e.g. `([1, 2, 3, 4] window 2) == [[1, 2], [2, 3], [3, 4]]`
| `prefixes` | 2 | List of same-type slices from the start by increasing length, e.g. `prefixes([1, 2, 3]) == [[], [1], [1, 2], [1, 2, 3]]`
| `suffixes` | 2 | List of same-type slices until the end by increasing length, e.g. `suffixes([1, 2, 3]) == [[], [3], [2, 3], [1, 2, 3]]`
| `frequencies` | 1 | Dictionary of elements to how often they appear, e.g. `frequencies([1, 1, 2, 1]) == {:0, 1: 3, 2: 1}`
| `++` | 2 | Concatenate two lists or like sequences.
| `.+` | 2 | Prepend an element to a list.
| `+.` | 2 | Take a list and append an element.
| `..` | 2 | Make a two-element list.
| `.*`, `*.` | 2 | Make a list with n copies of something. The element is on the side of the `.`.
| `**` | any | Cartesian product
| `^^` | 2 | Cartesian "exponentiation", repeated Cartesian product with itself.
| `!!`, `index` | 2 | Index into a sequence or access a dict, i.e. `a !! b` is basically `a[b]`.
| `!?`, `index?` | 2 | Index into a sequence or access a dict or `null`.
| `find` | 2 | First element equalling a value or satisfying a predicate.
| `find?` | 2 | First element equalling a value or satisfying a predicate, or null
| `locate` | 2 | Index of first element equalling a value or satisfying a predicate.
| `locate?` | 2 | Index of first element equalling a value or satisfying a predicate, or null
| `first` | 1 | First element
| `second` | 1 | Second element
| `third` | 1 | Third element
| `last` | 1 | Last element
| `tail` | 1 | All but first element
| `butlast` | 1 | All but last element
| `uncons` | 1 | First and all-but-first element. Errors on empty argument
| `uncons?` | 1 | First and all-but-first element, or `null`
| `unsnoc` | 1 | All-but-last and last element. Errors on empty argument
| `unsnoc?` | 1 | All-but-last and last element, or `null`
| `take` | 2 | Take first n elements or while predicate is satisfied
| `drop` | 2 | Drop first n elements or while predicate is satisfied
| `sort` | 1 or 2 | Sort by optional comparator (often `<=> on` some key function)
| `sort_on` | 1 | Sort by key (Schwartzian)
| `reverse` | 1 |
| `\|\|` | 2 | Union dictionaries, right-biased
| `\|.` | 2 | Add key with value `null`
| `\|\|+` | 2 | Union dictionaries, merging values at key collisions with `+`
| `\|\|-` | 2 | Union dictionaries, merging values at key collisions with `-`
| `-.`, `discard` | 2 | Remove key
| `insert`, `\|..` | 2 | Add key-value pair
| `&&` | 2 | Intersect sets; keeps values from left
| `--` | 2 | Removes right keys from left dictionary

### Streams (~lazy sequences)

| Function | Args | Definition |
| - | - | - |
| `repeat` | 1 | Infinite lazy sequence that just repeats one element forever.
| `cycle` | 1 | Infinite lazy sequence that just cycles through elements of given sequence in order.
| `iota` | 1 | Infinite lazy sequence counting from given integer up by 1 forever.
| `permutations` | 1 | Permutations of given sequence.
| `combinations` | 2 | All length-n subsequences of given sequence.
| `subsequences` | 1 | All subsequences of given sequence.
| `iterate` | 2 | Infinite lazy sequence that starts with first argument as its first element. Each subsequent element is obtained by calling the second argument on the previous element. Use with caution — no guarantees if the second argument is impure.
| `lazy_map` | 2 | Lazy map where each element is obtained by calling the second argument on an element of the first. Gracefully terminates if the second argument `break`s. No guarantees if the second argument is impure.
| `lazy_filter` | 2 | Lazy filter, first by second. No guarantees if the second argument is impure.

### Strings

- `$`: n-ary (including 1) string concatenation, coerces all arguments to strings.
- `$$`: exactly binary string concatenation, for partial application
- `*$`, `$*`: string replication; the string is on the side of the `$`
- `chr`, `ord`: convert from an integer to a length-1 string and vice versa
- `upper` `lower`
- `is_upper` `is_alpha` `is_alnum` `is_digit` `is_space` `is_lower` `is_ascii`
- `utf8_decode`/`utf8_encode`
- `hex_decode`/`hex_encode`
- `base64_decode`/`base64_encode`
- `json_decode`/`json_encode`
- `compress`/`decompress`
- `join`: join a sequence of values by a string
- `split`: split a string by another
- `starts_with` `ends_with`
- `words`: split by runs of whitespace
- `unwords`: join by space
- `lines`: split by newlines; if a trailing newline exists, it's ignored
- `unlines`: join by newlines and add a trailing newline
- `strip` `strip_start` `strip_end`. Synonymous with `trim` etc.; I haven't decided yet.
- `search`: find a regex, or `null`. If the regex has capture groups then return a list of captured strings, else return the found string.
- `search_all`: find all nonoverlapping occurrences of a regex. If the regex has capture groups then return a list of lists of captured strings, else return a list of found strings.
- `replace`: replace a regex everywhere by a replacement string.
- `str_radix` `int_radix`

## Types

- `number`: `int` `rational` `float` `complex`
- `str` `list` `dict` `vector` `bytes`
- `stream`
- `func`
- `type`
- `anything`

The `is` functions tests if something is of a type e.g. `3 is int`

`satisfying` turns a predicate function into a type, somehow.

`repr` converts to string more verbosely

## Functions

### Composition or simple argument juggling

| Function | Args | Definition |
| - | - | - |
| `id` | 1 | Identity function, returns its sole argument.
| `const` | 2 | Constant function, always returns its second argument. Can be partially applied.
| `.` | 2 | Reverse function application; calls second argument on first.
| `then` | 2 | Reverse function application; calls second argument on first.
| `.>` | 2 | Reverse function application; calls second argument on first.
| `<.` | 2 | Function application; calls first argument on second.
| `apply` | 2 | Reverse "splatted" function application; first argument should be a sequence, calls second argument with that sequence's elements as arguments.
| `of` | 2 | "Splatted" function application; second argument should be a sequence, calls first argument with that sequence's elements as arguments.
| `>>>` | 2 | Function composition: `(f >>> g)(...) = g(f(...))`
| `<<<`, `∘` | 2 | Function composition: `(f <<< g)(...) = f(g(...))`
| `on` | 2 | Lifted function composition: `(f on g)(a1, a2, ...) = f(g(a1), g(a2), ...)`. Typical usage is to convert a "key function" into a comparator with `<=> on key_func`.
| `***` | any | Parallel function composition: `(f ||| g)(a1, a2) = [f(a1), g(a2)]`
| `&&&` | any | Fanout function composition: `(f &&& g)(...) = [f(...), g(...)]`
| `equals` | any | Wacky equality helper. `(f equals g)(...) = f(...) == g(...)` where if `f` or `g` are not functions they get used directly.

### Higher-order functions on sequences

Functions are usually the last argument.

| Function | Args | Definition |
| - | - | - |
| `each` | 2 | Call second function on each element of first
| `map` | 2 | (Eagerly) Map second function over each element of first
| `map_keys` | 2 | (Eagerly) Map second function over each key of first dictionary, preserving values, to produce a new dict
| `map_values` | 2 | (Eagerly) Map second function over each value of first dictionary, preserving keys, to produce a new dict
| `flatten` | 1 | Flatten one level, producing a list
| `flat_map` | 2 | (Eagerly) Map second function over each element of first and then flatten
| `filter` | 2 | New sequence of same type with only elements satisfying a predicate
| `filter_keys` | 2 | Filter keys of dictionary
| `filter_values` | 2 | Filter values of dictionary
| `filter_items` | 2 | Filter items of dictionary. Function gets two arguments, key and value
| `reject` | 2 | New sequence of same type with only elements not satisfying a predicate
| `partition` | 2 | List of two sequences of same type; the first has only the elements satisfying the predicate, the second has the rest
| `any` | 1 or 2 | Whether any element is truthy / satisfies the predicate
| `all` | 1 or 2 | Whether all elements are truthy / satisfy the predicate
| `count` | 1 or 2 | Number of elements that are truthy / satisfy the predicate
| `group` | 1 or 2 | Split up sequence into same-type sequences of adjacent elements that are equal / satisfy a binary relation with the previous/next item in the group. Second argument can also be a positive integer to just make the same-type sequences the same size (the last group may be short).
| `group'` | 1 or 2 | Same, but errors if the sequence's length isn't evenly divisible.
| `group_all` | 1 or 2 | Split up sequence into subsequences of elements that satisfy a binary relation with each other (`group` where elements don't have to be adjacent)
| `zip` | any | Zip two or more sequences with an optional function.
| `ziplongest` | any | Zip two or more sequences with an optional function. If a function is provided, it's used to reduce each batch of elements pairwise instead of just called with all at once.
| `pairwise` | 2 | Zip a sequence with its own tail via a function.
| `merge` | any | Merge two or more dictionaries, with an optional function. Without a function, values from later dictionaries overwrite earlier ones when their keys collide; with a function, the values are combined with it.
| `fold` | 2 or 3 | Fold a sequence by a function, with an optional starting value (chainable with `from`).
| `scan` | 2 or 3 | Like `fold`, but collect all intermediate values into a list instead of just the final result.
| `par_each` | 2 | Parallel each?
| `par_map` | 2 | Parallel map?

## Input/output

- `print`: Output arguments, separated by spaces, followed by a newline
- `echo`: Output arguments, separated by spaces
- `write`: Output arguments
- `input`: read one line
- `read`: read until EOF
- `read_compressed`: read gzipped
- `interact`: Read all input, call the argument with it, then output the result. If multiple arguments, just runs 'em left to right
- `interact_lines`: Read all input as a list of lines, call the argument with it, then output the result, one thing per line. If multiple arguments, just runs 'em left to right
- `flush` (stdout)
- `debug`: Debug output.

### Filesystem

- `read_file`
- `read_file?`
- `read_file_bytes`
- `read_file_bytes?`
- `list_files`
- `write_file`
- `append_file`

- `path_parent`
- `path_join`

### Other

- `run_process`
- `time`: time since epoch as a float
- `now`: dictionary with keys `"year", "month", "day", "hour", "minute", "second", "nanosecond"`; accepts one optional argument, a number of hours N to get UTC+N
- `sleep`
- `request` `request_bytes` `request_json`

## Cryptography

Most of these were specifically put here for Cryptopals.

- `aes128_hazmat_encrypt_block(16-byte key, 16-byte block)`
- `aes128_hazmat_decrypt_block(16-byte key, 16-byte block)`
- `aes256_gcm_encrypt(32-byte key, 12-byte nonce, plaintext)`
- `aes256_gcm_decrypt(32-byte key, 12-byte nonce, ciphertext)`
- `md5(bytes)`
- `sha256(bytes)`
- `blake3(bytes)`

## Metaprogramming (?) / misc

- `eval`
- `vars`: dictionary of all vars in the current environment (writing to it doesn't do anything)
- `assert`: assert a condition is true else throw an error
- `memoize`: make a function memoized
- `is_big`: does an int internally use the small int or big int representation
- `HtmlTag(tag_name, children, attributes)`: struct that gets rendered as an html element by the WASM frontend
