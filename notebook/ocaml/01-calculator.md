## 1. OCaml as a calculator

A code cell holds OCaml *phrases*. For each one, the toplevel prints its type and its value:
`- : int = 14` says the value is the integer 14. Comments are written `(* … *)`.

**Numbers.** `int` is a 63-bit integer: `max_int` is $2^{62} - 1$, and arithmetic past it wraps
round silently. `/` divides and rounds toward zero, and `mod` is the remainder. Floating-point
numbers have their own type, `float`, and their own operators `+.`, `*.`, `/.`; OCaml never
mixes the two silently.

```ocaml
2 + 3 * 4
```

```ocaml
max_int
```

```ocaml
(17 / 5, 17 mod 5, 17. /. 5.)
```

The last cell is a *tuple*. Its type, `int * int * float`, lists the types of its parts.

**`let` and printing.** `let name = expr` gives a value a name for the rest of the notebook.
`let x = a in e` names `a` only inside the expression `e`. `Printf.printf` prints with a format
string: `%d` is an integer, `%s` a string, `%.1f` a float with one decimal, `\n` a new line, and
`%!` flushes the output so that it appears at once. Strings are joined with `^`.

```ocaml
let q, r = 17 / 5, 17 mod 5
let () = Printf.printf "17 = 5 * %d + %d %s\n%!" q r ("(" ^ "checked" ^ ")")
```

The first line also *destructures* a tuple: the pattern `q, r` names its two parts. The second
binds the pattern `()`, the only value of type `unit`. That is the usual way to run something
for its effect, here printing.

**Truth values.** `bool` has the values `true` and `false`. `=` and `<>` test equality and
inequality of any two values of the same type, comparing their structure. `&&`, `||` and `not`
combine truth values.

```ocaml
(3 < 5, 3 = 5, 3 <> 5, not (3 < 5) || true)
```
