## 1. Lean as a calculator

**`import`.** A Lean file begins by importing the modules it builds on. *Mathlib* is Lean's
library of formalized mathematics: numbers, finite sets, permutations, sums, and hundreds of
thousands of theorems about them. `import Mathlib` loads all of it. The library's own first
file, `Arnold/Defs.lean`, imports nothing, because it must compile into a fast program; we
import Mathlib at once, since we need it a few cells later.

```lean
import Mathlib
```

**`#eval`, `#check` and comments.** Commands that start with `#` ask Lean a question instead of
adding to the file. `#eval e` evaluates the expression `e` and prints the value. `#check e`
prints the *type* of `e`: every Lean expression has exactly one type, and Lean checks it before
doing anything else. Text after `--` up to the end of the line is a comment.

**Numbers and functions.** `Nat` is the type of natural numbers $0, 1, 2, \ldots$ Mathlib writes
it `ℕ` (type `\N` in an editor); the two names mean the same type. A numeral like `3` can stand
for a number of many types, and `(3 : ℕ)` says which one: this is a *type ascription*. A
function is applied by writing its argument after it, with a space and no parentheses:
`Nat.succ 4` is the successor of 4, and `max 3 7` applies `max` to two arguments. Subtraction on
`ℕ` stops at zero (`2 - 5 = 0`), `/` rounds down, and `%` is the remainder. `(a, b)` is the
pair of `a` and `b`; its type is written `A × B`. The arithmetic rules matter below,
because the formalization does a lot of arithmetic with bridge numbers.

```lean
#eval 2 + 3 * 4          -- 14
#eval (2 : ℕ) - 5        -- natural numbers stop at 0
#eval (17 / 5, 17 % 5)   -- quotient and remainder
#eval max 3 7
#check Nat.succ 4        -- the type of the expression, ℕ
#check (2 : ℕ) + 2 = 4   -- a statement is an expression too; its type is Prop
```

The last line shows the idea that the whole formalization rests on. `2 + 2 = 4` is an
expression whose type is `Prop`, the type of *propositions*. A proposition is a statement that
may or may not be true. To prove it is to build an expression whose type is that proposition, and
Lean checks such proofs exactly as it checks that `2 + 3 * 4` is a number.
