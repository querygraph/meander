## 12. Using the whole library

The rest of the formalization is about 3,000 lines: the correspondence between accepted action
sequences and meanders, the bound by Catalan numbers, and the certified values. Rather than
replay it, we import the compiled library. A cell that begins with `import` starts a new file,
so everything above is set aside, and we refer to the library's names with their full prefix.

```lean
import Arnold
```

### Accepted sequences are meanders

To prove that the transfer matrix counts meanders, the library runs a richer *decorated*
machine alongside it. Each open arc also remembers the actual piece of river it leads into, and
forgetting the decorations gives back the plain machine. Two maps connect the two sides:

* `encode m l` is the action sequence that a river with crossing order `l` induces: each point
  opens its arc on a side exactly when the other end of that arc lies to the east.
* `decode m w` runs the decorated machine on an accepted sequence `w` and reads off the one
  remaining piece, which is the whole river.

`#check` prints the statements. `decode_spec` says that decoding an accepted sequence gives a
meander that encodes back to the same sequence. `encode_spec` says that a meander's sequence is
accepted and decodes back to the meander. Together they are a bijection, and the main theorem
follows. The `@` in `#check @f` shows the implicit arguments too.

```lean
#check @Arnold.TM.decode_spec
#check @Arnold.TM.encode_spec
#check @Arnold.TM.tmCountWith_eq
#check Arnold.TM.tmCount_eq
```

```lean
#print axioms Arnold.TM.tmCount_eq
```

### Values checked by the kernel, and values computed by the compiler

**`decide +kernel`.** Plain `decide` first evaluates the decision procedure in the elaborator,
then has the kernel check the result. `decide +kernel` skips the first step and asks the kernel
alone, which is faster for large computations. `tmCountK` uses the merge by insertion, which the
kernel evaluates well. The library proves the first fourteen values this way
(`Arnold.openMeanderCount_values`); here is one of them, from scratch.

```lean
example : Arnold.openMeanderCount 11 = 1828 := by
  rw [← Arnold.TM.tmCountK_eq]
  decide +kernel
```

**`native_decide`.** For larger values the library compiles the decision procedure to machine
code and runs it. That trusts the compiler, and Lean records the trust as an extra axiom made
for the occasion, named after the theorem (here `arnold_20._native.native_decide.ax_1`), which
`#print axioms` reveals. The library's style linter flags
`native_decide`, so the theorem switches the linter off with `set_option … in`.

```lean
set_option linter.style.native false in
theorem arnold_20 : Arnold.openMeanderCount 20 = 19304190 := by
  rw [← Arnold.TM.tmCount_eq]
  native_decide

#print axioms arnold_20
```

```lean
#check Arnold.openMeanderCount_values
#check Arnold.closedMeanderCount_values
#check Arnold.openMeanderCount_values_native
```

### The Catalan bound

A closed meander is two non-crossing perfect matchings of its $2n$ bridges glued together, the
arcs above the road and the arcs below. A non-crossing matching is determined by its Dyck word,
and there are $C_n$ Dyck words of length $2n$, so there are at most $C_n^2$ closed meanders. The
library proves this in `Arnold/Catalan.lean`, with matchings as a structure whose fields include
proofs: the partner map, and proofs that it is an involution without fixed points that never
crosses.

```lean
#check @Arnold.NCMatching.nc
#check @Arnold.closedMeanderCount_le_catalan_sq
```

The bound is far from tight. `List.range' 1 8` is the list `[1, …, 8]`, and Mathlib's
`catalan n` is $C_n$. The closed count uses $\mathrm{closed}(n) = \mathrm{open}(2n-1)$ from
Section 6.

```lean
#eval (List.range' 1 8).map fun n => (n, Arnold.TM.tmCount (2 * n - 1), catalan n ^ 2)
```

### The `meanders` program

**Programs and `IO`.** A Lean program is a function `main` of type `IO Unit`, or `List String →
IO Unit` to receive command-line arguments. A value of type `IO α` is an action that interacts
with the world and returns an `α`. Actions are combined with `do`: each line is an action, `let
x := e` names a value, and `for x in l do` repeats an action. `IO.println` prints a line, and
`s!"…{e}…"` builds a string with the value of `e` inserted. `args.head?` is the first argument
as an `Option`, `String.toNat?` parses a number (also an `Option`), `o >>= f` chains two steps
that may fail like `Option.bind`, and `o.getD d` takes the value or the default `d`.

This is `Main.lean`, the program `lake exe meanders`, which prints Arnold's numbers with the
transfer matrix. `#eval` can run an `IO` action directly.

```lean
@include Main.lean def main
```

```lean
#eval main ["24"]
```

### Beyond the proofs

The repository also has two programs that run the same machine much faster, without proofs:
`rust/` in Rust and `oxcaml/` in OxCaml. They pack a state into a single 64-bit word. Reading
the open arcs along the cut from top to bottom, the pieces west of the cut never cross, so the
arcs form a non-crossing matching, which is a bracket word. Both programs spread each layer
over all cores. Their counts agree with `tmCount` wherever both have run, and with the published
values in the OEIS. They are checked, not proved: the Lean values are the reference.
