## 2. The road and the river: crossing chords

Draw the road as a horizontal line and number its bridges $0, 1, \ldots, n-1$ from west to
east. Between two consecutive crossings the river runs along an *arc* in one half-plane, below
the road or above it, and the arcs alternate sides. Two arcs on the same side are like two
chords of a disk: they cross exactly when their endpoints alternate along the road. So a river
is a meander exactly when no two arcs on the same side alternate. The first definition says
when two chords alternate.

**`namespace`.** Every name in the library lives in the namespace `Arnold`, so its full name is
`Arnold.Interleave`. `namespace Arnold` opens the namespace: until the matching `end Arnold`,
new names get the prefix automatically, and names inside it can be used without the prefix. The
namespace stays open across the next cells, as it would in one file.

**`def` and docstrings.** `def name (x y : T) : R := body` defines `name` as a function of
parameters `x` and `y` of type `T`, returning a value of type `R`. A comment between `/--` and
`-/` placed before a declaration is its *docstring*; Lean attaches it to the name, and editors
show it on hover.

**A definition whose value is a proposition.** `Interleave` returns a `Prop`: it does not
compute an answer, it *states* something about four numbers. The logical symbols are `¬`
(not), `∧` (and), `↔` (if and only if) and `<`. Read the body as: "`c` lies strictly between
`a` and `b`" is *not equivalent* to "`d` lies strictly between `a` and `b`". In other words,
exactly one of `c`, `d` is inside the chord `{a, b}`.

```lean
namespace Arnold

@include Arnold/Defs.lean def Interleave
```

**Type classes and `instance`.** Lean cannot evaluate an arbitrary proposition: most
propositions about all natural numbers have no algorithm that decides them. A proposition `p`
can be *decided* when there is a value of type `Decidable p`, an algorithm that returns either a
proof of `p` or a proof of `¬ p`. `Decidable` is a *type class*: a family of types whose values
Lean finds automatically when it needs them. An `instance` declaration supplies such a value.
The instance below tells Lean how to decide `Interleave a b c d` for any four numbers.

**Tactics: `by`, `unfold`, `infer_instance`.** Instead of writing a value directly, we can
write `by` followed by *tactics*, commands that build the value step by step. `unfold
Interleave` replaces `Interleave a b c d` by its definition. The goal then becomes "decide a
negated `↔` of conjunctions of `<`", and `infer_instance` finds that instance by combining the
library's instances for `¬`, `↔`, `∧` and `<` on `ℕ`. A `;` separates tactics on one line.

```lean
@include Arnold/Defs.lean instance (a b c d : Nat) : Decidable (Interleave
```

Now `#eval` can evaluate the proposition: it runs the decision procedure and prints `true` or
`false`. The chords $\{0, 2\}$ and $\{1, 3\}$ alternate; $\{0, 3\}$ and $\{1, 2\}$ are nested.

```lean
#eval Interleave 0 2 1 3
#eval Interleave 0 3 1 2
```

### No two arcs on one side cross

A river visits boundary points $P(0), P(1), P(2), \ldots$ and arc $k$ joins $P(k)$ to
$P(k+1)$. Arcs $0, 2, 4, \ldots$ lie on one side of the road and arcs $1, 3, 5, \ldots$ on the
other, so arcs $j$ and $k$ are on the same side exactly when $j \bmod 2 = k \bmod 2$.

**Function types and quantifiers.** `Nat → Nat` is the type of functions from `ℕ` to `ℕ`; the
river's path `P` is such a function. `∀ k < L, Q k` says "for every `k` with `k < L`, `Q k`",
and the `∀` can be followed by more conditions. Between propositions, `→` means *implies*:
`j % 2 = k % 2 → ¬ ...` reads "if arcs `j` and `k` are on the same side, they do not cross".
(Implication and function type are the same arrow, and that is no accident: a proof of
`A → B` is a function that turns any proof of `A` into a proof of `B`.)

```lean
@include Arnold/Defs.lean def NoCross
```

```lean
@include Arnold/Defs.lean instance (P : Nat → Nat) (L : Nat) : Decidable (NoCross
```

**Anonymous functions, lists and dot notation.** `fun x => e` is the function that sends `x`
to `e`. `[0, 2, 1, 3]` is a *list*, a finite sequence; its type is `List ℕ`. Functions about a
type live in the namespace of the type, so the function that reads entry `k` of a list, or a
default value if the list is too short, is `List.getD`. *Dot notation* abbreviates
`List.getD l k 0` to `l.getD k 0`: Lean sees that `l` is a list and looks for `getD` in the
namespace `List`. We test
`NoCross` on two paths with four boundary points. The first, $0 \to 1 \to 2 \to 3$, has arcs
$\{0,1\}$ and $\{2,3\}$ on the same side, which do not cross. The second, $0 \to 2 \to 1 \to 3$,
has arcs $\{0,2\}$ and $\{1,3\}$ on the same side, which do.

```lean
#eval NoCross (fun k => k) 3
#eval NoCross (fun k => [0, 2, 1, 3].getD k 0) 3
```
