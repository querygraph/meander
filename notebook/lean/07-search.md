## 7. A search with a parity rule

`openMeanderCount` looks at all $n!$ crossing orders, which is hopeless beyond $n \approx 10$.
The library's first fast algorithm builds the crossing order one bridge at a time and abandons
a partial order as soon as it cannot be finished. A partial order is a list `l` of the bridges
visited so far. `lpt n l k` is point `k` of its path, just as `pathPt` is for a permutation:
first the south end $n+1$, then the entries of `l`, then the east end $n$. That last value is
also what `getD` returns past the end of the list.

```lean
@include Arnold/Defs.lean def lpt
```

`StepOK n q t` says that arc `t` of the partial river `q` crosses no earlier arc on its side.
When the search adds a bridge, only the new arc needs to be checked against the old ones.

```lean
@include Arnold/Defs.lean def StepOK
```

```lean
@include Arnold/Defs.lean instance (n : Nat) (q : List Nat) (t : Nat) : Decidable (StepOK
```

### The parity rule

Take an arc $j$ that is already drawn, on side $s$, with ends $a < b$. Every later arc on side
$s$ has both ends strictly inside $(a, b)$ or both outside, since it may not cross arc $j$. So
the side-$s$ arc ends still to come inside $(a, b)$ pair up, and there are an even number of
them. These ends are:

* every unvisited bridge in $(a, b)$, since each bridge eventually gets one arc on each side;
* the current point, if the next arc is on side $s$;
* the east end $n$, if the final arc $n$ is on side $s$.

If the count is odd for some drawn arc, the partial river can never be finished. At eleven
crossings this rule cuts the search from 322,080 partial rivers to 14,471.

**`Bool` and `decide`.** Besides `Prop`, Lean has `Bool`, the type of the two values `true` and
`false`. A `Bool` is data a program can compute with; a `Prop` is a statement that may have no
algorithm at all. For a decidable proposition `p`, `decide p : Bool` runs the decision
procedure. In the other direction, a `Bool` `b` becomes the proposition `b = true`. The test
"is $x$ inside arc $j$" returns a `Bool`, because the search computes with it.

```lean
@include Arnold/Defs.lean def inArc
```

`l.countP f` counts the entries `x` of the list `l` with `f x = true`. `futureEnds` adds up the
three kinds of future ends inside arc `j`, and `ParityOK` requires the count to be even for
every drawn arc.

```lean
@include Arnold/Defs.lean def futureEnds
```

```lean
@include Arnold/Defs.lean def ParityOK
```

```lean
@include Arnold/Defs.lean instance (n : Nat) (q r : List Nat) : Decidable (ParityOK
```

### The depth-first search

**Definitions by pattern matching and recursion.** A function can be defined by cases on the
shape of its arguments. `def f : A → B → C` followed by lines `| pattern₁, pattern₂ => value`
gives the value for each case, tried in order. The pattern `0` matches zero, `k + 1` matches a
successor and names its predecessor `k`, a variable matches anything, and `_` matches anything
without naming it. A definition may call itself on smaller arguments, here `k` inside the case
`k + 1`. Lean checks that every case is covered and that the recursion terminates; for
*structural* recursion like this, on an argument that gets strictly smaller, the check is
automatic.

**List operations.** `l ++ l'` concatenates lists, `[x]` is the one-element list, and
`l.erase x` removes the first `x` from `l`. `(l.map f).sum` adds up the values of `f` on `l`.

`dfs n k p rem` counts the meanders whose crossing order starts with `p`, where `rem` holds the
`k` unused bridges. Each unused bridge `x` is tried next only if the new arc crosses no earlier
arc and the parity test still passes. When no bridges are left, the final arc to the east end
is checked.

```lean
@include Arnold/Defs.lean def dfs
```

```lean
#eval dfs 5 5 [] (List.range 5)
```

Eight meanders with five crossings, as `openMeanderCount 5` found by brute force.
