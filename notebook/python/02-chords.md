## 2. Crossing chords

Draw the road as a horizontal line and number its bridges $0, 1, \ldots, n-1$ from west to
east. Between two consecutive crossings, the river runs along an *arc* in one half-plane, below
the road or above it, and the arcs alternate sides. Two arcs on the same side are like two
chords of a disk: they cross exactly when their endpoints alternate along the road. So a river
is a meander exactly when no two arcs on the same side alternate.

**Functions.** `def name(a, b):` starts a function definition, and the indented lines below it
are its *body*. Indentation is part of Python's syntax: it marks which lines belong together.
`return value` ends the function with a result. A string literal on the first line of the body
is the function's *docstring*, its documentation.

**Chained comparisons.** `min(a, b)` and `max(a, b)` are the smaller and the larger argument.
`lo < c < hi` means `lo < c and c < hi`. Comparing two truth values
with `!=` is *exclusive or*: true when exactly one of them holds.

`interleave(a, b, c, d)` says that the chords $\{a, b\}$ and $\{c, d\}$ alternate: exactly one
of $c$, $d$ lies strictly between $a$ and $b$. This is the same condition as `Interleave` in
the Lean library.

```python
def interleave(a, b, c, d):
    """True when the chords {a, b} and {c, d} cross: exactly one of c, d lies inside (a, b)."""
    lo, hi = min(a, b), max(a, b)
    return (lo < c < hi) != (lo < d < hi)


print(interleave(0, 2, 1, 3), interleave(0, 3, 1, 2))
```

### No two arcs on one side cross

A river visits boundary points $P_0, P_1, P_2, \ldots$, and arc $k$ joins $P_k$ to $P_{k+1}$.
Arcs $j$ and $k$ lie on the same side exactly when $j$ and $k$ have the same parity.

**Lists and ranges.** `[0, 2, 1, 3]` is a *list*, a sequence that can grow and change. `P[k]`
is its entry at position `k`, counting from `0`, and `len(P)` its length. `range(n)` stands for
the numbers $0, 1, \ldots, n-1$.

**Generator expressions and `all`.** `(f(x) for x in s if c(x))` produces the values `f(x)` for
the `x` in `s` that pass the test `c(x)`, one at a time, without building a list. Several `for`
clauses nest, left to right. `all(...)` is `True` when every produced value is true. Inside a
function call the extra parentheses can be dropped.

`no_cross(P, L)` checks the first `L` arcs of the path `P` by comparing every pair of arcs on the
same side, as the Lean definition `NoCross` states it.

```python
def no_cross(P, L):
    """No two of the arcs 0, ..., L-1 of the path P on the same side of the road cross."""
    return all(not interleave(P[j], P[j + 1], P[k], P[k + 1])
               for k in range(L) for j in range(k) if j % 2 == k % 2)


print(no_cross([0, 1, 2, 3], 3), no_cross([0, 2, 1, 3], 3))
```

The first path's same-side arcs $\{0,1\}$ and $\{2,3\}$ are disjoint; the second's,
$\{0,2\}$ and $\{1,3\}$, cross.
