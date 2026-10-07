## 3. A river is a permutation

A meander is determined by the order in which the river crosses the bridges: its $i$-th
crossing is at bridge $\sigma(i)$, where $\sigma$ is a permutation of $\{0, \ldots, n-1\}$. The
two ends of the river go off to infinity: it comes in from the south and leaves to the east.
Compactify each half-plane to a disk, so that the road plus the point at infinity is its
boundary. Then the two ends touch the boundary east of every bridge: the east end, which we call
point $n$, and the south end, point $n+1$. The path of the river is the sequence of boundary
points
$$n+1,\ \sigma(0),\ \sigma(1),\ \ldots,\ \sigma(n-1),\ n,$$
and arc $k$ joins the $k$-th and $(k+1)$-st of them. The river starts in the south, so the even
arcs are below the road and the odd arcs above.

**`Fin n` and permutations.** `Fin n` is the type of natural numbers less than `n`. An element
of `Fin n` is a pair of a number `i` and a proof of `i < n`. `Equiv.Perm (Fin n)` is the type of
permutations of `Fin n`: bijections from `Fin n` to itself. A permutation can be applied like a
function, `σ i`.

**Implicit arguments.** In `pathPt {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)` the braces make
`n` *implicit*. We write `pathPt σ k`, and Lean works `n` out from the type of `σ`.

**Anonymous constructors and dependent `if`.** `⟨a, b⟩` builds a value of a structure type
from its fields, when Lean can tell the type from context. Here `⟨k - 1, h⟩ : Fin n` is the
number `k - 1` with the proof `h : k - 1 < n`. That proof comes from the test itself: in
`if h : c then t else e`, the branch `t` may use `h : c`, and `e` may use `h : ¬ c`. This is a
*dependent* `if`; the plain `if c then t else e` does not name the fact.

**Coercions.** `(σ ⟨k - 1, h⟩ : ℕ)` asks for the result as a natural number. The result is an
element of `Fin n`, and Lean inserts the *coercion* that forgets the proof and keeps the
number. Lean prints a coercion as `↑x`.

```lean
@include Arnold/Basic.lean def pathPt
```

The straight river that crosses bridges $0$ and $1$ in order visits $3, 0, 1, 2$. Here
`Equiv.refl` is the identity permutation, and `List.range 4` is the list `[0, 1, 2, 3]`.
`l.map f` applies the function `f` to every entry of the list `l`. A function of two
arguments given only its first, like `pathPt (Equiv.refl (Fin 2))`, is a function of the
remaining one.

```lean
#eval (List.range 4).map (pathPt (Equiv.refl (Fin 2)))
```

The definition of a meander is now one line, and the decision procedure comes from the one for
`NoCross`, exactly as before.

```lean
@include Arnold/Basic.lean def IsMeander
```

```lean
@include Arnold/Basic.lean instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (IsMeander
```

### Arnold's number

**Subtypes and `Fintype.card`.** `{σ : Equiv.Perm (Fin n) // IsMeander σ}` is the *subtype* of
permutations that are meanders. Its elements are pairs of a permutation and a proof that it is
a meander. A type with finitely many elements has a `Fintype` instance, and `Fintype.card T` is
the number of its elements. So the following is the definition of Arnold's number, word for
word: the number of permutations that describe a meander.

```lean
@include Arnold/Basic.lean def openMeanderCount
```

This definition is the *specification*. It is easy to check against the problem, and every
faster algorithm in the library is proved equal to it. It can also be run, though only for
small $n$, because it tests all $n!$ permutations. The first seven values are
$1, 1, 1, 2, 3, 8, 14$.

```lean
#eval (List.range 7).map openMeanderCount
```
