## 3. A river is a permutation

A meander is determined by the order in which the river crosses the bridges: its $i$-th
crossing is at bridge $\sigma(i)$, for a permutation $\sigma$ of $0, \ldots, n-1$. The two ends
of the river go off to infinity, and we treat them as two more boundary points east of every
bridge: the east end, point $n$, and the south end, point $n+1$. (Compactify each half-plane to
a disk, and the road plus infinity becomes its boundary.) The path of the river is then
$$n+1,\ \sigma(0),\ \sigma(1),\ \ldots,\ \sigma(n-1),\ n,$$
with $n + 1$ arcs; the even arcs lie below the road and the odd ones above.

**Unpacking into a list.** Inside a list display, `*s` inserts all the values of `s`. So
`[n + 1, *sigma, n]` is the path.

```python
def path(sigma):
    """The boundary points visited by the river with crossing order sigma."""
    n = len(sigma)
    return [n + 1, *sigma, n]


def is_meander(sigma):
    """The crossing order sigma describes a river that never crosses itself."""
    return no_cross(path(sigma), len(sigma) + 1)


print(path((0, 1, 2)), is_meander((0, 1, 2)), is_meander((1, 0, 2)))
```

**Modules and `import`.** Python's standard library is divided into *modules*. `import
itertools` loads one, and its contents are reached as `itertools.name`.
`itertools.permutations(s)` produces every ordering of `s`, each as a tuple.

**Summing truth values.** Since `True` counts as `1`, `sum(test(x) for x in s)` counts the `x`
that pass the test.

`open_meander_count(n)` is the definition, word for word: the number of permutations that
describe a meander. Like Lean's `openMeanderCount`, it is the specification that everything
faster must agree with, and it looks at all $n!$ orderings.

```python
import itertools


def open_meander_count(n):
    """Arnold's number by brute force: test every crossing order."""
    return sum(is_meander(s) for s in itertools.permutations(range(n)))
```

**List comprehensions.** `[f(x) for x in s]` builds the list of the values `f(x)`. It is a
generator expression in square brackets.

```python
[open_meander_count(n) for n in range(9)]
```
