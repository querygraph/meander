## 5. Closed meanders

A *closed* meander is a loop crossing the road $2n$ times. To count each loop once, start at the
westmost bridge $0$ and leave it upward. The loop visits bridges
$\sigma(0) = 0, \sigma(1), \ldots, \sigma(2n-1)$, and arc $k$ joins $\sigma(k)$ to
$\sigma(k+1)$, with positions taken modulo $2n$, so the last arc returns to bridge $0$.

**Tuples of a computed length.** `(0, *rest)` is the tuple `rest` with `0` in front.

```python
def is_closed_meander(sigma):
    """sigma starts at bridge 0 and no two arcs of the loop on one side cross."""
    m = len(sigma)
    loop = [sigma[k % m] for k in range(m + 1)]
    return sigma[0] == 0 and no_cross(loop, m)


def closed_meanders(n):
    """All closed meanders of order n, as crossing orders starting at 0."""
    return [(0, *rest) for rest in itertools.permutations(range(1, 2 * n))
            if is_closed_meander((0, *rest))]


[len(closed_meanders(n)) for n in range(1, 5)]
```

The counts $1, 2, 8, 42$ are the open counts for $1, 3, 5, 7$ crossings. Lean proves that this
holds for every $n$: delete bridge $0$ from a closed meander, so that its two arcs run off to
infinity in the west, then turn the picture through $180°$. The result is an open meander with
$2n - 1$ crossings. In the other direction, an open meander $\tau$ with $2n - 1$ crossings
becomes the closed meander $0, 2n - 1 - \tau(0), 2n - 1 - \tau(1), \ldots$ (Lean's `closeUp`).

**Sets.** A *set* holds values without order or repetition. `{f(x) for x in s}` is a set
comprehension, and two sets are equal when they have the same elements. `set(s)` makes a set
from any collection. For tuples, `+` concatenates.

We check the bijection itself, not just the counts: turning every open meander with $2n - 1$
crossings into a loop gives exactly the closed meanders of order $n$.

```python
def close_up(tau):
    """Turn an open meander with 2n-1 crossings into a closed one with 2n (Lean's closeUp)."""
    return (0,) + tuple(len(tau) - t for t in tau)


for n in range(1, 5):
    opens = [t for t in itertools.permutations(range(2 * n - 1)) if is_meander(t)]
    assert {close_up(t) for t in opens} == set(closed_meanders(n))
print("close_up is a bijection for n = 1, ..., 4")
```

