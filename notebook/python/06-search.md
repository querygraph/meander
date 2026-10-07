## 6. A search with a parity rule

Brute force looks at all $n!$ orders. A search builds the order one bridge at a time and
abandons a partial order as soon as it cannot be finished. The first test: the newest arc must
not cross an earlier arc on its side. The second is a rule from topology.

**The parity rule.** Take an arc $j$ already drawn, on side $s$, with ends $a < b$. Every later
arc on side $s$ has both ends inside $(a, b)$ or both outside, since it may not cross arc $j$.
So the side-$s$ arc ends still to come inside $(a, b)$ pair up, and there is an even number of
them. They are: every unvisited bridge inside $(a, b)$, since each bridge eventually gets one
arc on each side; the current point, if the next arc is on side $s$; and the east end $n$, if
the final arc $n$ is on side $s$. If the count is odd, the partial river cannot be finished.
Lean proves the rule sound (`Arnold.parityOK_of_noCross`); here we watch its effect.

**Nested functions and closures.** A function defined inside another can read the outer
function's variables; it is a *closure* over them. To *assign* to an outer variable, the inner
function must declare it `nonlocal`. A function may call itself: this is *recursion*.

**Changing lists and sets.** `order.append(x)` adds `x` at the end of the list and
`order.pop()` removes the last entry; `unused.add(x)` and `unused.remove(x)` do the same for a
set. Adding and then undoing is how a search explores a branch and comes back. `sorted(s)` is a
sorted list of the values in `s`. `x if c else y` is a conditional expression.

**`if`, `elif` and defaults.** `if c:` runs its block when `c` is true; `else:` runs otherwise.
In `def search(n, parity=True)` the parameter `parity` has a default value, used when the caller
leaves it out. A function can return a tuple, which the caller unpacks. `x += 1` is short for
`x = x + 1`. In a test, an empty collection counts as false, so `not unused` is true when no
bridges are left.

`search(n)` returns the number of meanders and the number of partial rivers it visited.

```python
def search(n, parity=True):
    """Count meanders with n crossings by depth-first search; also count the nodes visited."""
    order, unused = [], set(range(n))
    nodes = 0

    def point(k):  # point k of the path: south end, the bridges so far, then the east end
        if k == 0:
            return n + 1
        return order[k - 1] if k - 1 < len(order) else n

    def inside(j, x):  # x lies strictly inside arc j
        a, b = point(j), point(j + 1)
        return min(a, b) < x < max(a, b)

    def step_ok(t):  # arc t crosses no earlier arc on its side
        c, d = point(t), point(t + 1)
        return all(not interleave(point(j), point(j + 1), c, d)
                   for j in range(t) if j % 2 == t % 2)

    def parity_ok():  # every drawn arc encloses an even number of future ends on its side
        t = len(order)
        for j in range(t):
            ends = sum(inside(j, x) for x in unused)
            ends += t % 2 == j % 2 and inside(j, point(t))
            ends += n % 2 == j % 2 and inside(j, n)
            if ends % 2 == 1:
                return False
        return True

    def go():
        nonlocal nodes
        nodes += 1
        if not unused:  # all bridges used: check the final arc to the east end
            return 1 if step_ok(n) else 0
        total = 0
        for x in sorted(unused):
            order.append(x)
            unused.remove(x)
            if step_ok(len(order) - 1) and (not parity or parity_ok()):
                total += go()
            unused.add(x)
            order.pop()
        return total

    return go(), nodes
```


**Timing.** `time.perf_counter()` reads a clock in seconds; the difference of two readings is
the time between them. In a format specification, `{nodes:,}` groups digits with commas and
`{x:.1f}` shows one decimal.

```python
import time

for parity in (False, True):
    start = time.perf_counter()
    count, nodes = search(11, parity)
    print(f"parity={parity}: {count} meanders, {nodes:,} partial rivers, "
          f"{time.perf_counter() - start:.1f} s")
```

The parity rule cuts the partial rivers at eleven crossings from 322,080 to 14,471, the figures
in the paper. Indexing a call's result, `search(n)[0]`, takes the first value of the returned
tuple.

```python
assert [search(n)[0] for n in range(14)] == LEAN_VALUES[:14]
```

