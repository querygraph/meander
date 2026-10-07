## 7. The transfer matrix

The search follows the river. The transfer matrix scans the road instead, from west to east:
the bridges $0, \ldots, m-1$, then the east end $E = m$, which has one arc, on side
$m \bmod 2$. (The south end $S = m + 1$, with its one arc below, comes last and needs no step.)
At each point and on each side, the point either *opens* a new arc or *closes* an open one. Arcs
on one side never cross, so the open arcs on each side form a stack, and a point always closes
the top one. The machine counts all ways to make these choices that trace a single river.

**The state.** Cut the plane just east of the current point. The river west of the cut falls
into pieces, each joining two open arcs, or one open arc and the east end once $E$ has been
passed. Read the open arcs along the cut from top to bottom: the arcs above the road from the
outermost in, then the arcs below from the innermost out. The pieces lie west of the cut and
never cross, so they pair up the arcs like brackets. A state is therefore a *word* over `(`, `)`
and at most one `E` (an arc whose piece leads to the east end), together with `h`, the number of
arcs above the road. This is the encoding of the Rust and OxCaml programs; the Lean machine
stores the same information as two stacks of references.

**Strings.** A string is a sequence of characters: `word[i]` is one character, `word[a:b]` a
slice, `+` concatenates, and `len(word)` is its length. Strings cannot be changed in place. To
edit one, convert it to a list of characters with `list(word)`, change the list, and join it
back with `"".join(chars)`. `del chars[i]` removes an entry from a list.

**`while`.** `while c:` repeats its block as long as `c` is true; `while True:` repeats until a
`return` (or `break`) leaves it.

`partner(word, i)` finds the bracket matched with the one at position `i`, scanning right from
an opening bracket or left from a closing one, and skipping the `E`.

```python
def partner(word, i):
    """Position of the bracket matched with word[i]."""
    step = 1 if word[i] == "(" else -1
    depth, j = 0, i + step
    while True:
        if word[j] == word[i]:
            depth += 1
        elif word[j] != "E":
            if depth == 0:
                return j
            depth -= 1
        j += step
```


**Generators.** A function containing `yield` is a *generator*: calling it returns a sequence
that runs the body lazily, and each `yield value` hands out the next value. A `for` loop over the
call receives them one at a time.

`successors(m, x, state)` yields every state that point `x` can lead to.

* At a bridge, opening both sides puts a new pair `()` at the cut, joined at the bridge.
* Opening above and closing below leaves the word as it is: the closed arc's piece continues
  into the new arc, which takes its place on the cut. Only `h` changes; likewise the other way.
* Closing both tops joins their two pieces, unless the two tops are partners: that would close
  a loop. The tops' partners become partners of each other, so a bracket may have to turn round.
* The east end opens or closes one arc on its side, and the piece there now leads to `E`.

`a == b == "("` chains like `<`. Adding a truth value to a number adds `1` or `0`.

```python
def successors(m, x, state):
    """The states reachable from `state` by processing point x of a river with m crossings."""
    word, h = state
    dn = len(word) - h
    if x < m:
        yield word[:h] + "()" + word[h:], h + 1          # open above and below
        if dn > 0:
            yield word, h + 1                             # open above, close below
        if h > 0:
            yield word, h - 1                             # close above, open below
        if h > 0 and dn > 0:                              # close both
            i, j = h - 1, h
            a, b = word[i], word[j]
            if not (a == "(" and b == ")"):               # partners would close a loop
                chars = list(word)
                if a == "E":
                    chars[partner(word, j)] = "E"
                elif b == "E":
                    chars[partner(word, i)] = "E"
                elif a == b == "(":
                    chars[partner(word, j)] = "("
                elif a == b == ")":
                    chars[partner(word, i)] = ")"
                del chars[j], chars[i]
                yield "".join(chars), h - 1
    else:
        up = m % 2 == 1                                   # the side of the east end's arc
        yield word[:h] + "E" + word[h:], h + up           # open: its piece leads to E
        if (h > 0) if up else (dn > 0):                   # close the top arc on that side
            top = h - 1 if up else h
            if word[top] != "E":
                chars = list(word)
                chars[partner(word, top)] = "E"
                del chars[top]
                yield "".join(chars), h - up
```

A state is dropped as soon as it has more open arcs on a side than the remaining points can
close (Lean's `viable`). `cap(m, k, up)` counts the points $k, \ldots, m$ with an arc on that
side; below the road, the south end closes one more.

```python
def cap(m, k, up):
    """How many of the points k, ..., m have an arc on the given side."""
    return (m - k) + ((m % 2 == 1) == up) if k <= m else 0


def viable(m, k, state):
    word, h = state
    return h <= cap(m, k, True) and len(word) - h <= cap(m, k, False) + 1
```

**Dictionaries.** A *dictionary* maps keys to values: `{key: value}` makes one, `d[key]` reads
or sets an entry, `d.get(key, default)` reads with a fallback, and `d.items()` yields the pairs.
Keys must be unchangeable values such as numbers, strings and tuples. `defaultdict(int)` from
the `collections` module is a dictionary that treats a missing key as `0`. `from module import
name` imports one name directly.

A *layer* maps each state to the number of ways to reach it. Equal states are merged by adding
their counts: this is what makes the method fast. A river is accepted when, after the east
end, exactly one arc is open, below the road, leading to `E`: the state `("E", 0)`. In
`tm_count`, `pass` is a statement that does nothing: the loop just runs to the last layer.

```python
from collections import defaultdict


def layers(m):
    """The successive layers of the transfer matrix for m crossings."""
    layer = {("", 0): 1}
    yield layer
    for x in range(m + 1):
        nxt = defaultdict(int)
        for state, count in layer.items():
            for s in successors(m, x, state):
                if viable(m, x + 1, s):
                    nxt[s] += count
        layer = nxt
        yield layer


def tm_count(m):
    """Arnold's number by the transfer matrix."""
    for layer in layers(m):
        pass
    return layer.get(("E", 0), 0)
```

Here are the layers for three crossings. After the first bridge, the only state has one arc
above and one below, joined at the bridge. `enumerate(s)` pairs each value of `s` with its
position.

```python
for k, layer in enumerate(layers(3)):
    print(k, dict(layer))
```


Now all values up to $n = 30$. A negative index counts from the end, so `values[-3:]` is the
last three.

```python
start = time.perf_counter()
values = [tm_count(m) for m in range(31)]
print(f"{time.perf_counter() - start:.1f} s")
assert values[:25] == LEAN_VALUES
values[-3:]
```

All thirty-one values in seconds, the first twenty-five equal to Lean's certified values.
