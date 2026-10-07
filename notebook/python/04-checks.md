## 4. Checking what we cannot prove

The Lean library proves facts for every $n$: there is at least one meander and at most $n!$,
and its fast counters agree with the definition. Python can only check such facts for the
values we try. Checks are still worth writing down, because they catch mistakes, and here they
can be compared with values that Lean has certified.

**`assert`.** `assert condition, message` does nothing if `condition` is true, and stops the
program with the message if it is false. A notebook that runs to the end has passed all its
assertions.

**`for` loops and the `math` module.** `for x in s:` followed by an indented block runs the
block once for each value in `s`. `range(a, b)` counts from `a` up to `b - 1`. `math.factorial(n)`
is $n!$.

The river that zig-zags straight east, `(0, 1, ..., n-1)`, is always a meander, which is how
Lean proves there is at least one. `tuple(range(n))` turns the range into a tuple.

```python
import math

for n in range(9):
    count = open_meander_count(n)
    assert is_meander(tuple(range(n))), n
    assert 1 <= count <= math.factorial(n), n
print("checked n = 0, ..., 8")
```

The values below are certified in Lean. Those up to $n = 13$ were checked by Lean's kernel, and
those up to $n = 24$ by Lean's compiled code (`Arnold.openMeanderCount_values` and
`Arnold.openMeanderCount_values_native`). We name the list in capitals, the Python convention
for a constant.

**Slices.** `s[a:b]` is the part of a list (or tuple, or string) from position `a` up to `b - 1`.
A missing `a` means the start, and a missing `b` means the end, so `LEAN_VALUES[:9]` is the
first nine values.

```python
LEAN_VALUES = [1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538, 1828, 3926, 13820, 30694, 110954,
               252939, 933458, 2172830, 8152860, 19304190, 73424650, 176343390, 678390116,
               1649008456]

assert [open_meander_count(n) for n in range(9)] == LEAN_VALUES[:9]
```

