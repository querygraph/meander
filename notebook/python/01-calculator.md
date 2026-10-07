## 1. Python as a calculator

A code cell holds Python *statements*, run from top to bottom. If the last line is an
*expression*, Jupyter shows its value. Text after `#` is a comment.

**Numbers.** Python integers have no size limit, which matters here: the number of meanders
with 55 crossings has 26 digits. `**` is a power, `//` divides and rounds down, and `%` is the
remainder. `/` always gives a floating-point number.

```python
2 + 3 * 4
```

```python
2 ** 100
```

**Variables, tuples and `print`.** `name = value` stores a value under a name. A comma-separated
list of values, usually in parentheses, is a *tuple*. `print(...)` writes its arguments as a
line. An *f-string*, `f"... {expr} ..."`, inserts the values of expressions into text.

```python
q, r = 17 // 5, 17 % 5
print(q, r, 17 / 5)
print(f"17 = 5 * {q} + {r}")
```

The first line also shows *unpacking*: a tuple of names on the left takes the values of a tuple
on the right, in order.

**Truth values.** Comparisons give `True` or `False`, the two values of type `bool`. `==` tests
equality and `!=` inequality. `and`, `or` and `not` combine truth values. A `bool` is also a
number: `True` counts as `1` and `False` as `0`, which we use to count things.

```python
print(3 < 5, 3 == 5, 3 != 5, not 3 < 5)
print(True + True + False)
```
