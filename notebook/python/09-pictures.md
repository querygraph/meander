## 9. Pictures and growth

**Plotting with Matplotlib.** Matplotlib is the most widely used plotting library for Python. Its
module `matplotlib.pyplot` is imported under the short name `plt` (`import module as name`).
`plt.subplots(rows, cols)` makes a figure with a grid of *axes*, the individual plots;
`axes.flat` runs through them in order. On an axes `ax`, `ax.plot(xs, ys)` draws a line through
points, and `ax.add_patch` adds a shape. `matplotlib.patches.Arc` is a piece of an ellipse,
given by its centre, width, height, and start and end angles in degrees.

**`zip`.** `zip(s, t)` pairs the values of `s` and `t` position by position; the earlier
`zip(*rows)` is the same function applied to all the rows at once.

Here are all eight meanders with five crossings. The road is the horizontal line, the bridges
are the points $0, \ldots, 4$, and the two ends are drawn on the road east of the bridges, as in
the compactified picture: the east end at $5$ and the south end at $6$. Arc $k$ is a half-circle
below the road for even $k$ and above it for odd $k$. `zip(P, P[1:])` pairs each point with the
next one: the arcs. `abs(x)` is the absolute value. `map(f, s)` applies `f` to every value of
`s`, `" ".join(...)` joins strings with spaces, and `[0] * n` is a list of `n` zeros. On the
axes, `set_xlim` and `set_ylim` fix the visible range, `set_aspect("equal")` keeps circles
round, `axis("off")` hides the frame, and `set_title` writes a title.

```python
import matplotlib.pyplot as plt
from matplotlib.patches import Arc


def draw(ax, sigma):
    """Draw the meander with crossing order sigma on the axes ax."""
    P = path(sigma)
    n = len(sigma)
    ax.plot([-0.7, n + 1.7], [0, 0], color="0.6", lw=1)
    for k, (a, b) in enumerate(zip(P, P[1:])):
        lower = k % 2 == 0
        ax.add_patch(Arc(((a + b) / 2, 0), abs(b - a), abs(b - a),
                         theta1=180 if lower else 0, theta2=360 if lower else 180,
                         color="tab:blue", lw=2))
    ax.plot(range(n), [0] * n, "o", color="black", ms=4)
    ax.set_xlim(-0.7, n + 1.7)
    ax.set_ylim(-(n + 2) / 2, (n + 2) / 2)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title(" ".join(map(str, sigma)), fontsize=9)


rivers = [s for s in itertools.permutations(range(5)) if is_meander(s)]
fig, axes = plt.subplots(2, 4, figsize=(12, 4.5))
for ax, sigma in zip(axes.flat, rivers):
    draw(ax, sigma)
plt.show()
```


### How fast do the numbers grow?

The OEIS lists the values up to $n = 55$. Every value we computed matches.

```python
OEIS_VALUES = [
    1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538, 1828, 3926, 13820, 30694, 110954, 252939, 933458,
    2172830, 8152860, 19304190, 73424650, 176343390, 678390116, 1649008456, 6405031050,
    15730575554, 61606881612, 152663683494, 602188541928, 1503962954930, 5969806669034,
    15012865733351, 59923200729046, 151622652413194, 608188709574124, 1547365078534578,
    6234277838531806, 15939972379349178, 64477712119584604, 165597452660771610,
    672265814872772972, 1733609081727968492, 7060941974458061392, 18276178714484582264,
    74661728661167809752, 193909492888406631692, 794337831754570367812, 2069504277256274074724,
    8499066628515413229282, 22206891674746169557410, 91412898898828176826244,
    239489513356610743216954, 987975910996038555989486, 2594805632585289523975474,
    10726008363361842734385644
]

assert values == OEIS_VALUES[:len(values)]
```

Odd and even $n$ behave differently, so compare each value with the one two steps back. The
square root of $a(n+2)/a(n)$ estimates the growth factor per crossing. It creeps up slowly:
even at $n = 53$ it is below 3.3, because the counts carry a power-law correction that fades
only as $n$ grows. Iwan Jensen's transfer-matrix enumeration (2000) estimated the growth constant of
closed meanders, per pair of crossings, as $12.2629$; its square root, $3.5018$, is drawn as the
dashed line. `ax.semilogy` plots with a logarithmic vertical axis, `ax.axhline` draws a
horizontal line, and `set_xlabel` labels an axis. Dividing two integers with `/` gives a float,
and `** 0.5` is a square root.

```python
ns = range(2, 54)
ratios = [(OEIS_VALUES[n + 2] / OEIS_VALUES[n]) ** 0.5 for n in ns]
fig, (left, right) = plt.subplots(1, 2, figsize=(12, 4))
left.semilogy(range(len(OEIS_VALUES)), OEIS_VALUES, ".")
left.set_xlabel("crossings n")
left.set_title("open meanders a(n)")
right.plot(ns, ratios, ".-")
right.axhline(3.5018, color="0.6", ls="--")
right.set_xlabel("n")
right.set_title("sqrt(a(n+2) / a(n))")
plt.show()
print(f"sqrt(a(55)/a(53)) = {ratios[-1]:.4f}")
```


### Testing the meander exponent

Di Francesco, Golinelli and Guitter conjectured that the number $M_n$ of closed meanders of
order $n$ grows like $C A^n n^{-\alpha}$ with
$$\alpha = \frac{29 + \sqrt{145}}{12} \approx 3.4201,$$
an exponent from the physics of random surfaces. Borga, Gwynne and Sun (*Permutons, meanders,
and SLE-decorated Liouville quantum gravity*, J. Eur. Math. Soc., 2026) conjecture the matching
picture for random meanders: a Liouville quantum gravity surface carrying two independent
space-filling SLE$_8$ curves, one for the road and one for the river. Their *meandric
permutation* is our closed-meander crossing order, read the other way round.

Exact counts test the exponent. Section 5 checked that a closed meander of order $n$ is an open
meander with $2n - 1$ crossings, so $M_n$ is `OEIS_VALUES[2 * n - 1]`. If
$M_n \approx C A^n n^{-\alpha}$, then $M_{n+1}/M_n \approx A (1 + 1/n)^{-\alpha}$, so with
Jensen and Guttmann's estimate $A \approx 12.2629$,
$$\alpha_n = -\frac{\log\bigl(M_{n+1} / (A M_n)\bigr)}{\log(1 + 1/n)}$$
estimates $\alpha$ with an error of order $1/n$. Extrapolating linearly in $1/n$ from
$\alpha_{n-2}$ and $\alpha_n$ removes most of that error. `math.log` is the natural logarithm and
`math.sqrt` the square root.

```python
A = 12.262874
ALPHA = (29 + math.sqrt(145)) / 12


def closed(n):
    return OEIS_VALUES[2 * n - 1]


def alpha_estimate(n):
    return -math.log(closed(n + 1) / (A * closed(n))) / math.log(1 + 1 / n)


print(" n   alpha_n   extrapolated")
for n in range(12, 27, 2):
    a0, a1 = alpha_estimate(n - 2), alpha_estimate(n)
    extrapolated = a1 - (a1 - a0) / (1 / n - 1 / (n - 2)) / n
    print(f"{n:2}   {a1:.4f}    {extrapolated:.4f}")
print(f"conjecture      {ALPHA:.4f}")
```

The extrapolated estimates rise steadily towards $3.4201$: numerical support for the
conjecture, given the estimate of $A$, and no proof.
