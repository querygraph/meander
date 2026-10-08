"""Draw the header image assets/two-rivers.jpg: forty random meanders with 14 crossings in rust
copper and forty in OxCaml teal, slightly offset, over one road. Run from this directory with a
Python that has NumPy, Matplotlib and Pillow; it first enumerates all 30,694 meanders."""

import random

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from PIL import Image  # noqa: E402


def interleave(a, b, c, d):
    lo, hi = min(a, b), max(a, b)
    return (lo < c < hi) != (lo < d < hi)


def all_meanders(n):
    """Every crossing order of a meander with n crossings (the parity search)."""
    order, unused, out = [], set(range(n)), []

    def point(k):
        if k == 0:
            return n + 1
        return order[k - 1] if k - 1 < len(order) else n

    def inside(j, x):
        a, b = point(j), point(j + 1)
        return min(a, b) < x < max(a, b)

    def step_ok(t):
        c, d = point(t), point(t + 1)
        return all(not interleave(point(j), point(j + 1), c, d) for j in range(t) if j % 2 == t % 2)

    def parity_ok():
        t = len(order)
        for j in range(t):
            e = (sum(inside(j, x) for x in unused) + (t % 2 == j % 2 and inside(j, point(t)))
                 + (n % 2 == j % 2 and inside(j, n)))
            if e % 2:
                return False
        return True

    def go():
        if not unused:
            if step_ok(n):
                out.append(list(order))
            return
        for x in sorted(unused):
            order.append(x)
            unused.remove(x)
            if step_ok(len(order) - 1) and parity_ok():
                go()
            unused.add(x)
            order.pop()

    go()
    return out


def arc(ax, a, b, lower, dx, color, lw, alpha):
    c, r = (a + b) / 2 + dx, abs(b - a) / 2
    t = np.linspace(np.pi, 2 * np.pi, 120) if lower else np.linspace(0, np.pi, 120)
    ax.plot(c + r * np.cos(t), 0.92 * r * np.sin(t), color=color, lw=lw, alpha=alpha,
            solid_capstyle="round")


def main():
    n = 14
    ms = all_meanders(n)
    W, H = 2400, 1260
    fig = plt.figure(figsize=(W / 200, H / 200), dpi=200)
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(-2.2, n + 2.6)
    ax.set_ylim(-(n + 2.6) * H / W * 1.05, (n + 2.6) * H / W * 1.05)
    ax.axis("off")
    fig.patch.set_facecolor("#080b10")
    rng = random.Random(1988)
    for color, dx in (("#e2622b", -0.14), ("#3fc6d8", 0.14)):  # rust copper, OxCaml teal
        for sigma in rng.sample(ms, 40):
            P = [n + 1, *sigma, n]
            for k, (a, b) in enumerate(zip(P, P[1:])):
                for lw, al in ((7, 0.012), (3.2, 0.03), (1.0, 0.11)):  # a soft glow
                    arc(ax, a, b, k % 2 == 0, dx, color, lw, al)
    ax.plot([-2.2, n + 2.6], [0, 0], color="#c9d4e0", lw=1.1, alpha=0.35)  # the road
    ax.plot(range(n), [0] * n, "o", color="#e8eef5", ms=3.2, alpha=0.8)  # the bridges
    fig.savefig("assets/two-rivers.png", facecolor=fig.get_facecolor())
    Image.open("assets/two-rivers.png").convert("RGB").save(
        "assets/two-rivers.jpg", quality=88, optimize=True)


if __name__ == "__main__":
    main()
