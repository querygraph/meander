# Counting Arnold's Meanders in Python

### A Python companion to *Counting Arnold's Meanders with Verified Algorithms*

In 1988 Vladimir Arnold asked: in how many ways can a river cross a straight road $n$ times? The
river comes in from the south, crosses the road $n$ times without ever crossing itself, and
leaves to the east. The answers start $1, 1, 1, 2, 3, 8, 14, 42, 81, 262, \ldots$ (OEIS
A005316), and no formula is known.

The paper ([First Pair](https://firstpair.org/books/arnold-meanders/)) defines these numbers in
the Lean proof assistant and proves two fast algorithms correct. This notebook teaches Python by
building the same algorithms from scratch: the definition by brute force, the search with its
parity rule, and the transfer matrix, run first on one core and then on all of them. It assumes
no Python.

**How the notebook teaches.** Every Python feature is explained once, in a text cell, before the
first code cell that uses it, and then used freely. Each function is defined once. The index at
the end lists every feature with the section that introduces it.

**Python is not Lean.** In Lean, the fast algorithms are *proved* equal to the definition, for
every $n$. In Python we can only *test* them: we check them against each other, and against the
values that Lean's kernel has certified. Those values are copied into Section 4.

**Running it.** Any Python 3.10 or later runs Sections 1 to 8; Section 9 also needs Matplotlib.
Run the cells in order from the top.

## Contents

1. Python as a calculator
2. Crossing chords
3. A river is a permutation
4. Checking what we cannot prove
5. Closed meanders
6. A search with a parity rule
7. The transfer matrix
8. All cores at once
9. Pictures and growth
10. Index of Python features
