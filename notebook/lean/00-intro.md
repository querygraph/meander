# Counting Arnold's Meanders in Lean

### A Lean companion to *Counting Arnold's Meanders with Verified Algorithms*

In 1988 Vladimir Arnold asked: in how many ways can a river cross a straight road $n$ times? The
river comes in from the south, crosses the road $n$ times without ever crossing itself, and
leaves to the east. The answers start $1, 1, 1, 2, 3, 8, 14, 42, 81, 262, \ldots$ (OEIS
A005316). No formula is known.

The paper ([First Pair](https://firstpair.org/books/arnold-meanders/)) describes a Lean 4
formalization that defines these numbers precisely and proves two fast algorithms correct: a
search with a parity rule, and a transfer matrix. This notebook teaches Lean by working through
that formalization. It assumes no Lean, only the mathematics of the paper's first sections.

**How the notebook teaches.** Every Lean feature is explained once, in a text cell, before the
first code cell that uses it. After that it is used freely. Every definition and theorem
appears once, and the Lean code is the library's code: the notebook builder copies each
declaration from the source files in `Arnold/`, so what you run here is what the paper
describes. The index at the end lists every feature with the section that introduces it.

**Running it.** Install the kernel once with `notebook/kernel/install.sh`, which builds the
[Lean REPL](https://github.com/leanprover-community/repl) for this project and registers the
Jupyter kernel *Lean 4 (Arnold)*. Run `lake build` in the repository first, so that Mathlib and
the library are compiled. The first cell imports Mathlib and takes up to a minute; the others
take a second or two each.

**How the cells fit together.** A Lean program is a file, read from top to bottom. Here the
file is cut into cells. Each cell continues from the cell run before it, as if they were one
file. Running a cell again replays it from the state it started in, so you can edit a
definition and run it again. A cell that begins with `import` starts a new file.

## Contents

1. Lean as a calculator
2. The road and the river: crossing chords
3. A river is a permutation
4. First theorems
5. Closed meanders
6. Closed meanders are open meanders
7. A search with a parity rule
8. Fast code that provably computes the same thing
9. The search is correct
10. The transfer matrix
11. Merging states is harmless
12. Using the whole library
13. Index of Lean features
