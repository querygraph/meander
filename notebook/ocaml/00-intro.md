# Counting Arnold's Meanders in OCaml

### An OCaml companion to *Counting Arnold's Meanders with Verified Algorithms*

In 1988 Vladimir Arnold asked: in how many ways can a river cross a straight road $n$ times? The
river comes in from the south, crosses the road $n$ times without ever crossing itself, and
leaves to the east. The answers start $1, 1, 1, 2, 3, 8, 14, 42, 81, 262, \ldots$ (OEIS
A005316), and no formula is known.

The paper ([First Pair](https://firstpair.org/books/arnold-meanders/)) defines these numbers in
the Lean proof assistant and proves two fast algorithms correct. This notebook teaches OCaml by
building the same algorithms: the definition by brute force, the search with its parity rule,
and the transfer matrix, first on one core and then on all of them with OCaml 5's domains. The
last section explains how the repository's OxCaml program goes further, with OxCaml's
data-race-free parallelism and unboxed values. No OCaml is assumed.

**How the notebook teaches.** Every OCaml feature is explained once, in a text cell, before the
first code cell that uses it, and then used freely. Each function is defined once. The index at
the end lists every feature with the section that introduces it.

**OCaml is not Lean.** Lean proves the fast algorithms equal to the definition for every $n$.
Here we test them, against each other and against the values certified in Lean.

**Running it.** The notebook runs in the OCaml Jupyter kernel
([ocaml-jupyter](https://github.com/akabe/ocaml-jupyter)) with OCaml 5 and the `unix` library.
Run the cells in order from the top.

## Contents

1. OCaml as a calculator
2. Crossing chords
3. A river is a permutation
4. Checking what we cannot prove
5. Closed meanders
6. A search with a parity rule
7. The transfer matrix
8. All cores at once
9. OxCaml
10. Index of OCaml features
