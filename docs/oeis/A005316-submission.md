# OEIS A005316: extending the b-file to n = 58 (draft)

Status: **draft, not submitted.** It goes in through the OEIS edit form ("edit" on
https://oeis.org/A005316) under the submitter's OEIS account. The new b-file is
`docs/oeis/b005316.txt` (n = 0..58).

All three new terms were computed by two separately written programs (Rust and OxCaml, with
different state encodings). Each program checked each term through two independent splits,
and both programs reproduce every published term.

## New terms

```
56 28235899288344793178333732
57 116936079373841873422508566
58 308496356015441090010351094
```

## Edits to the entry

**LINKS.** Replace the b-file line

    Andrew Howroyd, Table of n, a(n) for n = 0..55 (first 44 terms from Iwan Jensen)

with

    Andrew Howroyd and Alexy Khrabrov, Table of n, a(n) for n = 0..58 (first 44 terms from Iwan Jensen, terms 44..55 from Andrew Howroyd)

and upload `b005316.txt` as the new b-file. Its lines 0..55 are byte-for-byte the current
values.

**LINKS** (new):

    Alexy Khrabrov, Counting Arnold's Meanders with Verified Algorithms, FirstPair, 2026.
    (https://firstpair.org/books/arnold-meanders/)

    Alexy Khrabrov, Lean 4, Rust and OxCaml programs (https://github.com/querygraph/meander)

**EXTENSIONS** (new):

    a(56)-a(58) added to b-file by Alexy Khrabrov, Oct 10 2026

## Discussion (for the editors)

How the new terms were computed:

- **Method: meet in the middle.** A(n) = Σ_s F_k(s) · G_{n−k}(s), where:
  - F_k is the layer of transfer-matrix states after k bridges from the west (open meanders
    with the east end not yet placed);
  - G_r counts the ways to finish from a state in r further bridges, built backwards by
    inverse transitions and pruned by depth;
  - the split is k = ⌈n/2⌉.

  The decomposition, and the agreement of its finishing counts with the forward transfer
  matrix, is proved in Lean 4 (`Arnold/TM/Middle.lean`, theorem `meet`). The Lean machine
  itself is proved to count open meanders (`Arnold/TM`).
- **Check by a second split.** Every value was also computed through the split
  k = ⌈n/2⌉ − 1, which uses different forward and backward layers. Both splits agree for every
  n ≤ 58.
- **Agreement with the published terms.** The same program reproduces a(0)..a(55) of the
  current b-file exactly.
- **Two independent implementations.** Rust and OxCaml, written separately in the same
  repository with different state encodings, each computed every a(n) for n ≤ 58. They agree
  on all 59 values, and each confirmed every value by its own second split.
- **Arithmetic.** Counts are exact: u128 in Rust, two 62-bit limbs in OxCaml. No modular
  reconstruction is involved.
- **Computation.** The layers were kept on disk (an out-of-core store, extended horizon by
  horizon from 48 to 58) on an 18-core Xeon W-2191B with 128 GB of RAM. The extension from 56
  to 58 took about 15 hours. The largest layer had 23.2 × 10^9 states. Results and logs are in
  the repository under `bench/results/` (`morrobay-mitm-58.tsv` from Rust,
  `morrobay-ox-mitm-58.tsv` from OxCaml, which took 8 hours to horizon 58).

Sanity check: the ratios a(56)/a(54) = 10.88, a(57)/a(55) = 10.90 and a(58)/a(56) = 10.93
keep rising slowly toward the known growth constant, about 12.26 per two crossings.
