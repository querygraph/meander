# Arnold's meander problem in Lean 4

*In how many ways can a river cross a straight road `n` times?* (V. I. Arnold, 1988)

No closed formula is known. This project states the problem precisely, proves facts about it,
and computes the counts with algorithms that are **proved** to give exactly the right answer.

- **Paper:** [*Counting Arnold's Meanders with Verified Algorithms*](https://firstpair.org/books/arnold-meanders/) on the
  First Pair library's Math shelf ([PDF](https://firstpair.org/arnold-meanders/pdf/),
  [EPUB](https://firstpair.org/arnold-meanders/epub/), [online](https://firstpair.org/read/arnold-meanders/));
  source in [`paper/meanders.tex`](paper/meanders.tex).
- **Visualization:** [firstpair.org/learn/arnold-meanders](https://firstpair.org/learn/arnold-meanders/)
  (source [`viz/index.html`](viz/index.html)).
- **Film:** a two-minute recording of the visualization, in the
  [v1.0.0 release](https://github.com/querygraph/meander/releases/tag/v1.0.0).
- **Blog post:** [`docs/blog/arnold-meanders/post.md`](docs/blog/arnold-meanders/post.md), for querygraph.ai.
- **Notebooks:** three companions to the paper, each teaching a language through the
  meander algorithms ([below](#notebooks)).
- **Fast counters:** parallel transfer matrices in [Rust](rust/) and [OxCaml](oxcaml/)
  ([below](#fast-counters)).

| File | Contents |
|---|---|
| `Arnold/Basic.lean` | The specification: `openMeanderCount n` = number of permutations of `Fin n` that are meanders; closed meanders; `0 < openMeanderCount n ≤ n!` |
| `Arnold/ClosedOpen.lean` | `closedMeanderCount n = openMeanderCount (2n - 1)` for all `n ≥ 1` |
| `Arnold/Catalan.lean` | `closedMeanderCount n ≤ catalan n ^ 2`, by injecting meanders into pairs of Dyck words |
| `Arnold/Defs.lean`, `Arnold/Fast.lean` | A pruned search (crossing check + parity argument), proved equal to the spec |
| `Arnold/TM/` | A transfer matrix: scan the road west to east, tracking how the open strands connect; proved equal to the spec (`TM.tmCount_eq`) |
| `Arnold/Values.lean` | Certified values: kernel-checked for `n ≤ 13`, `native_decide` for `n ≤ 24` |
| `Main.lean` | Executable `meanders`, running the transfer matrix |

## The transfer-matrix proof

`TM.tmCount m` counts action sequences (each point opens or closes its arc on each side) that a
state machine accepts, merging equal states layer by layer and dropping states with more open
arcs than the remaining points can close. The proof that it equals `openMeanderCount m`:

1. **Counting** (`TM/Count.lean`): the layered count, with merging and pruning, equals the number
   of accepted sequences.
2. **Decoding** (`TM/Decorated.lean` … `TM/Decode.lean`): a decorated machine also records each
   open strand's actual piece of river. A 20-part invariant, preserved by all five kinds of step,
   shows the final piece of an accepted run is a meander.
3. **Re-encoding** (`TM/EncodeDecode.lean`): the meander's own action sequence is the run's.
4. **Encoding** (`TM/Meander.lean` … `TM/Encode.lean`): every meander's action sequence is
   accepted (no loop is ever closed: a discrete intermediate-value argument on path positions)
   and decodes back to the meander.
5. **Bijection** (`TM/Main.lean`): accepted sequences and meanders correspond one-to-one.

## Usage

```
lake build                               # check all proofs (~3 min)
lake build meanders && .lake/build/bin/meanders 30   # n ≤ 30 in ~30 s
```

Values (OEIS A005316): 1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538, 1828, 3926, 13820, 30694,
110954, 252939, 933458, 2172830, 8152860, 19304190, …, 1503962954930 (n = 30). All values up to
n = 32 agree with the OEIS b-file.

## Notebooks

Each notebook teaches its language from scratch by building the meander algorithms, introducing
every language feature once, in a text cell, before the first code that uses it. They are saved
with their outputs.

| Notebook | Language | Kernel |
|---|---|---|
| [`arnold-meanders-lean.ipynb`](notebook/arnold-meanders-lean.ipynb) | Lean 4: the library's own code, from the definitions to the proof that the search is correct and the transfer matrix's counting argument | *Lean 4 (Arnold)*: `notebook/kernel/install.sh` |
| [`arnold-meanders-python.ipynb`](notebook/arnold-meanders-python.ipynb) | Python: brute force, the parity search, the transfer matrix, process-parallel layers, pictures | any Python 3.10+, with Matplotlib |
| [`arnold-meanders-ocaml.ipynb`](notebook/arnold-meanders-ocaml.ipynb) | OCaml 5: the same algorithms with variants, functors and domains, and how OxCaml goes further | [ocaml-jupyter](https://github.com/akabe/ocaml-jupyter) |

The notebooks are built from Markdown sources in `notebook/{lean,python,ocaml}/` by
`notebook/build.py`, which executes each in a fresh kernel and fails on any error. The Lean
notebook's code cells are cut from the library's source files, so each declaration appears
exactly as in `Arnold/`. The Lean kernel (`notebook/kernel/lean_kernel.py`) runs cells through the
[Lean REPL](https://github.com/leanprover-community/repl), each continuing from the one before.

```
notebook/kernel/install.sh                         # once: build the REPL, register the kernel
notebook/.venv/bin/python notebook/build.py lean   # or python, ocaml; all three by default
```

## Fast counters

[`rust/`](rust/) and [`oxcaml/`](oxcaml/) run the same machine as `TM.tmCount`, much faster and
without proofs. A state is packed into one 64-bit word: read along the cut, the open arcs form a
non-crossing matching, a bracket word. Each layer is spread over all cores in hash shards, each
with its own lock. Counts beyond 64 bits come from two sweeps, modulo `2^64` (or `2^63`) and
`2^61 - 1`, joined by the Chinese remainder theorem. Every count is checked against the values
certified in Lean and against the OEIS; [`bench/run.sh`](bench/run.sh) runs the benchmarks.

Timed runs on an Intel Xeon W-2191B (18 cores, 36 threads, 128 GB), one `n` per process, all
36 threads; every count equals the OEIS term. Raw results are in [`bench/results/`](bench/results/).

| n | open meanders | largest layer (states) | Rust | OxCaml |
|---|---|---|---|---|
| 40 | 165,597,452,660,771,610 | 22,007,687 | 3.3 s | 2.3 s |
| 42 | 1,733,609,081,727,968,492 | 56,637,978 | 6.1 s | 5.3 s |
| 44 | 18,276,178,714,484,582,264 | 142,200,409 | 30 s | 25 s |
| 46 | 193,909,492,888,406,631,692 | 349,363,805 | 79 s, 13.6 GB | 62 s, 22.9 GB |
| 49 | 8,499,066,628,515,413,229,282 | 1,415,496,980 | 516 s, 51.6 GB | |
| 50 | 22,206,891,674,746,169,557,410 | 2,252,446,749 | 1,052 s, 79.2 GB | |

From `n = 44` on, a count takes two sweeps (two moduli). Memory is the limit: `n = 50` is the
largest that fits in 128 GB, at about 35 bytes per state of the largest layer. On the same
machine the verified Lean program `meanders` takes 160 s for all `n ≤ 32`.

Both programs scale to the physical cores and no further (`n = 40`):

| threads | 1 | 4 | 9 | 18 | 36 |
|---|---|---|---|---|---|
| Rust | 20.1 s | 5.9 s | 3.4 s | 2.9 s | 3.2 s |
| OxCaml | 20.2 s | 5.5 s | 2.8 s | 2.2 s | 2.2 s |

OxCaml is written with OxCaml's data-race-free `Parallel` scheduler and capsules. On one thread
the two programs are equally fast; OxCaml scales better, probably because it pre-sizes each
layer's tables from the previous layers, so a shard rarely rehashes while its lock is held. It
needs more memory. Details are in
[`rust/README.md`](rust/README.md) and [`oxcaml/README.md`](oxcaml/README.md).

## Related work

The permutations counted by the specification are the *meandric permutations* of Borga, Gwynne
and Sun, [*Permutons, meanders, and SLE-decorated Liouville quantum
gravity*](https://arxiv.org/abs/2207.02319) (J. Eur. Math. Soc., 2026), who conjecture that random
meanders converge to Liouville quantum gravity decorated by two independent SLE₈ curves. Section 7.2
of the paper uses our counts to test the matching exponent conjecture of Di Francesco, Golinelli
and Guitter, α = (29 + √145)/12 ≈ 3.4201.
