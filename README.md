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

Largest values so far, each equal to the OEIS term. These ran on an Apple M1 Max (10 cores,
64 GB) while other jobs were running, so the times are indicative; timed runs on an 18-core,
128 GB machine are recorded in [`bench/results/`](bench/results/).

| n | open meanders | largest layer (states) | Rust, 10 threads |
|---|---|---|---|
| 44 | 18,276,178,714,484,582,264 | 142,200,409 | 83 s |
| 45 | 74,661,728,661,167,809,752 | 223,196,394 | 244 s |
| 46 | 193,909,492,888,406,631,692 | 349,363,805 | 464 s |
| 47 | 794,337,831,754,570,367,812 | 568,622,062 | 990 s |
| 48 | 2,069,504,277,256,274,074,724 | 872,527,061 | 3,400 s, 22.8 GB |

On the same laptop, the OxCaml program, written with OxCaml's data-race-free `Parallel`
scheduler and capsules, matches the Rust program's wall time for n = 38 to 42 (for example 3.3 s
against 3.6 s at n = 40), with somewhat more memory; see [`oxcaml/README.md`](oxcaml/README.md).
The verified Lean program takes 93 s for n = 32, which Rust does in 0.25 s.

## Related work

The permutations counted by the specification are the *meandric permutations* of Borga, Gwynne
and Sun, [*Permutons, meanders, and SLE-decorated Liouville quantum
gravity*](https://arxiv.org/abs/2207.02319) (J. Eur. Math. Soc., 2026), who conjecture that random
meanders converge to Liouville quantum gravity decorated by two independent SLE₈ curves. Section 7.2
of the paper uses our counts to test the matching exponent conjecture of Di Francesco, Golinelli
and Guitter, α = (29 + √145)/12 ≈ 3.4201.
