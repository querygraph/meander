# Arnold's meander problem in Lean 4

*In how many ways can a river cross a straight road `n` times?* (V. I. Arnold, 1988)

No closed formula is known. This project states the problem precisely, proves facts about it,
and computes the counts with algorithms that are **proved** to give exactly the right answer.

- **Paper:** [*Counting Arnold's meanders with verified algorithms*](paper/meanders.pdf)
  ([LaTeX source](paper/meanders.tex); builds with `tectonic paper/meanders.tex` or `pdflatex`).
- **Visualization:** [`viz/index.html`](viz/index.html), an animation of the rivers for
  n = 0 … 32; open it in a browser.

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
