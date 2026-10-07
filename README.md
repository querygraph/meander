# Arnold's meander problem in Lean 4

*In how many ways can a river cross a straight road `n` times?* (V. I. Arnold, 1988)

No closed formula is known. This project formalizes the question and proves facts about it.

| File | Contents |
|---|---|
| `Arnold/Defs.lean` | Core-only definitions: crossing chords, `NoCross`, the search `meanderCount`, and its array-based compiled implementation (`@[csimp]`, proved equal) |
| `Arnold/Basic.lean` | The specification: `openMeanderCount n` = number of permutations of `Fin n` that are meanders; closed meanders; `0 < openMeanderCount n ≤ n!` |
| `Arnold/ClosedOpen.lean` | `closedMeanderCount n = openMeanderCount (2n - 1)` for all `n ≥ 1` |
| `Arnold/Fast.lean` | `openMeanderCount n = meanderCount n` for all `n`, including soundness of the parity pruning; kernel-checked values for `n ≤ 9` |
| `Arnold/Catalan.lean` | `closedMeanderCount n ≤ catalan n ^ 2` and `openMeanderCount (2n+1) ≤ catalan (n+1) ^ 2`, by injecting meanders into pairs of Dyck words |
| `Main.lean` | Executable `meanders` that prints the counts |

```
lake build                         # check all proofs (~3 min)
lake build meanders && .lake/build/bin/meanders 17   # n ≤ 15 in ~5 s
```

Values (OEIS A005316): 1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538, 1828, 3926, 13820, 30694, 110954, …
