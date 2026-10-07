## 5. Closed meanders

A *closed* meander is a closed river, a loop, crossing the road $2n$ times. To count each loop
once, fix where it starts and which way it goes: start at the westmost bridge $0$ and leave it
upward. The river then visits bridges $\sigma(0) = 0, \sigma(1), \ldots, \sigma(2n-1)$, and arc
$k$ joins $\sigma(k)$ to $\sigma(k+1)$, indices taken modulo $2n$, so the last arc returns to
bridge $0$. Even arcs are above the road and odd arcs below.

**Proofs as arguments.** To evaluate $\sigma$ at position $k \bmod 2n$ we need an element of
`Fin (2 * n)`, so a proof that $k \bmod 2n < 2n$. The Mathlib lemma `Nat.mod_lt` is a function:
given `x` and a proof of `0 < y`, it returns a proof of `x % y < y`. We apply it like any
function, with `_` for the `x` that Lean can infer.

```lean
@include Arnold/Basic.lean def closedPt
```

**Quantifying over proofs.** The normalization "start at bridge 0" says `σ ⟨0, h⟩ = ⟨0, h⟩`,
which only makes sense when $0 < 2n$. `∀ h : 0 < 2 * n, …` says: for every proof `h` of
`0 < 2 * n`, the following holds. For $n = 0$ there is no such proof, and the condition is
empty.

```lean
@include Arnold/Basic.lean def IsClosedMeander
```

```lean
@include Arnold/Basic.lean instance {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) : Decidable (IsClosedMeander
```

```lean
@include Arnold/Basic.lean def closedMeanderCount
```

The closed counts start $1, 2, 8$ for $n = 1, 2, 3$. The next section proves the classical fact
behind the second line: a closed meander of order $n$ is an open meander with $2n - 1$
crossings.

```lean
#eval (closedMeanderCount 1, closedMeanderCount 2, closedMeanderCount 3)
#eval (openMeanderCount 1, openMeanderCount 3, openMeanderCount 5)
```
