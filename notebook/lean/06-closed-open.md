## 6. Closed meanders are open meanders

Take a closed meander with $2n$ crossings, started at bridge $0$. Delete that bridge: the two
arcs at it now run off to infinity in the west. Turn the picture through $180°$. The river now
comes in from infinity below the road, crosses it $2n - 1$ times, and leaves to the east: an
open meander. Every step can be undone, so the two kinds are in bijection. In Lean the
construction goes the other way, from an open meander $\tau$ with $2n+1$ crossings to a closed
one with $2n+2$.

**Equivalences.** `Equiv α β`, written `α ≃ β`, is a bijection packaged with its inverse. A
permutation is an `Equiv` from a type to itself. For `e : α ≃ β`, `e.symm : β ≃ α` is the
inverse, and for `f : β ≃ γ`, `e.trans f : α ≃ γ` is "first `e`, then `f`". `Fin.revPerm` is the
reversal $i \mapsto n - 1 - i$ of `Fin n`, the $180°$ turn. Mathlib's `Perm.decomposeFin` is an
equivalence between permutations of `Fin (n+1)` and pairs (where $0$ goes, a permutation of
`Fin n`). Its inverse, applied to `(0, τ.trans Fin.revPerm)`, builds the permutation that fixes
$0$ and follows the reversed $\tau$ on the rest.

**`open`.** `open Equiv` lets us write `Perm` for `Equiv.Perm`. Like `namespace`, it lasts until
the end of the enclosing namespace.

```lean
open Equiv

@include Arnold/ClosedOpen.lean def closeUp
```

**Proofs of `∀` are functions.** A proof of `∀ x, P x` is a function that takes `x` and returns
a proof of `P x`, so it can be written with `fun`. The next theorem says that `NoCross` holds
for one path exactly when it holds for another, provided the two paths agree on which pairs of
arcs alternate. The proof wraps the hypothesis `h` in Mathlib's *congruence lemmas*:
`forall₂_congr` says that if two statements are equivalent for every `x` and `y`, then so are
`∀ x y, …`; `imp_congr_right` and `not_congr` do the same for `→` and `¬`.

```lean
@include Arnold/ClosedOpen.lean theorem noCross_congr
```

**Disjunction and `this`.** `A ∨ B` means *A or B*. `pathPt_cases` says each point on the path
of an open meander with $2n+1$ crossings is the south end, a bridge, or the east end. `split_ifs
with h0 h1` names the facts for each nested `if` in turn. `have := e` without a name calls the
new fact `this`. `(σ i).isLt` is the proof stored in the `Fin` value `σ i` that its number is
below the bound.

```lean
@include Arnold/ClosedOpen.lean theorem pathPt_cases
```

**More tactics.** The next proof says that after the turn, closed point $k$ is open point $k$
reflected by $x \mapsto 2n+1-x$.

* `closedPt (n := n + 1) …` passes the implicit argument `n` by name.
* `↓reduceDIte` is `↓reduceIte` for dependent `if`.
* `ext` proves two `Fin` values equal by proving their numbers equal; in general it reduces
  equality to equality of components or values.
* `rcases e with h | h` splits on a disjunction `e`, naming the fact in each case.
* `t <;> s` runs `s` on every goal that `t` produces.

```lean
@include Arnold/ClosedOpen.lean theorem closedPt_closeUp
```

**`refine` and holes; `generalize`.** `refine e` proves the goal with an expression `e` that may
contain holes `?_`. Each hole becomes a new goal. Below, the hole is the body of a `fun`: for
each pair of arcs, show that they alternate before the turn exactly when they alternate after
it. `generalize pathPt τ j = a at *` replaces the expression by a fresh variable `a`
everywhere. That leaves `omega` a problem in plain variables, which it solves, using the
`pathPt_cases` facts for each point.

```lean
@include Arnold/ClosedOpen.lean theorem noCross_closeUp_iff
```

```lean
@include Arnold/ClosedOpen.lean theorem closeUp_zero
```

**Injectivity, `exact` and `simpa`.** `exact e` closes the goal with the term `e`, whose type
must be the goal. `Function.Injective f` means $f(a) = f(b) \to a = b$. If
`h : a = b`, then `congrArg f h : f a = f b`. `simpa [l] using e` simplifies both the goal and
the term `e`, then closes the goal with `e`. `Equiv.ext` proves two equivalences equal by
proving they agree at every point.

```lean
@include Arnold/ClosedOpen.lean theorem closeUp_injective
```

**Existentials and `obtain`.** `∃ x, P x` says that some `x` satisfies `P`. It is proved by an
anonymous constructor `⟨x, proof⟩`, and used by `obtain ⟨x, hx⟩ := h`, which takes the witness
and its property out of `h`. Patterns nest. The pattern `rfl` means: the fact here is an
equation `v = e`, so replace `v` by `e` everywhere. `subst h` does the same for a hypothesis
`h : v = e`, and `rw [l] at h` rewrites inside a hypothesis instead of the goal. `congr` proves
`f a = f b` from `a = b`.

```lean
@include Arnold/ClosedOpen.lean theorem closeUp_surjective
```

**Counting by a bijection.** Mathlib's `Fintype.card_of_bijective` says that two finite types
have the same number of elements if a bijective function maps one onto the other. Here the
function is given by name, `(f := …)`, and the bijectivity proof is the pair
`⟨injective, surjective⟩`, with both left as holes. An element `τ` of a subtype has the two
components `τ.1`, the value, and `τ.2`, the proof; `Subtype.ext` proves two elements equal from
equal values. On a proof of `A ↔ B`, `.1` and `.2` mean `.mp` and `.mpr`. `fun _ => e` ignores
its argument. `symm` turns a goal `a = b` into `b = a`. `rintro pattern` is `intro` followed by
`rcases` with that pattern.

```lean
@include Arnold/ClosedOpen.lean theorem closedMeanderCount_succ
```

The last proof writes $n = m + 1$, using a hypothesis `hn : 1 ≤ n` and the Mathlib lemma
`Nat.exists_eq_add_of_le'`, and finishes with `congr 1`, which reduces `f a = f b` to `a = b`,
one level deep. With the theorem proved, the table in Section 5 is no coincidence: it holds
for every $n$.

```lean
@include Arnold/ClosedOpen.lean theorem closedMeanderCount_eq
```
