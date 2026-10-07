## 9. The search is correct

The main theorem of `Arnold/Fast.lean` is `openMeanderCount n = meanderCount n` for every `n`.
The proof has two steps.

1. The search equals filtering an explicit list `perms n (List.range n)` of all orderings, built
   by the same recursion as `dfs`, because a pruned branch contains no meanders. This needs the
   parity rule to be *sound*: a partial river that fails it really cannot be finished.
2. Permutations of `Fin n` correspond one to one with the members of that list.

**Cons and the `·` shorthand.** `x :: l` is the list `l` with `x` in front. `l.flatMap f`
applies `f`, which returns a list, to every entry and concatenates the results. `(x :: ·)` is
short for `fun l => x :: l`: a `·` in parentheses marks the argument of an anonymous function.
`perms k rem` lists all orderings of `rem`, built exactly like the search tree of `dfs`.

```lean
@include Arnold/Fast.lean def perms
```

### Bookkeeping for `NoCross`

These lemmas use only features we have seen. `NoCross P (L+1)` adds the conditions on arc `L`
to `NoCross P L`. It only looks at the points `P 0, …, P L`. And appending to a crossing order
does not move points already determined.

```lean
@include Arnold/Fast.lean theorem noCross_succ
```

```lean
@include Arnold/Fast.lean theorem noCross_mono
```

```lean
@include Arnold/Fast.lean theorem noCross_congr_pts
```

```lean
@include Arnold/Fast.lean theorem noCross_lpt_succ
```

```lean
@include Arnold/Fast.lean theorem lpt_append
```

### Step 1: the search equals filtering `perms`

**Membership, permutations of lists, and `cases`.** `x ∈ l` says that `x` is an entry of `l`.
`l.Perm l'` says that `l` and `l'` have the same entries, counted with multiplicity, in any
order. `cases l with | nil => … | cons x s => …` splits on how the list `l` was built: empty,
or `x :: s`. `simp … at h` simplifies a hypothesis, as `rw … at h` rewrites one.

```lean
@include Arnold/Fast.lean theorem mem_perms
```

**`Nodup`, implicit lambdas, `.symm`.** `l.Nodup` says that `l` has no repeated entries.
`List.nodup_flatMap` reduces it for `flatMap` to two facts: each piece has no repeats, and
different pieces share no entries. In `fun {x y} hxy => …` the braces bind `x` and `y` as
implicit arguments of the function. For `h : a = b`, `h.symm : b = a`. `simp only [l] at h h'`
simplifies two hypotheses at once.

```lean
@include Arnold/Fast.lean theorem nodup_perms
```

### The parity rule is sound

`ind P j i` is `1` if point `i` of the path `P` lies strictly inside arc `j`, else `0`.

```lean
@include Arnold/Fast.lean def ind
```

**Finite sums, `suffices`, and other induction principles.** `∑ i ∈ Finset.Ico a b, f i` is
the sum of `f i` over $a \le i < b$. `Finset` is Mathlib's type of finite sets, and
`Finset.Ico a b` is the interval $[a, b)$. `suffices H : Q by tac` states an intermediate goal
`Q`, proves the original goal from `H : Q` with `tac`, and leaves `Q` to prove next.
`induction m, hm using Nat.le_induction with | base => … | succ m hm ih => …` is induction that
starts at a number other than zero: from `hm : t + 1 ≤ m` it proves the claim for `m = t + 1`
and then from `m` to `m + 1`. `intro _` introduces a hypothesis without naming it. `if_congr`
says that two `if`s agree when their conditions and branches do, and `not_not` removes a double
negation.

The proof follows the mathematical argument: walk along the river from the current point to
the east end, and keep the count of ends inside arc `j` even, two at a time. Each later
same-side arc puts both of its ends inside arc `j` or neither.

```lean
@include Arnold/Fast.lean theorem parity_future
```

**A recursive proof.** A theorem can be proved by pattern matching and recursion, exactly like a
function is defined; the recursive call is the induction hypothesis. `countP_eq_sum` relates
counting the entries of `s` to summing over their positions on the path `q ++ s`, by recursion
on `s`.

```lean
@include Arnold/Fast.lean theorem countP_eq_sum
```

**Rewriting backwards.** `rw [← h]` rewrites with `h : a = b` from right to left, replacing `b`
by `a`. With that, soundness of the parity rule follows from `parity_future`: if `q ++ s` is a
meander and `s` uses the bridges `r`, then `q` passes the parity test with remaining bridges
`r`.

```lean
@include Arnold/Fast.lean theorem parityOK_of_noCross
```

**`obtain` with a type, and `swap`.** `obtain rfl : n = p.length := by omega` proves the
equation and substitutes it at once. `swap` exchanges the first two goals, so the second can be
proved first. With these, the search equals the count of meanders among the orderings in
`perms`, at every node of the search tree.

```lean
@include Arnold/Fast.lean theorem dfs_eq
```

### Step 2: permutations of `Fin n` are the orderings in `perms`

**Lists from functions.** `List.ofFn f`, for `f : Fin n → α`, is the list `[f 0, …, f (n-1)]`.
`toList σ` is the crossing order of `σ` as a list of numbers.

```lean
@include Arnold/Fast.lean def toList
```

```lean
@include Arnold/Fast.lean theorem pathPt_eq_lpt
```

```lean
@include Arnold/Fast.lean theorem toList_perm
```

`congrFun h x : f x = g x` applies an equation of functions `h : f = g` at a point.

```lean
@include Arnold/Fast.lean theorem toList_injective
```

**Indexing with a proof.** `l[i]'h` is entry `i` of the list `l`, where `h : i < l.length`
proves that the index is in range, so no default is needed. Below, `let f : Fin n → Fin n :=
…` defines inside a proof the function that a list `l` describes. `Equiv.ofBijective` turns a
bijective function into an equivalence, and on a finite type an injective function is
bijective (`Finite.injective_iff_bijective`).

```lean
@include Arnold/Fast.lean theorem exists_toList_eq
```

**Instance arguments.** In `(Q : List ℕ → Prop) [DecidablePred Q]`, the square brackets take
an *instance* argument: callers never pass it, because Lean finds it by type class search.
`DecidablePred Q` says that `Q l` is decidable for every `l`. `Finset.card_bij` proves that two
finite sets have the same size, given a map between them that sends one into the other, is
injective, and hits everything.

```lean
@include Arnold/Fast.lean theorem card_eq_countP
```

### The main theorems

`Fintype.card_congr` says that equivalent types have the same number of elements, and
`Equiv.subtypeEquivRight` says that two subtypes of the same type are equivalent when their
conditions are equivalent. From `h : P` and `hn : ¬ P`, `absurd h hn` proves anything; the
first theorem uses it to dismiss the impossible `k < 0`.

```lean
@include Arnold/Fast.lean theorem openMeanderCount_eq_meanderCount
```

```lean
@include Arnold/Fast.lean theorem closedMeanderCount_eq_meanderCount
```

**`#print axioms`.** Lean proofs may use a few standard axioms of mathematics beyond its type
theory: `propext` (equivalent propositions are equal), `Quot.sound` (for quotient types), and
`Classical.choice` (the axiom of choice). `#print axioms t` lists the axioms that the theorem `t`
depends on, through all the lemmas it uses. Nothing else is assumed.

```lean
#print axioms openMeanderCount_eq_meanderCount
```

Now a value of Arnold's number can be *proved* with the fast search: rewrite with the theorem,
then let the kernel run `meanderCount`. The `;` runs the two tactics in turn. (Brute force
would check $8! = 40{,}320$ permutations inside the kernel; the search visits about 500
partial rivers.)

```lean
example : openMeanderCount 8 = 81 := by rw [openMeanderCount_eq_meanderCount]; decide
```
