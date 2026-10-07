## 8. Fast code that provably computes the same thing

`dfs` is written for proving: lists, propositions, and decision procedures assembled by type
class search. Looking up entry `k` of a list takes `k` steps. The library runs a second version
on arrays, with Boolean tests written out by hand, and proves that both compute the same
function. A compiler annotation then makes every call to `dfs` run the fast one. The speed-up
cannot change an answer, because the proof says so.

**Boolean operators.** On `Bool`, `&&` is *and*, `||` is *or*, `!b` is *not*, and `a == b` and
`a != b` test equality and inequality. Unlike `∧` and `∨`, these compute.

`allLt f t` checks `f j` for every `j < t`, by structural recursion on `t`.

```lean
@include Arnold/Defs.lean def allLt
```

**Induction.** `induction t with | zero => … | succ t ih => …` proves a statement for every
natural number `t`: once for `0`, and once for `t + 1` with the *induction hypothesis* `ih`,
the statement for `t`. Two more tactics appear in the proof. `constructor` splits a goal
`A ↔ B` into the two directions, or `A ∧ B` into its two halves, and `rintro` patterns like
`⟨h, ht⟩` take a conjunction apart. `Nat.lt_succ_iff_lt_or_eq` turns `j < t + 1` into
`j < t ∨ j = t`.

```lean
@include Arnold/Defs.lean theorem allLt_iff
```

**Arrays and `let`.** `Array Nat` is a sequence stored contiguously in memory, with
constant-time access `a.getD k d`, size `a.size`, and `a.push x` to append. `l.toArray` converts
a list. `let x := e` inside a definition names an intermediate value. These are the array
versions of `lpt`, `StepOK` and `ParityOK`.

```lean
@include Arnold/Defs.lean def apt
```

```lean
@include Arnold/Defs.lean def stepOKb
```

```lean
@include Arnold/Defs.lean def parityOKb
```

```lean
@include Arnold/Defs.lean def dfsArr
```

```lean
@include Arnold/Defs.lean def dfsFast
```

**Three bridges between the versions.** `split` splits on the first `if` in the goal, like
`split_ifs` but without names. `simp_all` simplifies every hypothesis and the goal with each
other until nothing changes. `Bool.eq_iff_iff` turns an equation of Booleans into an `↔`, and
`decide_eq_true_iff` says `decide p = true ↔ p`. For a disjunction `h : A ∨ B`,
`h.resolve_left hna : B` uses `hna : ¬ A`. `Or.inl a : A ∨ B` and `Or.inr b : A ∨ B` build a
disjunction from either side. In a term, `show P from e` states the type `P` of `e`, and
`funext h` proves two functions equal from a proof `h` that they agree at every point.

```lean
@include Arnold/Defs.lean theorem apt_toArray
```

```lean
@include Arnold/Defs.lean theorem stepOKb_toArray
```

```lean
@include Arnold/Defs.lean theorem parityOKb_toArray
```

**Attributes, `@`, and `apply`.** `@[attr]` before a declaration attaches an *attribute*.
`@[csimp]` on a theorem `@f = @g` tells the compiler to replace `f` by `g` in all compiled code.
Lean accepts it only for a proved equation. `@f` refers to `f` with all its arguments explicit,
so `@dfs = @dfsFast` is an equation between two functions. The tactic `funext n k` reduces it
to an equation for each `n` and `k`. `apply l` proves the goal by the lemma `l` and leaves its
hypotheses as new goals. `List.map_congr_left` says that two maps over a list agree if the
functions agree on each entry.

```lean
@include Arnold/Defs.lean @[csimp] theorem dfs_eq_dfsFast
```

The counter is declared after the `@[csimp]` theorem, so its compiled code calls `dfsArr`.

```lean
@include Arnold/Defs.lean def meanderCount
```

```lean
#eval (List.range 14).map meanderCount
```

These fourteen values take a fraction of a second. Brute force would test
$13! \approx 6 \cdot 10^9$ permutations for the last one alone.
