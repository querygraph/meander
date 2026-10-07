## 11. Merging states is harmless

`Arnold/TM/Count.lean` proves that `tmCount m` equals the number of action sequences, one action
per point $0, \ldots, m$, that drive the machine from `init` to `final`. The key idea: the number
of accepted continuations from a state depends only on the state. So adding up the counts of
equal states, or dropping states with no accepted continuation, changes no total.

**`set_option`.** `set_option name value` changes a setting of Lean for the rest of the file
(or, followed by `in`, for one declaration). The file switches off warnings about deprecated
library names.

**`Option.bind`.** `o.bind f` is `none` if `o` is `none`, and `f a` if `o` is `some a`. It chains
steps that may fail: `runFrom` runs the machine on a whole action sequence.

```lean
@include Arnold/TM/Count.lean set_option linter.deprecated false

@include Arnold/TM/Count.lean def sufWords
```

```lean
@include Arnold/TM/Count.lean def runFrom
```

```lean
@include Arnold/TM/Count.lean def cntFrom
```

```lean
@include Arnold/TM/Count.lean theorem cntFrom_zero
```

**`cases` with an equation.** `cases h : e with | none => … | some s' => …` splits on the
value of `e` and records which one it is as `h : e = none` or `h : e = some s'`.

```lean
@include Arnold/TM/Count.lean theorem cntFrom_succ
```

### Merging preserves weighted sums

`wsum g L` is $\sum c \cdot g(s)$ over the pairs $(s, c)$ of the layer `L`.

```lean
@include Arnold/TM/Count.lean def wsum
```

**Functional induction and `ring`.** For a function defined by recursion, Lean generates an
induction principle that follows its cases: `induction T using mergeAdj.induct with | case1 =>
… | case2 … | case3 … | case4 …` has one case for each branch of `mergeAdj`, with an induction
hypothesis wherever `mergeAdj` calls itself. `ring` proves equations that hold in every
commutative ring, such as $(c + c') g = c g + c' g$. A location `at h ⊢` makes `simp` or `rw`
work on the hypothesis `h` and on the goal, written `⊢`.

```lean
@include Arnold/TM/Count.lean theorem mergeAdj_wsum
```

`List.mergeSort_perm` says sorting permutes the list, and a sum over a permuted list is the
same. In the next proofs, `rw [← wsum]` rewrites with the definition of `wsum` backwards,
folding its body back into the name.

```lean
@include Arnold/TM/Count.lean theorem compress_wsum
```

```lean
@include Arnold/TM/Count.lean theorem filterMap_wsum
```

```lean
@include Arnold/TM/Count.lean theorem expand_wsum
```

### Dropping states that cannot be finished

These lemmas track the stack heights through a step. `cases σ <;> cases τ` tries all four
combinations of two Booleans.

```lean
@include Arnold/TM/Count.lean theorem length_setRef
```

```lean
@include Arnold/TM/Count.lean theorem stk_push_len
```

```lean
@include Arnold/TM/Count.lean theorem stk_pop_len
```

```lean
@include Arnold/TM/Count.lean theorem len_pos_of_getLast
```

**Splitting a step.** `rcases a with ⟨_ | _, _ | _⟩` splits the action pair into its four
Boolean cases (`false` is the first constructor of `Bool`, `true` the second). `split_ifs at h`
splits on the `if`s in a hypothesis. `dsimp only at h` unfolds definitions in `h` without using
lemmas. `reduceCtorEq` is a simproc that turns an equation between different constructors, such
as `none = some s`, into `False`, and `Option.some.injEq` turns `some a = some b` into `a = b`.
`if_pos hx` rewrites `if c then a else b` to `a` given `hx : c`, and `if_neg` to `b`.

```lean
@include Arnold/TM/Count.lean theorem step_len
```

```lean
@include Arnold/TM/Count.lean theorem cap_succ
```

`viable_of_cnt` says
that a state with at least one accepted continuation is viable. If a sum is not zero, then some
term is not zero (`List.exists_mem_ne_zero_of_sum_ne_zero`), and that term is a successor with
an accepted continuation.

```lean
@include Arnold/TM/Count.lean theorem viable_of_cnt
```

**`by_contra`.** `by_contra h` proves a goal `P` by assuming `h : ¬ P` and deriving a
contradiction. Dropping non-viable states changes no weighted sum, because their weight is
zero.

```lean
@include Arnold/TM/Count.lean theorem filter_viable_wsum
```

```lean
@include Arnold/TM/Count.lean theorem insertAdd_wsum
```

```lean
@include Arnold/TM/Count.lean theorem compressK_wsum
```

### The count

**Hypotheses about functions.** `layer_wsum` takes any merge `comp` together with a proof
`hcomp` that it keeps all weighted sums, `∀ g L, wsum g (comp L) = wsum g L`. By induction on
the number of points processed, the weighted count of accepted continuations of the current
layer never changes, so it equals the total for the initial state.

```lean
@include Arnold/TM/Count.lean theorem layer_wsum
```

```lean
@include Arnold/TM/Count.lean theorem tmCountWith_eq_countP
```

What remains is the hard part: accepted action sequences correspond one to one with meanders.
That proof is 2,500 lines across eight files, and the next section uses it from the compiled
library.
