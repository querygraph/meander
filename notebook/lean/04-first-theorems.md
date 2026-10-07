## 4. First theorems

The first facts in the library are that every $n$ has at least one meander and at most $n!$.
For at least one, take the river that zig-zags straight east across bridges
$0, 1, \ldots, n-1$. Its path is $n+1, 0, 1, \ldots, n-1, n$. Arc $0$ joins $n+1$ to $0$ and
encloses every later point; every other arc joins two neighbouring points, with nothing
strictly between them. So no two arcs alternate.

**`theorem` and `example`.** `theorem name (x : T) : P := proof` declares that `proof` proves
the proposition `P`, for every `x`. Lean checks that `proof` has type `P`, exactly as it checks
the value of a `def`. `example : P := proof` is a theorem without a name: Lean checks it and
then forgets it. We use examples to try out tactics before the real proofs.

**The goal and the first tactics.** Inside `by`, Lean shows a *goal*: hypotheses above a line,
the statement to prove below. Each tactic changes the goal until nothing is left.

* `intro x h` moves a `∀ x` or an `A →` from the goal into the hypotheses, naming them. It
  unfolds definitions if needed to find the `∀`.
* `rw [h]`, for `h : a = b`, rewrites `a` to `b` in the goal. `rw [h x y]` first fills in the
  arguments of a lemma `h`.
* `omega` proves goals in linear arithmetic over `ℕ` and `ℤ`: `+`, `-`, `*` by constants, `/`
  and `%` by constants, `<`, `≤`, `=`, and the logic connecting them. It is the workhorse of
  the library. `a ≠ b` means `¬ (a = b)`.

```lean
example : ∀ a b : ℕ, a = b + 1 → a ≠ 0 := by
  intro a b h
  rw [h]
  omega
```

**Case splits.** `split_ifs with h` splits a goal containing `if c then … else …` into two
goals: one with `h : c` and the branch `then`, one with `h : ¬ c` and the branch `else`. The
indented `·` (a centred dot) starts the proof of one goal, and the next `·` the next goal.
`by_cases h : c` splits on any decidable `c` in the same way.

```lean
example (a : ℕ) : (if a = 0 then 1 else a) ≠ 0 := by
  split_ifs with h
  · omega
  · omega
```

**`simp`, `show … by`, `rfl`.** `simp only [l₁, l₂]` rewrites the goal with the given lemmas,
repeatedly, and closes it if it becomes trivially true. `↓reduceIte` is a *simproc*, a small
procedure for `simp`: it replaces `if c then a else b` by `a` when it can prove `c`, or by `b`
when it can prove `¬ c`. A proof written inline as `show P by tac` hands `simp` the fact `P`.
`simp [l₁]` without `only` also uses the hundreds of lemmas Mathlib marks as simplification
rules. `rfl` proves `a = a`, and more generally `a = b` whenever both sides compute to the same
value. `unfold f` replaces `f` by its definition, as in Section 2.

```lean
example (m : ℕ) (h : 1 ≤ m) : (if m = 0 then 5 else m) = m := by
  simp only [show m ≠ 0 by omega, ↓reduceIte]
```

**`have`.** `have name : P := by …` proves an intermediate fact `P` and adds it to the
hypotheses. A lemma with side conditions takes their proofs as arguments, and `by` may appear
anywhere a term is expected, so `hpt k (by omega) (by omega)` proves the two side conditions of
`hpt` on the spot. Below, `hpt` computes every point of the straight river at once: point `m` is
`m - 1` for $1 \le m \le n+1$. The proof then reduces the claim to arithmetic about these
points, which `omega` finishes.

```lean
@include Arnold/Basic.lean theorem isMeander_refl
```

**Proofs as terms.** A proof need not use tactics. `openMeanderCount_pos` is proved by a
single expression. `Fintype.card_pos_iff` is the Mathlib lemma `0 < Fintype.card α ↔ Nonempty α`.
For a proof `h : A ↔ B`, `h.mp : A → B` and `h.mpr : B → A` are its two directions. `Nonempty α`
is proved by an anonymous constructor holding an element of `α`, and the element of the subtype
is itself the pair `⟨σ, proof that σ is a meander⟩`. An underscore `_` asks Lean to fill in a
term it can infer, here the `n` in `Fin n`.

```lean
@include Arnold/Basic.lean theorem openMeanderCount_pos
```

**`calc`.** A `calc` block proves a chain of relations, one step per line. `_` at the start of a
line stands for the previous right-hand side, and the first `_` for the left side of the goal.
The bound $n!$ is the number of all permutations: a subtype has at most as many elements as the
whole type (`Fintype.card_subtype_le`), and there are $n!$ permutations of `Fin n`. Note
`n.factorial`: dot notation works on any value, here `Nat.factorial n`.

```lean
@include Arnold/Basic.lean theorem openMeanderCount_le_factorial
```

**`decide`.** For a decidable proposition, the tactic `decide` runs the decision procedure
*inside Lean's kernel*, the small program that checks every proof. If it returns `true`, the
kernel has verified the proposition by computation. These four facts are checked by enumerating
all permutations.

```lean
@include Arnold/Basic.lean theorem openMeanderCount_0
@include Arnold/Basic.lean theorem openMeanderCount_1
@include Arnold/Basic.lean theorem openMeanderCount_2
@include Arnold/Basic.lean theorem openMeanderCount_3
```
