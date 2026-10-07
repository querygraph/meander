## 13. Index of Lean features

Each feature is explained in the section listed, before its first use.

| Feature | Section |
|---|---|
| `import`, Mathlib | 1 |
| `#eval`, `#check`, `--` comments | 1 |
| `Nat`, `ℕ`, type ascription `(e : T)`, function application | 1 |
| truncated `-`, `/`, `%`, pairs `(a, b)` and `A × B` | 1 |
| `Prop`, propositions as types | 1 |
| `namespace`, `end` | 2, 10 |
| `def`, docstrings `/-- … -/` | 2 |
| `¬`, `∧`, `↔`, `<`, `min`, `max` | 2 |
| type classes, `instance`, `Decidable` | 2 |
| tactic blocks `by`, `unfold`, `infer_instance`, `;` | 2 |
| function types `A → B`, `∀ x < n,`, implication `→` | 2 |
| `fun x => e`, lists `[a, b]`, `List ℕ`, dot notation | 2 |
| `Fin n`, `Equiv.Perm` | 3 |
| implicit arguments `{x : T}` | 3 |
| anonymous constructor `⟨a, b⟩`, dependent `if h : c` | 3 |
| coercions `↑x` | 3 |
| `List.range`, `List.map`, partial application | 3 |
| subtypes `{x // P x}`, `Fintype.card` | 3 |
| `theorem`, `example` | 4 |
| goals; `intro`, `rw`, `omega`, `≠` | 4 |
| `split_ifs`, `by_cases`, `·` | 4 |
| `simp`, `simp only`, simprocs `↓reduceIte`, `show … by`, `rfl` | 4 |
| `have`, `(by tac)` as an argument | 4 |
| term-mode proofs, `.mp`, `.mpr`, `Nonempty`, `_` | 4 |
| `calc` | 4 |
| `decide` | 4 |
| lemmas as functions, e.g. `Nat.mod_lt` | 5 |
| `∀ h : P,` over proofs | 5 |
| `Equiv`, `≃`, `.symm`, `.trans`, `Fin.revPerm`, `Perm.decomposeFin` | 6 |
| `open` | 6 |
| proofs of `∀` as functions; congruence lemmas | 6 |
| `∨`, `have :=` and `this`, `.isLt` | 6 |
| named arguments `(n := e)`, `↓reduceDIte`, `ext`, `rcases … with h \| h`, `<;>` | 6 |
| `refine` with holes `?_`, `generalize` | 6 |
| `exact`, `Function.Injective`, `congrArg`, `simpa`, `Equiv.ext` | 6 |
| `∃`, `obtain`, the pattern `rfl`, `subst`, `rw … at h`, `congr` | 6 |
| `Fintype.card_of_bijective`, `Subtype.ext`, `.1`, `.2`, `fun _ =>`, `symm`, `rintro` | 6 |
| `congr 1` | 6 |
| `Bool`, `decide`, `b = true` | 7 |
| `List.countP` | 7 |
| definitions by pattern matching, structural recursion | 7 |
| `++`, `[x]`, `List.erase`, `List.sum` | 7 |
| `&&`, `\|\|`, `!`, `==`, `!=` | 8 |
| `induction … with`, `constructor` | 8 |
| `Array`, `let` | 8 |
| `split`, `simp_all`, `Or.inl`, `Or.inr`, `.resolve_left`, `show … from`, `funext` | 8 |
| attributes `@[…]`, `@[csimp]`, `@f`, `apply` | 8 |
| `::`, `flatMap`, `(f ·)` | 9 |
| `∈`, `List.Perm`, `cases … with`, `simp … at h` | 9 |
| `Nodup`, `fun {x} =>`, `.symm` on equations | 9 |
| `∑ i ∈ s, f i`, `Finset`, `suffices`, `Nat.le_induction` | 9 |
| recursive proofs | 9 |
| `rw [← h]` | 9 |
| `obtain … : T := …`, `swap` | 9 |
| `List.ofFn`, `congrFun`, `l[i]'h` | 9 |
| instance arguments `[C α]`, `DecidablePred`, `Finset.card_bij` | 9 |
| `absurd` | 9 |
| `#print axioms` | 9 |
| `inductive`, constructors, `deriving` | 10 |
| `structure`, fields, `{ s with … }` | 10 |
| `Option`, `match` | 10 |
| matching several values, literal patterns | 10 |
| automatic `decide` from `Prop` to `Bool` | 10 |
| well-founded recursion | 10 |
| `filterMap`, `Option.map`, `filter`, `mergeSort`, `foldr` | 10 |
| functions as parameters | 10 |
| `set_option`, `Option.bind` | 11 |
| `cases h : e with` | 11 |
| functional induction `f.induct`, `ring`, `at h ⊢` | 11 |
| `rcases` on Booleans, `split_ifs at`, `dsimp`, `reduceCtorEq`, `if_pos` | 11 |
| `by_contra` | 11 |
| `decide +kernel`, `native_decide` and its axiom | 12 |
| structures with proof fields | 12 |
| `IO`, `do`, `for`, `s!"…"`, `>>=`, `main` | 12 |
