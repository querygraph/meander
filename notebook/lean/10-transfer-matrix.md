## 10. The transfer matrix

The search follows the river. The transfer matrix scans the road instead, from west to east:
the bridges $0, \ldots, m-1$, then the east end $E = m$, which has one arc on side $m \bmod 2$.
The south end $S = m+1$, with its one arc below, comes last and needs no step. At each point the
machine chooses, for each side, whether the point *opens* a new arc or *closes* an open one. Arcs
on one side never cross, so the open arcs on each side form a stack, and a point always closes
the top one.

The river west of the cut falls into pieces, each joining two open arcs (or one open arc and
$E$). The *state* records, for each open arc, which arc its piece leads to. Joining the two ends
of one piece would close a loop, so the machine refuses that move. A whole river is accepted
when, after $E$, exactly one arc is open: below the road, with its piece leading to $E$, ready
for $S$ to close it. Equal states are merged and their counts added, which is what makes the
method fast.

**`end` and nested namespaces.** The machine lives in `Arnold.TM`. We close `Arnold` and open
`Arnold.TM`, a namespace inside it, so names from `Arnold` stay available without the prefix.

**Inductive types.** `inductive T where | c₁ … | c₂ …` defines a new type whose values are
built by the listed *constructors*, and only by them. A reference to an open arc is either the
east end `E`, or `s σ i`, position `i` in the stack of side `σ` (`true` above the road). `Ref.E`
and `Ref.s true 3` are values of the type `Ref`.

**`deriving`.** `deriving DecidableEq, Repr, Inhabited` asks Lean to write three instances: an
algorithm deciding whether two `Ref`s are equal, a way to print them (used by `#eval`), and a
default value.

```lean
end Arnold

namespace Arnold.TM

@include Arnold/TM/Defs.lean inductive Ref
```

**Structures.** `structure St where` followed by fields defines a record type, here a state
with two stacks of references. `s.up` and `s.dn` are its fields, and `⟨u, d⟩` builds one.

```lean
@include Arnold/TM/Defs.lean structure St
```

**Functions in a type's namespace.** The stack operations are declared in the namespace `St`,
so dot notation finds them: `s.push σ r` means `St.push s σ r`. `{ s with up := l }` is `s`
with the field `up` replaced. `l.dropLast` removes the last entry, and `l.set i r` replaces
entry `i`. In patterns, `.E` and `.s σ i` abbreviate `Ref.E` and `Ref.s σ i`, since Lean knows
the type.

```lean
namespace St

@include Arnold/TM/Defs.lean def stk
@include Arnold/TM/Defs.lean def setStk
@include Arnold/TM/Defs.lean def push
@include Arnold/TM/Defs.lean def pop
@include Arnold/TM/Defs.lean def setRef

end St
```

**`Option` and `match`.** A step can fail, and `Option α` holds either `none` (no value) or
`some a` for `a : α`. `l.getLast? : Option α` is the last entry of `l`, if any. `match e with |
pattern => value …` chooses a case by the shape of `e`, as a definition by pattern matching does.
`openClose s σ` opens an arc on side `σ` and closes the top arc on the other side `!σ`. The new
arc continues the closed arc's piece.

```lean
@include Arnold/TM/Defs.lean def openClose
```

**Matching several values.** `match a with | (true, true) => …` matches a pair against literal
patterns, and `match e₁, e₂ with | some p, some q => … | _, _ => …` matches two values at
once. `step m x s a` processes point `x` with action `a = (above, below)`, where `true` means
*open*. A bridge has four actions. The east end `x = m` uses only its side and reads `a.1`, the
first component of the pair. When both tops close, the machine refuses if the upper top's piece
leads to the lower top: that would close a loop.

```lean
@include Arnold/TM/Defs.lean def step
```

```lean
@include Arnold/TM/Defs.lean def acts
@include Arnold/TM/Defs.lean def init
```

```lean
@include Arnold/TM/Defs.lean def final
```

One step from the empty state at the first of three bridges, opening above and below. `Repr`
lets `#eval` print the state: one arc above, whose piece leads to the arc below, and vice versa.

```lean
#eval step 3 0 init (true, true)
```

### Counting with merged states

A *layer* is a list of pairs (state, number of action sequences that reach it). Merging sorts
the layer by a numeric key and adds up neighbours with equal states. Any key is correct; a good
one puts equal states next to each other.

**Bool from Prop, again.** In `a < b || (a == b && lexLe l l')`, the proposition `a < b` stands
where a `Bool` is expected, and Lean inserts `decide` automatically.

```lean
@include Arnold/TM/Defs.lean def refCode
```

```lean
@include Arnold/TM/Defs.lean def key
```

```lean
@include Arnold/TM/Defs.lean def lexLe
```

**Well-founded recursion.** `mergeAdj` calls itself on `(k, s, c + c') :: rest`, which is not
a piece of its argument, so the recursion is not structural. Lean then tries to prove that some
measure decreases, here the length of the list, and accepts the definition when it succeeds.
Triples are nested pairs: `(k, s, c)` is `(k, (s, c))`, so for a triple `t`, `t.2.1` is `s`.

```lean
@include Arnold/TM/Defs.lean def mergeAdj
```

`l.mergeSort le` sorts a list by the Boolean comparison `le`.

```lean
@include Arnold/TM/Defs.lean def compress
```

**`filterMap` and `Option.map`.** `l.filterMap f` applies `f : α → Option β` to every entry and
keeps the values inside the `some`s. `o.map f` applies `f` inside an `Option`. `expand` makes
every successor of every state of a layer, carrying the counts along.

```lean
@include Arnold/TM/Defs.lean def expand
```

A state with more open arcs on a side than the remaining points can close is dropped at once.
`cap m k σ` counts the points $k, \ldots, m$ that have an arc on side `σ`. `l.filter f` keeps the
entries with `f x = true`.

```lean
@include Arnold/TM/Defs.lean def cap
```

```lean
@include Arnold/TM/Defs.lean def viable
```

**Functions as parameters.** `layerWith` takes the merge step `comp` as an argument, a function
from layers to layers. Correctness is proved once, for any merge that keeps weighted sums, and
then applies to both merges the library uses.

```lean
@include Arnold/TM/Defs.lean def layerWith
```

```lean
@include Arnold/TM/Defs.lean def tmCountWith
```

```lean
@include Arnold/TM/Defs.lean def tmCount
```

The second merge inserts states one at a time by structural recursion, which Lean's kernel can
evaluate efficiently. `l.foldr f b` combines the entries of `l` from the right:
`f x₁ (f x₂ (… (f xₖ b)))`.

```lean
@include Arnold/TM/Defs.lean def insertAdd
@include Arnold/TM/Defs.lean def compressK
```

```lean
@include Arnold/TM/Defs.lean def tmCountK
```

```lean
#eval (List.range 25).map tmCount
```

These are the values up to $n = 24$, in about a second, even interpreted. The compiled program
`meanders` reaches $n = 32$ in a minute and a half.
