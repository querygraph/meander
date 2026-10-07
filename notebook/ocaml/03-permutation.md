## 3. A river is a permutation

A meander is determined by the order in which the river crosses the bridges: its $i$-th
crossing is at bridge $\sigma(i)$, for a permutation $\sigma$ of $0, \ldots, n-1$. Treat the two
ends of the river, which go off to infinity, as two more boundary points east of every bridge:
the east end $n$ and the south end $n+1$. (Compactify each half-plane to a disk; the road plus
infinity is its boundary.) The path of the river is
$$n+1,\ \sigma(0),\ \ldots,\ \sigma(n-1),\ n,$$
with $n + 1$ arcs, the even ones below the road.

**Lists.** `[1; 2; 3]` is a list, `[]` the empty list, `x :: l` the list `l` with `x` in front,
and `l @ l'` concatenates. Lists are immutable and built from the front. `List.length l` is
the length of `l`, and `Array.of_list l` copies it into an array.

```ocaml
let path sigma =
  let n = List.length sigma in
  Array.of_list ((n + 1) :: sigma @ [ n ])

let is_meander sigma = no_cross (path sigma) (List.length sigma + 1)
```

**Pattern matching and recursion.** `function | pattern -> e | …` is a function that looks at
the shape of its argument: `[]` matches the empty list, and `x :: rest` matches a non-empty one
and names its head and tail. A function that calls itself is declared with `let rec`.
`List.filter p l` keeps the entries satisfying `p`, `List.map f l` applies `f` to every entry,
and `List.concat_map f l` applies `f`, which returns lists, and concatenates the results.

All orderings of a list: pick each element `x` in turn to go first, and follow it with every
ordering of the others.

```ocaml
let rec permutations = function
  | [] -> [ [] ]
  | xs ->
      List.concat_map
        (fun x ->
          List.map (fun rest -> x :: rest) (permutations (List.filter (fun y -> y <> x) xs)))
        xs
```

**The pipeline operator.** `x |> f` is `f x`, so a chain of steps reads left to right.
`open_meander_count n` is the definition, word for word: the number of permutations that
describe a meander. It is the specification that everything faster must agree with.

```ocaml
let open_meander_count n =
  permutations (List.init n Fun.id) |> List.filter is_meander |> List.length

let small = List.init 9 open_meander_count
```

The toplevel prints the list as `[1; 1; 1; 2; 3; 8; 14; 42; 81]`.
