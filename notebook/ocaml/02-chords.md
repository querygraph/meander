## 2. Crossing chords

Draw the road as a horizontal line and number its bridges $0, 1, \ldots, n-1$ from west to
east. Between consecutive crossings the river runs along an *arc*, below the road or above it,
and the arcs alternate sides. Two arcs on the same side are like two chords of a disk: they
cross exactly when their endpoints alternate. So a river is a meander exactly when no two arcs
on the same side alternate.

**Functions.** `let f a b = body` defines a function of two arguments, and `f 1 2` applies it.
`let a = … and b = … in` makes two definitions at once. Comparing truth values with `<>` is
*exclusive or*.

**Type inference and type variables.** OCaml *infers* every type. For `interleave` the toplevel
answers `'a -> 'a -> 'a -> 'a -> bool`: a function of four arguments of the same type `'a`,
returning a truth value. `'a` is a *type variable*. OCaml's comparisons `<`, `=`, `min` and `max`
work on values of any type, so nothing forces the arguments to be integers, and the function is
*polymorphic*: it works for every type `'a`. We will only use it with integers.

```ocaml
let interleave a b c d =
  let lo = min a b and hi = max a b in
  (lo < c && c < hi) <> (lo < d && d < hi)

let () = Printf.printf "%b %b\n%!" (interleave 0 2 1 3) (interleave 0 3 1 2)
```

`%b` prints a `bool`.

### No two arcs on one side cross

A river visits boundary points $P_0, P_1, \ldots$, and arc $k$ joins $P_k$ to $P_{k+1}$. Arcs
$j$ and $k$ are on the same side exactly when $j$ and $k$ have the same parity.

**Arrays, anonymous functions and higher-order functions.** `[| 0; 2; 1; 3 |]` is an *array*,
with constant-time access `p.(k)`. `fun x -> e` is an anonymous function. Functions are values:
`List.for_all f l` is true when `f x` is true for every `x` in the list `l`, and
`List.init n f` is the list `[f 0; f 1; …; f (n-1)]`. `Fun.id` is the identity function, so
`List.init n Fun.id` is `[0; 1; …; n-1]`.

```ocaml
let no_cross p l =
  List.for_all (fun k ->
      List.for_all (fun j ->
          j mod 2 <> k mod 2 || not (interleave p.(j) p.(j + 1) p.(k) p.(k + 1)))
        (List.init k Fun.id))
    (List.init l Fun.id)

let () = Printf.printf "%b %b\n%!" (no_cross [| 0; 1; 2; 3 |] 3) (no_cross [| 0; 2; 1; 3 |] 3)
```

The type of `no_cross` is `'a array -> int -> bool`: OCaml worked out from `p.(j)` that `p` is an
array, and from `j + 1` that its indices are integers; its entries can be of any type.
