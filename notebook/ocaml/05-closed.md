## 5. Closed meanders

A *closed* meander is a loop crossing the road $2n$ times. To count each loop once, start at the
westmost bridge $0$ and leave it upward. Arc $k$ joins $\sigma(k)$ to $\sigma(k+1)$, positions
taken modulo $2n$. `Array.init n f` is the array `[| f 0; …; f (n-1) |]`.

```ocaml
let is_closed_meander sigma =
  let m = List.length sigma in
  let s = Array.of_list sigma in
  let loop = Array.init (m + 1) (fun k -> s.(k mod m)) in
  s.(0) = 0 && no_cross loop m

let closed_meanders n =
  permutations (List.init (2 * n - 1) (fun i -> i + 1))
  |> List.map (fun rest -> 0 :: rest)
  |> List.filter is_closed_meander

let closed_counts = List.init 4 (fun i -> List.length (closed_meanders (i + 1)))
```

The counts $1, 2, 8, 42$ are the open counts for $1, 3, 5, 7$ crossings. Lean proves this for
every $n$: delete bridge $0$ from a closed meander and turn the picture through $180°$, and you
get an open meander with $2n - 1$ crossings. Conversely an open meander $\tau$ with $2n-1$
crossings becomes the closed meander $0, 2n - 1 - \tau(0), 2n - 1 - \tau(1), \ldots$ (Lean's
`closeUp`).

**Sorting and structural equality.** `List.sort compare l` sorts a list; `compare` is OCaml's
built-in ordering, which works on lists of integers too. Two sorted lists are equal with `=`
exactly when they hold the same elements, so this checks the bijection itself, not just the
counts.

```ocaml
let close_up tau =
  let n = List.length tau in
  0 :: List.map (fun t -> n - t) tau

let () =
  for n = 1 to 4 do
    let opens = permutations (List.init (2 * n - 1) Fun.id) |> List.filter is_meander in
    assert (List.sort compare (List.map close_up opens) = List.sort compare (closed_meanders n))
  done;
  print_endline "close_up is a bijection for n = 1, ..., 4"
```
