## 6. A search with a parity rule

A search builds the crossing order one bridge at a time and abandons a partial order as soon as
the newest arc crosses an earlier one on its side, or as soon as the parity rule fails.

**The parity rule.** Take an arc $j$ already drawn, on side $s$, with ends $a < b$. Every later
arc on side $s$ has both ends inside $(a, b)$ or both outside, since it may not cross arc $j$, so
the side-$s$ arc ends still to come inside $(a, b)$ pair up. They are the unvisited bridges in
$(a, b)$, the current point if the next arc is on side $s$, and the east end $n$ if the final
arc is on side $s$. An odd count means the river cannot be finished. Lean proves the rule sound
(`Arnold.parityOK_of_noCross`).

**Mutable state.** OCaml values are immutable unless declared otherwise. `ref v` is a mutable
cell holding `v`, `!r` reads it, `r := v` writes it, and `incr r`, `decr r` add or subtract one.
Arrays are mutable: `a.(i) <- v` writes an entry, and `Array.make n v` makes an array of `n`
copies of `v`. `begin … end` groups a sequence, like parentheses. `if c then a else b` is an
expression; without `else`, the branch must have type `unit`.

**Optional and labelled arguments.** `?(parity = true)` declares an optional argument with a
default; a caller writes `~parity:false` to set it. Functions defined inside `search` can see
its variables.

```ocaml
let search ?(parity = true) n =
  let order = Array.make n 0 and used = Array.make n false in
  let len = ref 0 and nodes = ref 0 in
  (* point k of the path: the south end, the bridges so far, then the east end *)
  let point k = if k = 0 then n + 1 else if k - 1 < !len then order.(k - 1) else n in
  let inside j x =
    let a = point j and b = point (j + 1) in
    min a b < x && x < max a b
  in
  let step_ok t =
    let c = point t and d = point (t + 1) in
    let rec ok j =
      j >= t
      || ((j mod 2 <> t mod 2 || not (interleave (point j) (point (j + 1)) c d)) && ok (j + 1))
    in
    ok 0
  in
  let parity_ok () =
    let t = !len in
    let rec ok j =
      j >= t
      ||
      let ends = ref 0 in
      for x = 0 to n - 1 do
        if (not used.(x)) && inside j x then incr ends
      done;
      if t mod 2 = j mod 2 && inside j (point t) then incr ends;
      if n mod 2 = j mod 2 && inside j n then incr ends;
      !ends mod 2 = 0 && ok (j + 1)
    in
    ok 0
  in
  let rec go () =
    incr nodes;
    if !len = n then if step_ok n then 1 else 0
    else begin
      let total = ref 0 in
      for x = 0 to n - 1 do
        if not used.(x) then begin
          order.(!len) <- x;
          used.(x) <- true;
          incr len;
          if step_ok (!len - 1) && ((not parity) || parity_ok ()) then total := !total + go ();
          decr len;
          used.(x) <- false
        end
      done;
      !total
    end
  in
  let count = go () in
  (count, !nodes)
```

**Libraries and timing.** Lines starting with `#` are *toplevel directives*, commands to the
toplevel itself; `;;` ends each one. `#use "topfind"` loads findlib, OCaml's library manager,
and `#require "unix"` then loads the `unix` library, whose `Unix.gettimeofday ()` reads the wall clock in seconds as a `float`.
`List.iter f l` calls `f` on every entry of `l`, for its effect. Below, `~parity` alone passes
the variable `parity` as the labelled argument of the same name, and `fst` takes the first part
of a pair.

```ocaml
#use "topfind";;
#require "unix";;
```

```ocaml
let () =
  List.iter
    (fun parity ->
      let t = Unix.gettimeofday () in
      let count, nodes = search ~parity 11 in
      Printf.printf "parity=%b: %d meanders, %d partial rivers, %.1f s\n%!" parity count nodes
        (Unix.gettimeofday () -. t))
    [ false; true ]

let () = assert (List.init 14 (fun n -> fst (search n)) = first 14 lean_values)
```

The parity rule cuts the partial rivers at eleven crossings from 322,080 to 14,471, as in the
paper.
