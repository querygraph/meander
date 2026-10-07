## 4. Checking what we cannot prove

Lean proves that there is at least one meander and at most $n!$ for every $n$, and that its
fast counters agree with the definition. OCaml can check such facts for the values we try.

**`assert`, loops and sequencing.** `assert c` raises an exception, stopping the cell, if `c` is
false. `for i = a to b do body done` runs `body` for `i = a, …, b`; the body must have type
`unit`. `e1; e2` runs `e1` for its effect, then `e2`. A recursive function can be defined with
pattern matching on numbers too, using a guard: `| n when n > 0 -> …` matches only if the
condition holds, and `_` matches anything. `print_endline s` prints the string `s` and a new
line. `List.nth l i` is entry `i` of the list `l`.

```ocaml
let rec factorial = function n when n > 0 -> n * factorial (n - 1) | _ -> 1

let () =
  for n = 0 to 8 do
    let count = List.nth small n in
    assert (is_meander (List.init n Fun.id));
    assert (1 <= count && count <= factorial n)
  done;
  print_endline "checked n = 0, ..., 8"
```

The straight river `0, 1, …, n-1` is always a meander, which is how Lean proves there is at
least one.

These values are certified in Lean: by its kernel up to $n = 13$, by compiled code up to
$n = 24$ (`Arnold.openMeanderCount_values`, `Arnold.openMeanderCount_values_native`).
`List.filteri f l` keeps the entries whose position `i` and value pass `f i x`.

```ocaml
let lean_values =
  [ 1; 1; 1; 2; 3; 8; 14; 42; 81; 262; 538; 1828; 3926; 13820; 30694; 110954; 252939; 933458;
    2172830; 8152860; 19304190; 73424650; 176343390; 678390116; 1649008456 ]

let first k l = List.filteri (fun i _ -> i < k) l
let () = assert (small = first 9 lean_values)
```
