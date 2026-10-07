## 7. The transfer matrix

The transfer matrix scans the road from west to east: the bridges $0, \ldots, m-1$, then the
east end $E = m$, which has one arc, on side $m \bmod 2$ (the south end, last, needs no step).
At each point and on each side, the point *opens* a new arc or *closes* an open one. Arcs on a
side never cross, so the open arcs on each side form a stack, and a point closes the top one.

**The state.** Cut the plane just east of the current point. The river west of the cut falls
into pieces, each joining two open arcs, or one open arc and the east end once it has been
passed. Read the open arcs along the cut from top to bottom. The pieces never cross, so they
pair the arcs like brackets. A state is a *word* of opening and closing brackets with at most
one `E` (an arc whose piece leads to the east end), and `h`, the number of arcs above the road.

**Variant types.** `type mark = Op | Cl | E` defines a new type with exactly three values, its
*constructors*. Pattern matching on a variant must cover every constructor; the compiler warns
otherwise.

**Records.** `type state = { word : mark list; h : int }` defines a record type with two named
fields. `{ word = w; h = 1 }` builds one, `s.h` reads a field, and the pattern `{ word; h }`
takes both fields apart, naming them after the fields. `show` prints a state as text:
`Printf.sprintf` formats into a string instead of printing, and `String.concat sep l` joins a
list of strings.

```ocaml
type mark = Op | Cl | E
type state = { word : mark list; h : int }

let show { word; h } =
  let char = function Op -> "(" | Cl -> ")" | E -> "E" in
  Printf.sprintf "%s/%d" (String.concat "" (List.map char word)) h
```


**Editing lists by position.** Lists have no positions to write into, so a change builds a new
list. Recursion walks to position `i` and rebuilds the front. `invalid_arg msg` raises an
exception for an impossible input, and `List.mapi f l` is `List.map` with positions.

```ocaml
let rec insert_at i x l =
  if i = 0 then x :: l
  else match l with y :: rest -> y :: insert_at (i - 1) x rest | [] -> invalid_arg "insert_at"

let rec remove_at i = function
  | [] -> invalid_arg "remove_at"
  | y :: rest -> if i = 0 then rest else y :: remove_at (i - 1) rest

let set_at i x l = List.mapi (fun j y -> if j = i then x else y) l
```

`partner w i` finds the bracket matched with the one at position `i`, scanning right from an
opening bracket or left from a closing one and skipping the `E`. The inner recursive function
carries the position and the depth as arguments instead of mutable variables.

```ocaml
let partner w i =
  let a = Array.of_list w in
  let step = if a.(i) = Op then 1 else -1 in
  let rec scan j depth =
    if a.(j) = a.(i) then scan (j + step) (depth + 1)
    else if a.(j) = E then scan (j + step) depth
    else if depth = 0 then j
    else scan (j + step) (depth - 1)
  in
  scan (i + step) 0
```

**Callbacks, and matching on tuples.** `successors m x s emit` calls the function `emit` on
every state that point `x` can lead to, instead of building a list of them. `match a, b with`
matches two values at once, and `_` in a pattern matches anything.

* At a bridge, opening both sides puts a new pair at the cut, joined at the bridge.
* Opening above and closing below leaves the word alone: the closed arc's piece continues into
  the new arc. Only `h` changes; likewise the other way round.
* Closing both tops joins their pieces, unless the tops are partners, which would close a loop.
  Their partners become partners of each other, so a bracket may have to turn round.
* The east end opens or closes one arc on its side, and that piece now leads to `E`.

```ocaml
let successors m x { word; h } emit =
  let dn = List.length word - h in
  if x < m then begin
    emit { word = insert_at h Op (insert_at h Cl word); h = h + 1 };
    if dn > 0 then emit { word; h = h + 1 };
    if h > 0 then emit { word; h = h - 1 };
    if h > 0 && dn > 0 then begin
      let i = h - 1 and j = h in
      let a = List.nth word i and b = List.nth word j in
      if not (a = Op && b = Cl) then begin
        let w =
          match a, b with
          | E, _ -> set_at (partner word j) E word
          | _, E -> set_at (partner word i) E word
          | Op, Op -> set_at (partner word j) Op word
          | Cl, Cl -> set_at (partner word i) Cl word
          | _ -> word
        in
        emit { word = remove_at i (remove_at j w); h = h - 1 }
      end
    end
  end
  else begin
    let up = m mod 2 = 1 in
    emit { word = insert_at h E word; h = (if up then h + 1 else h) };
    let top = if up then h - 1 else h in
    if (if up then h > 0 else dn > 0) && List.nth word top <> E then
      emit { word = remove_at top (set_at (partner word top) E word);
             h = (if up then h - 1 else h) }
  end
```

A state is dropped as soon as a side has more open arcs than the remaining points can close
(Lean's `viable`).

```ocaml
let cap m k up = if k <= m then m - k + (if (m mod 2 = 1) = up then 1 else 0) else 0
let viable m k s = s.h <= cap m k true && List.length s.word - s.h <= cap m k false + 1
```

**Modules and functors.** A *module* groups definitions: `struct … end` writes one, and
`module Key = struct … end` names it. A *functor* is a function from modules to modules.
`Hashtbl.Make (Key)` builds a hash table specialized to keys of `Key.t`, using `Key.equal` and
`Key.hash`. The default hash looks only at the first few cells of a list, so long words would
collide; `Hashtbl.hash_param 100 100` looks much further. A *layer* maps each state to the
number of ways to reach it, and equal states are merged by adding their counts.

**`option`.** A value of type `'a option` is `None` or `Some v`. `States.find_opt t k` returns
`Some count` if `k` is in the table, and `Option.value o ~default:0` takes the value or `0`.
`States.replace t k v` sets an entry, `States.iter f t` calls `f k v` on every entry,
`States.create n` makes an empty table (`n` is a size hint), and `States.length t` counts its
entries. `layers m` collects every layer in a list, newest first, and `List.rev` reverses it. A
river is accepted when, after the east end, one arc is open, below the road, leading to `E`: the
state `E/0`.

```ocaml
module Key = struct
  type t = state
  let equal = ( = )
  let hash s = Hashtbl.hash_param 100 100 s
end

module States = Hashtbl.Make (Key)

let add tbl s c = States.replace tbl s (c + Option.value (States.find_opt tbl s) ~default:0)

let layers m =
  let layer = ref (States.create 1) in
  States.replace !layer { word = []; h = 0 } 1;
  let all = ref [ !layer ] in
  for x = 0 to m do
    let next = States.create (2 * States.length !layer) in
    States.iter
      (fun s c -> successors m x s (fun s' -> if viable m (x + 1) s' then add next s' c))
      !layer;
    layer := next;
    all := next :: !all
  done;
  List.rev !all

let final = { word = [ E ]; h = 0 }

let tm_count m =
  let last = List.nth (layers m) (m + 1) in
  Option.value (States.find_opt last final) ~default:0
```

The layers for three crossings:

`States.fold f t init` combines the entries of a table into one value, here a list of strings,
and `List.iteri` is `List.iter` that also passes each entry's position.

```ocaml
let () =
  List.iteri
    (fun k layer ->
      let entries = States.fold (fun s c acc -> Printf.sprintf "%s -> %d" (show s) c :: acc) layer [] in
      Printf.printf "%d: %s\n%!" k (String.concat ", " entries))
    (layers 3)
```

```ocaml
let () =
  let t = Unix.gettimeofday () in
  let values = List.init 27 tm_count in
  Printf.printf "%.1f s; n = 26: %d\n%!" (Unix.gettimeofday () -. t) (List.nth values 26);
  assert (first 25 values = lean_values)
```

The values agree with Lean's up to $n = 24$. OCaml's 63-bit integers hold the counts up to
$n = 42$; from $n = 43$ on, the compiled programs keep counts modulo two large numbers and
recover them by the Chinese remainder theorem.
