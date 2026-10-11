(* The meet-in-the-middle key, and the bridge steps on it in both directions. The same
   algorithm as rust/src/bits.rs.

   The states of the meet-in-the-middle layers never contain 'E' (forward layers come before
   the east end, and backward states are what the east end will finish), so their key has no
   field for its position:

     h << 58 | 1 << (len - 1) | inner      (the empty word: h << 58)

   Every word is balanced (each arc is paired with another through the river further west:
   the steps insert, re-pair or remove matched pairs), so its first bracket is '(' and its last
   is ')'. Only the [len - 2] brackets between them are stored: bracket i (0 < i < len - 1) at
   bit i - 1, 1 = '(' and 0 = ')'. That fits words of up to 58 brackets in an OCaml int, enough
   for horizon 58, the forward layer after k bridges having words of up to 2k brackets. [make]
   checks the first and last brackets, so a word breaking the rule fails loudly. The
   transitions work on the full word [b] (bracket i at bit i), unpacked by [unpack].
   [of_word] and [to_word] convert from and to the [Word] key, which keeps a field for 'E' and
   fits 50 brackets.

   - [depth k = len - bal(h)], where [bal(h) = 2 popcount(brackets below bit h) - h] is the
     excess of '(' left of the cut: the fewest bridges that build the state from the west.
   - The inverse of "close both tops" re-splits one pair of the word at the cut. A pair right
     of the cut can be split only if it is at top level there (the letters between the cut and
     it are balanced), likewise on the left, and among the pairs straddling the cut only the
     innermost one qualifies. One scan outward from the cut on each side finds them all.

   [predecessors] emits exactly the states of the reference [Back.Reference.predecessors]
   (checked by the tests). *)

let h_shift = 58
let bits_mask = (1 lsl h_shift) - 1
let max_len = 58

let[@inline always] popcount x = Ocaml_intrinsics_kernel.Int.count_set_bits x
let[@inline always] low b i = b land ((1 lsl i) - 1)

(* The excess of '(' over ')' in positions [0, i). *)
let[@inline always] bal b i = (2 * popcount (low b i)) - i

(* Insert letters [x] at position [i] and [y] at [i + 1]. *)
let[@inline always] insert2 b i x y =
  low b i lor (x lsl i) lor (y lsl (i + 1)) lor ((b lsr i) lsl (i + 2))
;;

let[@inline always] make b len h =
  if len > max_len || h > 31 then failwith "Back.make: state does not fit in 63 bits";
  if len = 0
  then h lsl h_shift
  else (
    if b land 1 = 0 || (b lsr (len - 1)) land 1 = 1
    then failwith "Back.make: not a balanced word";
    (h lsl h_shift) lor (1 lsl (len - 1)) lor ((b lsr 1) land ((1 lsl (len - 2)) - 1)))
;;

(* #(h, len, full word) of a key. *)
let[@inline always] unpack k =
  let h = k lsr h_shift in
  let sb = k land bits_mask in
  if sb = 0
  then #(h, 0, 0)
  else (
    let t = Word.top_bit sb in
    #(h, t + 1, ((sb lxor (1 lsl t)) lsl 1) lor 1))
;;

let length k =
  let #(_, len, _) = unpack k in
  len
;;

(* The empty state, and the pair "()" with [p] arcs above the road. *)
let init = 0
let pair p = make 1 2 p

(* From and to the [Word] key (a word without 'E'). *)
let of_word k =
  let sb = k land Word.bits_mask in
  let len = Word.top_bit sb in
  make (sb lxor (1 lsl len)) len (k lsr Word.h_shift)
;;

let to_word k =
  let #(h, len, b) = unpack k in
  (h lsl Word.h_shift) lor (Word.no_end lsl Word.e_shift) lor (1 lsl len) lor b
;;

(* [emit t] for every successor [t] of [k] under a bridge step, with no pruning: the bridge
   cases of [Word.successors] ([Arnold.TM.bstep] in Lean), on this key. *)
let[@inline always] successors k (emit : (int -> unit) @ local) =
  let #(h, len, b) = unpack k in
  let dn = len - h in
  (* open both: a pair "()" at the cut, joined at this bridge. *)
  emit (make (insert2 b h 1 0) (len + 2) (h + 1));
  (* open above, close below; close above, open below: the word is unchanged. *)
  if dn > 0 then emit (make b len (h + 1));
  if h > 0 then emit (make b len (h - 1));
  (* close both tops and join their pieces, unless they are partners (a loop). *)
  if h > 0 && dn > 0
  then (
    let i = h - 1 in
    let ci = (b lsr i) land 1
    and cj = (b lsr h) land 1 in
    if not (ci = 1 && cj = 0)
    then (
      let b' =
        if ci = 1 && cj = 1
        then b lor (1 lsl Word.partner_open b h)
        else if ci = 0 && cj = 0
        then b land lnot (1 lsl Word.partner_close b i)
        else b
      in
      emit (make (low b' i lor ((b' lsr (i + 2)) lsl i)) (len - 2) (h - 1)) [@nontail]))
;;

(* The fewest bridges that build the state from the west. *)
let[@inline always] depth k =
  let #(h, len, b) = unpack k in
  len - bal b h
;;

(* [emit t] for every predecessor [t] of [k] under a bridge step with
   [lower < depth t <= bound] ([lower = -1]: no lower limit). *)
let[@inline always] predecessors ~lower ~bound k (emit : (int -> unit) @ local) =
  let #(h, len, b) = unpack k in
  let[@inline always] out b2 len2 h2 =
    let d = len2 - bal b2 h2 in
    if d <= bound && d > lower then emit (make b2 len2 h2)
  in
  (* open both: a matched pair "()" at h-1, h. *)
  if h >= 1 && h < len && (b lsr (h - 1)) land 1 = 1 && (b lsr h) land 1 = 0
  then out (low b (h - 1) lor ((b lsr (h + 1)) lsl (h - 1))) (len - 2) (h - 1);
  (* open above, close below. *)
  if h >= 1 then out b len (h - 1);
  (* close above, open below. *)
  if h < len then out b len (h + 1);
  (* close both, a pair right of the cut: "((" inserted at h, the pair's '(' at p turned ')'.
     The pairs at top level right of the cut are found by jumping from each '(' to just past
     its partner ([Word.partner_open] skips a byte at a time), until a ')' closes the level. *)
  (* (Loops, not recursive functions, so that flambda inlines [out] and [emit] into them and
     no closure is allocated per state.) *)
  let p = ref h in
  while !p < len && (b lsr !p) land 1 = 1 do
    out (insert2 (b land lnot (1 lsl !p)) h 1 1) (len + 2) (h + 1);
    p := Word.partner_open b !p + 1
  done;
  (* a pair left of the cut: "))" inserted at h, the pair's ')' at q turned '('. Jumping left
     over the top-level pairs, a '(' is the innermost pair straddling the cut: ")(" inserted
     at h. *)
  let q = ref (h - 1) in
  while !q >= 0 && (b lsr !q) land 1 = 0 do
    out (insert2 (b lor (1 lsl !q)) h 0 0) (len + 2) (h + 1);
    q := Word.partner_close b !q - 1
  done;
  if !q >= 0 then out (insert2 b h 0 1) (len + 2) (h + 1) [@nontail]
;;

(* The slow reference (rust/src/state.rs, [#[cfg(test)] predecessors] and [depth]) on decoded
   words: a word is a [bool array] (true = '(') with the cut [h]. Used by the tests. *)
module Reference = struct
  type w =
    { w : bool array
    ; h : int
    }

  let decode k =
    let #(h, len, b) = unpack k in
    { w = Array.init len (fun i -> (b lsr i) land 1 = 1); h }
  ;;

  let encode { w; h } =
    let b = ref 0 in
    Array.iteri (fun i c -> if c then b := !b lor (1 lsl i)) w;
    make !b (Array.length w) h
  ;;

  let balances w =
    let n = Array.length w in
    let bal = Array.make (n + 1) 0 in
    for i = 0 to n - 1 do
      bal.(i + 1) <- (bal.(i) + if w.(i) then 1 else -1)
    done;
    bal
  ;;

  let depth { w; h } = Array.length w - (balances w).(h)

  let insert w i c =
    let n = Array.length w in
    Array.init (n + 1) (fun j -> if j < i then w.(j) else if j = i then c else w.(j - 1))
  ;;

  let remove w i =
    Array.init (Array.length w - 1) (fun j -> if j < i then w.(j) else w.(j + 1))
  ;;

  let predecessors ({ w; h } as s) emit =
    let len = Array.length w in
    let bal = balances w in
    if h >= 1 && h < len && w.(h - 1) && not w.(h)
    then emit { w = remove (remove w h) (h - 1); h = h - 1 };
    if h >= 1 then emit { s with h = h - 1 };
    if h < len then emit { s with h = h + 1 };
    let partner = Array.make len 0 in
    let stack = ref [] in
    for i = 0 to len - 1 do
      if w.(i)
      then stack := i :: !stack
      else (
        match !stack with
        | o :: rest ->
          partner.(o) <- i;
          partner.(i) <- o;
          stack := rest
        | [] -> failwith "unbalanced")
    done;
    let balanced a b =
      let ok = ref (bal.(b) = bal.(a)) in
      for i = a to b do
        if bal.(i) < bal.(a) then ok := false
      done;
      !ok
    in
    for p = 0 to len - 1 do
      if w.(p)
      then (
        let q = partner.(p) in
        let t = Array.copy w in
        let r =
          if p >= h
          then
            if balanced h p
            then (
              t.(p) <- false;
              Some (insert (insert t h true) h true))
            else None
          else if q < h
          then
            if balanced (q + 1) h
            then (
              t.(q) <- true;
              Some (insert (insert t h false) h false))
            else None
          else if balanced (p + 1) h
          then Some (insert (insert t h true) h false)
          else None
        in
        match r with
        | Some t -> emit { w = t; h = h + 1 }
        | None -> ())
    done
  ;;
end
