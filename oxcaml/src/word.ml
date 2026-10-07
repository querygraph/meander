(* The transfer-matrix state of [Arnold.TM] (Arnold/TM/Defs.lean), packed into one OCaml
   immediate [int].

   A state lists the open arcs along the cut from top to bottom (the upper stack bottom..top,
   then the lower stack top..bottom). They form a non-crossing matching, written as a word over
   '(' and ')', plus at most one 'E' (an arc whose piece of river leads to the east end),
   together with [h], the number of arcs above the road.

   Layout of a key (63-bit OCaml int, always non-negative):

     bits 57..61  h        (5 bits; h <= 31 holds for every n <= 60)
     bits 51..56  epos     (word position of 'E', or 63 when there is none)
     bits  0..50  brackets other than 'E' (bit j = bracket j, 1 = '(' and 0 = ')') under a
                  leading sentinel 1, so at most 50 brackets.

   The largest key is below 2^62, so [key + 1] is still a positive immediate; the hash tables
   store [key + 1] so that an empty slot is [0].

   Unlike the Rust program, which widens every key to a 2-bit-per-letter [u128] word to compute
   successors, this module works directly on the bracket bits and the position of 'E': the
   word position [i] holds 'E' if [i = epos], and otherwise bracket [i - (1 if i > epos)].
   Everything stays in registers as machine integers: flambda2 inlines [successors] into the
   sweep's inner loop (the rarer (close, close) join and the east end are direct calls), and
   it returns an unboxed tuple, so the successor computation allocates nothing. *)

let h_shift = 57
let e_shift = 51
let bits_mask = (1 lsl e_shift) - 1
let no_end = 63
let max_brackets = 50

(* [clz] on the tagged int compiles to a single [clz] instruction (ocaml_intrinsics_kernel). *)
let[@inline always] top_bit x = 62 - Ocaml_intrinsics_kernel.Int.count_leading_zeros x

let[@inline always] encode ~h ~e ~b ~nb =
  if nb > max_brackets || h > 31 then failwith "Word.encode: state does not fit in 63 bits";
  (h lsl h_shift) lor (e lsl e_shift) lor b lor (1 lsl nb)
;;

(* The initial state (nothing open) and [final] (one arc below the road, leading to E). *)
let init = encode ~h:0 ~e:no_end ~b:0 ~nb:0
let final = encode ~h:0 ~e:0 ~b:0 ~nb:0

(* [cap m k up]: how many of the points k..m still to come have an arc on side [up]. *)
let[@inline always] cap m k up =
  if k <= m then m - k + if (m land 1 = 1) = up then 1 else 0 else 0
;;

(* Bits [0, j) of [b]. *)
let[@inline always] low b j = b land ((1 lsl j) - 1)

(* Insert bit [c] at index [j]. *)
let[@inline always] ins b j c = low b j lor (c lsl j) lor ((b lsr j) lsl (j + 1))

(* Remove bit [j]. *)
let[@inline always] del b j = low b j lor ((b lsr (j + 1)) lsl j)

(* Remove the adjacent bits [j] and [j + 1]. *)
let[@inline always] del2 b j = low b j lor ((b lsr (j + 2)) lsl j)

(* Partner search, a byte at a time. For each byte value [v], [fwd.(v)] packs the minimum
   prefix sum and the total of its bits read upward (bit 0 first, '(' = +1, ')' = -1), and
   [bwd.(v)] the same read downward (bit 7 first, ')' = +1, '(' = -1); both biased by 8.
   A whole byte is skipped when the running depth cannot reach -1 inside it. The tables are
   immutable [iarray]s, so portable code may read them. *)
let pack ~min ~sum = (min + 8) lor ((sum + 8) lsl 8)

let fwd : int iarray =
  Base.Iarray.init 256 ~f:(fun v ->
    let s = ref 0
    and m = ref 8 in
    for k = 0 to 7 do
      s := !s + if (v lsr k) land 1 = 1 then 1 else -1;
      if !s < !m then m := !s
    done;
    pack ~min:!m ~sum:!s)
;;

let bwd : int iarray =
  Base.Iarray.init 256 ~f:(fun v ->
    let s = ref 0
    and m = ref 8 in
    for k = 7 downto 0 do
      s := !s + if (v lsr k) land 1 = 0 then 1 else -1;
      if !s < !m then m := !s
    done;
    pack ~min:!m ~sum:!s)
;;

(* The partner of the '(' at bracket index [j]: scan right, counting depth. A partner
   always exists below bit 50, so [i] stays below 58 and the shifts are in range. *)
let partner_open b j =
  let rec bits b i d =
    if (b lsr i) land 1 = 1
    then bits b (i + 1) (d + 1)
    else if d = 0
    then i
    else bits b (i + 1) (d - 1)
  in
  let rec bytes b i d =
    let t = Base.Iarray.unsafe_get fwd ((b lsr i) land 255) in
    if d + (t land 255) - 8 >= 0 then bytes b (i + 8) (d + (t lsr 8) - 8) else bits b i d
  in
  bytes b (j + 1) 0
;;

(* The partner of the ')' at bracket index [j]: scan left, counting depth. *)
let partner_close b j =
  let rec bits b i d =
    if (b lsr i) land 1 = 0
    then bits b (i - 1) (d + 1)
    else if d = 0
    then i
    else bits b (i - 1) (d - 1)
  in
  let rec bytes b i d =
    if i < 7
    then bits b i d
    else (
      let t = Base.Iarray.unsafe_get bwd ((b lsr (i - 7)) land 255) in
      if d + (t land 255) - 8 >= 0 then bytes b (i - 8) (d + (t lsr 8) - 8) else bits b i d)
  in
  bytes b (j - 1) 0
;;

let[@inline always] partner b j =
  if (b lsr j) land 1 = 1 then partner_open b j else partner_close b j
;;

(* The key of a successor if it is viable after point [x] (h2 <= cu and l2 - h2 <= cd), else
   [-1]. *)
let[@inline always] mk ~cu ~cd ~h2 ~l2 ~e2 ~b2 ~nb2 =
  if h2 <= cu && l2 - h2 <= cd then encode ~h:h2 ~e:e2 ~b:b2 ~nb:nb2 else -1
;;

(* (close, close) at a bridge, h > 0 and dn > 0: close both top arcs (word positions h-1 and
   h) and join their pieces, unless that closes a loop. *)
let join ~cu ~cd ~h ~e ~he ~b ~nb ~l =
  let i = h - 1
  and j = h in
  (* Word position of bracket index [q]. *)
  let[@inline always] wpos q = if he && q >= e then q + 1 else q in
  if he && (e = i || e = j)
  then (
    (* One of them is E: the other's partner now leads to E. The other is bracket [i] in both
       cases (if w[i] = E, w[j] is bracket j - 1 = i). *)
    let q = i in
    let p = partner b q in
    let wp = wpos p in
    let fp = if wp < i then wp else wp - 2 in
    let lo = if p < q then p else q
    and hi = if p < q then q else p in
    mk ~cu ~cd ~h2:(h - 1) ~l2:(l - 2) ~e2:fp ~b2:(del (del b hi) lo) ~nb2:(nb - 2))
  else (
    let ii = if he && i > e then i - 1 else i in
    let ci = (b lsr ii) land 1
    and cj = (b lsr (ii + 1)) land 1 in
    if ci = 1 && cj = 0
    then -1
    else (
      let b' =
        if ci = 1 && cj = 1
        then b lor (1 lsl partner_open b (ii + 1))
        else if ci = 0 && cj = 0
        then b land lnot (1 lsl partner_close b ii)
        else b
      in
      mk
        ~cu
        ~cd
        ~h2:(h - 1)
        ~l2:(l - 2)
        ~e2:(if he && e > j then e - 2 else e)
        ~b2:(del2 b' ii)
        ~nb2:(nb - 2)))
;;

(* The east end x = m: one arc, on side [m mod 2]. No state has an E before this point. *)
let east ~m ~cu ~cd ~h ~e ~he ~b ~nb ~l ~dn =
  if he then failwith "Word.successors: E before the east end";
  let up = m land 1 = 1 in
  (* open: its piece leads to E. *)
  let s0 = mk ~cu ~cd ~h2:(if up then h + 1 else h) ~l2:(l + 1) ~e2:h ~b2:b ~nb2:nb in
  (* close the top arc on that side; its partner's piece now leads to E. *)
  let top = if up then h - 1 else if dn > 0 then h else -1 in
  let s1 =
    if top >= 0
    then (
      let p = partner b top in
      let fp = if p < top then p else p - 1 in
      let lo = if p < top then p else top
      and hi = if p < top then top else p in
      mk
        ~cu
        ~cd
        ~h2:(if up then h - 1 else h)
        ~l2:(l - 1)
        ~e2:fp
        ~b2:(del (del b hi) lo)
        ~nb2:(nb - 2))
    else -1
  in
  ignore e;
  #(s0, s1)
;;

(* [successors m x k] is the (up to 4) viable successors of state [k] at point [x] of an
   [m]-crossing river, as an unboxed 4-tuple with [-1] for "none". The unboxed tuple is
   returned in registers: nothing is allocated, and there is no callback closure. *)
let[@inline always] successors m x k : #(int * int * int * int) =
  let h = k lsr h_shift in
  let e = (k lsr e_shift) land 63 in
  let sb = k land bits_mask in
  let nb = top_bit sb in
  let b = sb lxor (1 lsl nb) in
  let he = e <> no_end in
  let l = if he then nb + 1 else nb in
  let dn = l - h in
  let cu = cap m (x + 1) true in
  let cd = cap m (x + 1) false + 1 in
  if x < m
  then (
    (* (open, open): insert "()" at word positions h, h+1 (bracket index jh). *)
    let jh = if he && h > e then h - 1 else h in
    let s0 =
      mk
        ~cu
        ~cd
        ~h2:(h + 1)
        ~l2:(l + 2)
        ~e2:(if he && e >= h then e + 2 else e)
        ~b2:(low b jh lor (1 lsl jh) lor ((b lsr jh) lsl (jh + 2)))
        ~nb2:(nb + 2)
    in
    (* (open above, close below): the word is unchanged. *)
    let s1 = if dn > 0 then mk ~cu ~cd ~h2:(h + 1) ~l2:l ~e2:e ~b2:b ~nb2:nb else -1 in
    (* (close above, open below). *)
    let s2 = if h > 0 then mk ~cu ~cd ~h2:(h - 1) ~l2:l ~e2:e ~b2:b ~nb2:nb else -1 in
    (* (close, close). *)
    let s3 = if h > 0 && dn > 0 then join ~cu ~cd ~h ~e ~he ~b ~nb ~l else -1 in
    #(s0, s1, s2, s3))
  else (
    let #(s0, s1) = east ~m ~cu ~cd ~h ~e ~he ~b ~nb ~l ~dn in
    #(s0, s1, -1, -1))
;;
