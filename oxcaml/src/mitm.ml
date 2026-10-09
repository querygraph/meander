(* Meet in the middle, in memory: A(n) = sum_s F_k(s) G^p_r(s) for every split n = k + r
   ([meet] in Arnold/TM/Middle.lean). The same algorithm as rust/src/mitm.rs:

   - [F_k], the forward layer after [k] bridges, mentions no target. It is computed once, with
     no pruning, by the bridge steps of [Back.successors].
   - [G^p_r(s)], the number of ways to finish from [s] with [r] more bridges and then the east
     end on side [p], is computed backwards from [G^p_0] by the inverse transitions
     ([Back.predecessors]). For a horizon [B] a state is kept in [G_r] only if some forward
     layer can meet it, [depth s <= B - r]. Dropping the others is exact: a state's
     predecessors are at least as deep, minus one, so a dropped state never feeds a kept one.

   Each backward layer [G^p_r] gives A(n) for n = 2r + p (the split k = r + p) and checks the
   A(n - 2) of the previous layer through a second split, k = r + p - 2.

   Parallelism and memory layout are those of [Sweep]: 4096 hash shards, each an
   open-addressing table in its own capsule ([Capsule.Sync.With_mutex.t]); one parallel
   subtask per worker, each with its own sub-slice of one parallel scratch array, claims
   source shards from an atomic counter and sends batches of 128 successors to the target
   shards under their locks. Counts are exact: two 62-bit limbs ([Limb]), held in two more
   unboxed [float#] arrays next to the keys (barrier-free stores, see [Sweep]).

   Two differences from the Rust program, neither of which changes any state or count:

   - The forward layers are frozen into immutable [iarray]s once built. They are shared by
     every worker without locks, both as the source of the next forward step and for lookups.
   - The dot products are fused into the backward step: a worker that takes a source shard of
     [G_r] (out of its capsule) looks every state up in the forward layers of both splits
     while expanding it, so a backward layer is read exactly once. The last layer of each
     family is read by a step that emits nothing. *)

open! Base
open! Await
module S = Parallel.Arrays.Array.Slice

type raw = float#

let shards = Sweep.shards
let batch = Sweep.batch
let[@inline always] hash k = Sweep.hash k
let[@inline always] shard_of hv = Sweep.shard_of hv
let[@inline always] to_raw i = Sweep.to_raw i
let[@inline always] of_raw f = Sweep.of_raw f
let[@inline always] uget a i = Sweep.uget a i
let[@inline always] uset a i v = Sweep.uset a i v
let ucreate n = Sweep.ucreate n

(* The table's hot loop works on unboxed [int64#] values, not tagged [int]s: a cell's raw
   bits are its [int64#] value (one [fmov]), and the comparisons, limb additions and carries
   need no tagging or untagging. *)
module U = Stdlib_upstream_compatible.Int64_u
module F = Stdlib_upstream_compatible.Float_u

let[@inline always] rget (a : raw array) i : int64# =
  U.bits_of_float (F.to_float (Array.unsafe_get a i))
;;

let[@inline always] rset (a : raw array) i (v : int64#) =
  Array.unsafe_set a i (F.of_float (U.float_of_bits v))
;;

let[@inline always] iget (a : raw iarray @ local) i : int64# =
  U.bits_of_float (F.to_float (Iarray.unsafe_get a i))
;;

(* A forward step makes every bridge move: no target, so viability never prunes. *)
let no_target = 120

(* An open-addressing table of (state, count) with exact two-limb counts. Slot [i] is three
   consecutive cells of one flat unboxed array: [3i] the key + 1 (so that [0] is empty),
   [3i + 1] the high limb, [3i + 2] the low limb. Keeping a slot's cells together means one
   cache miss per probe instead of three. *)
module Table = struct
  type t =
    { mutable cells : raw array
    ; mutable len : int
    ; want : int
    }

  let create want = { cells = ucreate 0; len = 0; want }
  let[@inline always] slot hv size = Sweep.Table.slot hv size
  let[@inline always] slots cells = Array.length cells / 3

  (* Add (ch, cl) at key [k1 = key + 1] in a table of [n] slots known to have room; [true]
     if the key is new. *)
  let[@inline always] place cells n (k1 : int64#) hv (ch : int64#) (cl : int64#) =
    let rec probe i =
      let j = 3 * i in
      let ki = rget cells j in
      if U.equal ki k1
      then (
        let s = U.add (rget cells (j + 2)) cl in
        rset cells (j + 2) (U.logand s #0x3FFF_FFFF_FFFF_FFFFL);
        rset cells (j + 1) (U.add (U.add (rget cells (j + 1)) ch) (U.shift_right_logical s 62));
        false)
      else if U.equal ki #0L
      then (
        rset cells j k1;
        rset cells (j + 1) ch;
        rset cells (j + 2) cl;
        true)
      else probe (if i + 1 = n then 0 else i + 1)
    in
    probe (slot hv n)
  ;;

  let grow t =
    let old = t.cells in
    let n = if Array.length old = 0 then t.want else Int.max 64 (slots old * 3 / 2) in
    let cells = ucreate (3 * n) in
    for i = 0 to slots old - 1 do
      let k1 = rget old (3 * i) in
      if not (U.equal k1 #0L)
      then
        ignore
          (place
             cells
             n
             k1
             (hash (U.to_int k1 - 1))
             (rget old ((3 * i) + 1))
             (rget old ((3 * i) + 2))
           : bool)
    done;
    t.cells <- cells
  ;;

  let[@inline always] needs_grow len size = (len + 1) * 5 > size * 4

  let add t k ch cl =
    if needs_grow t.len (slots t.cells) then grow t;
    if place t.cells (slots t.cells) (U.of_int (k + 1)) (hash k) (U.of_int ch) (U.of_int cl)
    then t.len <- t.len + 1
  ;;

  (* Add a batch of [n] interleaved (key, hi, lo) triples, keeping the array and size in
     registers. *)
  (* The inserts miss the cache; each iteration also loads the home slot of the insert
     [ahead] places later (there is no prefetch instruction in the libraries here), folded
     into [touch] so that the load stays. *)
  let ahead = 8
  let touch_magic = #0x2B7E_1516_28AE_D2A6L

  let add_batch t (b : raw iarray @ local) n =
    let rec go i cells size len touch =
      if i = n
      then (
        t.len <- len;
        if U.equal touch touch_magic then t.len <- len)
      else if needs_grow len size
      then (
        t.len <- len;
        grow t;
        go i t.cells (slots t.cells) len touch)
      else (
        let touch =
          if i + ahead < n
          then
            U.logxor
              touch
              (rget cells (3 * slot (hash (U.to_int (iget b (3 * (i + ahead))))) size))
          else touch
        in
        let k = iget b (3 * i) in
        let fresh =
          place
            cells
            size
            (U.add k #1L)
            (hash (U.to_int k))
            (iget b ((3 * i) + 1))
            (iget b ((3 * i) + 2))
        in
        go (i + 1) cells size (if fresh then len + 1 else len) touch)
    in
    go 0 t.cells (slots t.cells) t.len #0L [@nontail]
  ;;
end

type shard = Table.t Capsule.Sync.With_mutex.t

let new_layer slots : shard iarray =
  Iarray.init shards ~f:(fun _ ->
    Capsule.Sync.With_mutex.create (fun () -> Table.create slots))
;;

(* A frozen shard: a table's cells, copied into an immutable array that any worker may read. *)
type frozen = raw iarray

let empty_frozen : frozen = (Iarray.of_array [@kind float64]) (ucreate 0)

(* Per-worker scratch region: one batch of [batch] interleaved (key, hi, lo) triples per target
   shard, the batch fill levels, then the worker's results (two dot products as (hi, lo)). *)
let off_fill = 3 * shards * batch
let off_res = off_fill + shards
let region = off_res + 4

let[@inline always] sget (buf : raw S.t @ local) i =
  of_raw ((S.unsafe_get [@kind float64]) buf i)
;;

let[@inline always] sset (buf : raw S.t @ local) i v =
  (S.unsafe_set [@kind float64]) buf i (to_raw v)
;;

let[@inline never] insert_batch (par @ local) (shard : shard) b n =
  Capsule.Sync.With_mutex.with_lock (Parallel.sync par) shard ~f:(fun _ t ->
    Table.add_batch t b n)
  [@nontail]
;;

(* An immutable stack copy of the batch for target shard [d], as in [Sweep.flush]: a fresh
   [local] array, filled and then frozen; sound because it is never mutated after the freeze
   and dies when the caller returns. *)
let[@inline always] batch_copy (buf : raw S.t @ local) d n = exclave_
  let base = 3 * d * batch in
  let a : raw array = Array.create_local ~len:(3 * n) #0.0 in
  for i = 0 to (3 * n) - 1 do
    Array.unsafe_set a i ((S.unsafe_get [@kind float64]) buf (base + i))
  done;
  Iarray.unsafe_of_array__promise_no_mutation a
;;

(* Hand the batch for target shard [d] over to it. *)
let[@inline never] flush (par @ local) (buf : raw S.t @ local) next d =
  let n = sget buf (off_fill + d) in
  insert_batch par (Iarray.get next d) (batch_copy buf d n) n;
  sset buf (off_fill + d) 0
;;

(* Append (k2, ch, cl) to the batch of its target shard; [full] is called when it fills up. *)
let[@inline always] append (buf : raw S.t @ local) k2 ch cl =
  let d = shard_of (hash k2) in
  let f = sget buf (off_fill + d) in
  let j = 3 * ((d * batch) + f) in
  sset buf j k2;
  sset buf (j + 1) ch;
  sset buf (j + 2) cl;
  sset buf (off_fill + d) (f + 1);
  if f + 1 = batch then d else -1
;;

let[@inline always] push (par @ local) (buf : raw S.t @ local) next k2 ch cl =
  let d = append buf k2 ch cl in
  if d >= 0 then flush par buf next d
;;

(* Add [a * b] into the result cells [off], [off + 1] of the worker's region. *)
let[@inline always] accumulate (buf : raw S.t @ local) off ah al bh bl =
  let #(ph, pl) = Limb.mul ah al bh bl in
  let #(h, l) = Limb.add (sget buf off) (sget buf (off + 1)) ph pl in
  sset buf off h;
  sset buf (off + 1) l
;;

(* The count of [k] in a table's cells, [#(hi, lo)]; zero if absent. *)
let[@inline always] lookup_cells cells k =
  let n = Table.slots cells in
  if n = 0
  then #(0, 0)
  else (
    let k1 = k + 1 in
    let rec probe i =
      let j = 3 * i in
      let ki = uget cells j in
      if ki = k1
      then #(uget cells (j + 1), uget cells (j + 2))
      else if ki = 0
      then #(0, 0)
      else probe (if i + 1 = n then 0 else i + 1)
    in
    probe (Table.slot (hash k) n))
;;

(* Add sum_s F(s) G(s) over one shard into the result cells [off]: F a frozen shard, G a
   table's cells. Iterates over F, which is much smaller than G. *)
let dot_shard (buf : raw S.t @ local) off (f : frozen) cells =
  if Array.length cells > 0
  then (
    let fc = f in
    for i = 0 to (Iarray.length fc / 3) - 1 do
      let k1 = of_raw (Iarray.unsafe_get fc (3 * i)) in
      if k1 <> 0
      then (
        let #(gh, gl) = lookup_cells cells (k1 - 1) in
        if gh lor gl <> 0
        then
          accumulate
            buf
            off
            (of_raw (Iarray.unsafe_get fc ((3 * i) + 1)))
            (of_raw (Iarray.unsafe_get fc ((3 * i) + 2)))
            gh
            gl)
    done)
;;

(* The source of a step: a frozen (forward) layer, read in place, or a backward layer in
   capsules, taken shard by shard and freed as it is read. *)
type source =
  | Frozen of frozen iarray
  | Owned of shard iarray

(* What a step does with each source state: the forward bridge steps, or the backward steps
   bounded by [depth <= bound] (nothing at all when [bound < 0]); and the forward layers to
   take dot products with (the main and the check split). *)
type job =
  { backward : bool
  ; bound : int
  ; main : frozen iarray option
  ; check : frozen iarray option
  }

let worker (par @ local) (buf : raw S.t @ local) ~(src : source) ~next ~claim ~(job : job) =
  for i = 0 to 3 do
    sset buf (off_res + i) 0
  done;
  let backward = job.backward
  and bound = job.bound in
  let[@inline always] visit k ch cl =
    if backward
    then
      if bound >= 0
      then
        Back.predecessors ~lower:(-1) ~bound k (fun t -> push par buf next t ch cl) [@nontail]
      else ()
    else Back.successors k (fun t -> push par buf next t ch cl) [@nontail]
  in
  let rec claim_loop (par @ local) =
    let s = Portable.Atomic.fetch_and_add claim 1 in
    if s < shards
    then (
      (match src with
       | Frozen layer ->
         let fc = Iarray.unsafe_get layer s in
         for i = 0 to (Iarray.length fc / 3) - 1 do
           let k1 = of_raw (Iarray.unsafe_get fc (3 * i)) in
           if k1 <> 0
           then
             visit
               (k1 - 1)
               (of_raw (Iarray.unsafe_get fc ((3 * i) + 1)))
               (of_raw (Iarray.unsafe_get fc ((3 * i) + 2)))
         done
       | Owned layer ->
         (* Take the source shard out of its capsule: we now own it. *)
         let t = Capsule.Sync.With_mutex.destroy (Parallel.sync par) (Iarray.get layer s) in
         let cells = t.cells in
         t.cells <- ucreate 0;
         t.len <- 0;
         (* The dot products: each state of the (small) forward shard looked up here. *)
         (match job.main with
          | Some f -> dot_shard buf off_res (Iarray.unsafe_get f s) cells
          | None -> ());
         (match job.check with
          | Some f -> dot_shard buf (off_res + 2) (Iarray.unsafe_get f s) cells
          | None -> ());
         for i = 0 to Table.slots cells - 1 do
           let k1 = uget cells (3 * i) in
           if k1 <> 0 then visit (k1 - 1) (uget cells ((3 * i) + 1)) (uget cells ((3 * i) + 2))
         done);
      claim_loop par)
  in
  claim_loop par;
  for d = 0 to shards - 1 do
    if sget buf (off_fill + d) > 0 then flush par buf next d
  done
;;

let shard_len (par @ local) (s : shard) =
  Capsule.Sync.With_mutex.with_lock (Parallel.sync par) s ~f:(fun _ t -> t.len) [@nontail]
;;

let layer_size (par @ local) (l : shard iarray) =
  let n = ref 0 in
  for s = 0 to shards - 1 do
    n := !n + shard_len par (Iarray.get l s)
  done;
  !n
;;

(* Freeze a finished layer: take each shard out of its capsule and copy its cells into an
   immutable array (a safe copy; forward layers are small). *)
let freeze (par @ local) (l : shard iarray) : frozen iarray =
  Iarray.init shards ~f:(fun d ->
    let t = Capsule.Sync.With_mutex.destroy (Parallel.sync par) (Iarray.get l d) in
    if t.len = 0 then empty_frozen else (Iarray.of_array [@kind float64]) t.cells)
  [@nontail]
;;

(* Slots per shard for the next layer ([Sweep.predict_slots]); an empty layer stays small. *)
let predict ~size ~prev ~prev2 =
  if size = 0 then 64 else Sweep.predict_slots ~size ~prev ~prev2
;;

(* A run: the scratch array, its pivots, and the worker count. *)
type ctx =
  { scratch : raw Parallel.Arrays.Array.t
  ; pivots : int iarray
  ; threads : int
  }

let make_ctx threads =
  { scratch = Parallel.Arrays.Array.of_array (ucreate (threads * region))
  ; pivots = Iarray.init (threads - 1) ~f:(fun w -> (w + 1) * region)
  ; threads
  }
;;

(* One parallel step from [src] into a fresh layer of [slots]-slot shards. Returns the new
   layer and the two dot products #(main hi, main lo, check hi, check lo). *)
let step (par @ local) ctx ~src ~job ~slots =
  let next = new_layer slots in
  let claim = Portable.Atomic.make 0 in
  (S.fori [@kind float64]) par ~pivots:ctx.pivots ((S.slice [@kind float64]) ctx.scratch)
    ~f:(fun par _ buf -> worker par buf ~src ~next ~claim ~job);
  let all = (S.slice [@kind float64]) ctx.scratch in
  let mh = ref 0
  and ml = ref 0
  and ch = ref 0
  and cl = ref 0 in
  for w = 0 to ctx.threads - 1 do
    let o = (w * region) + off_res in
    let #(h, l) = Limb.add !mh !ml (sget all o) (sget all (o + 1)) in
    mh := h;
    ml := l;
    let #(h, l) = Limb.add !ch !cl (sget all (o + 2)) (sget all (o + 3)) in
    ch := h;
    cl := l
  done;
  next, (!mh, !ml), (!ch, !cl)
;;

let singleton (par @ local) entries : shard iarray =
  let l = new_layer 64 in
  List.iter entries ~f:(fun k ->
    Capsule.Sync.With_mutex.with_lock
      (Parallel.sync par)
      (Iarray.get l (shard_of (hash k)))
      ~f:(fun _ t -> Table.add t k 0 1) [@nontail]);
  l
;;

(* [G^p_0]: the states from which the east end on side [p] finishes. A matched pair of open
   arcs, one above and one below the road for p = 1, both below for p = 0; for p = 0 the
   empty state also finishes (A(0) = 1). *)
let finishers p = if p = 0 then [ Back.pair 0; Back.init ] else [ Back.pair 1 ]

type row =
  { n : int
  ; count : string
  ; check : string option
  ; forward_states : int
  ; backward_states : int
  }

let to_string (h, l) = Limb.to_string h l

(* A(n) for every n <= [horizon], each by the split k = ceil(n/2), checked by k - 1. *)
let run (par @ local) ~horizon ~threads =
  let ctx = make_ctx threads in
  let kmax = horizon - (horizon / 2) in
  let fwd = Array.create ~len:(kmax + 1) (Iarray.init shards ~f:(fun _ -> empty_frozen)) in
  fwd.(0) <- freeze par (singleton par [ Back.init ]);
  let forward = { backward = false; bound = 0; main = None; check = None } in
  let fsize = Array.create ~len:(kmax + 1) 1 in
  for k = 1 to kmax do
    let size = fsize.(k - 1) in
    let prev = if k >= 2 then fsize.(k - 2) else 0
    and prev2 = if k >= 3 then fsize.(k - 3) else 0 in
    let next, _, _ =
      step
        par
        ctx
        ~src:(Frozen fwd.(k - 1))
        ~job:forward
        ~slots:(predict ~size ~prev ~prev2)
    in
    fsize.(k) <- layer_size par next;
    fwd.(k) <- freeze par next
  done;
  let rows : row option array = Array.create ~len:(horizon + 1) None in
  for p = 0 to 1 do
    let g = ref (singleton par (finishers p)) in
    let size = ref (List.length (finishers p))
    and prev = ref 0
    and prev2 = ref 0 in
    let r = ref 0
    and continue = ref true in
    while !continue do
      let r_ = !r in
      let n = (2 * r_) + p in
      let main = if n <= horizon then Some fwd.(r_ + p) else None in
      let check =
        if r_ >= 1 && n >= 2 && n - 2 <= horizon && r_ + p >= 2
        then Some fwd.(r_ + p - 2)
        else None
      in
      let last = n >= horizon + 2 in
      (* G_{r+1}: predecessors, kept if a forward layer can still meet them. *)
      let bound = if last then -1 else Int.max 0 (horizon - (r_ + 1)) in
      let next, mainv, checkv =
        step
          par
          ctx
          ~src:(Owned !g)
          ~job:{ backward = true; bound; main; check }
          ~slots:
            (if last then 64 else predict ~size:!size ~prev:!prev ~prev2:!prev2)
      in
      if n <= horizon
      then
        rows.(n)
        <- Some
             { n
             ; count = to_string mainv
             ; check = None
             ; forward_states = fsize.(r_ + p)
             ; backward_states = !size
             };
      (match check with
       | Some _ ->
         (match rows.(n - 2) with
          | Some row -> rows.(n - 2) <- Some { row with check = Some (to_string checkv) }
          | None -> ())
       | None -> ());
      if last
      then continue := false
      else (
        g := next;
        prev2 := !prev;
        prev := !size;
        size := layer_size par next;
        r := r_ + 1)
    done
  done;
  Array.filter_map rows ~f:Fn.id
;;
