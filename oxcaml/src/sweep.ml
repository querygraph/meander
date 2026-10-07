(* The parallel layer sweep: the same algorithm as rust/src/par.rs, written with OxCaml's
   data-race-free parallelism (the [Parallel] scheduler, capsules and parallel arrays).

   A layer is split into [shards] = 4096 hash shards. Each shard is an open-addressing table
   that lives in its own capsule, protected by that capsule's mutex
   ([Capsule.Sync.With_mutex.t]). For each point [x], one parallel subtask per worker claims
   source shards from an atomic counter, computes the successors of every state in the shard,
   and batches them per target shard. A full batch (128 states) is added into its target
   shard under that shard's lock. A source shard is freed as soon as it has been read, so the
   sweep holds little more than one layer at a time.

   How the modes make this data-race free:

   - Shard tables are only ever touched inside their capsule: through
     [With_mutex.with_lock], whose callback must be [portable] (it cannot capture any
     unprotected mutable state), or after [With_mutex.destroy], which poisons the mutex and
     merges the table into the caller's capsule, giving it sole ownership. A worker uses
     [destroy] to take its claimed source shard: it reads it without locking and frees it.

   - Each worker needs a large mutable scratch area (4096 batches of 128 keys and counts)
     that persists across layers, but a [Parallel.for_] body is only [shareable]: it may read,
     not write, what it captures. The scratch is therefore one parallel array
     ([Parallel.Arrays.Array]) allocated once per sweep and split by
     [Parallel.Arrays.Array.Slice.fori] into disjoint sub-slices, one per worker. Each
     subtask receives its own sub-slice [uncontended], so it may write to it; the type
     system guarantees no two subtasks share one.

   - A batch must cross into the lock's [portable] callback. A mutable buffer would be
     [contended] there, hence unreadable, so [flush] copies the batch into two immutable
     [iarray]s on the stack ([local]: freed when [flush] returns, never seen by the GC).
     Immutable arrays of unboxed scalars cross contention, so the portable callback may read
     them. The copies are built the way [Base.Iarray.init [@alloc stack]] builds its result
     (fill a fresh local array, then freeze it with [unsafe_of_array__promise_no_mutation]),
     because the library function's per-element closure call and barriered stores cost 20%
     of the single-thread run. This is the program's only [unsafe_]-named call; it is sound
     because the arrays are fresh, never mutated after the freeze, and die with [flush].

   OxCaml performance features used here:

   - Unboxed arrays ([float# array], see "barrier-free stores" below) for the shard tables and
     the scratch. They are not scanned by the GC (with [int array]s of several GB the major
     GC spent seconds marking immediates), and the [float64] instances of the templated
     parallel-array accessors ([Slice.unsafe_get [@kind float64]]) compile to a plain load or
     store (the value-kind accessors are out-of-line calls).

   - Barrier-free stores. On arm64, OCaml 5 emits [dmb ishld] before every mutable word
     store, so that racy programs keep the OCaml memory model; in a store loop that barrier
     costs ~10 ns per store here (vs ~2 ns for the loop without it). Stores of unboxed
     [float#] are exempt (the backend applies the barrier only to word-sized int and value
     stores). The program is data-race free by construction, so the barrier buys nothing:
     every table and buffer cell holds an OCaml [int] as its raw 64-bit pattern in a
     [float#] slot, converted with [Int64_u.float_of_bits]/[bits_of_float] (one bit-exact
     [fmov] each way; no float arithmetic ever touches them). This one change took the
     single-thread n = 34 time from 1.27 s to 0.89 s (Rust: 0.75-0.83 s on the same box).

   - Stack allocation ([local] slices, closures and batch copies): the inner loop and [flush]
     allocate nothing on the GC heap, so OCaml 5's stop-the-world minor collections (which
     stall every domain) stay rare.

   - Unboxed tuples: [Word.successors] returns its (up to four) successors as an unboxed
     [#(int * int * int * int)] in registers, with no callback closure.

   - flambda2 at -O3 with [@inline always] on the hot helpers; dune's release profile (not
     the default dev profile, which compiles with -opaque and so blocks cross-module
     inlining).

   Two algorithmic refinements over the Rust program, neither of which changes any state or
   count: each next-layer shard is pre-sized from the observed layer growth
   ([predict_slots]) and allocated lazily by the first worker to insert into it, so tables
   rarely rehash; and a batch insert keeps the table size in a register.
*)

open! Base
open! Await
module U = Stdlib_upstream_compatible.Int64_u
module F = Stdlib_upstream_compatible.Float_u
module S = Parallel.Arrays.Array.Slice

let shard_bits = 12
let shards = 1 lsl shard_bits
let batch = 128
let p61 = (1 lsl 61) - 1

(* A 63-bit mixer (multiply, xorshift, multiply, xorshift). The shard is taken from the top
   12 bits, and the slot from 31 independent bits below them. *)
let[@inline always] hash k =
  let x = k * 0x2545F4914F6CDD1D in
  let x = x lxor (x lsr 29) in
  let x = x * 0x1F3D5B79A6C2E987 in
  x lxor (x lsr 32)
;;

let[@inline always] shard_of hv = (hv lsr 51) land (shards - 1)

(* Counts are modulo 2^63 (native [int] wraparound) or modulo the Mersenne prime 2^61 - 1. *)
module type Modulus = sig @@ portable
  val add : int -> int -> int
end

module Mod63 = struct
  let[@inline always] add a b = a + b
end

module Mod61 = struct
  let[@inline always] add a b =
    let s = a + b in
    (* both < 2^61, so s < 2^62 fits *)
    if s >= p61 then s - p61 else s
  ;;
end

(* Raw 64-bit cells. Every table and buffer holds OCaml ints as raw 64-bit patterns in
   unboxed [float#] slots (moved bit-exactly with [fmov]; no float arithmetic is ever done
   on them). See "Barrier-free stores" in the header comment. *)
type raw = float#

let[@inline always] to_raw (i : int) : raw = F.of_float (U.float_of_bits (U.of_int i))
let[@inline always] of_raw (f : raw) : int = U.to_int (U.bits_of_float (F.to_float f))
let[@inline always] uget (a : raw array) i = of_raw (Array.unsafe_get a i)
let[@inline always] uset (a : raw array) i v = Array.unsafe_set a i (to_raw v)
let[@inline always] ucreate n : raw array = Array.create ~len:n #0.0

(* An open-addressing table of (state, count) with linear probing, keys and counts in
   separate flat unboxed arrays. A slot stores [key + 1], so an empty slot is [0]. Tables
   start empty and grow by half when 80% full, as in the Rust program. The size need not be a
   power of two: the slot is [(r * size) lsr 31] for a 31-bit hash fragment [r]. *)
module Table = struct
  type t =
    { mutable keys : raw array
    ; mutable cnts : raw array
    ; mutable len : int
    ; want : int (* slots to allocate on the first insert *)
    }

  (* Tables are allocated lazily, on the first insert, by whichever worker holds the lock:
     allocating and zeroing them all up front would be serial work in the main task.
     [want] is the predicted size ([predict_slots]). *)
  let create want = { keys = ucreate 0; cnts = ucreate 0; len = 0; want }
  let[@inline always] slot hv size = (((hv lsr 20) land 0x7FFF_FFFF) * size) lsr 31

  module Make (M : Modulus) = struct
    (* Insert into a table known to have room; [true] if a new slot was used. *)
    let[@inline always] place keys cnts k1 hv c =
      let n = Array.length keys in
      let rec probe i =
        let ki = uget keys i in
        if ki = k1
        then (
          uset cnts i (M.add (uget cnts i) c);
          false)
        else if ki = 0
        then (
          uset keys i k1;
          uset cnts i c;
          true)
        else probe (if i + 1 = n then 0 else i + 1)
      in
      probe (slot hv n)
    ;;

    let grow t =
      let old_keys = t.keys
      and old_cnts = t.cnts in
      let n =
        if Array.length old_keys = 0 then t.want else Int.max 64 (Array.length old_keys * 3 / 2)
      in
      let keys = ucreate n
      and cnts = ucreate n in
      for i = 0 to Array.length old_keys - 1 do
        let k1 = uget old_keys i in
        if k1 <> 0 then ignore (place keys cnts k1 (hash (k1 - 1)) (uget old_cnts i) : bool)
      done;
      t.keys <- keys;
      t.cnts <- cnts
    ;;

    let[@inline always] add t k hv c =
      if (t.len + 1) * 5 > Array.length t.keys * 4 then grow t;
      if place t.keys t.cnts (k + 1) hv c then t.len <- t.len + 1
    ;;

    (* Add a batch, keeping the table's arrays and size in registers: [len] is a boxed record
       field, and every mutable word store costs a barrier (see the header comment). *)
    let add_batch t (ks : raw iarray @ local) (cs : raw iarray @ local) n =
      let rec go i keys cnts len =
        if i = n
        then t.len <- len
        else if (len + 1) * 5 > Array.length keys * 4
        then (
          t.len <- len;
          grow t;
          go i t.keys t.cnts len)
        else (
          let k = of_raw (Iarray.unsafe_get ks i) in
          let c = of_raw (Iarray.unsafe_get cs i) in
          let fresh = place keys cnts (k + 1) (hash k) c in
          go (i + 1) keys cnts (if fresh then len + 1 else len))
      in
      go 0 t.keys t.cnts t.len [@nontail]
    ;;
  end

  let find t k =
    let k1 = k + 1 in
    let r = ref 0 in
    for i = 0 to Array.length t.keys - 1 do
      if uget t.keys i = k1 then r := uget t.cnts i
    done;
    !r
  ;;
end

type shard = Table.t Capsule.Sync.With_mutex.t

(* A fresh layer whose shard tables have [slots] slots each. *)
let new_layer slots : shard iarray =
  Iarray.init shards ~f:(fun _ ->
    Capsule.Sync.With_mutex.create (fun () -> Table.create slots))
;;

(* Slots per shard for the next layer, predicted from the last three layer sizes so that
   tables rarely need to grow (rehashing was a quarter of the single-thread time), without
   over-allocating near the peak, where the growth ratio falls quickly (about 2, 1.6, 1.3,
   0.9, 0.5 per layer): the ratio [r = size / prev] is extrapolated geometrically,
   [r * r / r_prev], clamped to [0.25, 2.5], and the table is sized for load 0.75. A
   misprediction only costs a growth step (too small) or some slack (too large). *)
let predict_slots ~size ~prev ~prev2 =
  let f = Float.of_int in
  let r = if prev > 0 then f size /. f prev else 2.5 in
  let r_prev = if prev2 > 0 then f prev /. f prev2 else r in
  let r_next = Float.max 0.25 (Float.min 2.5 (r *. r /. r_prev)) in
  Int.max 64 (Float.iround_up_exn (f size *. r_next /. f shards /. 0.75))
;;

(* Per-worker scratch, one region of the sweep's parallel array: batch keys, batch counts,
   and the fill level of each batch. *)
let region = (2 * shards * batch) + shards
let off_cnt = shards * batch
let off_fill = 2 * shards * batch
let[@inline always] sget (buf : raw S.t @ local) i = of_raw ((S.unsafe_get [@kind float64]) buf i)

let[@inline always] sset (buf : raw S.t @ local) i v =
  (S.unsafe_set [@kind float64]) buf i (to_raw v)
;;

module Run (M : Modulus) = struct
  module T = Table.Make (M)

  (* Add [n] successors (keys [ks], counts [cs]) into [shard] under its lock. The callback is
     [portable]: it sees the table [uncontended] and the immutable batch. *)
  let[@inline never] insert_batch (par @ local) (shard : shard) (ks : raw iarray @ local)
    (cs : raw iarray @ local) n
    =
    Capsule.Sync.With_mutex.with_lock (Parallel.sync par) shard ~f:(fun _ t ->
      T.add_batch t ks cs n)
    [@nontail]
  ;;

  (* Hand the batch for target shard [d] over to it. *)
  let[@inline never] flush (par @ local) (buf : raw S.t @ local) next d =
    let n = sget buf (off_fill + d) in
    let base = d * batch in
    (* Immutable copies of the batch on the stack (see the header comment): fresh [local]
       arrays, filled and then frozen, exactly as [Base.Iarray.init [@alloc stack]] does it.
       Sound: they are never mutated after the freeze and die when [flush] returns. *)
    let ka : raw array = Array.create_local ~len:n #0.0
    and ca : raw array = Array.create_local ~len:n #0.0 in
    for i = 0 to n - 1 do
      Array.unsafe_set ka i ((S.unsafe_get [@kind float64]) buf (base + i));
      Array.unsafe_set ca i ((S.unsafe_get [@kind float64]) buf (off_cnt + base + i))
    done;
    let ks = Iarray.unsafe_of_array__promise_no_mutation ka
    and cs = Iarray.unsafe_of_array__promise_no_mutation ca in
    insert_batch par (Iarray.get next d) ks cs n;
    sset buf (off_fill + d) 0
  ;;

  (* Append successor [k2] (with count [c]) to the batch of its target shard. *)
  let[@inline always] push (par @ local) (buf : raw S.t @ local) next k2 c =
    if k2 >= 0
    then (
      let d = shard_of (hash k2) in
      let f = sget buf (off_fill + d) in
      sset buf ((d * batch) + f) k2;
      sset buf (off_cnt + (d * batch) + f) c;
      sset buf (off_fill + d) (f + 1);
      if f + 1 = batch then flush par buf next d)
  ;;

  (* One worker's share of point [x]: [buf] is its own sub-slice of the scratch array. *)
  let worker (par @ local) (buf : raw S.t @ local) ~m ~x ~(layer : shard iarray)
    ~(next : shard iarray) ~claim
    =
    let rec claim_loop (par @ local) =
      let s = Portable.Atomic.fetch_and_add claim 1 in
      if s < shards
      then (
        (* Take the source shard out of its capsule: we now own it. *)
        let src = Capsule.Sync.With_mutex.destroy (Parallel.sync par) (Iarray.get layer s) in
        let keys = src.keys
        and cnts = src.cnts in
        src.keys <- ucreate 0;
        src.cnts <- ucreate 0;
        src.len <- 0;
        for i = 0 to Array.length keys - 1 do
          let k1 = uget keys i in
          if k1 <> 0
          then (
            let c = uget cnts i in
            let #(s0, s1, s2, s3) = Word.successors m x (k1 - 1) in
            push par buf next s0 c;
            push par buf next s1 c;
            push par buf next s2 c;
            push par buf next s3 c)
        done;
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

  (* One sweep for [m] crossings: (count of the final state, peak layer, total states). *)
  let sweep (par @ local) ~m ~threads =
    let layer = ref (new_layer 64) in
    (let k = Word.init in
     let hv = hash k in
     Capsule.Sync.With_mutex.with_lock
       (Parallel.sync par)
       (Iarray.get !layer (shard_of hv))
       ~f:(fun _ t -> T.add t k hv 1));
    let peak = ref 1
    and total = ref 0
    and size = ref 1
    and prev = ref 0
    and prev2 = ref 0 in
    (* All per-worker scratch, allocated once per sweep and split by [pivots]. *)
    let scratch = Parallel.Arrays.Array.of_array (ucreate (threads * region)) in
    let pivots = Iarray.init (threads - 1) ~f:(fun w -> (w + 1) * region) in
    for x = 0 to m do
      let next = new_layer (predict_slots ~size:!size ~prev:!prev ~prev2:!prev2) in
      let claim = Portable.Atomic.make 0 in
      let layer_x = !layer in
      (S.fori [@kind float64]) par ~pivots ((S.slice [@kind float64]) scratch)
        ~f:(fun par _ buf -> worker par buf ~m ~x ~layer:layer_x ~next ~claim);
      layer := next;
      prev2 := !prev;
      prev := !size;
      size := 0;
      for s = 0 to shards - 1 do
        size := !size + shard_len par (Iarray.get next s)
      done;
      peak := Int.max !peak !size;
      total := !total + !size
    done;
    let f = Word.final in
    let c =
      Capsule.Sync.With_mutex.with_lock
        (Parallel.sync par)
        (Iarray.get !layer (shard_of (hash f)))
        ~f:(fun _ t -> Table.find t f)
    in
    c, !peak, !total
  ;;
end

module Run63 = Run (Mod63)
module Run61 = Run (Mod61)
