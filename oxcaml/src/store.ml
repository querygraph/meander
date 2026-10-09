(* The persistent, stepwise meet-in-the-middle store: the algorithm and the directory layout of
   rust/src/store.rs and rust/src/mitm_store.rs.

   A store at [root] holds the forward layers [F/kkk], the backward layers [G{p}/rrr] for both
   sides [p] of the east end, a [manifest] and the computed [values]. It is built for
   increasing horizons B0 < B1 < ...: segment [i] of a backward layer [G^p_r] holds the states
   with [B_{i-1} - r < depth <= B_i - r] (all states with [depth <= B0 - r] for [i = 0]).

   A layer is a directory. Its states are split into the 4096 hash shards of [Sweep], and each
   segment [s] of the layer is two files: [seg{s}.dat], the shards' records one after another,
   each shard sorted by state and written as varint (state difference, count) records, and
   [seg{s}.idx], the byte range of every shard (4096 x (offset, length), u64 little-endian).
   Segments of one layer hold disjoint sets of states. A segment exists once its index does.

   [step] builds one new segment from a source layer: workers stream source shards (each
   segment in turn: they are disjoint), apply a transition, and add the results into capped
   in-memory tables, one per target shard, each in its own capsule. A table that grows past
   the cap is sorted and appended to the step's one spill file [dst/tmp/spill]. At the end each
   target shard's spilled ranges and remainder are merged in memory and appended to the
   segment file. Readers open a layer's few files once per worker and read byte ranges: a step
   creates three files, not thousands (one file per shard, created and closed by dozens of
   threads at once, hung an HFS+ SoftRAID volume).

   [extend root B'] raises the horizon from B to B'. The forward layers grow by the missing
   ones. Every backward layer gains one segment: the states newly admitted by B', pushed from
   ALL segments of the previous layer by the inverse transitions. Existing values never
   change, so nothing is recomputed. Each new A(n) is the dot product (a merge-join per shard)
   of F_{ceil(n/2)} and G^{n mod 2}_{floor(n/2)}, checked by the second split
   F_{ceil(n/2)-1} . G_{floor(n/2)+1}. A file [PAUSE] in the store, or too little free disk,
   stops [extend] at the next layer boundary; running it again with the same horizon resumes.

   The keys are [Back] keys (63-bit OCaml ints), not Rust's, so the segment files differ
   from the Rust store's; the [values] files and the per-layer state counts are the same. The
   manifest's format line says so ([meanders-ox-mitm-2]). *)

open! Await
module S = Parallel.Arrays.Array.Slice
module RA = Base.Array (* layout-polymorphic: used on the unboxed [raw] arrays *)
module Atomic = Portable.Atomic
module Iarray = Base.Iarray
module With_mutex = Capsule.Sync.With_mutex

type raw = float#

let shards = Sweep.shards
let batch = Mitm.batch
let[@inline always] hash k = Sweep.hash k
let[@inline always] shard_of hv = Sweep.shard_of hv
let[@inline always] of_raw f = Sweep.of_raw f
let[@inline always] uget a i = Sweep.uget a i
let[@inline always] uset a i v = Sweep.uset a i v
let ucreate n = Sweep.ucreate n
let[@inline always] sget buf i = Mitm.sget buf i
let[@inline always] sset buf i v = Mitm.sset buf i v


(* ---- Sorted runs on disk ---- *)

(* The readers and writers keep their mutable state in unboxed [float#] cells, not in mutable
   record fields: on arm64 every mutable word store carries a barrier (see [Sweep]), and the
   state changes for every record. A record is decoded from the byte buffer by pure
   recursive functions returning unboxed tuples. *)

(* A streaming reader of a sorted varint run: the byte range [off, off + len) of a file. [fd]
   is the calling worker's own descriptor of that file (it is moved with [lseek]), [rbuf] its
   read buffer. State cells: position, limit, current key, high limb, low limb, live, file
   offset of the next read, bytes of the range left to read. *)
type reader =
  { fd : Unix.file_descr
  ; rbuf : Bytes.t
  ; st : raw array
  }

let st_pos = 0
let st_lim = 1
let st_key = 2
let st_hi = 3
let st_lo = 4
let st_live = 5
let st_off = 6
let st_rem = 7

(* The longest record: a 9-byte key difference and an 18-byte count. *)
let max_record = 32
let[@inline always] live r = uget r.st st_live <> 0
let[@inline always] key r = uget r.st st_key
let[@inline always] chi r = uget r.st st_hi
let[@inline always] clo r = uget r.st st_lo
let corrupt () = failwith "Store: run ends inside a record"

(* States are ordered as unsigned 63-bit numbers: a [Back] key with [h >= 16] is a negative
   OCaml int. [bias] maps that order to the signed one; the key [-1] (all bits set) cannot
   occur, so [bias (-1) = max_int] serves as the end marker of merges. *)
let[@inline always] bias k = k lxor min_int
let[@inline always] byte buf p lim = if p < lim then Char.code (Bytes.unsafe_get buf p) else corrupt ()

(* A varint of up to 63 bits at [p] (key differences wrap modulo 2^63): #(value, next
   position). *)
let rec dec_small buf p lim v shift =
  let c = byte buf p lim in
  let v = v lor ((c land 0x7f) lsl shift) in
  if c < 0x80 then #(v, p + 1) else dec_small buf (p + 1) lim v (shift + 7)
;;

(* A two-limb varint at [p]: #(hi, lo, next position). *)
let rec dec_count buf p lim hi lo shift =
  let c = byte buf p lim in
  let b = c land 0x7f in
  let #(hi, lo) =
    if shift + 7 <= Limb.bits
    then #(hi, lo lor (b lsl shift))
    else if shift >= Limb.bits
    then #(hi lor (b lsl (shift - Limb.bits)), lo)
    else #(hi lor (b lsr (Limb.bits - shift)), lo lor ((b lsl shift) land Limb.mask))
  in
  if c < 0x80 then #(hi, lo, p + 1) else dec_count buf (p + 1) lim hi lo (shift + 7)
;;

(* Read [len] bytes at file offset [off] into [buf] at [pos]. *)
let pread fd off buf pos len =
  ignore (Unix.lseek fd off SEEK_SET : int);
  let rec go pos len =
    if len > 0
    then (
      let got = Unix.read fd buf pos len in
      if got = 0 then failwith "Store: file shorter than its index";
      go (pos + got) (len - got))
  in
  go pos len
;;

(* Write the first [len] bytes of [s] at file offset [off]. *)
let pwrite fd off s len =
  ignore (Unix.lseek fd off SEEK_SET : int);
  ignore (Unix.write_substring fd s 0 len : int)
;;

(* Move the unread bytes to the front and fill the rest of the buffer from the range. *)
let refill r =
  let pos = uget r.st st_pos
  and lim = uget r.st st_lim in
  let rest = lim - pos in
  Bytes.blit r.rbuf pos r.rbuf 0 rest;
  let n = Int.min (Bytes.length r.rbuf - rest) (uget r.st st_rem) in
  let off = uget r.st st_off in
  pread r.fd off r.rbuf rest n;
  uset r.st st_off (off + n);
  uset r.st st_rem (uget r.st st_rem - n);
  uset r.st st_pos 0;
  uset r.st st_lim (rest + n)
;;

let advance r =
  if uget r.st st_lim - uget r.st st_pos < max_record && uget r.st st_rem > 0 then refill r;
  let pos = uget r.st st_pos
  and lim = uget r.st st_lim in
  if pos = lim
  then uset r.st st_live 0
  else (
    let #(d, p) = dec_small r.rbuf pos lim 0 0 in
    let #(hi, lo, p) = dec_count r.rbuf p lim 0 0 0 in
    uset r.st st_pos p;
    uset r.st st_key (uget r.st st_key + d);
    uset r.st st_hi hi;
    uset r.st st_lo lo)
;;

let open_range fd rbuf off len =
  let r = { fd; rbuf; st = ucreate 8 } in
  uset r.st st_live 1;
  uset r.st st_off off;
  uset r.st st_rem len;
  advance r;
  r
;;

(* A growable output buffer, one per worker, reused for every run it writes (a fresh buffer
   and a copy per shard would be garbage the size of the layer). *)
type obuf = { mutable ob : Bytes.t }

(* A streaming writer of a sorted varint run into the caller's (reused) byte buffer [wb],
   flushed into the front of the caller's [out]. State cells: position, previous key, records,
   bytes. *)
type writer =
  { out : obuf
  ; wb : Bytes.t
  ; ws : raw array
  }

let write_buffer_size = 1 lsl 16
let create_writer wb out = { out; wb; ws = ucreate 4 }

let[@inline always] put wb p c = Bytes.unsafe_set wb p (Char.unsafe_chr c)

let rec put_small wb p v =
  if v land lnot 0x7f = 0
  then (
    put wb p v;
    p + 1)
  else (
    put wb p (v land 0x7f lor 0x80);
    put_small wb (p + 1) (v lsr 7))
;;

(* The two-limb value hi 2^62 + lo, 7 bits per byte, low bits first. *)
let rec put_count wb p hi lo =
  if hi = 0
  then put_small wb p lo
  else (
    put wb p (lo land 0x7f lor 0x80);
    put_count wb (p + 1) (hi lsr 7) ((lo lsr 7) lor ((hi land 0x7f) lsl (Limb.bits - 7))))
;;

let flush_writer w =
  let n = uget w.ws 0 in
  let have = uget w.ws 3 in
  if have + n > Bytes.length w.out.ob
  then (
    let b = Bytes.create (Int.max (have + n) (2 * Bytes.length w.out.ob)) in
    Bytes.blit w.out.ob 0 b 0 have;
    w.out.ob <- b);
  Bytes.blit w.wb 0 w.out.ob have n;
  uset w.ws 3 (uget w.ws 3 + n);
  uset w.ws 0 0
;;

let push_record w k hi lo =
  let p = put_small w.wb (uget w.ws 0) (k - uget w.ws 1) in
  let p = put_count w.wb p hi lo in
  uset w.ws 0 p;
  uset w.ws 1 k;
  uset w.ws 2 (uget w.ws 2 + 1);
  if p > Bytes.length w.wb - max_record then flush_writer w
;;

(* Flush; (records, bytes). The run is the first [bytes] bytes of [w.out.ob]. *)
let finish_writer w =
  flush_writer w;
  uget w.ws 2, uget w.ws 3
;;

(* ---- Sorting a table ---- *)

(* The entries of a table sorted by key, as (key + 1, hi, lo) triples in a flat array, and
   their number; the table must not be used afterwards. The entries are compacted to the
   front of the table's own cells (counting the digits on the way), then sorted by an LSD
   radix sort with 11-bit digits, skipping the digits that all keys share. A comparison sort
   was 2.5x slower here (its branches on random keys mispredict half the time); it is used
   only for small tables. *)
let radix_bits = 11
let radix = 1 lsl radix_bits
let passes = 6 (* 66 bits cover the 63-bit keys, in unsigned order *)

(* Quicksort of the first [n] triples of [cells] by key, for small tables (a radix sort's
   counters would cost more than the data). *)
let quicksort cells n =
  let[@inline always] key e = bias (uget cells (3 * e)) in
  let[@inline always] swap a b =
    let k = RA.unsafe_get cells (3 * a)
    and h = RA.unsafe_get cells ((3 * a) + 1)
    and l = RA.unsafe_get cells ((3 * a) + 2) in
    RA.unsafe_set cells (3 * a) (RA.unsafe_get cells (3 * b));
    RA.unsafe_set cells ((3 * a) + 1) (RA.unsafe_get cells ((3 * b) + 1));
    RA.unsafe_set cells ((3 * a) + 2) (RA.unsafe_get cells ((3 * b) + 2));
    RA.unsafe_set cells (3 * b) k;
    RA.unsafe_set cells ((3 * b) + 1) h;
    RA.unsafe_set cells ((3 * b) + 2) l
  in
  let rec qsort lo hi =
    if hi - lo < 16
    then
      for i = lo + 1 to hi do
        let j = ref i in
        while !j > lo && key (!j - 1) > key !j do
          swap (!j - 1) !j;
          decr j
        done
      done
    else (
      let mid = lo + ((hi - lo) / 2) in
      if key mid < key lo then swap mid lo;
      if key hi < key lo then swap hi lo;
      if key hi < key mid then swap hi mid;
      let pivot = key mid in
      let i = ref lo
      and j = ref hi in
      while !i <= !j do
        while key !i < pivot do
          incr i
        done;
        while key !j > pivot do
          decr j
        done;
        if !i <= !j
        then (
          swap !i !j;
          incr i;
          decr j)
      done;
      if !j - lo < hi - !i
      then (
        qsort lo !j;
        qsort !i hi)
      else (
        qsort !i hi;
        qsort lo !j))
  in
  qsort 0 (n - 1)
;;

let small_sort = 1024

(* A growable buffer of (key, hi, lo) triples, one per worker, reused for every shard. *)
type vec =
  { mutable v : raw array
  ; mutable vn : int
  }

(* Sort the [n] triples at the front of [cells] by key (unsigned); the sorted triples are at
   the front of the returned array, [cells] or the worker's scratch [sc] (grown as needed: a
   fresh one per shard would be garbage the size of the layer). *)
let sort_front (sc : vec) cells n =
  if n <= small_sort
  then (
    quicksort cells n;
    cells)
  else (
    let cnt = ucreate (passes * radix) in
    for i = 0 to n - 1 do
      let k1 = uget cells (3 * i) in
      for p = 0 to passes - 1 do
        let c = (p * radix) + ((k1 lsr (p * radix_bits)) land (radix - 1)) in
        uset cnt c (uget cnt c + 1)
      done
    done;
    let src = ref cells
    and dst =
      ref
        (if RA.length sc.v >= 3 * n
         then sc.v
         else (
           let b = ucreate (Int.max (3 * n) (3 * RA.length sc.v / 2)) in
           sc.v <- b;
           b))
    in
    for p = 0 to passes - 1 do
      let base = p * radix
      and shift = p * radix_bits in
      let first = (uget !src 0 lsr shift) land (radix - 1) in
      if uget cnt (base + first) <> n
      then (
        (* counts to start offsets *)
        let sum = ref 0 in
        for d = 0 to radix - 1 do
          let c = uget cnt (base + d) in
          uset cnt (base + d) !sum;
          sum := !sum + c
        done;
        let s = !src
        and o = !dst in
        for i = 0 to n - 1 do
          let k1 = uget s (3 * i) in
          let c = base + ((k1 lsr shift) land (radix - 1)) in
          let pos = uget cnt c in
          uset cnt c (pos + 1);
          RA.unsafe_set o (3 * pos) (RA.unsafe_get s (3 * i));
          RA.unsafe_set o ((3 * pos) + 1) (RA.unsafe_get s ((3 * i) + 1));
          RA.unsafe_set o ((3 * pos) + 2) (RA.unsafe_get s ((3 * i) + 2))
        done;
        src := o;
        dst := s)
    done;
    !src)
;;

(* The entries of a table sorted by key, compacted to the front of its own cells first; the
   table must not be used afterwards. *)
let sorted_with (sc : vec) (t : Mitm.Table.t) =
  let cells = t.cells in
  let j = ref 0 in
  for i = 0 to Mitm.Table.slots cells - 1 do
    if uget cells (3 * i) <> 0
    then (
      if !j < i
      then (
        RA.unsafe_set cells (3 * !j) (RA.unsafe_get cells (3 * i));
        RA.unsafe_set cells ((3 * !j) + 1) (RA.unsafe_get cells ((3 * i) + 1));
        RA.unsafe_set cells ((3 * !j) + 2) (RA.unsafe_get cells ((3 * i) + 2)));
      incr j)
  done;
  sort_front sc cells !j, !j
;;

let sorted t = sorted_with { v = ucreate 0; vn = 0 } t

(* Write [n] sorted triples as a run into [out]; (records, bytes). *)
let write_sorted wb out cells n =
  let w = create_writer wb out in
  for i = 0 to n - 1 do
    push_record w (uget cells (3 * i) - 1) (uget cells ((3 * i) + 1)) (uget cells ((3 * i) + 2))
  done;
  finish_writer w
;;

(* ---- Files ---- *)

let rec mkdir_p dir =
  if not (Sys.file_exists dir)
  then (
    mkdir_p (Filename.dirname dir);
    try Sys.mkdir dir 0o755 with
    | Sys_error _ when Sys.file_exists dir -> ())
;;

let rec remove_all path =
  if Sys.file_exists path
  then
    if Sys.is_directory path
    then (
      Array.iter (fun f -> remove_all (Filename.concat path f)) (Sys.readdir path);
      Sys.rmdir path)
    else Sys.remove path
;;

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s
;;

let write_atomically path text =
  let tmp = path ^ ".tmp" in
  let oc = open_out_bin tmp in
  output_string oc text;
  close_out oc;
  Sys.rename tmp path
;;

(* Free bytes on the filesystem holding [path] (from [df]; [max_int] if it cannot tell). *)
let free_bytes path =
  try
    let ic = Unix.open_process_args_in "df" [| "df"; "-Pk"; path |] in
    let _header = input_line ic in
    let line = input_line ic in
    ignore (Unix.close_process_in ic : Unix.process_status);
    match List.filter (( <> ) "") (String.split_on_char ' ' line) with
    | _ :: _ :: _ :: avail :: _ -> 1024 * int_of_string avail
    | _ -> max_int
  with
  | _ -> max_int
;;

(* ---- Layers ---- *)

let seg_dat dir s = Filename.concat dir (Printf.sprintf "seg%d.dat" s)
let seg_idx dir s = Filename.concat dir (Printf.sprintf "seg%d.idx" s)

(* One segment: its data file and the (offset, length) of every shard, flattened. *)
type segment =
  { dat : string
  ; index : int iarray
  }

(* A layer on disk: its existing segments (a missing one is empty). *)
type layer =
  { dir : string
  ; segs : segment iarray
  }

let read_index path =
  let s = read_file path in
  if String.length s <> 16 * shards then failwith ("Store: bad segment index " ^ path);
  Iarray.init (2 * shards) ~f:(fun i -> Int64.to_int (String.get_int64_le s (8 * i)))
;;

let open_layer dir segments =
  { dir
  ; segs =
      Iarray.of_list
        (List.filter_map
           (fun s ->
             if Sys.file_exists (seg_idx dir s)
             then Some { dat = seg_dat dir s; index = read_index (seg_idx dir s) }
             else None)
           (List.init segments Fun.id))
  }
;;

(* A worker's own descriptors of the layer's data files. *)
let open_fds (l : layer) =
  Array.init (Iarray.length l.segs) (fun i ->
    Unix.openfile (Iarray.get l.segs i).dat [ O_RDONLY ] 0)
;;

let close_fds fds = Array.iter Unix.close fds

let remove_segment dir s =
  (try Sys.remove (seg_idx dir s) with Sys_error _ -> ());
  try Sys.remove (seg_dat dir s) with Sys_error _ -> ()
;;

(* Flush the data, then publish the index: a segment exists once its index does. *)
let publish fd dir s idx =
  Unix.fsync fd;
  Unix.close fd;
  let b = Bytes.create (16 * shards) in
  Array.iteri (fun i v -> Bytes.set_int64_le b (8 * i) (Int64.of_int v)) idx;
  write_atomically (seg_idx dir s) (Bytes.to_string b)
;;

let create_dat dir s =
  mkdir_p dir;
  remove_segment dir s;
  Unix.openfile (seg_dat dir s) [ O_WRONLY; O_CREAT; O_TRUNC ] 0o644
;;

(* Write the given (state, count) entries, counts below 2^62, as segment [seg] of [dir]. *)
let write_states dir seg entries =
  let fd = create_dat dir seg in
  let idx = Array.make (2 * shards) 0 in
  let out = { ob = Bytes.create 256 } in
  let pos = ref 0 in
  for d = 0 to shards - 1 do
    let mine =
      List.sort
        (fun (a, _) (b, _) -> compare (bias a) (bias b))
        (List.filter (fun (k, _) -> shard_of (hash k) = d) entries)
    in
    if mine <> []
    then (
      let w = create_writer (Bytes.create 256) out in
      List.iter (fun (k, c) -> push_record w k 0 c) mine;
      let _, len = finish_writer w in
      let s = Bytes.sub_string out.ob 0 len in
      pwrite fd !pos s (String.length s);
      idx.(2 * d) <- !pos;
      idx.((2 * d) + 1) <- String.length s;
      pos := !pos + String.length s)
  done;
  publish fd dir seg idx
;;

(* A file being appended to by several workers, under a lock: its descriptor, its length, and
   (for a segment) the range of every shard. *)
type appender =
  { afd : Unix.file_descr
  ; mutable apos : int
  ; aidx : int array
  }

(* Flush a file being appended to every this many bytes, so that the dirty pages waiting for
   a slow volume stay bounded (as in rust/src/store.rs: a hard hang of Morrobay, on an HFS+
   SoftRAID RAID 5 in a Thunderbolt enclosure, probably began with writes piling up in memory
   behind a volume that had stopped keeping up). *)
let sync_bytes = 256 lsl 20

(* Append the first [len] bytes of [s] under the lock; its offset. Records it as shard [d]'s range if [d >= 0]. *)
let append (par @ local) (a : appender With_mutex.t) (d : int) (s : string) (len : int) =
  With_mutex.with_lock (Parallel.sync par) a ~f:(fun _ a ->
    let off = a.apos in
    pwrite a.afd off s len;
    a.apos <- off + len;
    if a.apos / sync_bytes <> off / sync_bytes then Unix.fsync a.afd;
    if d >= 0
    then (
      a.aidx.(2 * d) <- off;
      a.aidx.((2 * d) + 1) <- len);
    off)
  [@nontail]
;;

(* ---- One step: build a segment from a source layer ---- *)

(* A target shard while a step runs: the capped table and the (offset, length) of the runs it
   has spilled. *)
type acc =
  { mutable tbl : Mitm.Table.t
  ; mutable runs : (int * int) list
  }

type tshard = acc With_mutex.t

(* What a step applies to each state: the bridge steps, or the backward steps keeping
   [lower < depth <= upper]. *)
type job =
  { backward : bool
  ; lower : int
  ; upper : int
  }

type sink =
  { tables : tshard iarray
  ; spill : appender With_mutex.t
  ; cap : int
  ; spilled : int Atomic.t
  }

(* The slots of a table that will hold [cap] states: load 2/3 when it spills (linear probing
   slows down sharply near the maximum load 0.8). *)
let full_slots cap = (3 * cap / 2) + 64

(* A worker's buffers for spilling: the run's bytes, and two arrays for the copied-out
   entries and the radix sort. *)
type wctx =
  { wb : Bytes.t
  ; out : obuf
  ; sa : vec
  ; sb : vec
  }

let make_wctx () =
  { wb = Bytes.create write_buffer_size
  ; out = { ob = Bytes.create 0 }
  ; sa = { v = ucreate 0; vn = 0 }
  ; sb = { v = ucreate 0; vn = 0 }
  }
;;

(* Spill a full table: under its lock, only copy its entries out and empty it (reusing its
   cells: all shards spill at about the same time, and a fresh table each would double the
   memory until the next major collection). The sort and the encoding run outside the lock,
   in the worker's own buffers, so that other workers are not kept waiting for this shard;
   then the run is appended to the spill file and recorded. *)
let[@inline never] insert_batch (par @ local) (wk : wctx) (sink : sink) d b n =
  let cap = sink.cap in
  let tshard = Iarray.get sink.tables d in
  let full =
    With_mutex.with_lock (Parallel.sync par) tshard ~f:(fun _ a ->
      Mitm.Table.add_batch a.tbl b n;
      if a.tbl.len > cap
      then (
        let t = a.tbl in
        let cells = t.cells in
        let copy = ucreate (3 * t.len) in
        let j = ref 0 in
        for i = 0 to Mitm.Table.slots cells - 1 do
          if uget cells (3 * i) <> 0
          then (
            RA.unsafe_set copy (3 * !j) (RA.unsafe_get cells (3 * i));
            RA.unsafe_set copy ((3 * !j) + 1) (RA.unsafe_get cells ((3 * i) + 1));
            RA.unsafe_set copy ((3 * !j) + 2) (RA.unsafe_get cells ((3 * i) + 2));
            uset cells (3 * i) 0;
            incr j)
        done;
        t.len <- 0;
        (* never mutated again: frozen to leave the capsule *)
        Some (Iarray.unsafe_of_array__promise_no_mutation copy))
      else None)
  in
  match full with
  | None -> ()
  | Some (fz : raw iarray) ->
    let m = Iarray.length fz / 3 in
    if RA.length wk.sa.v < 3 * m then wk.sa.v <- ucreate (Int.max (3 * m) (3 * RA.length wk.sa.v / 2));
    let a = wk.sa.v in
    for i = 0 to (3 * m) - 1 do
      RA.unsafe_set a i (Iarray.unsafe_get fz i)
    done;
    let cells = sort_front wk.sb a m in
    let _, len = write_sorted wk.wb wk.out cells m in
    ignore (Atomic.fetch_and_add sink.spilled m : int);
    let off = append par sink.spill (-1) (Bytes.unsafe_to_string wk.out.ob) len in
    With_mutex.with_lock (Parallel.sync par) tshard ~f:(fun _ a ->
      a.runs <- (off, len) :: a.runs)
    [@nontail]
;;

let[@inline never] flush (par @ local) (buf : raw S.t @ local) wk sink d =
  let n = sget buf (Mitm.off_fill + d) in
  insert_batch par wk sink d (Mitm.batch_copy buf d n) n;
  sset buf (Mitm.off_fill + d) 0
;;

let[@inline always] push (par @ local) (buf : raw S.t @ local) wk sink k2 ch cl =
  let d = Mitm.append buf k2 ch cl in
  if d >= 0 then flush par buf wk sink d
;;

let read_buffer_size = 1 lsl 16

let step_worker (par @ local) (buf : raw S.t @ local) ~(src : layer) ~sink ~claim ~(job : job) =
  let rbuf = Bytes.create read_buffer_size in
  let wk = make_wctx () in
  let fds = open_fds src in
  let backward = job.backward
  and lower = job.lower
  and upper = job.upper in
  let rec claim_loop (par @ local) =
    let s = Atomic.fetch_and_add claim 1 in
    if s < shards
    then (
      for i = 0 to Iarray.length src.segs - 1 do
        let ix = (Iarray.get src.segs i).index in
        let len = Iarray.get ix ((2 * s) + 1) in
        if len > 0
        then (
          let r = open_range fds.(i) rbuf (Iarray.get ix (2 * s)) len in
          while live r do
            let k = key r
            and ch = chi r
            and cl = clo r in
            if backward
            then Back.predecessors ~lower ~bound:upper k (fun t -> push par buf wk sink t ch cl)
            else Back.successors k (fun t -> push par buf wk sink t ch cl);
            advance r
          done)
      done;
      claim_loop par)
  in
  claim_loop par;
  for d = 0 to shards - 1 do
    if sget buf (Mitm.off_fill + d) > 0 then flush par buf wk sink d
  done;
  close_fds fds
;;

(* Merge a sorted remainder and sorted runs, adding the counts of equal states, into [out].
   Returns (distinct states, bytes). *)
let merge_into wb out (cells, n) readers =
  let w = create_writer wb out in
  let readers = Array.of_list readers in
  let nr = Array.length readers in
  let i = ref 0 in
  let continue = ref true in
  while !continue do
    let m = ref (if !i < n then bias (uget cells (3 * !i) - 1) else max_int) in
    for j = 0 to nr - 1 do
      let r = readers.(j) in
      if live r && bias (key r) < !m then m := bias (key r)
    done;
    if !m = max_int
    then continue := false
    else (
      let k = bias !m in
      let ch = ref 0
      and cl = ref 0 in
      if !i < n && uget cells (3 * !i) - 1 = k
      then (
        ch := uget cells ((3 * !i) + 1);
        cl := uget cells ((3 * !i) + 2);
        incr i);
      for j = 0 to nr - 1 do
        let r = readers.(j) in
        while live r && key r = k do
          let #(h, l) = Limb.add !ch !cl (chi r) (clo r) in
          ch := h;
          cl := l;
          advance r
        done
      done;
      push_record w k !ch !cl)
  done;
  finish_writer w
;;

type stats =
  { states : int
  ; bytes : int
  ; spilled_records : int
  }

(* Build segment [seg] of the layer in [dst] from every state of [src]. [want]: the initial
   slots of each target table (predicted from the last layer sizes, so that tables rarely
   rehash); a table that has spilled is emptied and reused. [after_read] runs once the
   source has been read in full, before compaction (a caller that no longer needs the source
   can delete it there, so that source and result are never both whole on disk). *)
let step
  (par @ local)
  (ctx : Mitm.ctx)
  ~(src : layer)
  ~dst
  ~seg
  ~cap
  ~want
  ~(job : job)
  ~(after_read : unit -> unit)
  =
  let tmp = Filename.concat dst "tmp" in
  remove_all tmp;
  mkdir_p tmp;
  let spill_path = Filename.concat tmp "spill" in
  let sfd = Unix.openfile spill_path [ O_WRONLY; O_CREAT; O_TRUNC ] 0o644 in
  let sink =
    { tables =
        Iarray.init shards ~f:(fun _ ->
          With_mutex.create (fun () -> { tbl = Mitm.Table.create want; runs = [] }))
    ; spill = With_mutex.create (fun () -> { afd = sfd; apos = 0; aidx = [||] })
    ; cap
    ; spilled = Atomic.make 0
    }
  in
  let claim = Atomic.make 0 in
  (S.fori [@kind float64]) par ~pivots:ctx.pivots ((S.slice [@kind float64]) ctx.scratch)
    ~f:(fun par _ buf -> step_worker par buf ~src ~sink ~claim ~job);
  after_read ();
  Unix.close (With_mutex.destroy (Parallel.sync par) sink.spill).afd;
  (* Compact: merge each shard's runs and remainder and append it to the segment. *)
  let dfd = create_dat dst seg in
  let writer =
    With_mutex.create (fun () -> { afd = dfd; apos = 0; aidx = Array.make (2 * shards) 0 })
  in
  let states = Atomic.make 0
  and claim = Atomic.make 0 in
  let tables = sink.tables in
  Parallel.for_ par ~start:0 ~stop:ctx.threads ~f:(fun par _ ->
    let wb = Bytes.create write_buffer_size in
    let out = { ob = Bytes.create (1 lsl 20) } in
    let scratch = { v = ucreate 0; vn = 0 } in
    let rfd = Unix.openfile spill_path [ O_RDONLY ] 0 in
    let rec loop (par @ local) =
      let d = Atomic.fetch_and_add claim 1 in
      if d < shards
      then (
        let a = With_mutex.destroy (Parallel.sync par) (Iarray.get tables d) in
        let rest = sorted_with scratch a.tbl in
        a.tbl <- Mitm.Table.create 0;
        let _, nrest = rest in
        if nrest > 0 || a.runs <> []
        then (
          let readers =
            List.rev_map
              (fun (off, len) -> open_range rfd (Bytes.create read_buffer_size) off len)
              a.runs
          in
          let n, len = merge_into wb out rest readers in
          ignore (Atomic.fetch_and_add states n : int);
          ignore (append par writer d (Bytes.unsafe_to_string out.ob) len : int));
        loop par)
    in
    loop par;
    Unix.close rfd);
  let w = With_mutex.destroy (Parallel.sync par) writer in
  publish w.afd dst seg w.aidx;
  remove_all tmp;
  { states = Atomic.get states; bytes = w.apos; spilled_records = Atomic.get sink.spilled }
;;

(* ---- Dot products ---- *)

(* Read shard [d] of [l] (all segments; [l] has one, sorted) into [vec]. *)
let read_all rbuf fds vec (l : layer) d =
  let n = ref 0 in
  for i = 0 to Iarray.length l.segs - 1 do
    let ix = (Iarray.get l.segs i).index in
    let len = Iarray.get ix ((2 * d) + 1) in
    if len > 0
    then (
      let r = open_range fds.(i) rbuf (Iarray.get ix (2 * d)) len in
      while live r do
        if 3 * !n = RA.length vec.v
        then (
          let b = ucreate (2 * RA.length vec.v) in
          for i = 0 to (3 * !n) - 1 do
            RA.unsafe_set b i (RA.unsafe_get vec.v i)
          done;
          vec.v <- b);
        let v = vec.v in
        uset v (3 * !n) (key r);
        uset v ((3 * !n) + 1) (chi r);
        uset v ((3 * !n) + 2) (clo r);
        incr n;
        advance r
      done)
  done;
  vec.vn <- !n
;;

(* sum_s a(s) b(s), by a merge-join of each shard: [a] (one segment, sorted) is loaded, and
   each segment of [b] (sorted, disjoint) is streamed against it. Exact. *)
let dot (par @ local) (ctx : Mitm.ctx) (a : layer) (b : layer) =
  let claim = Atomic.make 0 in
  (S.fori [@kind float64]) par ~pivots:ctx.pivots ((S.slice [@kind float64]) ctx.scratch)
    ~f:(fun par _ buf ->
      let off = Mitm.off_res in
      sset buf off 0;
      sset buf (off + 1) 0;
      let rbuf = Bytes.create read_buffer_size in
      let afds = open_fds a
      and bfds = open_fds b in
      let vec = { v = ucreate 3072; vn = 0 } in
      let rec loop (par @ local) =
        let d = Atomic.fetch_and_add claim 1 in
        if d < shards
        then (
          read_all rbuf afds vec a d;
          let fv = vec.v
          and n = vec.vn in
          if n > 0
          then
            for i = 0 to Iarray.length b.segs - 1 do
              let ix = (Iarray.get b.segs i).index in
              let len = Iarray.get ix ((2 * d) + 1) in
              if len > 0
              then (
                let r = open_range bfds.(i) rbuf (Iarray.get ix (2 * d)) len in
                let j = ref 0 in
                while live r do
                  let k = key r in
                  let bk = bias k in
                  while !j < n && bias (uget fv (3 * !j)) < bk do
                    incr j
                  done;
                  if !j < n && uget fv (3 * !j) = k
                  then
                    Mitm.accumulate
                      buf
                      off
                      (uget fv ((3 * !j) + 1))
                      (uget fv ((3 * !j) + 2))
                      (chi r)
                      (clo r);
                  advance r
                done)
            done;
          loop par)
      in
      loop par;
      close_fds afds;
      close_fds bfds);
  let all = (S.slice [@kind float64]) ctx.scratch in
  let h = ref 0
  and l = ref 0 in
  for w = 0 to ctx.threads - 1 do
    let o = (w * Mitm.region) + Mitm.off_res in
    let #(h2, l2) = Limb.add !h !l (sget all o) (sget all (o + 1)) in
    h := h2;
    l := l2
  done;
  Limb.to_string !h !l
;;

(* ---- Manifest and values ---- *)

type manifest =
  { mutable horizons : int list (* increasing *)
  ; mutable kmax : int
  ; rmax : int array
  ; mutable partial : (int * int array) option
  ; mutable discarded : bool
    (* backward layers were deleted once used, so the store cannot be extended *)
  }

let format_line = "format meanders-ox-mitm-2"
let lines s = List.filter (fun l -> l <> "") (String.split_on_char '\n' s)

let load_manifest root =
  let m =
    { horizons = []; kmax = 0; rmax = [| 0; 0 |]; partial = None; discarded = false }
  in
  let path = Filename.concat root "manifest" in
  if Sys.file_exists path
  then
    List.iter
      (fun line ->
        match String.split_on_char ' ' line with
        | [ "format"; f ] ->
          if "format " ^ f <> format_line
          then failwith ("Store: not a meanders_ox store of this layout (" ^ line ^ ")")
        | [ "horizons"; v ] ->
          m.horizons
          <- List.map int_of_string (List.filter (( <> ) "") (String.split_on_char ',' v))
        | [ "kmax"; v ] -> m.kmax <- int_of_string v
        | [ "rmax0"; v ] -> m.rmax.(0) <- int_of_string v
        | [ "rmax1"; v ] -> m.rmax.(1) <- int_of_string v
        | [ "discarded"; v ] -> m.discarded <- v = "1"
        | [ "partial"; v ] ->
          (match List.map int_of_string (String.split_on_char ',' v) with
           | [ b; d0; d1 ] -> m.partial <- Some (b, [| d0; d1 |])
           | _ -> failwith "Store: bad partial line")
        | _ -> ())
      (lines (read_file path));
  m
;;

let save_manifest root m =
  let b = Buffer.create 128 in
  Buffer.add_string b (format_line ^ "\n");
  Printf.bprintf
    b
    "horizons %s\nkmax %d\nrmax0 %d\nrmax1 %d\n"
    (String.concat "," (List.map string_of_int m.horizons))
    m.kmax
    m.rmax.(0)
    m.rmax.(1);
  (match m.partial with
   | Some (t, d) -> Printf.bprintf b "partial %d,%d,%d\n" t d.(0) d.(1)
   | None -> ());
  if m.discarded then Buffer.add_string b "discarded 1\n";
  write_atomically (Filename.concat root "manifest") (Buffer.contents b)
;;

(* values: n -> (count, check), counts as decimal strings. *)
let load_values root =
  let path = Filename.concat root "values" in
  let v = Hashtbl.create 64 in
  if Sys.file_exists path
  then
    List.iter
      (fun line ->
        if line.[0] <> '#'
        then (
          match String.split_on_char '\t' line with
          | [ n; c; k ] ->
            Hashtbl.replace v (int_of_string n) (c, if k = "-" then None else Some k)
          | _ -> failwith "Store: bad values line"))
      (lines (read_file path));
  v
;;

let save_values root v =
  let b = Buffer.create 4096 in
  Buffer.add_string b "# n\tcount\tcheck (the same count through a second split)\n";
  let ns = List.sort compare (Hashtbl.fold (fun n _ acc -> n :: acc) v []) in
  List.iter
    (fun n ->
      let c, k = Hashtbl.find v n in
      Printf.bprintf b "%d\t%s\t%s\n" n c (Option.value k ~default:"-"))
    ns;
  write_atomically (Filename.concat root "values") (Buffer.contents b)
;;

let fdir root k = Filename.concat (Filename.concat root "F") (Printf.sprintf "%03d" k)

let gdir root p r =
  Filename.concat (Filename.concat root (Printf.sprintf "G%d" p)) (Printf.sprintf "%03d" r)
;;

let finishers p = List.map (fun k -> k, 1) (Mitm.finishers p)

(* How [extend] ended. *)
type outcome =
  | Complete
  | Paused

(* Whether to stop at this layer boundary: a file [PAUSE] in the store, or less free disk than
   [min_free] bytes. *)
let pause_requested root ~min_free ~out =
  Sys.file_exists (Filename.concat root "PAUSE")
  || (min_free > 0
      &&
      let free = free_bytes root in
      free < min_free
      && (out (Printf.sprintf "low disk: %.1f GB free" (Float.of_int free /. 1e9));
          true))
;;

(* Extend the store at [root] to horizon [target], computing every new A(n). Stops early, with
   every finished layer saved, if a pause is requested; running it again with the same target
   resumes (the layer in progress is redone). [discard]: delete each backward layer as soon as
   the next one has read it: far less disk, but the store cannot be extended later, and a
   crash (not a pause) inside a step means starting over, since that step's source is gone. *)
let extend
  (par @ local)
  ?(discard = false)
  ?(min_free = 0)
  ~root
  ~target
  ~threads
  ~cap
  ~(out : string -> unit)
  ()
  =
  mkdir_p root;
  let start = Unix.gettimeofday () in
  let elapsed () = Unix.gettimeofday () -. start in
  let m = load_manifest root in
  let old = match List.rev m.horizons with b :: _ -> Some b | [] -> None in
  let resuming = match m.partial with Some (b, _) -> b = target | None -> false in
  match old with
  | Some b when target <= b ->
    out (Printf.sprintf "store already has horizon %d" b);
    Complete
  | Some _ when m.discarded && not resuming ->
    out "this store discarded its backward layers and cannot be extended; build a new one";
    Complete
  | _ ->
    m.discarded <- m.discarded || discard;
    let ctx = Mitm.make_ctx threads in
    let seg = List.length m.horizons in
    let fin =
      match m.partial with
      | Some (b, d) when b = target -> Array.copy d
      | _ -> [| 0; 0 |]
    in
    m.partial <- Some (target, Array.copy fin);
    save_manifest root m;
    let values = load_values root in
    let paused what =
      out (Printf.sprintf "paused before %s at %.0f s" what (elapsed ()));
      Paused
    in
    (* Forward layers: universal, one segment each. *)
    let kmax = target - (target / 2) in
    if m.kmax = 0 && not (Sys.file_exists (seg_idx (fdir root 0) 0))
    then write_states (fdir root 0) 0 [ Back.init, 1 ];
    (* Initial table sizes, predicted from the recent layer sizes ([Sweep.predict_slots]). *)
    let predict hist =
      let w =
        match !hist with
        | s :: p :: p2 :: _ -> Sweep.predict_slots ~size:s ~prev:p ~prev2:p2
        | [ s; p ] -> Sweep.predict_slots ~size:s ~prev:p ~prev2:0
        | [ s ] -> Sweep.predict_slots ~size:s ~prev:0 ~prev2:0
        | [] -> 64
      in
      (* a little generous: the sizes of new segments vary more than whole layers do *)
      Int.max 64 (Int.min (5 * w / 4) (full_slots cap))
    in
    let fhist = ref [] in
    let rec forward () =
      if m.kmax >= kmax
      then Complete
      else if pause_requested root ~min_free ~out
      then paused (Printf.sprintf "F %d" (m.kmax + 1))
      else (
        let src = open_layer (fdir root m.kmax) 1 in
        let dst = fdir root (m.kmax + 1) in
        remove_all dst;
        let st =
          step
            par
            ctx
            ~src
            ~dst
            ~seg:0
            ~cap
            ~want:(predict fhist)
            ~job:{ backward = false; lower = -1; upper = 0 }
            ~after_read:ignore
        in
        fhist := st.states :: !fhist;
        m.kmax <- m.kmax + 1;
        save_manifest root m;
        out
          (Printf.sprintf
             "F %3d  states %13d  %10.2f GB  %8.0f s"
             m.kmax
             st.states
             (Float.of_int st.bytes /. 1e9)
             (elapsed ()));
        forward () [@nontail])
    in
    let f k = open_layer (fdir root k) 1 in
    let newer n = match old with None -> true | Some b -> n > b in
    let backward p =
      let rmax_new = (target / 2) + 1 in
      if seg = 0 && fin.(p) = 0 && not (Sys.file_exists (seg_idx (gdir root p 0) 0))
      then write_states (gdir root p 0) 0 (finishers p);
      let g r = open_layer (gdir root p r) (seg + 1) in
      let value_at r =
        let n = (2 * r) + p in
        if n <= target && newer n
        then (
          let c = dot par ctx (f (r + p)) (g r) in
          Hashtbl.replace values n (c, None);
          out (Printf.sprintf "A(%d) = %s" n c));
        if r + p >= 2 && n >= 2 && n - 2 <= target && newer (n - 2)
        then (
          let c = dot par ctx (f (r + p - 2)) (g r) in
          match Hashtbl.find_opt values (n - 2) with
          | Some (v, _) ->
            Hashtbl.replace values (n - 2) (v, Some c);
            let ok = if v = c then "agrees" else "DISAGREES" in
            out (Printf.sprintf "A(%d) second split %s: %s" (n - 2) ok c)
          | None -> ())
      in
      let ghist = ref [] in
      if fin.(p) = 0
      then (
        value_at 0;
        save_values root values);
      let rec layer r =
        if r > rmax_new
        then (
          m.rmax.(p) <- rmax_new;
          Complete)
        else if pause_requested root ~min_free ~out
        then paused (Printf.sprintf "G%d %d" p r)
        else (
          let lower =
            match old with
            | Some b when r <= m.rmax.(p) -> Int.max 0 (b - r)
            | _ -> -1
          in
          let upper = Int.max 0 (target - r) in
          let dst = gdir root p r in
          let src_dir = gdir root p (r - 1) in
          remove_segment dst seg;
          let st =
            step
              par
              ctx
              ~src:(g (r - 1))
              ~dst
              ~seg
              ~cap
              ~want:(predict ghist)
              ~job:{ backward = true; lower; upper }
              ~after_read:(fun () ->
                (* the source's values were taken when it was built *)
                if discard && r >= 2 then remove_all src_dir)
          in
          ghist := if st.states = 0 then [] else st.states :: !ghist;
          out
            (Printf.sprintf
               "G%d %3d  new states %13d  %10.2f GB  spilled %13d  %8.0f s"
               p
               r
               st.states
               (Float.of_int st.bytes /. 1e9)
               st.spilled_records
               (elapsed ()));
          value_at r;
          save_values root values;
          fin.(p) <- r;
          m.partial <- Some (target, Array.copy fin);
          save_manifest root m;
          if discard then remove_all src_dir;
          layer (r + 1) [@nontail])
      in
      layer (fin.(p) + 1) [@nontail]
    in
    (match forward () with
     | Paused -> Paused
     | Complete ->
       (match backward 0 with
        | Paused -> Paused
        | Complete -> backward 1 [@nontail]))
    |> (function
     | Paused -> Paused
     | Complete ->
       m.horizons <- m.horizons @ [ target ];
       m.partial <- None;
       save_manifest root m;
       out (Printf.sprintf "horizon %d complete in %.0f s" target (elapsed ()));
       Complete)
;;
