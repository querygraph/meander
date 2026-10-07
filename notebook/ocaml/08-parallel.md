## 8. All cores at once

OCaml 5 runs code in parallel on several *domains*, each an operating-system thread with its own
share of the runtime, all in one address space. The repository's Rust and OxCaml programs, and
the function below, share one algorithm:

* A layer is split into *shards* by a hash of the state, each shard its own table with its own
  lock.
* Workers take source shards one at a time from a shared counter. For every state they make the
  successors and send each to the shard its hash selects.
* A worker collects successors per target shard in a small buffer, and adds a full buffer to its
  shard under that shard's lock. Locks are taken rarely, and two workers block each other only
  when they flush to the same shard at the same moment.

**Domains, atomics and mutexes.** `Domain.spawn f` runs `f ()` on a new domain and returns a
handle; `Domain.join d` waits for it and returns its result.
`Domain.recommended_domain_count ()` is the number of cores. Plain mutable values shared between
domains are a *data race* if two domains touch them at once without synchronization. Two tools
prevent that. An `Atomic.t`, made by `Atomic.make v`, is a cell whose operations are indivisible:
`Atomic.fetch_and_add a 1` adds one and returns the old value, so every worker gets a different
shard number. A `Mutex.t`, made by `Mutex.create ()`, admits one domain at a time: `Mutex.protect m f` locks
`m`, runs `f`, and unlocks, even if `f` raises.

The shard comes from high bits of the hash, because the table inside a shard uses the low bits:
taking both from the same bits would crowd each shard's states into a few buckets. `lsr` shifts
right, and `land` is bitwise *and*. `Array.iteri` is `List.iteri` for arrays.

```ocaml
let shards = 64
let batch = 64
let shard_of s = (Key.hash s lsr 24) land (shards - 1)

let tm_count_parallel ?(domains = Domain.recommended_domain_count ()) m =
  let fresh () = Array.init shards (fun _ -> States.create 16) in
  let locks = Array.init shards (fun _ -> Mutex.create ()) in
  let layer = ref (fresh ()) in
  let start = { word = []; h = 0 } in
  States.replace !layer.(shard_of start) start 1;
  for x = 0 to m do
    let src = !layer and next = fresh () in
    let claim = Atomic.make 0 in
    let work () =
      let bufs = Array.make shards [] and sizes = Array.make shards 0 in
      let flush d =
        Mutex.protect locks.(d) (fun () -> List.iter (fun (s, c) -> add next.(d) s c) bufs.(d));
        bufs.(d) <- [];
        sizes.(d) <- 0
      in
      let rec loop () =
        let i = Atomic.fetch_and_add claim 1 in
        if i < shards then begin
          States.iter
            (fun s c ->
              successors m x s (fun s' ->
                  if viable m (x + 1) s' then begin
                    let d = shard_of s' in
                    bufs.(d) <- (s', c) :: bufs.(d);
                    sizes.(d) <- sizes.(d) + 1;
                    if sizes.(d) = batch then flush d
                  end))
            src.(i);
          loop ()
        end
      in
      loop ();
      Array.iteri (fun d b -> if b <> [] then flush d) bufs
    in
    let helpers = List.init (domains - 1) (fun _ -> Domain.spawn work) in
    work ();
    List.iter Domain.join helpers;
    layer := next
  done;
  Option.value (States.find_opt !layer.(shard_of final) final) ~default:0
```

The calling domain works too, so `domains - 1` helpers are spawned. Each worker's buffers are
its own, so only `claim`, the locks and the target tables are shared, and the tables are touched
only under their locks.

```ocaml
let () =
  List.iter
    (fun m ->
      let t0 = Unix.gettimeofday () in
      let a = tm_count m in
      let t1 = Unix.gettimeofday () in
      let b = tm_count_parallel m in
      let t2 = Unix.gettimeofday () in
      assert (a = b);
      Printf.printf "n = %d: %d   one domain %.1f s, %d domains %.1f s\n%!" m a (t1 -. t0)
        (Domain.recommended_domain_count ()) (t2 -. t1))
    [ 24; 28 ]
```

The notebook runs OCaml as bytecode in the toplevel, and its states are lists of variants, so
much of the time goes to allocation and garbage collection, which the domains share. The
compiled programs pack a state into one machine word instead.
