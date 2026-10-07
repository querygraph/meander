## 9. OxCaml

[OxCaml](https://oxcaml.org/) is Jane Street's branch of the OCaml compiler. It adds
features for writing fast, safe parallel code. The repository's `oxcaml/` program,
`meanders_ox`, runs the transfer matrix of Section 7 on all cores with the sharded sweep of
Section 8. It packs each state into one integer, so it handles hundreds of millions of states
per layer. This section explains the OxCaml features it uses. Its code is shown here as text,
because this notebook's kernel runs standard OCaml 5. Build and run it with:

```text
cd oxcaml
opam exec --switch=5.2.0+ox -- dune build
./_build/default/bin/meanders_ox.exe 40 --from 36
```

**The state in one word.** The word of Section 7 needs only one bit per bracket (`1` for `(`),
the position of the `E` and `h`. Under a leading `1` that marks where the word ends, it fits in
one 63-bit OCaml integer: `h lsl 57 lor epos lsl 51 lor brackets`. Every transition becomes a
few shifts and masks on that integer, and a state costs no allocation at all.

**Modes.** OxCaml attaches *modes* to values, checked by the compiler alongside types, and
written `@ mode`.

* `local` values live on the stack and must not escape the function that made them. The
  default, `global`, lives on the garbage-collected heap. The hot loop allocates only local
  values, so it never triggers a collection.
* `portable` functions capture nothing that would be unsafe on another core, and may run
  there. `contended` values may be shared with other cores, so their mutable parts cannot be
  read or written; `uncontended` values belong to the current task. Together these modes rule
  out data races at compile time: two cores can never touch the same mutable data without
  synchronization.

**Capsules.** A capsule wraps mutable data that several cores share, with a mutex as its only
key. Each shard of a layer is a `Capsule.Sync.With_mutex.t`. A worker adds a batch to a shard
by locking it. The callback must be `portable`, so it can see the shard's table, but only
what it is handed and nothing it captured:

```oxcaml
let insert_batch (par @ local) (shard : shard) (ks : raw iarray @ local)
    (cs : raw iarray @ local) n =
  Capsule.Sync.With_mutex.with_lock (Parallel.sync par) shard ~f:(fun _ t ->
    T.add_batch t ks cs n)
```

The batch is passed as two immutable arrays (`iarray`) on the stack. The first version passed
the worker's mutable buffer instead, and the compiler rejected it: inside a `portable`
function that buffer is `contended`, so it cannot be read.

**The `Parallel` scheduler.** Instead of spawning domains by hand, the program runs inside
`Parallel_scheduler.with_parallel`, a work-stealing scheduler. A parallel loop gives each
worker its own slice of one scratch array. The slices are disjoint, and the type system knows
it, so each worker may write to its own:

```oxcaml
(S.fori [@kind float64]) par ~pivots ((S.slice [@kind float64]) scratch)
  ~f:(fun par _ buf -> worker par buf ~m ~x ~layer:layer_x ~next ~claim)
```

Workers claim source shards from a `Portable.Atomic` counter, exactly as the domains of
Section 8 do. A worker takes a claimed shard out of its capsule with `With_mutex.destroy`,
which hands it sole ownership, so it reads the shard without a lock and frees it.

**Unboxed types.** OCaml normally boxes values that are not small integers, which costs
allocation and pointer chasing. OxCaml adds *unboxed* types: `float#` and `int64#` are raw
machine numbers, `#(a * b * c * d)` is a tuple returned in registers, and arrays of them are
flat memory that the garbage collector never scans. `Word.successors` returns the up to four
successors of a state as an unboxed tuple, with `-1` for "none":

```oxcaml
let #(s0, s1, s2, s3) = Word.successors m x (k1 - 1) in
push par buf next s0 c;
push par buf next s1 c;
push par buf next s2 c;
push par buf next s3 c
```

**A store barrier, avoided safely.** On ARM processors, OCaml 5 places a memory barrier
before every store of a word into mutable memory. That keeps the language's guarantees for
programs that race, at about 10 ns per store. Stores of unboxed floats get no barrier. The
modes already prove the program race-free, so the tables keep each integer as its raw 64 bits
in a `float#` slot. One `fmov` instruction moves the bits each way, and no floating-point
arithmetic ever touches them. That single change made the single-thread sweep about 30% faster.

**How it compares.** On the development laptop (10 cores) the OxCaml program matches the
Rust program's wall time for $n = 38$ to $42$ (3.3 s against 3.6 s at $n = 40$), using a
little less CPU and somewhat more memory. Both reproduce the published counts, and both run
the machine whose correctness the Lean library proves. The repository's README has the larger
runs.
