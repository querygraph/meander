# meanders_ox: Arnold's open meanders in OxCaml

`meanders_ox` counts Arnold's open meanders (OEIS A005316) with the same parallel transfer
matrix as the Rust program in `../rust` (which runs the verified Lean machine
`Arnold/TM/Defs.lean`, `tmCount`). It uses OxCaml's data-race-free parallelism: the
`Parallel` work-stealing scheduler, capsules protected by mutexes, and parallel arrays. It
spawns no domains by hand.

## Build and run

OxCaml is the opam switch `5.2.0+ox`. Use it per command and leave the global switch alone:

```sh
cd oxcaml
opam exec --switch=5.2.0+ox -- dune build          # release profile, see dune-workspace
opam exec --switch=5.2.0+ox -- dune test           # CRT vectors + parallel vs serial, n <= 28
./_build/default/bin/meanders_ox.exe [N] [--from M] [--threads T] [--two-moduli] [--check]
```

The CLI and output match `meanders-rs`:

```
# n	count	peak_states	total_states	seconds	threads=10
40	165597452660771610	22007687	100820657	3.252
```

- `--threads T` sets the worker count (`Parallel_scheduler.with_parallel ~max_workers:T`). The
  default is `Domain.recommended_domain_count ()`.
- `--two-moduli` forces the second sweep modulo 2^61 − 1 and the CRT reconstruction. It
  runs automatically for n ≥ 44.
- `--check` compares every count with a sequential `Hashtbl` sweep (slow; use for small n).

`dune-workspace` selects the release profile. Keep it: the dev profile compiles libraries
with `-opaque`, which blocks flambda2's cross-module inlining and makes the program about
2x slower. Library flags are `-O3 -unboxed-types`.

## Layout

| file | contents |
|---|---|
| `src/word.ml` | the state encoding and the transitions (`successors`) |
| `src/sweep.ml` | the parallel layer sweep, shard tables, capsules, scratch slices |
| `src/crt.ml` | CRT recombination (mod 2^63, mod 2^61 − 1) and ~124-bit decimal printing |
| `src/serial.ml` | the sequential reference sweep behind `--check` |
| `src/back.ml` | the meet-in-the-middle state key (E-free, `h << 58 \| 1 << len \| bits`), the bridge steps, depth and the packed inverse steps |
| `src/limb.ml` | exact two-limb (2 x 62-bit) counts |
| `src/mitm.ml` | meet in the middle in memory (`--mitm`) |
| `src/store.ml` | the persistent, stepwise store on disk (`--store`) |
| `bin/meanders_ox.ml` | the CLI |
| `test/test_meanders.ml` | CRT test vectors (including A005316(44..46)); parallel = serial = OEIS for n ≤ 28 |
| `test/test_mitm.ml` | inverse steps vs a reference, long words, `--mitm` = OEIS for n ≤ 30, store extension, discard, pause/resume |

## The algorithm

The algorithm is the one in `rust/src/par.rs`, transition for transition:

- **State.** A state is a word over `(`, `)` and at most one `E`, plus `h`, the number of
  arcs above the road. It is packed into one immediate 63-bit `int`:
  `h << 57 | epos << 51 | brackets`. The bracket bits sit under a leading sentinel 1 in
  bits 0..50, with 1 = `(`, and `epos = 63` means there is no `E`. That allows up to 50
  brackets and `h ≤ 31`, enough for n ≤ 60. `encode` checks both bounds and fails loudly if
  they are exceeded.
- **Transitions.** `Word.successors` computes the transitions directly on the bracket bits
  and `epos`. Rust widens to a 2-bit-per-letter `u128` instead; here, word position `i` is
  `E` if `i = epos` and otherwise bracket `i − [i > epos]`. The transitions are the four
  bridge actions, with the loop rejection and the `E` propagation, plus the east-end
  open/close, and the same viability bound `cap`. A partner search skips a byte at a time
  using two 256-entry immutable tables.
- **Sweep.** Each layer is split into 4096 hash shards. Each shard is an open-addressing,
  linear-probing table with separate key and count arrays. Slots hold `key + 1`, so 0 means
  empty, and a table grows by 1.5x at load 0.8. For each point, workers claim source shards
  from an atomic counter, compute successors, and batch them per target shard (batches of
  128). A full batch is inserted under that shard's lock, and a source shard is freed once
  it has been read.
- **Counts.** Counts are kept modulo 2^63 (native `int` wraparound). For n ≥ 44 a second
  sweep runs modulo the Mersenne prime p = 2^61 − 1, and the two are combined by CRT:
  2^63 ≡ 4 and 4⁻¹ ≡ 2^59 (mod p), and multiplying by 2^59 is a 61-bit rotation. The result
  x = a + 2^63·t < 2^124 is printed in decimal by a small base-10^9 limb routine, with no
  Zarith. A005316(43) < 2^63 ≤ A005316(44), so one sweep is exact up to n = 43.

Two refinements change no state or count. Both are memory/time tuning:

- **Pre-sized next-layer shards.** Each next-layer shard is sized from the last three layer
  sizes: the growth ratio is extrapolated geometrically and the table is sized for load
  0.75. Tables are allocated lazily by the first worker that inserts into them, so tables
  rarely rehash. Rehashing had been a quarter of the single-thread time.
- **Batch inserts.** A batch insert keeps the table size in a register.

## How OxCaml's parallelism is used

The program does not fall back to anything. `Domain.spawn` is never called, and the whole
sweep runs inside `Parallel_scheduler.with_parallel`.

- **Shards are capsules.** Each shard table is a `Capsule.Sync.With_mutex.t`:
  `Table.t` lives in its own capsule, guarded by that capsule's mutex. Inserting a batch
  uses `With_mutex.with_lock (Parallel.sync par) shard ~f`. The callback `f` must be
  `portable`, so it cannot capture unprotected mutable state.
- **Taking a source shard.** A worker calls `With_mutex.destroy`, which poisons the mutex
  and merges the table into the worker's own capsule. The worker then owns it outright,
  reads it with no lock, and drops its arrays.
- **Per-worker scratch.** The shard-sized batch buffers must persist across layers and be
  writable by exactly one worker. A `Parallel.for_` body is only `shareable` (it can read
  but not write what it captures), so it cannot do this. Instead the scratch is one
  `Parallel.Arrays.Array` allocated per sweep. `Parallel.Arrays.Array.Slice.fori` splits it
  into disjoint sub-slices and hands each subtask its own sub-slice at `uncontended` mode,
  which lets the subtask write to it. One subtask runs per worker, and each loops on the
  shared `Portable.Atomic` claim counter, as in Rust.
- **Moving a batch into the lock.** A mutable buffer captured by the `portable` callback is
  `contended` there, so it cannot be read. The compiler rejects that version:

  ```
  Error: This value is "contended" because it is used inside the function ...
         which is expected to be "portable".
         However, the highlighted expression is expected to be "uncontended".
  ```

  So `flush` copies the batch into two immutable `iarray`s on the stack. They are `local`:
  freed when `flush` returns and never seen by the GC. Immutable arrays of unboxed scalars
  cross contention, so the portable callback can read them.
- **The one `unsafe_`-named call.** The two copies are built the way
  `Base.Iarray.init [@alloc stack]` builds its own result: a fresh `Array.create_local`,
  filled, then frozen with `Iarray.unsafe_of_array__promise_no_mutation`. Calling
  `(Iarray.init [@alloc stack])` itself also works and is fully checked, but its
  per-element closure call and barriered stores cost about 20% of the single-thread time.
  The freeze is sound because the arrays are fresh, are never written after the freeze,
  and die with `flush`.

## OxCaml performance features, and why

- **Barrier-free stores via unboxed `float#` cells.** This is the biggest single win.
  On arm64, OCaml 5 emits `dmb ishld` before every mutable word store, which keeps the OCaml
  memory model for racy programs. In a store loop on this machine it costs ~10 ns per store,
  against ~2.5 ns for the same loop storing `float#`. The backend exempts unboxed float
  stores (see `backend/arm64/emit.ml`: "assignments other than Word_int and Word_val ... do
  not emit a barrier"). The program is data-race free by construction, so the barrier buys
  nothing. Every table and scratch cell therefore holds the OCaml `int` as its raw 64-bit
  pattern in a `float#` slot, converted with `Int64_u.float_of_bits`/`bits_of_float`. That
  is one bit-exact `fmov` each way, and no float arithmetic ever touches these values.
  Single-thread n = 34 went from 1.27 s to 0.89 s user (Rust: 0.75–0.83 s).
- **Unboxed arrays** (`float# array`, and the `[@kind float64]` instances of the templated
  `Parallel.Arrays` slice accessors):
  - The GC never scans them. With several GB of `int array`s, the major GC had spent
    seconds marking immediates.
  - The accessors compile to a plain `ldr`/`str`. The generic value-kind slice accessors
    are out-of-line calls with a write barrier.
- **Unboxed tuples.** `Word.successors` returns `#(int * int * int * int)` in registers
  (−1 = none). There is no callback closure and no allocation per state.
- **Stack allocation.** Slices, closures and batch copies are `local`, so the inner loop
  and `flush` allocate nothing on the GC heap. That matters because OCaml 5 minor
  collections stop every domain.
- **flambda2 `-O3` and `[@inline always]`** on the hot helpers (`hash`, `place`, `push`,
  `successors`, `mk`). The modulus is a functor argument (`Run (Mod63)`, `Run (Mod61)`),
  so each sweep is specialised.
- **GC tuning.** The big arrays are never scanned, so a major cycle is cheap. The CLI
  therefore sets `space_overhead = 30` (unless `OCAMLRUNPARAM` is set) so that freed
  tables return to the allocator soon.

## Validation

All runs were on the development machine: 10-core arm64 macOS, 64 GB.

- **n = 0..40, default run.** All 41 counts equal the expected values (OEIS A005316).
- **n = 41 and 42.** `672265814872772972` and `1733609081727968492`, both correct.
- **n = 30..40 with `--two-moduli`.** All 11 counts are exact through the CRT path.
- **CRT for values ≥ 2^63.** The unit tests check `Crt.combine` on the residues of
  A005316(44), (45) and (46): `18276178714484582264`, `74661728661167809752` and
  `193909492888406631692`. They also check 2^63 − 1, 2^63, 2^63 + 1 and the maximum
  (2^61 − 1)·2^63 − 1.
- **Agreement with Rust.** `peak_states` and `total_states` are identical to
  `meanders-rs` for every n = 30..42.
- **Parallel vs serial.** `dune test` checks the parallel sweep (4 and 3 workers, one and
  two moduli) against the serial sweep and OEIS for n ≤ 28. `--check` passed for n ≤ 30.

## Performance against `meanders-rs`

Both programs were built in release mode and run with `--threads 10`, one n per process,
interleaved Rust/OxCaml. Times are `/usr/bin/time -l` wall and user seconds; memory is
peak memory footprint and maximum RSS.

The machine was heavily loaded throughout, so treat the numbers as indicative. The
1-minute load average was 166–178 during this run. Lightroom and a Lean REPL were busy,
and earlier runs shared the box with another `meanders-rs` job using ~7 cores. Rust and
OxCaml runs were interleaved so both saw similar conditions.

| n | Rust wall | OxCaml wall | Rust user | OxCaml user | Rust peak footprint | OxCaml peak footprint | Rust max RSS | OxCaml max RSS |
|---|---|---|---|---|---|---|---|---|
| 38 | 1.40 s | 1.34 s | 7.05 s | 6.70 s | 0.54 GB | 0.99 GB | 1.01 GB | 1.06 GB |
| 39 | 2.20 s | 2.32 s | 11.38 s | 10.33 s | 0.80 GB | 1.67 GB | 1.43 GB | 1.79 GB |
| 40 | 3.60 s | 3.29 s | 17.86 s | 17.29 s | 1.24 GB | 1.45 GB | 1.89 GB | 1.96 GB |
| 41 | 6.33 s | 5.29 s | 29.95 s | 28.15 s | 1.82 GB | 2.52 GB | 2.53 GB | 3.07 GB |
| 42 | 9.39 s | 9.52 s | 50.55 s | 46.07 s | 2.47 GB | 3.52 GB | 3.13 GB | 4.07 GB |

- **Time.** Wall time is on par (within ±15% either way). OxCaml uses 3–10% less CPU.
- **Memory.** OxCaml needs 1.0–1.3x the maximum RSS and 1.2–2x the peak footprint.
  - Freed tables return to the system only after a major GC cycle.
  - The pre-sized next-layer tables exist while the current layer drains, whereas Rust
    grows tables on demand.
  - For the larger runs, `OCAMLRUNPARAM=o=20` trades a little CPU for a lower footprint.
    Lowering the 0.75 target load in `predict_slots` is the other knob.
- **Single thread, n = 34, best of 3.** OxCaml 0.84–0.89 s user, Rust 0.69–0.83 s.

## Meet in the middle

The second algorithm of `../rust` (`mitm.rs`, `store.rs`, `mitm_store.rs`), proved in
`Arnold/TM/Middle.lean` (`meet`): A(n) = Σ_s F_k(s) · G_{n−k}(s), with F the forward bridge
layers and G the backward layers (inverse steps, pruned by depth). Each value is checked by
a second split.

```sh
./_build/default/bin/meanders_ox.exe --mitm 44                  # in memory, all A(n), n <= 44
./_build/default/bin/meanders_ox.exe --store DIR --horizon 48 [--mem-gb 16 | --cap N] \
    [--discard] [--min-free-gb G] [--passes P|auto]
```

- **The store** keeps every layer on disk and is extended in place: `--horizon 50` on a
  horizon-48 store adds one segment per backward layer and computes only A(49), A(50).
  - Each segment is two files, `seg{s}.dat` and `seg{s}.idx`, as in Rust. A step writes one
    spill file. Workers read byte ranges through their own descriptors.
  - `touch DIR/PAUSE` stops at the next layer boundary, and so does free disk below
    `--min-free-gb`; either way the exit code is 3. The same command resumes.
  - `--discard` deletes each backward layer once the next one has read it. That needs far
    less disk, but the store can no longer be extended.
  - `--passes P` builds each step in P passes over its source, one group of target shards
    per pass. Each group's tables get P times the cap, so a big layer spills less, but the
    transitions are recomputed on every pass. `auto` picks enough passes per step to avoid
    spilling. One pass is the default. In Rust on the laptop (horizon 50, cap 60000), `auto`
    spilled nothing but took 598 s against 497 s, with the same peak disk.
- **Keys** are 63-bit OCaml ints with h in the top 5 bits. A key with h ≥ 16 is therefore a
  negative int, so the store orders states as unsigned numbers throughout: radix sort,
  merges, joins and varint differences.
- **Validated** against `meanders-rs`:
  - the `values` files are identical for horizon 40 extended to 44, and for direct horizons
    46 and 48;
  - every layer's state count is identical;
  - every second split agrees.

M1 Max, 10 threads, `--mem-gb 16`. The laptop was busy with other work, so treat the times
as ±5%.

| run | Rust wall / user / RSS | OxCaml wall / user / RSS |
|---|---|---|
| `--mitm 44` | 17.6 s / 115 s / – | 16.2 s / 123 s / – |
| `--store`, horizon 46 | 49 s / 399 s / 5.8 GB | 57 s / 490 s / 7.3 GB |
| `--store`, horizon 48 | 148 s / 1173 s / 6.0 GB | 170 s / 1387 s / 7.4 GB |

Store optimizations, at horizon 48 (the first port took 176 s with an 11.7 GB RSS):

- **Tables sized like Rust's.** A table that spills is emptied and reused, so all 4096
  shards spilling together no longer doubles the memory.
- **Per-worker buffers.** The output and radix-sort buffers are reused across shards.
- **`space_overhead` 10** for `--store`.
- **Sort and encode outside the shard lock.** Under the lock a spill only copies the
  entries out.
- **Look-ahead loads** in the batch insert (also used by `--mitm`). This cut `--mitm 44`
  from 130 s to 123 s user.

On the M1 Max laptop, in memory, OxCaml is on par with Rust. On disk it is about 15% slower
and needs about 1.2x the RSS. The profile is dominated by table probes (cache misses) and the
inverse steps, the same as Rust's. Faster varint decoding gained nothing measurable.

### The race on Morrobay

Morrobay is a Xeon W-2191B (18 cores, 36 threads, 128 GB) with the stores on Apo, an HFS+
SoftRAID RAID 5 of SATA SSDs. Runs used 32 threads, the October 2026 code (Rust d5647bf), and
fresh stores. The caps give about 45 GB of tables each: Rust 380000, OxCaml 300000 (OxCaml
sizes its tables at 1.5x the cap). The values are identical.

| run | Rust wall / user / sys / RSS | OxCaml wall / user / sys / RSS |
|---|---|---|
| `--mitm 46` | 67 s / 913 s / 75 s / 12.9 GB | **37 s** / 747 s / 50 s / 17.6 GB |
| `--store`, horizon 52 | 2953 s / 17925 s / **24581 s** / 62.0 GB | **1310 s** / 21196 s / 2095 s / 58.5 GB |

At horizon 52 OxCaml wins 2.25x. Rust spends more CPU time in the kernel than in its own code.

| horizon 52 store | Rust | OxCaml |
|---|---|---|
| involuntary context switches | 376 million | 27 million |
| minor page faults | 221 million | 122 million |
| machine CPU, user / sys | 51% / 28% | 86% / 8% |

The profiles (`sample`, 20 s every 4 min) show where the two differ:

- **Rust's sort.** `sort_unstable` on (key, count) pairs is Rust's top frame, about a fifth
  of its samples. OxCaml's LSD radix sort, with 11-bit digits and per-worker scratch, takes
  about 5% of OxCaml's.
- **Rust's lock waits.** Workers wait on the shard mutexes (`psynch_mutexwait`, about 10% of
  samples). A full table is emptied in place under its lock (`Table::drain`, which scans all
  its slots). That was added to stop allocator churn (d5647bf), but it holds the lock long
  enough for 31 other threads to block in the kernel. OxCaml copies under the lock too, but
  its futex-based mutex parks waiters far more cheaply (`__ulock_wait`).
- **Rust's fresh buffers.** Each spill collects into a new `Vec`, each compacted shard sorts
  into a new `Vec`, and each spilled range gets a new 1 MB read buffer. On macOS these large
  allocations are fresh mappings, so every one page-faults its memory in again. OxCaml
  reuses per-worker buffers for all three.
- **OxCaml's profile** is what both should look like: table inserts (`Mitm.go`) about half,
  inverse steps (`claim_loop`) about a fifth, then reads, sort and decoding.

Those fixes were then ported to Rust (8211168):
- a per-worker spare table, swapped in under the lock in O(1);
- reused drain, sort and read buffers;
- the radix sort.

So were the fixes for its in-memory driver (0dbf7b3), whose profile showed the same lock
waits and allocation churn:
- presized tables, allocated by the first worker to use them;
- parallel dot products;
- forward layers read in place instead of copied.

Rerun on Morrobay with the same settings, values identical:

| run | Rust before | Rust after | OxCaml |
|---|---|---|---|
| `--store`, horizon 52 | 2953 s | **1055 s**, 1934 s sys, 55.9 GB | 1272 s, 2135 s sys, 57.0 GB |
| `--mitm 46` | 72 s | **40 s**, 14.4 GB | 44 s, 16.4 GB |
| `--mitm 48` | | **92 s**, 32.0 GB | 100 s, 37.0 GB |

With the same design, Rust leads by 8 to 17 percent and uses a little less memory. On the
laptop, under heavy load (load average about 110), the store at horizon 48 took 194 s in Rust
and 222 s in OxCaml. Why OxCaml had the better design first is in `../rust-vs-ocaml.md`.

## Compromises

- **Two `unsafe_` calls.** Both are `Iarray.unsafe_of_array__promise_no_mutation`.
  - One freezes a fresh local batch array, explained above.
  - The other, in the store, freezes the entries a spill copies out of a shard's capsule.
    That array is fresh and never written again.

  Everything else is checked by the mode system.
- **Raw bits in `float#` slots.** The `float#` storage holds raw 64-bit patterns, not
  floats. It exists only to avoid the arm64 store barrier, and the conversions are confined
  to `to_raw`/`of_raw` in `sweep.ml`.
- **Sweep refinements.** The size prediction and lazy allocation are not in the Rust
  program. They change no state or count.
