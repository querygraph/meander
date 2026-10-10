# Rust vs OxCaml: why OxCaml keeps getting it right first

The same pattern has come up twice. OxCaml does something well, and Rust catches up later:

- **The transfer-matrix sweep.** See the blog post `docs/blog/rust-vs-oxcaml/post.md`: "OxCaml
  takes the lead", then "Rust catches up".
- **The meet-in-the-middle store.** On Morrobay at horizon 52, OxCaml took 1310 s and Rust 2953 s.
  Rust spent 24,581 s of CPU in the kernel; OxCaml spent 2,095 s.

These are notes on why, and on how we work so that it doesn't keep happening. The cause is
mostly our process, not the languages.

## 1. OxCaml was always the second implementation

Rust was written first, as the working baseline. The OxCaml port came later, explicitly as the
"hyperoptimized" version. It was profiled on purpose, and the profile drove its design:

- a radix sort;
- per-worker buffers;
- tables emptied in place instead of regrown.

Rust never got a dedicated pass like that; it got fixes only when something broke. The second
implementation inherits all the lessons, so its "right first time" is hindsight. Whichever
language got the tuning pass would look like the smarter one.

## 2. OxCaml makes the costs visible early; Rust hides them

**Allocation.** In OCaml, allocation goes through the GC, and the GC counts it. The first
OxCaml store allocated 121 GB on the major heap at horizon 46, and that number forced buffer
reuse. In Rust, `Vec::new()` and `collect()` in a loop are idiomatic and look free. On macOS
a large allocation is a fresh memory mapping that has to be faulted in. That cost showed up
only as kernel time at scale: 221 million page faults at horizon 52 against OxCaml's 122
million.

**Locks.** OxCaml's mode system forbids sharing mutable buffers across domains and holding
two capsule locks at once. That pushed the design toward explicit per-worker buffers and
short critical sections from the start. Rust's `Mutex` makes it easy to do a lot under a lock.
Emptying a full table in place under the lock (`Table::drain`) held it long enough for 31
threads to block in the kernel: 376 million involuntary context switches against OxCaml's 27
million.

**Defaults.** Rust's `sort_unstable` is a good default, so we never questioned it. It became
the top frame of the profile. OCaml has no good built-in sort for unboxed arrays, so we had to
write one, and an LSD radix sort was the natural choice.

## 3. We tuned on the wrong machine

Both implementations were optimized on the M1 Max laptop, where page faults are cheap and the
SSD is fast. There, Rust's store spent 51 s in the kernel at horizon 48. On the Xeon, at full
scale, the same habits cost 24,581 s. OxCaml's fixes, motivated by GC numbers, happened to
remove the operating-system costs too.

## It isn't one-sided

- **Rust found the structural fixes first:**
  - the few-large-files store layout (thousands of small files hung an HFS+ SoftRAID volume);
  - periodic syncs to bound dirty pages;
  - refusing stores of the old layout.
- **OxCaml shipped a real bug.** Keys with h ≥ 16 are negative OCaml ints, and the first
  OxCaml store compared them as signed, so layers from F₁₆ on were written corrupt.
- **OxCaml's in-memory run uses more memory** (17.6 GB against 12.9 GB at `--mitm 46`), and on
  the laptop its store was slower until it was tuned.

## How we work now

- **Every optimization applies to both implementations.** When one gets a profiling pass, the
  other gets the same pass before we compare them.
- **Benchmark on the target machine early.** Morrobay (Xeon, 128 GB, Apo), not only the
  laptop. Record user and sys CPU, context switches and page faults, not just wall time.
- **Allocation in a hot loop is a smell in either language.** Reuse per-worker buffers, keep
  critical sections O(1), and don't take a library default on trust in the hot path.
- **Profile short runs too.** Sample a few seconds in, not on a fixed 4-minute timer.

The race with equal tuning (October 2026) is the first comparison of the two languages rather
than of how much effort each got. Its numbers go in the blog post.
