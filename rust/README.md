# meanders-rs: a parallel transfer-matrix counter in Rust

`meanders-rs` counts Arnold's open meanders (OEIS A005316), the number of ways a river can cross
a straight road `n` times. It runs the same machine as the verified Lean counter
`Arnold.TM.tmCount` (see `Arnold/TM/Defs.lean`), which is proved equal to the definition of
the numbers. This program is not proved. It is checked: against the serial reference in this
crate, against Lean's certified values, and against the published OEIS terms.

```sh
cargo build --release
./target/release/meanders-rs 40                  # n = 0, ..., 40
./target/release/meanders-rs 46 --from 44        # n = 44, 45, 46
./target/release/meanders-rs 30 --check          # also compare with the serial reference
cargo test --release
```

Options: `--threads T` (default: all logical CPUs), `--two-moduli` (force the exact two-sweep
count even when one would do), `--check`. Output is tab-separated: `n`, the count, the largest
layer (states), the total number of states over all layers, and seconds.

## The state

Lean's state is two stacks of references, one per side of the road, saying where each open
arc's piece of river leads. Read the open arcs along the cut from top to bottom: the upper stack
from its bottom up, then the lower stack from its top down. The pieces west of the cut never
cross, so in that order they form a non-crossing matching: a bracket word, with at most one `E`
for the arc whose piece leads to the east end. With `h`, the number of arcs above the road, this
is the whole state.

The four bridge actions become word operations: open both sides inserts `()` at the cut; open
one side and close the other only moves `h`; closing both tops joins their pieces (refused if
they are partners, which would close a loop) and may turn one bracket round; the east end
inserts or closes an `E`. `src/state.rs` is the readable version on a decoded word,
`src/word.rs` the same transitions on a packed `u128` (two bits per position). The parallel
sweep stores a state in 64 bits: `h` (5 bits), the position of `E` (6 bits), and one bit per
bracket under a sentinel. That fits words of up to 52 brackets, which suffices up to `n = 52`
(the longest words have about `n + 1` letters; the program asserts the bound). Packing and
unpacking are constant-time bit interleavings (`spread`, `compact`).

## The parallel sweep

A layer is split into 4,096 hash shards, each an open-addressing table (linear probing, keys
and counts in separate arrays, empty slot `0`, grown by half at 80% load) behind its own mutex.
For each point of the road, worker threads (`std::thread::scope`) claim source shards from an
atomic counter, generate every viable successor, and batch them per target shard; a full batch
of 128 is added under that shard's lock. A source shard is freed as soon as it has been read,
so memory holds little more than one layer: 16 bytes per state plus table slack.

Counts are kept modulo `2^64`. From `n = 44`, where the count may pass `2^64`, a second sweep
runs modulo the Mersenne prime `2^61 - 1`, and the Chinese remainder theorem recovers the
exact count below `2^125`.

## Results

See `bench/` in the repository root for the benchmark harness and recorded results.
