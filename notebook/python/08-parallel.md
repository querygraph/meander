## 8. All cores at once

The Rust and OxCaml programs in this repository run the transfer matrix on every core. Each
layer is split into *shards* by a hash of the state. Workers expand the shards in parallel and
send each successor to the shard its hash selects; then the shards are merged in parallel. No two
workers ever merge into the same shard at once, so they need no coordination beyond that.

**Why processes.** A Python program runs its bytecode one thread at a time: the *global
interpreter lock* lets threads take turns, not run together. (Experimental builds of Python
3.13 and later can remove it.) To use several cores, Python starts several *processes*, each
with its own interpreter and memory, and sends data between them by *pickling*: turning objects
into bytes and back. That costs time, so each piece of work should be large.

**A hash that every process agrees on.** Python's built-in `hash` of a string changes from one
process to the next, a defence against crafted inputs. Shard numbers must agree across
processes, so we use the CRC-32 checksum from the `zlib` module. `s.encode()` turns a string
into bytes, which is what checksums read.

```python
import zlib

SHARDS = 64


def shard_of(state):
    word, h = state
    return zlib.crc32(f"{h}:{word}".encode()) % SHARDS
```

**The two phases of a step.** `expand_shard` takes one source shard and returns its successors
split by target shard. `merge_shard` takes, for one target shard, the pieces from every source,
and adds them up. A function that a worker process runs must receive everything it needs in its
arguments, so each takes a tuple. `_` is an ordinary name, used by convention for a value that
is not needed.

```python
def expand_shard(task):
    m, x, shard = task
    out = [defaultdict(int) for _ in range(SHARDS)]
    for state, count in shard.items():
        for s in successors(m, x, state):
            if viable(m, x + 1, s):
                out[shard_of(s)][s] += count
    return out


def merge_shard(pieces):
    total = defaultdict(int)
    for piece in pieces:
        for state, count in piece.items():
            total[state] += count
    return total
```


**Process pools.** `ProcessPoolExecutor` from `concurrent.futures` keeps a pool of worker
processes. `pool.map(f, tasks)` runs `f` on every task across the pool and yields the results in
order. A `with` statement opens the pool and shuts it down when the block ends, even after an
error. Workers are made by *forking* this process, which copies the functions defined in the
notebook into them (`multiprocessing.get_context("fork")`; the default on macOS starts fresh
interpreters, which cannot see notebook functions). `os.cpu_count()` is the number of cores.

**`zip` with `*`.** `zip(*rows)` turns a list of rows into the list of columns: here, from
"for each source, its pieces for every target" to "for each target, its pieces from every
source".

```python
import multiprocessing
import os
from concurrent.futures import ProcessPoolExecutor


def tm_count_parallel(m, workers=os.cpu_count()):
    """tm_count with every layer expanded and merged on `workers` processes."""
    start = ("", 0)
    shards = [{} for _ in range(SHARDS)]
    shards[shard_of(start)][start] = 1
    context = multiprocessing.get_context("fork")
    with ProcessPoolExecutor(workers, mp_context=context) as pool:
        for x in range(m + 1):
            rows = list(pool.map(expand_shard, [(m, x, s) for s in shards]))
            shards = list(pool.map(merge_shard, zip(*rows)))
    final = ("E", 0)
    return shards[shard_of(final)].get(final, 0)
```

```python
for m in (24, 32):
    t0 = time.perf_counter()
    serial = tm_count(m)
    t1 = time.perf_counter()
    parallel = tm_count_parallel(m)
    t2 = time.perf_counter()
    assert serial == parallel
    print(f"n = {m}: {serial:,}   one core {t1 - t0:.1f} s, "
          f"{os.cpu_count()} processes {t2 - t1:.1f} s")
```

For small $n$ the pool's overhead dominates, and one core wins. For larger $n$ the pool pays,
but by a factor of about two, not by the number of cores: every piece of every layer passes
through the parent process twice, once from `expand_shard` and once to `merge_shard`, and the
parent does that work alone. Adding workers then changes little. The compiled programs avoid
that: their workers share one address space and add into the shared shards under a lock
per shard, and store a state in one 64-bit word instead of a Python tuple. The repository's
README records how far they get.
