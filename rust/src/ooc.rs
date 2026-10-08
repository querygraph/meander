//! Out-of-core sweep: layers larger than memory spill to disk as sorted runs.
//!
//! The next layer is built in memory exactly as in `par.rs`: 4,096 hash shards, each an
//! open-addressing table behind its own lock. Here a shard has a cap on its entries. When an
//! insert takes it past the cap, the table is swapped out under the lock, and the worker sorts it
//! by state and writes it to disk as a *run*, outside the lock. Counts are exact, so one sweep
//! suffices for every `n`.
//!
//! A run stores each record as two LEB128 varints: the difference from the previous state (the
//! states are sorted, so it is positive) and the count. Shards are chosen by a hash of the state,
//! so a run's states spread over the whole key range and a difference still takes about 6 bytes;
//! the larger saving is the count, which takes 7 to 10 bytes instead of 16.
//!
//! One sweep also yields every smaller `n`. The bridge steps do not depend on `n`, and pruning
//! never changes the count of a state that survives it, so after `m` bridges the layer holds the
//! same counts in every sweep for `n ≥ m`. After `m` bridges exactly one state can still finish
//! with `m` crossings: one matched pair of open arcs, above and below the road for odd `m`, both
//! below for even `m`. Its count is A(m), so `count` reads A(1), …, A(n) off a single sweep.
//!
//! A shard of the next layer is then its runs on disk plus the table left in memory. When that
//! layer is processed, a worker reads the shard as a k-way merge of the sorted runs and the
//! sorted remainder, adding the counts of equal states as they meet: one sequential write and
//! one sequential read per spilled record, with no separate merge pass. Run files are deleted as
//! soon as they have been read.
//!
//! Memory holds at most one capped table per shard for the layer being built, plus the
//! remainders of the layer being read, so the cap bounds memory whatever the layer size.

use crate::state::{INIT, final_key};
use crate::word::{Key64 as Key, narrow, successors, widen};
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

pub(crate) const SHARD_BITS: u32 = 12;
pub(crate) const SHARDS: usize = 1 << SHARD_BITS;
const BATCH: usize = 128;
const MAX_LOAD: f64 = 0.8;
const READ_BUF: usize = 1 << 20;

#[inline(always)]
pub(crate) fn hash(k: Key) -> u64 {
    let p = (k as u128).wrapping_mul(0x9E37_79B9_7F4A_7C15_u128);
    (p as u64) ^ ((p >> 64) as u64)
}

#[inline(always)]
pub(crate) fn shard_of(hv: u64) -> usize {
    (hv >> (64 - SHARD_BITS)) as usize
}

/// A growable open-addressing table with exact counts (slots hold `key + 1`; `0` is empty).
#[derive(Default)]
pub(crate) struct Table {
    keys: Vec<Key>,
    cnts: Vec<u128>,
    pub(crate) len: usize,
}

impl Table {
    pub(crate) fn get(&self, k: Key) -> u128 {
        if self.keys.is_empty() {
            return 0;
        }
        let n = self.keys.len();
        let mut i = (((hash(k) << SHARD_BITS) as u128 * n as u128) >> 64) as usize;
        loop {
            let ki = self.keys[i];
            if ki == k + 1 {
                return self.cnts[i];
            }
            if ki == 0 {
                return 0;
            }
            i += 1;
            if i == n {
                i = 0;
            }
        }
    }

    fn with_slots(slots: usize) -> Table {
        Table { keys: vec![0; slots], cnts: vec![0; slots], len: 0 }
    }

    #[inline(always)]
    pub(crate) fn add(&mut self, k: Key, hv: u64, c: u128) {
        if (self.len + 1) as f64 > self.keys.len() as f64 * MAX_LOAD {
            let slots = (self.keys.len() * 3 / 2).max(64);
            let old = std::mem::replace(self, Table::with_slots(slots));
            for (k, c) in old.entries() {
                self.add(k, hash(k), c);
            }
        }
        let n = self.keys.len();
        let k1 = k + 1;
        let mut i = (((hv << SHARD_BITS) as u128 * n as u128) >> 64) as usize;
        loop {
            let ki = self.keys[i];
            if ki == k1 {
                self.cnts[i] += c;
                return;
            }
            if ki == 0 {
                self.keys[i] = k1;
                self.cnts[i] = c;
                self.len += 1;
                return;
            }
            i += 1;
            if i == n {
                i = 0;
            }
        }
    }

    pub(crate) fn entries(&self) -> impl Iterator<Item = (Key, u128)> + '_ {
        self.keys.iter().zip(&self.cnts).filter(|e| *e.0 != 0).map(|(k, c)| (k - 1, *c))
    }

    pub(crate) fn sorted(self) -> Vec<(Key, u128)> {
        let mut v: Vec<(Key, u128)> = self.entries().collect();
        v.sort_unstable_by_key(|e| e.0);
        v
    }
}

/// One shard of a layer under construction: its in-memory table and the runs it has spilled.
#[derive(Default)]
struct Shard {
    table: Table,
    runs: Vec<PathBuf>,
}

/// A finished shard, ready to be read: sorted runs on disk and a sorted remainder in memory.
#[derive(Default)]
struct Frozen {
    runs: Vec<PathBuf>,
    rest: Vec<(Key, u128)>,
}

#[inline(always)]
fn put_varint(buf: &mut Vec<u8>, mut v: u128) {
    while v >= 0x80 {
        buf.push((v as u8) | 0x80);
        v >>= 7;
    }
    buf.push(v as u8);
}

/// Write a sorted run: (state difference, count) as two varints per record. Returns its bytes.
pub(crate) fn write_run(path: &Path, entries: &[(Key, u128)]) -> std::io::Result<u64> {
    let mut buf = Vec::with_capacity(entries.len() * 16);
    let mut prev: Key = 0;
    for &(k, c) in entries {
        put_varint(&mut buf, (k - prev) as u128);
        put_varint(&mut buf, c);
        prev = k;
    }
    let mut w = BufWriter::new(File::create(path)?);
    w.write_all(&buf)?;
    w.flush()?;
    Ok(buf.len() as u64)
}

/// A sorted run being read back.
pub(crate) struct RunReader {
    r: BufReader<File>,
    prev: Key,
    pub(crate) head: Option<(Key, u128)>,
}

impl RunReader {
    pub(crate) fn open(path: &Path) -> RunReader {
        let r = BufReader::with_capacity(READ_BUF, File::open(path).expect("open run"));
        let mut rr = RunReader { r, prev: 0, head: None };
        rr.advance();
        rr
    }

    /// The next varint, or `None` at the end of the run.
    fn varint(&mut self) -> Option<u128> {
        let (mut v, mut shift) = (0u128, 0);
        let mut b = [0u8; 1];
        loop {
            if self.r.read_exact(&mut b).is_err() {
                assert!(shift == 0, "run file ends inside a record");
                return None;
            }
            v |= ((b[0] & 0x7f) as u128) << shift;
            if b[0] < 0x80 {
                return Some(v);
            }
            shift += 7;
        }
    }

    pub(crate) fn advance(&mut self) {
        self.head = self.varint().map(|d| {
            let k = self.prev + d as Key;
            self.prev = k;
            let c = self.varint().expect("run file ends inside a record");
            (k, c)
        });
    }
}

/// The one state, after `m ≥ 1` bridges, from which the east end can finish a river with `m`
/// crossings: a matched pair of open arcs, one above and one below the road for odd `m` (the east
/// end closes the upper one), both below for even `m` (it closes the top one below).
fn finishing_state(m: usize) -> Key {
    use crate::state::{CLOSE, OPEN, Word, encode};
    let mut w = [0u8; 64];
    w[0] = OPEN;
    w[1] = CLOSE;
    narrow(encode(&Word { w, len: 2, h: m % 2 }))
}

/// Visit the states of a frozen shard in increasing order, each once, with its total count.
fn merge(f: Frozen, mut visit: impl FnMut(Key, u128)) {
    let mut runs: Vec<RunReader> = f.runs.iter().map(|p| RunReader::open(p)).collect();
    let mut rest = f.rest.into_iter().peekable();
    loop {
        let mut min = rest.peek().map(|e| e.0);
        for r in &runs {
            if let Some((k, _)) = r.head {
                min = Some(min.map_or(k, |m: Key| m.min(k)));
            }
        }
        let Some(k) = min else { break };
        let mut c = 0u128;
        if rest.peek().is_some_and(|e| e.0 == k) {
            c += rest.next().unwrap().1;
        }
        for r in runs.iter_mut() {
            while r.head.is_some_and(|h| h.0 == k) {
                c += r.head.unwrap().1;
                r.advance();
            }
        }
        visit(k, c);
    }
    for p in &f.runs {
        let _ = fs::remove_file(p);
    }
}

pub struct Stats {
    pub count: u128,
    pub peak_states: usize,
    pub total_states: usize,
    pub spilled_records: u64,
    pub spilled_bytes: u64,
    pub spilled_bytes_peak: u64,
    /// A(m) for m = 0, …, n, read off this one sweep.
    pub all: Vec<u128>,
}

/// Count the meanders with `m` crossings, keeping at most `cap` states in memory per shard of
/// the layer being built and spilling the rest to sorted runs under `dir`.
pub fn count(m: usize, threads: usize, cap: usize, dir: &Path) -> Stats {
    fs::create_dir_all(dir).expect("create spill directory");
    let run_id = AtomicU64::new(0);
    let spilled = AtomicU64::new(0);
    let spilled_bytes = AtomicU64::new(0);
    let on_disk = AtomicU64::new(0);
    let disk_peak = AtomicU64::new(0);
    let mut layer: Vec<Mutex<Frozen>> = (0..SHARDS).map(|_| Mutex::new(Frozen::default())).collect();
    let init = narrow(INIT);
    layer[shard_of(hash(init))].lock().unwrap().rest.push((init, 1));
    let (mut peak, mut total) = (1usize, 0usize);
    let visited = AtomicUsize::new(0);
    let mut all = vec![0u128; m + 1];
    all[0] = 1;
    let found = Mutex::new(0u128);
    let start = std::time::Instant::now();
    for x in 0..=m {
        let target = if x >= 1 && x < m { Some(finishing_state(x)) } else { None };
        let next: Vec<Mutex<Shard>> = (0..SHARDS).map(|_| Mutex::new(Shard::default())).collect();
        let claim = AtomicUsize::new(0);
        let spill = |d: usize, table: Table| {
            let entries = table.sorted();
            let id = run_id.fetch_add(1, Ordering::Relaxed);
            let path = dir.join(format!("run-{x:02}-{d:04}-{id}.bin"));
            let bytes = write_run(&path, &entries).expect("write run");
            spilled.fetch_add(entries.len() as u64, Ordering::Relaxed);
            spilled_bytes.fetch_add(bytes, Ordering::Relaxed);
            disk_peak.fetch_max(on_disk.fetch_add(bytes, Ordering::Relaxed) + bytes, Ordering::Relaxed);
            next[d].lock().unwrap().runs.push(path);
        };
        std::thread::scope(|sc| {
            for _ in 0..threads {
                sc.spawn(|| {
                    let mut bufs: Vec<Vec<(Key, u64, u128)>> = (0..SHARDS).map(|_| Vec::new()).collect();
                    let flush = |d: usize, buf: &mut Vec<(Key, u64, u128)>| {
                        let full = {
                            let mut s = next[d].lock().unwrap();
                            for &(k, hv, c) in buf.iter() {
                                s.table.add(k, hv, c);
                            }
                            if s.table.len > cap { Some(std::mem::take(&mut s.table)) } else { None }
                        };
                        buf.clear();
                        if let Some(t) = full {
                            spill(d, t);
                        }
                    };
                    loop {
                        let s = claim.fetch_add(1, Ordering::Relaxed);
                        if s >= SHARDS {
                            break;
                        }
                        let src = std::mem::take(&mut *layer[s].lock().unwrap());
                        let bytes: u64 = src
                            .runs
                            .iter()
                            .map(|p| fs::metadata(p).map_or(0, |md| md.len()))
                            .sum();
                        merge(src, |k, c| {
                            visited.fetch_add(1, Ordering::Relaxed);
                            if Some(k) == target {
                                *found.lock().unwrap() = c;
                            }
                            successors(m, x, widen(k), |k2| {
                                let k2 = narrow(k2);
                                let hv = hash(k2);
                                let d = shard_of(hv);
                                let buf = &mut bufs[d];
                                if buf.capacity() == 0 {
                                    buf.reserve_exact(BATCH);
                                }
                                buf.push((k2, hv, c));
                                if buf.len() == BATCH {
                                    flush(d, buf);
                                }
                            });
                        });
                        on_disk.fetch_sub(bytes, Ordering::Relaxed);
                    }
                    for (d, buf) in bufs.iter_mut().enumerate() {
                        if !buf.is_empty() {
                            flush(d, buf);
                        }
                    }
                });
            }
        });
        if target.is_some() {
            all[x] = std::mem::take(&mut *found.lock().unwrap());
        }
        // Layer x has now been read in full, so its size (distinct states) is known exactly.
        let size = visited.swap(0, Ordering::Relaxed);
        if x > 0 {
            peak = peak.max(size);
            total += size;
        }
        eprintln!(
            "layer {x:2}  states {size:>13}  {:>8.0} s  on disk {:>7.2} GB{}",
            start.elapsed().as_secs_f64(),
            on_disk.load(Ordering::Relaxed) as f64 / 1e9,
            if target.is_some() { format!("  A({x}) = {}", all[x]) } else { String::new() }
        );
        layer = next
            .into_iter()
            .map(|s| {
                let s = s.into_inner().unwrap();
                let rest = if s.runs.is_empty() {
                    s.table.entries().collect()
                } else {
                    s.table.sorted()
                };
                Mutex::new(Frozen { runs: s.runs, rest })
            })
            .collect();
    }
    let f = narrow(final_key());
    let mut count = 0u128;
    let last = std::mem::take(&mut *layer[shard_of(hash(f))].lock().unwrap());
    let mut last_size = 0usize;
    merge(last, |k, c| {
        last_size += 1;
        if k == f {
            count += c;
        }
    });
    // The other shards of the last layer: read them only to count their states.
    for s in &layer {
        let f = std::mem::take(&mut *s.lock().unwrap());
        merge(f, |_, _| last_size += 1);
    }
    peak = peak.max(last_size);
    total += last_size;
    Stats {
        count,
        peak_states: peak,
        total_states: total,
        spilled_records: spilled.load(Ordering::Relaxed),
        spilled_bytes: spilled_bytes.load(Ordering::Relaxed),
        all: {
            all[m] = count;
            all
        },
        spilled_bytes_peak: disk_peak.load(Ordering::Relaxed),
    }
}
