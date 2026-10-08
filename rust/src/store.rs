//! A persistent store of layers on disk.
//!
//! A layer is a directory. Its states are split into the 4,096 hash shards of `ooc.rs`, and shard
//! `d` is stored as one or more *segments*, files `{d:04}.{seg}.bin`, each sorted by state and
//! written as varint (state difference, count) records. Segments of one layer hold disjoint sets
//! of states (each comes from one horizon of the meet-in-the-middle store), so reading a shard is
//! a merge of its segments. A missing file is an empty segment.
//!
//! `step` builds a new segment from a source layer: workers stream source shards, apply a
//! transition, and add the results into capped in-memory tables, one per target shard, which
//! spill sorted runs to a scratch directory when full. At the end each target shard's runs and
//! remainder are merged into its single segment file, so a layer never has more than one file per
//! shard and segment, and readers open few files at once.

use crate::ooc::{RunReader, SHARDS, Table, hash, shard_of, write_run};
use crate::word::Key64 as Key;
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

const BATCH: usize = 128;

/// Raise the limit on open files to the hard limit (macOS defaults to 256).
pub fn raise_fd_limit() {
    unsafe {
        let mut r = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
        if libc::getrlimit(libc::RLIMIT_NOFILE, &mut r) == 0 {
            r.rlim_cur = r.rlim_max.min(65_536);
            libc::setrlimit(libc::RLIMIT_NOFILE, &r);
        }
    }
}

/// A layer on disk: a directory and its number of segments.
#[derive(Clone, Debug)]
pub struct Layer {
    pub dir: PathBuf,
    pub segments: usize,
}

impl Layer {
    pub fn new(dir: PathBuf, segments: usize) -> Layer {
        Layer { dir, segments }
    }

    fn file(&self, d: usize, seg: usize) -> PathBuf {
        self.dir.join(format!("{d:04}.{seg}.bin"))
    }

    /// Visit shard `d` in increasing state order, merging its segments.
    pub fn read_shard(&self, d: usize, mut visit: impl FnMut(Key, u128)) {
        let mut runs: Vec<RunReader> = (0..self.segments)
            .map(|s| self.file(d, s))
            .filter(|p| p.exists())
            .map(|p| RunReader::open(&p))
            .collect();
        loop {
            let mut best: Option<(usize, Key)> = None;
            for (i, r) in runs.iter().enumerate() {
                if let Some((k, _)) = r.head
                    && best.is_none_or(|(_, b)| k < b)
                {
                    best = Some((i, k));
                }
            }
            let Some((i, k)) = best else { break };
            let c = runs[i].head.unwrap().1;
            runs[i].advance();
            debug_assert!(runs.iter().all(|r| r.head.is_none_or(|h| h.0 != k)), "segments overlap");
            visit(k, c);
        }
    }
}

/// Write the given states as segment `seg` of the layer in `dir`.
pub fn write_states(dir: &Path, seg: usize, states: &[(Key, u128)]) -> Layer {
    fs::create_dir_all(dir).expect("create layer directory");
    let mut by: Vec<Vec<(Key, u128)>> = (0..SHARDS).map(|_| Vec::new()).collect();
    for &(k, c) in states {
        by[shard_of(hash(k))].push((k, c));
    }
    for (d, mut v) in by.into_iter().enumerate() {
        if !v.is_empty() {
            v.sort_unstable_by_key(|e| e.0);
            write_run(&dir.join(format!("{d:04}.{seg}.bin")), &v).expect("write segment");
        }
    }
    Layer::new(dir.to_path_buf(), seg + 1)
}

pub struct StepStats {
    pub states: u64,
    pub bytes: u64,
    pub spilled_records: u64,
}

/// Build segment `seg` of the layer in `dst` from every state of `src`: each state `k` with count
/// `c` sends `c` to every state `f(k)` emits. Keeps at most `cap` states per target shard in
/// memory and spills the rest to sorted runs in `dst/tmp`.
pub fn step(
    src: &Layer,
    dst: &Path,
    seg: usize,
    threads: usize,
    cap: usize,
    f: &(dyn Fn(Key, &mut dyn FnMut(Key)) + Sync),
) -> StepStats {
    let tmp = dst.join("tmp");
    fs::create_dir_all(&tmp).expect("create scratch directory");
    let tables: Vec<Mutex<(Table, Vec<PathBuf>)>> =
        (0..SHARDS).map(|_| Mutex::new((Table::default(), Vec::new()))).collect();
    let run_id = AtomicU64::new(0);
    let spilled = AtomicU64::new(0);
    let claim = AtomicUsize::new(0);
    let spill = |d: usize, table: Table| {
        let entries = table.sorted();
        let id = run_id.fetch_add(1, Ordering::Relaxed);
        let path = tmp.join(format!("{d:04}-{id}.run"));
        write_run(&path, &entries).expect("write run");
        spilled.fetch_add(entries.len() as u64, Ordering::Relaxed);
        tables[d].lock().unwrap().1.push(path);
    };
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut bufs: Vec<Vec<(Key, u64, u128)>> = (0..SHARDS).map(|_| Vec::new()).collect();
                let flush = |d: usize, buf: &mut Vec<(Key, u64, u128)>| {
                    let full = {
                        let mut t = tables[d].lock().unwrap();
                        for &(k, hv, c) in buf.iter() {
                            t.0.add(k, hv, c);
                        }
                        if t.0.len > cap { Some(std::mem::take(&mut t.0)) } else { None }
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
                    src.read_shard(s, |k, c| {
                        f(k, &mut |k2| {
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
                }
                for (d, buf) in bufs.iter_mut().enumerate() {
                    if !buf.is_empty() {
                        flush(d, buf);
                    }
                }
            });
        }
    });
    // Compact: merge each shard's runs and remainder into its segment file.
    let states = AtomicU64::new(0);
    let bytes = AtomicU64::new(0);
    let claim = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                loop {
                    let d = claim.fetch_add(1, Ordering::Relaxed);
                    if d >= SHARDS {
                        break;
                    }
                    let (table, runs) = std::mem::take(&mut *tables[d].lock().unwrap());
                    let rest = table.sorted();
                    if rest.is_empty() && runs.is_empty() {
                        continue;
                    }
                    let (n, b) = merge_into(&dst.join(format!("{d:04}.{seg}.bin")), rest, &runs);
                    states.fetch_add(n, Ordering::Relaxed);
                    bytes.fetch_add(b, Ordering::Relaxed);
                    for p in &runs {
                        let _ = fs::remove_file(p);
                    }
                }
            });
        }
    });
    let _ = fs::remove_dir(&tmp);
    StepStats {
        states: states.load(Ordering::Relaxed),
        bytes: bytes.load(Ordering::Relaxed),
        spilled_records: spilled.load(Ordering::Relaxed),
    }
}

/// Merge a sorted remainder and sorted runs, adding counts of equal states, into one file.
/// Returns (distinct states, bytes).
fn merge_into(path: &Path, rest: Vec<(Key, u128)>, runs: &[PathBuf]) -> (u64, u64) {
    let mut w = Writer::create(path);
    let mut runs: Vec<RunReader> = runs.iter().map(|p| RunReader::open(p)).collect();
    let mut rest = rest.into_iter().peekable();
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
        w.push(k, c);
    }
    w.finish()
}

/// A streaming writer of a sorted varint file (the format of `ooc::write_run`).
struct Writer {
    w: BufWriter<File>,
    prev: Key,
    n: u64,
    bytes: u64,
    buf: Vec<u8>,
}

impl Writer {
    fn create(path: &Path) -> Writer {
        let w = BufWriter::with_capacity(1 << 20, File::create(path).expect("create segment"));
        Writer { w, prev: 0, n: 0, bytes: 0, buf: Vec::with_capacity(32) }
    }

    fn push(&mut self, k: Key, c: u128) {
        debug_assert!(self.n == 0 || k > self.prev);
        self.buf.clear();
        for mut v in [(k - self.prev) as u128, c] {
            while v >= 0x80 {
                self.buf.push((v as u8) | 0x80);
                v >>= 7;
            }
            self.buf.push(v as u8);
        }
        self.w.write_all(&self.buf).expect("write segment");
        self.bytes += self.buf.len() as u64;
        self.prev = k;
        self.n += 1;
    }

    fn finish(mut self) -> (u64, u64) {
        self.w.flush().expect("flush segment");
        (self.n, self.bytes)
    }
}

/// Σ_s a(s) · b(s), by a merge-join of each shard of the two layers.
pub fn dot(a: &Layer, b: &Layer, threads: usize) -> u128 {
    let total = Mutex::new(0u128);
    let claim = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut sum = 0u128;
                loop {
                    let d = claim.fetch_add(1, Ordering::Relaxed);
                    if d >= SHARDS {
                        break;
                    }
                    let mut av: Vec<(Key, u128)> = Vec::new();
                    a.read_shard(d, |k, c| av.push((k, c)));
                    if av.is_empty() {
                        continue;
                    }
                    let mut i = 0;
                    b.read_shard(d, |k, c| {
                        while i < av.len() && av[i].0 < k {
                            i += 1;
                        }
                        if i < av.len() && av[i].0 == k {
                            sum += av[i].1 * c;
                        }
                    });
                }
                *total.lock().unwrap() += sum;
            });
        }
    });
    total.into_inner().unwrap()
}
