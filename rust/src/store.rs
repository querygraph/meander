//! A persistent store of layers on disk, in a few large files.
//!
//! A layer is a directory. Its states are split into the 4,096 hash shards of `ooc.rs`, and each
//! *segment* of the layer is two files: `seg{s}.dat`, the shards' records one after another, each
//! shard sorted by state and written as varint (state difference, count) records, and
//! `seg{s}.idx`, the byte range of every shard. Segments of one layer hold disjoint sets of
//! states (each comes from one horizon of the meet-in-the-middle store), so reading a shard is a
//! merge of its ranges in the segments.
//!
//! `step` builds a new segment from a source layer. Workers stream source shards, apply a
//! transition, and add the results into capped in-memory tables, one per target shard. A full
//! table is sorted and appended to its worker's single spill file. At the end each target shard's
//! spilled ranges and remainder are merged in memory and appended to the segment file. A step
//! therefore creates one spill file per worker and two files for the segment, and readers open a
//! layer's files once and read ranges with `pread`: few files, mostly sequential writes. (An
//! earlier layout with one file per shard, thousands per layer, created and closed by dozens of
//! threads at once, is the likely cause of a filesystem hang on an HFS+ SoftRAID volume.)

use crate::ooc::{SHARDS, Table, hash, shard_of};
use crate::word::Key64 as Key;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::FileExt;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

const BATCH: usize = 128;
const CHUNK: usize = 1 << 20;
/// Flush a file being appended to every this many bytes, so that the dirty pages waiting
/// for a slow volume stay bounded. (A hard hang of Morrobay, on an HFS+ SoftRAID RAID 5 in a
/// Thunderbolt enclosure, probably began with writes piling up in memory behind a volume that
/// had stopped keeping up.)
const SYNC_BYTES: u64 = 256 << 20;

/// Append `bytes` to a file whose length is `g.1`; returns the offset written at.
fn append(g: &mut (File, u64), bytes: &[u8], what: &str) -> u64 {
    let off = g.1;
    g.0.write_all(bytes).unwrap_or_else(|e| panic!("write {what}: {e}"));
    g.1 += bytes.len() as u64;
    if g.1 / SYNC_BYTES != off / SYNC_BYTES {
        g.0.sync_data().unwrap_or_else(|e| panic!("sync {what}: {e}"));
    }
    off
}

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

/// Free bytes on the filesystem holding `path`.
pub fn free_bytes(path: &Path) -> u64 {
    use std::ffi::CString;
    let c = CString::new(path.as_os_str().as_encoded_bytes()).unwrap();
    unsafe {
        let mut s: libc::statvfs = std::mem::zeroed();
        if libc::statvfs(c.as_ptr(), &mut s) == 0 {
            s.f_bavail as u64 * s.f_frsize as u64
        } else {
            u64::MAX
        }
    }
}

fn put_varint(buf: &mut Vec<u8>, mut v: u128) {
    while v >= 0x80 {
        buf.push((v as u8) | 0x80);
        v >>= 7;
    }
    buf.push(v as u8);
}

/// Append sorted records to `buf` as varint (state difference, count); returns how many.
fn encode(buf: &mut Vec<u8>, entries: impl IntoIterator<Item = (Key, u128)>) -> u64 {
    let mut prev: Key = 0;
    let mut n = 0;
    for (k, c) in entries {
        put_varint(buf, (k - prev) as u128);
        put_varint(buf, c);
        prev = k;
        n += 1;
    }
    n
}

/// A sorted run of records in a byte range of a file, read in chunks with `pread`.
struct RangeReader<'a> {
    file: &'a File,
    pos: u64,
    end: u64,
    buf: Vec<u8>,
    at: usize,
    prev: Key,
    head: Option<(Key, u128)>,
}

impl<'a> RangeReader<'a> {
    /// A reader using a buffer from `pool` (a worker's, so that buffers are reused rather than
    /// mapped and faulted in afresh for every range: on macOS a large allocation is a new
    /// mapping). Return it with `release`.
    fn new(file: &'a File, start: u64, len: u64, pool: &mut Vec<Vec<u8>>) -> RangeReader<'a> {
        let mut buf = pool.pop().unwrap_or_default();
        buf.clear();
        let mut r = RangeReader { file, pos: start, end: start + len, buf, at: 0, prev: 0, head: None };
        r.advance();
        r
    }

    fn release(self, pool: &mut Vec<Vec<u8>>) {
        pool.push(self.buf);
    }

    /// Make at least `need` bytes available, unless the range ends first.
    fn fill(&mut self, need: usize) {
        if self.buf.len() - self.at >= need || self.pos >= self.end {
            return;
        }
        self.buf.drain(..self.at);
        self.at = 0;
        let want = ((self.end - self.pos) as usize).min(CHUNK.max(need));
        let old = self.buf.len();
        self.buf.resize(old + want, 0);
        self.file.read_exact_at(&mut self.buf[old..], self.pos).expect("read segment");
        self.pos += want as u64;
    }

    fn varint(&mut self) -> u128 {
        let (mut v, mut shift) = (0u128, 0);
        loop {
            let b = self.buf[self.at];
            self.at += 1;
            v |= ((b & 0x7f) as u128) << shift;
            if b < 0x80 {
                return v;
            }
            shift += 7;
        }
    }

    fn advance(&mut self) {
        self.fill(48); // a record takes at most 10 + 19 bytes
        if self.at >= self.buf.len() {
            self.head = None;
            return;
        }
        let k = self.prev + self.varint() as Key;
        self.prev = k;
        let c = self.varint();
        self.head = Some((k, c));
    }
}

/// Sort (state, count) pairs by state: an LSD radix sort with 11-bit digits, skipping the
/// digits all states share, in the caller's reused `scratch` (as in OxCaml's store; a
/// comparison sort was the top frame of the store's profile on Morrobay).
pub(crate) fn radix_sort(v: &mut Vec<(Key, u128)>, scratch: &mut Vec<(Key, u128)>) {
    const BITS: u32 = 11;
    const R: usize = 1 << BITS;
    const PASSES: usize = 6; // 66 bits cover the 64-bit keys
    let n = v.len();
    if n <= 1024 {
        v.sort_unstable_by_key(|e| e.0);
        return;
    }
    let mut cnt = vec![0usize; PASSES * R];
    for e in v.iter() {
        for p in 0..PASSES {
            cnt[p * R + ((e.0 >> (p as u32 * BITS)) as usize & (R - 1))] += 1;
        }
    }
    scratch.clear();
    scratch.resize(n, (0, 0));
    let mut in_scratch = false;
    for p in 0..PASSES {
        let c = &mut cnt[p * R..(p + 1) * R];
        if c.contains(&n) {
            continue;
        }
        let mut sum = 0;
        for x in c.iter_mut() {
            let t = *x;
            *x = sum;
            sum += t;
        }
        let shift = p as u32 * BITS;
        let (src, dst) = if in_scratch { (&*scratch, &mut *v) } else { (&*v, &mut *scratch) };
        for e in src.iter() {
            let d = (e.0 >> shift) as usize & (R - 1);
            dst[c[d]] = *e;
            c[d] += 1;
        }
        in_scratch = !in_scratch;
    }
    if in_scratch {
        std::mem::swap(v, scratch);
    }
}

/// Merge sorted runs and a sorted remainder, adding counts of equal states.
fn merge_runs(runs: &mut [RangeReader<'_>], rest: &[(Key, u128)], mut visit: impl FnMut(Key, u128)) {
    let mut rest = rest.iter().copied().peekable();
    loop {
        let mut min = rest.peek().map(|e| e.0);
        for r in runs.iter() {
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
}

/// One segment of a layer: its data file and the byte range of each shard.
struct Segment {
    file: File,
    index: Vec<(u64, u64)>,
}

fn read_index(path: &Path) -> Vec<(u64, u64)> {
    let bytes = fs::read(path).expect("read segment index");
    assert_eq!(bytes.len(), SHARDS * 16, "segment index {}", path.display());
    (0..SHARDS)
        .map(|d| {
            let a = u64::from_le_bytes(bytes[16 * d..16 * d + 8].try_into().unwrap());
            let b = u64::from_le_bytes(bytes[16 * d + 8..16 * d + 16].try_into().unwrap());
            (a, b)
        })
        .collect()
}

/// A layer on disk: a directory and its segments (missing segments are empty).
pub struct Layer {
    segments: Vec<Segment>,
}

impl Layer {
    pub fn new(dir: PathBuf, segments: usize) -> Layer {
        let segs = (0..segments)
            .filter_map(|s| {
                let idx = dir.join(format!("seg{s}.idx"));
                if !idx.exists() {
                    return None;
                }
                let file = File::open(dir.join(format!("seg{s}.dat"))).expect("open segment");
                Some(Segment { file, index: read_index(&idx) })
            })
            .collect();
        Layer { segments: segs }
    }

    /// Visit shard `d` in increasing state order, merging its segments.
    pub fn read_shard(&self, d: usize, pool: &mut Vec<Vec<u8>>, visit: impl FnMut(Key, u128)) {
        let mut runs: Vec<RangeReader<'_>> = Vec::new();
        for s in self.segments.iter().filter(|s| s.index[d].1 > 0) {
            runs.push(RangeReader::new(&s.file, s.index[d].0, s.index[d].1, pool));
        }
        merge_runs(&mut runs, &[], visit);
        for r in runs {
            r.release(pool);
        }
    }
}

/// The number of states in segment `seg` of the layer in `dir`: from `seg{s}.count`, written by
/// `step`, or else estimated from the data size (about 4.5 bytes a record in large layers).
pub fn segment_states(dir: &Path, seg: usize) -> Option<u64> {
    if let Some(n) = fs::read_to_string(dir.join(format!("seg{seg}.count"))).ok().and_then(|t| t.trim().parse().ok()) {
        return Some(n);
    }
    let len = fs::metadata(dir.join(format!("seg{seg}.dat"))).ok()?.len();
    Some((len as f64 / 4.5) as u64)
}

/// How many passes `step` should make so that a layer of about `states` states fits its
/// tables of `cap` states per shard without spilling (a fifth to spare), at most 16.
pub fn passes_for(states: u64, cap: usize) -> usize {
    let per_pass = (SHARDS as f64) * cap as f64 / 1.2;
    ((states as f64 / per_pass).ceil() as usize).clamp(1, 16)
}

/// Remove segment `seg` of the layer in `dir`, if present.
pub fn remove_segment(dir: &Path, seg: usize) {
    let _ = fs::remove_file(dir.join(format!("seg{seg}.count")));
    let _ = fs::remove_file(dir.join(format!("seg{seg}.idx")));
    let _ = fs::remove_file(dir.join(format!("seg{seg}.dat")));
}

/// Writes the shards of one segment into its data file, in any order, and then its index.
struct SegmentWriter {
    dat: Mutex<(File, u64)>,
    index: Mutex<Vec<(u64, u64)>>,
    dir: PathBuf,
    seg: usize,
}

impl SegmentWriter {
    fn create(dir: &Path, seg: usize) -> SegmentWriter {
        fs::create_dir_all(dir).expect("create layer directory");
        remove_segment(dir, seg);
        let f = File::create(dir.join(format!("seg{seg}.dat"))).expect("create segment");
        SegmentWriter { dat: Mutex::new((f, 0)), index: Mutex::new(vec![(0, 0); SHARDS]), dir: dir.to_path_buf(), seg }
    }

    fn put(&self, d: usize, bytes: &[u8]) {
        if bytes.is_empty() {
            return;
        }
        let off = {
            let mut g = self.dat.lock().unwrap();
            append(&mut g, bytes, "segment")
        };
        self.index.lock().unwrap()[d] = (off, bytes.len() as u64);
    }

    /// Flush the data, then publish the index: a segment exists once its index does.
    fn finish(self) -> u64 {
        let (f, len) = self.dat.into_inner().unwrap();
        f.sync_all().expect("sync segment");
        let mut buf = Vec::with_capacity(SHARDS * 16);
        for (a, b) in self.index.into_inner().unwrap() {
            buf.extend_from_slice(&a.to_le_bytes());
            buf.extend_from_slice(&b.to_le_bytes());
        }
        let tmp = self.dir.join(format!("seg{}.idx.tmp", self.seg));
        fs::write(&tmp, &buf).expect("write segment index");
        fs::rename(&tmp, self.dir.join(format!("seg{}.idx", self.seg))).expect("publish segment index");
        len
    }
}

/// Write the given states as segment `seg` of the layer in `dir`.
pub fn write_states(dir: &Path, seg: usize, states: &[(Key, u128)]) {
    let w = SegmentWriter::create(dir, seg);
    let mut by: Vec<Vec<(Key, u128)>> = (0..SHARDS).map(|_| Vec::new()).collect();
    for &(k, c) in states {
        by[shard_of(hash(k))].push((k, c));
    }
    for (d, mut v) in by.into_iter().enumerate() {
        v.sort_unstable_by_key(|e| e.0);
        let mut buf = Vec::new();
        encode(&mut buf, v);
        w.put(d, &buf);
    }
    w.finish();
}

pub struct StepStats {
    pub states: u64,
    pub bytes: u64,
    pub spilled_records: u64,
}

/// Build segment `seg` of the layer in `dst` from every state of `src`: each state `k` with count
/// `c` sends `c` to every state `f(k)` emits. Keeps at most `cap` states per target shard in
/// memory and spills the rest as sorted ranges of one file per worker under `dst/tmp`.
///
/// With `passes > 1` the target shards are built in that many contiguous groups, one per pass
/// over the whole source: each pass applies `f` to every state again but keeps only the targets
/// in its group. Only that group's tables exist, so each may hold `passes * cap` states in the
/// memory that `cap` gives all of them, and a layer too big for the tables is built with little
/// or no spilling. A pass costs a read
/// of the source and the transitions; a spilled record costs a write, a read and a merge, and
/// the scratch space.
///
/// `after_read` runs once the source has been read in full for the last time, before the last
/// compaction (a caller that no longer needs the source can delete it there, so source and
/// result are never both whole on disk).
#[allow(clippy::too_many_arguments)]
pub fn step(
    src: Layer,
    dst: &Path,
    seg: usize,
    threads: usize,
    cap: usize,
    passes: usize,
    f: &(dyn Fn(Key, &mut dyn FnMut(Key)) + Sync),
    after_read: &mut dyn FnMut(),
) -> StepStats {
    let passes = passes.clamp(1, SHARDS);
    // Only the tables of one pass's shards exist at a time, so each may hold `passes` times
    // as many states in the same memory.
    let cap = cap * passes;
    let tmp = dst.join("tmp");
    let _ = fs::remove_dir_all(&tmp); // left by an interrupted step
    fs::create_dir_all(&tmp).expect("create scratch directory");
    let writer = SegmentWriter::create(dst, seg);
    let states = AtomicU64::new(0);
    let spilled = AtomicU64::new(0);
    let mut src = Some(src);
    for pass in 0..passes {
        let (lo, hi) = (pass * SHARDS / passes, (pass + 1) * SHARDS / passes);
        let spills: Vec<Mutex<(File, u64)>> = (0..threads)
            .map(|w| {
                let f = OpenOptions::new()
                    .create(true)
                    .truncate(true)
                    .read(true)
                    .write(true)
                    .open(tmp.join(format!("w{w}.spill")))
                    .expect("create spill file");
                Mutex::new((f, 0))
            })
            .collect();
        // Per target shard: the in-memory table and its spilled ranges (worker, offset, length).
        let tables: Vec<Mutex<(Table, Vec<(usize, u64, u64)>)>> =
            (0..SHARDS).map(|_| Mutex::new((Table::default(), Vec::new()))).collect();
        let claim = AtomicUsize::new(0);
        let worker_id = AtomicUsize::new(0);
        let source = src.as_ref().unwrap();
        std::thread::scope(|sc| {
            for _ in 0..threads {
                sc.spawn(|| {
                    let me = worker_id.fetch_add(1, Ordering::Relaxed);
                    let mut bufs: Vec<Vec<(Key, u64, u128)>> = (0..SHARDS).map(|_| Vec::new()).collect();
                    let mut bytes = Vec::new();
                    let mut pool: Vec<Vec<u8>> = Vec::new();
                    // A full table is swapped, under its lock, for this worker's spare (an
                    // emptied table of the same size, once it has one), and drained, sorted
                    // and encoded outside the lock in buffers the worker reuses.
                    let mut spare = Table::default();
                    let mut ents: Vec<(Key, u128)> = Vec::new();
                    let mut scratch: Vec<(Key, u128)> = Vec::new();
                    let mut flush = |d: usize, buf: &mut Vec<(Key, u64, u128)>| {
                        let full = {
                            let mut t = tables[d].lock().unwrap();
                            for &(k, hv, c) in buf.iter() {
                                t.0.add(k, hv, c);
                            }
                            if t.0.len > cap {
                                std::mem::swap(&mut t.0, &mut spare);
                                true
                            } else {
                                false
                            }
                        };
                        buf.clear();
                        if full {
                            ents.clear();
                            spare.drain_into(&mut ents);
                            radix_sort(&mut ents, &mut scratch);
                            bytes.clear();
                            spilled.fetch_add(encode(&mut bytes, ents.iter().copied()), Ordering::Relaxed);
                            let off = {
                                let mut g = spills[me].lock().unwrap();
                                append(&mut g, &bytes, "spill")
                            };
                            tables[d].lock().unwrap().1.push((me, off, bytes.len() as u64));
                        }
                    };
                    loop {
                        let s = claim.fetch_add(1, Ordering::Relaxed);
                        if s >= SHARDS {
                            break;
                        }
                        source.read_shard(s, &mut pool, |k, c| {
                            f(k, &mut |k2| {
                                let hv = hash(k2);
                                let d = shard_of(hv);
                                if d < lo || d >= hi {
                                    return;
                                }
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
                    for d in lo..hi {
                        if !bufs[d].is_empty() {
                            let mut b = std::mem::take(&mut bufs[d]);
                            flush(d, &mut b);
                        }
                    }
                });
            }
        });
        if pass + 1 == passes {
            src = None;
            after_read();
        }
        let spill_files: Vec<File> = spills.into_iter().map(|m| m.into_inner().unwrap().0).collect();
        // Compact: merge each shard's spilled ranges and remainder, and append it to the segment.
        let claim = AtomicUsize::new(lo);
        std::thread::scope(|sc| {
            for _ in 0..threads {
                sc.spawn(|| {
                    let mut out = Vec::new();
                    let mut pool: Vec<Vec<u8>> = Vec::new();
                    let mut rest: Vec<(Key, u128)> = Vec::new();
                    let mut scratch: Vec<(Key, u128)> = Vec::new();
                    loop {
                        let d = claim.fetch_add(1, Ordering::Relaxed);
                        if d >= hi {
                            break;
                        }
                        let (table, ranges) = std::mem::take(&mut *tables[d].lock().unwrap());
                        rest.clear();
                        rest.extend(table.entries());
                        drop(table);
                        if rest.is_empty() && ranges.is_empty() {
                            continue;
                        }
                        radix_sort(&mut rest, &mut scratch);
                        let mut runs: Vec<RangeReader<'_>> = Vec::with_capacity(ranges.len());
                        for &(w, off, len) in &ranges {
                            runs.push(RangeReader::new(&spill_files[w], off, len, &mut pool));
                        }
                        out.clear();
                        let mut prev: Key = 0;
                        let mut n = 0u64;
                        merge_runs(&mut runs, &rest, |k, c| {
                            put_varint(&mut out, (k - prev) as u128);
                            put_varint(&mut out, c);
                            prev = k;
                            n += 1;
                        });
                        for r in runs {
                            r.release(&mut pool);
                        }
                        states.fetch_add(n, Ordering::Relaxed);
                        writer.put(d, &out);
                    }
                });
            }
        });
    }
    drop(src);
    let bytes = writer.finish();
    let states = states.load(Ordering::Relaxed);
    let _ = fs::write(dst.join(format!("seg{seg}.count")), format!("{states}\n"));
    let _ = fs::remove_dir_all(&tmp);
    StepStats { states, bytes, spilled_records: spilled.load(Ordering::Relaxed) }
}

/// Σ_s a(s) · b(s), by a merge-join of each shard of the two layers.
pub fn dot(a: &Layer, b: &Layer, threads: usize) -> u128 {
    let total = Mutex::new(0u128);
    let claim = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut sum = 0u128;
                let mut pool: Vec<Vec<u8>> = Vec::new();
                let mut av: Vec<(Key, u128)> = Vec::new();
                loop {
                    let d = claim.fetch_add(1, Ordering::Relaxed);
                    if d >= SHARDS {
                        break;
                    }
                    av.clear();
                    a.read_shard(d, &mut pool, |k, c| av.push((k, c)));
                    if av.is_empty() {
                        continue;
                    }
                    let mut i = 0;
                    b.read_shard(d, &mut pool, |k, c| {
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
