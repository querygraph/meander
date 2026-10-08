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
    fn new(file: &'a File, start: u64, len: u64) -> RangeReader<'a> {
        let mut r = RangeReader { file, pos: start, end: start + len, buf: Vec::new(), at: 0, prev: 0, head: None };
        r.advance();
        r
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

/// Merge sorted runs and a sorted remainder, adding counts of equal states.
fn merge_runs(mut runs: Vec<RangeReader<'_>>, rest: Vec<(Key, u128)>, mut visit: impl FnMut(Key, u128)) {
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
    pub fn read_shard(&self, d: usize, visit: impl FnMut(Key, u128)) {
        let runs = self
            .segments
            .iter()
            .filter(|s| s.index[d].1 > 0)
            .map(|s| RangeReader::new(&s.file, s.index[d].0, s.index[d].1))
            .collect();
        merge_runs(runs, Vec::new(), visit);
    }
}

/// Remove segment `seg` of the layer in `dir`, if present.
pub fn remove_segment(dir: &Path, seg: usize) {
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
            let off = g.1;
            g.0.write_all(bytes).expect("write segment");
            g.1 += bytes.len() as u64;
            off
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
/// `after_read` runs once the source has been read in full, before compaction (a caller that
/// no longer needs the source can delete it there, so source and result are never both whole on
/// disk).
pub fn step(
    src: Layer,
    dst: &Path,
    seg: usize,
    threads: usize,
    cap: usize,
    f: &(dyn Fn(Key, &mut dyn FnMut(Key)) + Sync),
    after_read: &mut dyn FnMut(),
) -> StepStats {
    let tmp = dst.join("tmp");
    let _ = fs::remove_dir_all(&tmp); // left by an interrupted step
    fs::create_dir_all(&tmp).expect("create scratch directory");
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
    let spilled = AtomicU64::new(0);
    let claim = AtomicUsize::new(0);
    let worker_id = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let me = worker_id.fetch_add(1, Ordering::Relaxed);
                let mut bufs: Vec<Vec<(Key, u64, u128)>> = (0..SHARDS).map(|_| Vec::new()).collect();
                let mut bytes = Vec::new();
                let mut flush = |d: usize, buf: &mut Vec<(Key, u64, u128)>| {
                    let full = {
                        let mut t = tables[d].lock().unwrap();
                        for &(k, hv, c) in buf.iter() {
                            t.0.add(k, hv, c);
                        }
                        if t.0.len > cap { Some(std::mem::take(&mut t.0)) } else { None }
                    };
                    buf.clear();
                    if let Some(t) = full {
                        bytes.clear();
                        spilled.fetch_add(encode(&mut bytes, t.sorted()), Ordering::Relaxed);
                        let off = {
                            let mut g = spills[me].lock().unwrap();
                            let off = g.1;
                            g.0.write_all(&bytes).expect("write spill");
                            g.1 += bytes.len() as u64;
                            off
                        };
                        tables[d].lock().unwrap().1.push((me, off, bytes.len() as u64));
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
                for d in 0..SHARDS {
                    if !bufs[d].is_empty() {
                        let mut b = std::mem::take(&mut bufs[d]);
                        flush(d, &mut b);
                    }
                }
            });
        }
    });
    drop(src);
    after_read();
    let spill_files: Vec<File> = spills.into_iter().map(|m| m.into_inner().unwrap().0).collect();
    // Compact: merge each shard's spilled ranges and remainder, and append it to the segment.
    let writer = SegmentWriter::create(dst, seg);
    let states = AtomicU64::new(0);
    let claim = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut out = Vec::new();
                loop {
                    let d = claim.fetch_add(1, Ordering::Relaxed);
                    if d >= SHARDS {
                        break;
                    }
                    let (table, ranges) = std::mem::take(&mut *tables[d].lock().unwrap());
                    let rest = table.sorted();
                    if rest.is_empty() && ranges.is_empty() {
                        continue;
                    }
                    let runs: Vec<RangeReader<'_>> =
                        ranges.iter().map(|&(w, off, len)| RangeReader::new(&spill_files[w], off, len)).collect();
                    out.clear();
                    let mut prev: Key = 0;
                    let mut n = 0u64;
                    merge_runs(runs, rest, |k, c| {
                        put_varint(&mut out, (k - prev) as u128);
                        put_varint(&mut out, c);
                        prev = k;
                        n += 1;
                    });
                    states.fetch_add(n, Ordering::Relaxed);
                    writer.put(d, &out);
                }
            });
        }
    });
    let bytes = writer.finish();
    drop(spill_files);
    let _ = fs::remove_dir_all(&tmp);
    StepStats { states: states.load(Ordering::Relaxed), bytes, spilled_records: spilled.load(Ordering::Relaxed) }
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
