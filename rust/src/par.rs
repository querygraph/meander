//! The parallel layer sweep.
//!
//! A layer is split into `SHARDS` hash shards, each an open-addressing table behind its own
//! lock. For each point, worker threads claim source shards from an atomic counter, generate
//! the viable successors of every state, and batch them into per-shard buffers. A full buffer
//! is added into its target shard under that shard's lock. A source shard is freed as soon as
//! it has been read, so the sweep holds little more than one layer at a time.
//!
//! States are stored as 64-bit keys (`word::narrow`) and counts modulo a 64-bit modulus, 16
//! bytes per state. `count` runs the sweep modulo `2^64` and, when the answer may not fit, again modulo the
//! Mersenne prime `2^61 - 1`, and recovers the exact count by the Chinese remainder theorem.

use crate::state::{INIT, final_key};
use crate::word::{Key64 as Key, narrow, successors, widen};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

const SHARD_BITS: u32 = 12;
pub const SHARDS: usize = 1 << SHARD_BITS;
const BATCH: usize = 128;
const MAX_LOAD: f64 = 0.8;
const P61: u64 = (1 << 61) - 1;

#[inline(always)]
fn addm<const M61: bool>(a: u64, b: u64) -> u64 {
    if M61 {
        let s = a + b; // both < 2^61
        if s >= P61 { s - P61 } else { s }
    } else {
        a.wrapping_add(b)
    }
}

#[inline(always)]
fn hash(k: Key) -> u64 {
    let p = (k as u128).wrapping_mul(0x9E37_79B9_7F4A_7C15_u128);
    (p as u64) ^ ((p >> 64) as u64)
}

#[inline(always)]
fn shard_of(hv: u64) -> usize {
    (hv >> (64 - SHARD_BITS)) as usize
}

/// An open-addressing table of `(state, count)` with linear probing, keys and counts in
/// separate arrays. A slot stores `key + 1`, so an empty slot is `0` and a new table is lazily
/// zeroed memory. Tables start small and grow by half when 80% full, so a layer is built while
/// the previous one is freed shard by shard. The size need not be a power of two.
#[derive(Default)]
pub struct Table {
    keys: Vec<Key>,
    cnts: Vec<u64>,
    len: usize,
}

impl Table {
    fn with_slots(slots: usize) -> Table {
        Table { keys: vec![0; slots], cnts: vec![0; slots], len: 0 }
    }

    #[inline(always)]
    fn slot(&self, hv: u64) -> usize {
        (((hv << SHARD_BITS) as u128 * self.keys.len() as u128) >> 64) as usize
    }

    #[inline(always)]
    fn add<const M61: bool>(&mut self, k: Key, hv: u64, c: u64) {
        let k = k + 1;
        if (self.len + 1) as f64 > self.keys.len() as f64 * MAX_LOAD {
            self.grow::<M61>();
        }
        let n = self.keys.len();
        let mut i = self.slot(hv);
        loop {
            let ki = unsafe { *self.keys.get_unchecked(i) };
            if ki == k {
                let ci = unsafe { self.cnts.get_unchecked_mut(i) };
                *ci = addm::<M61>(*ci, c);
                return;
            }
            if ki == 0 {
                unsafe {
                    *self.keys.get_unchecked_mut(i) = k;
                    *self.cnts.get_unchecked_mut(i) = c;
                }
                self.len += 1;
                return;
            }
            i += 1;
            if i == n {
                i = 0;
            }
        }
    }

    fn grow<const M61: bool>(&mut self) {
        let old = std::mem::replace(self, Table::with_slots((self.keys.len() * 3 / 2).max(64)));
        for (k, c) in old.iter() {
            self.add::<M61>(k, hash(k), c);
        }
    }

    fn iter(&self) -> impl Iterator<Item = (Key, u64)> + '_ {
        self.keys.iter().copied().zip(self.cnts.iter().copied()).filter(|s| s.0 != 0).map(|(k, c)| (k - 1, c))
    }

    fn get(&self, k: Key) -> u64 {
        self.iter().find(|s| s.0 == k).map_or(0, |s| s.1)
    }
}

pub struct Stats {
    pub count: u128,
    pub peak_states: usize,
    pub total_states: usize,
}

/// One sweep for `m` crossings, with counts modulo `2^64` or `2^61 - 1`.
fn sweep<const M61: bool>(m: usize, threads: usize) -> (u64, usize, usize) {
    let mut layer: Vec<Mutex<Table>> = (0..SHARDS).map(|_| Mutex::new(Table::default())).collect();
    let init = narrow(INIT);
    layer[shard_of(hash(init))].lock().unwrap().add::<M61>(init, hash(init), 1);
    let (mut peak, mut total) = (1usize, 0usize);
    for x in 0..=m {
        let next: Vec<Mutex<Table>> = (0..SHARDS).map(|_| Mutex::new(Table::default())).collect();
        let claim = AtomicUsize::new(0);
        std::thread::scope(|sc| {
            for _ in 0..threads {
                sc.spawn(|| {
                    let mut bufs: Vec<Vec<(Key, u64, u64)>> =
                        (0..SHARDS).map(|_| Vec::new()).collect();
                    let flush = |d: usize, buf: &mut Vec<(Key, u64, u64)>| {
                        let mut t = next[d].lock().unwrap();
                        for &(k, hv, c) in buf.iter() {
                            t.add::<M61>(k, hv, c);
                        }
                        buf.clear();
                    };
                    loop {
                        let s = claim.fetch_add(1, Ordering::Relaxed);
                        if s >= SHARDS {
                            break;
                        }
                        let src = std::mem::take(&mut *layer[s].lock().unwrap());
                        for (k, c) in src.iter() {
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
                        }
                    }
                    for (d, buf) in bufs.iter_mut().enumerate() {
                        if !buf.is_empty() {
                            flush(d, buf);
                        }
                    }
                });
            }
        });
        layer = next;
        let size: usize = layer.iter().map(|t| t.lock().unwrap().len).sum();
        peak = peak.max(size);
        total += size;
    }
    let f = narrow(final_key());
    let c = layer[shard_of(hash(f))].lock().unwrap().get(f);
    (c, peak, total)
}

/// The `x < 2^125` with `x ≡ a (mod 2^64)` and `x ≡ b (mod 2^61 - 1)`.
pub fn crt(a: u64, b: u64) -> u128 {
    // 2^64 ≡ 8 (mod p), and 8 · 2^58 = 2^61 ≡ 1, so 2^-64 ≡ 2^58.
    let am = a % P61;
    let t = ((b + P61 - am) % P61) as u128 * (1u128 << 58) % P61 as u128;
    a as u128 + (t << 64)
}

/// Count the meanders with `m` crossings on `threads` threads. A second sweep modulo
/// `2^61 - 1` runs only when the count might reach `2^64` (`m ≥ 44`; A005316(44) < 2^64).
pub fn count(m: usize, threads: usize, force_two: bool) -> Stats {
    let (a, peak, total) = sweep::<false>(m, threads);
    let count = if m >= 44 || force_two {
        let (b, _, _) = sweep::<true>(m, threads);
        crt(a, b)
    } else {
        a as u128
    };
    Stats { count, peak_states: peak, total_states: total }
}
