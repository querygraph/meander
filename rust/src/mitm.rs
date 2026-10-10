//! Meet in the middle: A(n) = Σ_s F_k(s) · G^p_r(s) for every split n = k + r (`meet` in
//! `Arnold/TM/Middle.lean`).
//!
//! * `F_k`, the forward layer after `k` bridges, mentions no target: it is computed once, with no
//!   pruning, by the bridge steps of `word::successors`.
//! * `G^p_r(s)`, the number of ways to finish from `s` with `r` more bridges and then the east end
//!   on side `p` (`finish p r` in Lean), is computed backwards from `G^p_0` by the inverse
//!   transitions `state::predecessors`. For a horizon `B` (the largest `n` wanted) a state is kept
//!   in `G_r` only if some forward layer can meet it, `depth(s) ≤ B − r`. Dropping the others is
//!   exact: a state's predecessors are at least as deep, minus one, so a dropped state never
//!   feeds a kept one.
//!
//! Each backward layer `G^p_r` gives A(n) for `n = 2r + p` (the split `k = r + p`) and checks
//! the A(n − 2) of the previous layer through a second split, `k = r + p − 2`. Only the current
//! backward layer and the small forward layers are held at once.

use crate::ooc::{SHARDS, Table, hash, shard_of};
use crate::state::{CLOSE, INIT, OPEN, Word, encode};
use crate::bits::Key;
use crate::word::successors;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

const BATCH: usize = 128;
/// A target large enough that viability never prunes: every forward step is a bridge step.
const NO_TARGET: usize = 120;

type Layer = Vec<Mutex<Table>>;

fn new_layer() -> Layer {
    (0..SHARDS).map(|_| Mutex::new(Table::default())).collect()
}

fn layer_size(l: &Layer) -> usize {
    l.iter().map(|t| t.lock().unwrap().len).sum()
}

/// One parallel step: every state of `src`, with its count, is sent to the states `f` emits.
/// With `consume`, `src` is emptied shard by shard as it is read (its memory freed as the next
/// layer grows); otherwise it is kept (the forward layers serve every split).
///
/// Each target table is allocated by the first worker to insert into it, at `slots` slots
/// (predicted from the layer sizes, as in OxCaml's driver and `par.rs --presize`), so tables
/// rarely rehash and the zeroing is spread over the workers.
fn step(src: &Layer, consume: bool, slots: usize, threads: usize, f: &(dyn Fn(Key, &mut dyn FnMut(Key)) + Sync)) -> Layer {
    let next = new_layer();
    let claim = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut bufs: Vec<Vec<(Key, u64, u128)>> = (0..SHARDS).map(|_| Vec::new()).collect();
                let flush = |d: usize, buf: &mut Vec<(Key, u64, u128)>| {
                    let mut t = next[d].lock().unwrap();
                    if t.unallocated() {
                        *t = Table::with_slots(slots);
                    }
                    for &(k, hv, c) in buf.iter() {
                        t.add(k, hv, c);
                    }
                    buf.clear();
                };
                let mut visit = |k: Key, c: u128| {
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
                };
                loop {
                    let s = claim.fetch_add(1, Ordering::Relaxed);
                    if s >= SHARDS {
                        break;
                    }
                    if consume {
                        let table = std::mem::take(&mut *src[s].lock().unwrap());
                        for (k, c) in table.entries() {
                            visit(k, c);
                        }
                    } else {
                        let table = src[s].lock().unwrap();
                        for (k, c) in table.entries() {
                            visit(k, c);
                        }
                    }
                }
                drop(visit);
                for (d, buf) in bufs.iter_mut().enumerate() {
                    if !buf.is_empty() {
                        flush(d, buf);
                    }
                }
            });
        }
    });
    next
}

fn singleton(entries: &[(Key, u128)]) -> Layer {
    let l = new_layer();
    for &(k, c) in entries {
        let hv = hash(k);
        l[shard_of(hv)].lock().unwrap().add(k, hv, c);
    }
    l
}

/// Σ_s F(s) · G(s), shard by shard on all threads.
fn dot(f: &Layer, g: &Layer, threads: usize) -> u128 {
    let total = std::sync::Mutex::new(0u128);
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
                    let (tf, tg) = (f[d].lock().unwrap(), g[d].lock().unwrap());
                    let (small, big) = if tf.len <= tg.len { (&tf, &tg) } else { (&tg, &tf) };
                    for (k, c) in small.entries() {
                        sum += c * big.get(k);
                    }
                }
                *total.lock().unwrap() += sum;
            });
        }
    });
    total.into_inner().unwrap()
}

/// The state after `m ≥ 1` bridges from which the east end finishes a river with `m` crossings
/// on side `p = m % 2`: a matched pair of open arcs, one above and one below for `p = 1`, both
/// below for `p = 0` (`G^p_0`). For `p = 0` the empty state also finishes (A(0) = 1).
fn finishers(p: usize) -> Vec<(Key, u128)> {
    let mut w = [0u8; 64];
    w[0] = OPEN;
    w[1] = CLOSE;
    let pair = crate::bits::from_state(encode(&Word { w, len: 2, h: p }));
    if p == 0 { vec![(pair, 1), (crate::bits::from_state(INIT), 1)] } else { vec![(pair, 1)] }
}

pub struct Row {
    pub n: usize,
    pub count: u128,
    /// The same count through a second split, when one was available.
    pub check: Option<u128>,
    pub forward_states: usize,
    pub backward_states: usize,
}

/// A(n) for every n ≤ `horizon`, each by the split `k = ⌈n/2⌉` and checked by `k − 1`.
pub fn run(horizon: usize, threads: usize, mut report: impl FnMut(&Row)) {
    let kmax = horizon - horizon / 2;
    // Forward layers: small, kept for the whole run.
    let mut fwd: Vec<Layer> = vec![singleton(&[(crate::bits::from_state(INIT), 1)])];
    let bridge = |k: Key, emit: &mut dyn FnMut(Key)| {
        successors(NO_TARGET, 0, crate::bits::to_state(k), |k2| emit(crate::bits::from_state(k2)));
    };
    // Layer sizes, newest last, for predicting the next layer's table size.
    let predict = |sizes: &[usize]| -> usize {
        match sizes {
            [.., p2, p, s] => crate::par::predict_slots(*s, *p, *p2),
            [.., p, s] => crate::par::predict_slots(*s, *p, 0),
            [s] => crate::par::predict_slots(*s, 0, 0),
            [] => 64,
        }
    };
    let mut fsize: Vec<usize> = vec![1];
    for _ in 0..kmax {
        let next = step(fwd.last().unwrap(), false, predict(&fsize), threads, &bridge);
        fsize.push(layer_size(&next));
        fwd.push(next);
    }
    // The two backward families, in turn: the east end below (p = 0) or above (p = 1).
    let mut rows: Vec<Option<Row>> = (0..=horizon).map(|_| None).collect();
    for p in 0..2 {
        let mut g = singleton(&finishers(p));
        let mut gsize: Vec<usize> = vec![layer_size(&g)];
        let mut r = 0;
        loop {
            // Main split for n = 2r + p, k = r + p; check the n of the previous layer.
            let n = 2 * r + p;
            if n <= horizon {
                let k = r + p;
                rows[n] = Some(Row {
                    n,
                    count: dot(&fwd[k], &g, threads),
                    check: None,
                    forward_states: fsize[k],
                    backward_states: *gsize.last().unwrap(),
                });
            }
            if r >= 1 && n >= 2 && n - 2 <= horizon && r + p >= 2 {
                let k = r + p - 2;
                if let Some(row) = rows[n - 2].as_mut() {
                    row.check = Some(dot(&fwd[k], &g, threads));
                }
            }
            if n >= horizon + 2 {
                break;
            }
            // G_{r+1}: predecessors, kept if a forward layer can still meet them.
            let bound = horizon.saturating_sub(r + 1);
            let back = move |k: Key, emit: &mut dyn FnMut(Key)| {
                crate::bits::predecessors(k, bound, |t| emit(t));
            };
            g = step(&g, true, predict(&gsize), threads, &back);
            gsize.push(layer_size(&g));
            r += 1;
        }
    }
    for row in rows.into_iter().flatten() {
        report(&row);
    }
}
