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
use crate::word::{Key64 as Key, narrow, successors, widen};
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
    l.iter().map(|t| t.lock().unwrap().entries().count()).sum()
}

/// One parallel step: every state of `src`, with its count, is sent to the states `f` emits.
/// `src` is consumed shard by shard.
fn step(src: Layer, threads: usize, f: &(dyn Fn(Key, &mut dyn FnMut(Key)) + Sync)) -> Layer {
    let next = new_layer();
    let claim = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut bufs: Vec<Vec<(Key, u64, u128)>> = (0..SHARDS).map(|_| Vec::new()).collect();
                let flush = |d: usize, buf: &mut Vec<(Key, u64, u128)>| {
                    let mut t = next[d].lock().unwrap();
                    for &(k, hv, c) in buf.iter() {
                        t.add(k, hv, c);
                    }
                    buf.clear();
                };
                loop {
                    let s = claim.fetch_add(1, Ordering::Relaxed);
                    if s >= SHARDS {
                        break;
                    }
                    let table = std::mem::take(&mut *src[s].lock().unwrap());
                    for (k, c) in table.entries() {
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

/// Σ_s F(s) · G(s), iterating over the smaller layer.
fn dot(f: &Layer, g: &Layer) -> u128 {
    let mut sum = 0u128;
    for (tf, tg) in f.iter().zip(g) {
        let (tf, tg) = (tf.lock().unwrap(), tg.lock().unwrap());
        for (k, c) in tf.entries() {
            sum += c * tg.get(k);
        }
    }
    sum
}

/// The state after `m ≥ 1` bridges from which the east end finishes a river with `m` crossings
/// on side `p = m % 2`: a matched pair of open arcs, one above and one below for `p = 1`, both
/// below for `p = 0` (`G^p_0`). For `p = 0` the empty state also finishes (A(0) = 1).
fn finishers(p: usize) -> Vec<(Key, u128)> {
    let mut w = [0u8; 64];
    w[0] = OPEN;
    w[1] = CLOSE;
    let pair = narrow(encode(&Word { w, len: 2, h: p }));
    if p == 0 { vec![(pair, 1), (narrow(INIT), 1)] } else { vec![(pair, 1)] }
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
    let mut fwd: Vec<Layer> = vec![singleton(&[(narrow(INIT), 1)])];
    let bridge = |k: Key, emit: &mut dyn FnMut(Key)| {
        successors(NO_TARGET, 0, widen(k), |k2| emit(narrow(k2)));
    };
    for _ in 0..kmax {
        let copy: Layer = fwd
            .last()
            .unwrap()
            .iter()
            .map(|t| {
                let t = t.lock().unwrap();
                let mut c = Table::default();
                for (k, v) in t.entries() {
                    c.add(k, hash(k), v);
                }
                Mutex::new(c)
            })
            .collect();
        fwd.push(step(copy, threads, &bridge));
    }
    let fsize: Vec<usize> = fwd.iter().map(layer_size).collect();
    // The two backward families, in turn: the east end below (p = 0) or above (p = 1).
    let mut rows: Vec<Option<Row>> = (0..=horizon).map(|_| None).collect();
    for p in 0..2 {
        let mut g = singleton(&finishers(p));
        let mut r = 0;
        loop {
            // Main split for n = 2r + p, k = r + p; check the n of the previous layer.
            let n = 2 * r + p;
            if n <= horizon {
                let k = r + p;
                rows[n] = Some(Row {
                    n,
                    count: dot(&fwd[k], &g),
                    check: None,
                    forward_states: fsize[k],
                    backward_states: layer_size(&g),
                });
            }
            if r >= 1 && n >= 2 && n - 2 <= horizon && r + p >= 2 {
                let k = r + p - 2;
                if let Some(row) = rows[n - 2].as_mut() {
                    row.check = Some(dot(&fwd[k], &g));
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
            g = step(g, threads, &back);
            r += 1;
        }
    }
    for row in rows.into_iter().flatten() {
        report(&row);
    }
}
