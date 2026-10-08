//! The stepwise meet-in-the-middle store: every layer kept on disk, every count computed once.
//!
//! A store at `root` holds the forward layers `F/k`, the backward layers `G{p}/r` for both sides
//! `p` of the east end, a `manifest` and the computed `values`. A store is built for a list of
//! increasing horizons B₀ < B₁ < …: segment `i` of a backward layer `G^p_r` holds the states with
//! `B_{i−1} − r < depth ≤ B_i − r` (all states with `depth ≤ B₀ − r` for `i = 0`).
//!
//! `extend(root, B')` raises the horizon from `B` to `B'`. The forward layers grow by the missing
//! ones (they mention no target). In every backward layer it adds one segment: the states newly
//! admitted by `B'`, pushed from all of the previous layer by the inverse transitions. Values of
//! existing states never change (their successors are no deeper than they are, plus one, so they
//! never involve new states), so nothing is recomputed. Then each new A(n), `B < n ≤ B'`, is the
//! dot product `F_{⌈n/2⌉} · G^{n%2}_{⌊n/2⌋}` (`meet` in `Arnold/TM/Middle.lean`), checked by the
//! second split `F_{⌈n/2⌉−1} · G_{⌊n/2⌋+1}`.

use crate::state::{CLOSE, INIT, OPEN, Word, encode};
use crate::store::{self, Layer};
use crate::bits::Key;
use crate::word::successors;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

const NO_TARGET: usize = 120;

/// What the store holds, saved in `manifest` as `key value` lines.
#[derive(Default, Debug)]
struct Manifest {
    horizons: Vec<usize>,
    kmax: usize,
    /// For each side p: the largest r whose layer is complete for the last horizon.
    rmax: [usize; 2],
    /// An extension in progress: target horizon, and per side the last finished r.
    partial: Option<(usize, [usize; 2])>,
    /// Backward layers were deleted once used, so the store cannot be extended.
    discarded: bool,
}

impl Manifest {
    fn load(root: &Path) -> Manifest {
        let mut m = Manifest::default();
        let Ok(text) = fs::read_to_string(root.join("manifest")) else { return m };
        for line in text.lines() {
            let mut it = line.split_whitespace();
            match (it.next(), it.next()) {
                (Some("horizons"), Some(v)) => {
                    m.horizons = v.split(',').filter(|s| !s.is_empty()).map(|s| s.parse().unwrap()).collect()
                }
                (Some("kmax"), Some(v)) => m.kmax = v.parse().unwrap(),
                (Some("rmax0"), Some(v)) => m.rmax[0] = v.parse().unwrap(),
                (Some("rmax1"), Some(v)) => m.rmax[1] = v.parse().unwrap(),
                (Some("discarded"), Some(v)) => m.discarded = v == "1",
                (Some("partial"), Some(v)) => {
                    let p: Vec<usize> = v.split(',').map(|s| s.parse().unwrap()).collect();
                    m.partial = Some((p[0], [p[1], p[2]]));
                }
                _ => {}
            }
        }
        m
    }

    fn save(&self, root: &Path) {
        let mut s = String::from("format meanders-mitm-1\n");
        let hs: Vec<String> = self.horizons.iter().map(|h| h.to_string()).collect();
        s += &format!("horizons {}\nkmax {}\nrmax0 {}\nrmax1 {}\n", hs.join(","), self.kmax, self.rmax[0], self.rmax[1]);
        if let Some((b, done)) = self.partial {
            s += &format!("partial {b},{},{}\n", done[0], done[1]);
        }
        if self.discarded {
            s += "discarded 1\n";
        }
        let tmp = root.join("manifest.tmp");
        fs::write(&tmp, s).expect("write manifest");
        fs::rename(tmp, root.join("manifest")).expect("replace manifest");
    }
}

fn load_values(root: &Path) -> BTreeMap<usize, (u128, Option<u128>)> {
    let mut v = BTreeMap::new();
    if let Ok(text) = fs::read_to_string(root.join("values")) {
        for line in text.lines().filter(|l| !l.starts_with('#')) {
            let f: Vec<&str> = line.split('\t').collect();
            let check = if f[2] == "-" { None } else { Some(f[2].parse().unwrap()) };
            v.insert(f[0].parse().unwrap(), (f[1].parse().unwrap(), check));
        }
    }
    v
}

fn save_values(root: &Path, v: &BTreeMap<usize, (u128, Option<u128>)>) {
    let mut s = String::from("# n\tcount\tcheck (the same count through a second split)\n");
    for (n, (c, k)) in v {
        s += &format!("{n}\t{c}\t{}\n", k.map_or("-".to_string(), |k| k.to_string()));
    }
    let tmp = root.join("values.tmp");
    fs::write(&tmp, s).expect("write values");
    fs::rename(tmp, root.join("values")).expect("replace values");
}

fn fdir(root: &Path, k: usize) -> PathBuf {
    root.join("F").join(format!("{k:03}"))
}

fn gdir(root: &Path, p: usize, r: usize) -> PathBuf {
    root.join(format!("G{p}")).join(format!("{r:03}"))
}

/// `G^p_0`: the states from which the east end on side `p` finishes (`finish p 0` in Lean).
fn finishers(p: usize) -> Vec<(Key, u128)> {
    let mut w = [0u8; 64];
    w[0] = OPEN;
    w[1] = CLOSE;
    let pair = crate::bits::from_state(encode(&Word { w, len: 2, h: p }));
    if p == 0 { vec![(pair, 1), (crate::bits::from_state(INIT), 1)] } else { vec![(pair, 1)] }
}

/// How a run treats its layers and the disk.
#[derive(Clone, Copy)]
pub struct Options {
    pub threads: usize,
    /// States per shard kept in memory before spilling.
    pub cap: usize,
    /// Delete each backward layer as soon as the next one has read it: far less disk, but the
    /// store cannot be extended later, and a crash (not a pause) during a step means starting
    /// over, since that step's source is gone.
    pub discard: bool,
    /// Pause, as for `PAUSE`, when the disk has less free space than this.
    pub min_free: u64,
}

/// Whether to stop at this layer boundary: a file `PAUSE` in the store, or too little free disk.
/// Every finished layer is saved, and running `extend` again with the same horizon resumes.
fn pause_requested(root: &Path, opt: &Options, out: &mut dyn FnMut(&str)) -> bool {
    if root.join("PAUSE").exists() {
        return true;
    }
    let free = store::free_bytes(root);
    if free < opt.min_free {
        out(&format!("low disk: {:.1} GB free", free as f64 / 1e9));
        return true;
    }
    false
}

/// How `extend` ended.
#[derive(PartialEq, Debug)]
pub enum Outcome {
    Complete,
    Paused,
}

/// Extend the store at `root` to horizon `target`, computing every new A(n). Stops early, with
/// all finished layers saved, if a pause is requested.
pub fn extend(root: &Path, target: usize, opt: Options, out: &mut dyn FnMut(&str)) -> Outcome {
    let (threads, cap) = (opt.threads, opt.cap);
    store::raise_fd_limit();
    fs::create_dir_all(root).expect("create store");
    let start = Instant::now();
    let mut m = Manifest::load(root);
    let old = m.horizons.last().copied();
    if old.is_some_and(|b| target <= b) {
        out(&format!("store already has horizon {}", old.unwrap()));
        return Outcome::Complete;
    }
    if old.is_some() && m.discarded && m.partial.is_none_or(|(b, _)| b != target) {
        out("this store discarded its backward layers and cannot be extended; build a new one");
        return Outcome::Complete;
    }
    m.discarded |= opt.discard;
    let seg = m.horizons.len();
    let mut done = match m.partial {
        Some((b, d)) if b == target => d,
        _ => [0, 0],
    };
    m.partial = Some((target, done));
    m.save(root);
    let mut values = load_values(root);

    // Forward layers: universal, one segment each.
    let kmax = target - target / 2;
    if m.kmax == 0 && !fdir(root, 0).exists() {
        store::write_states(&fdir(root, 0), 0, &[(crate::bits::from_state(INIT), 1)]);
    }
    let bridge = |k: Key, emit: &mut dyn FnMut(Key)| {
        successors(NO_TARGET, 0, crate::bits::to_state(k), |k2| emit(crate::bits::from_state(k2)));
    };
    while m.kmax < kmax {
        if pause_requested(root, &opt, out) {
            out(&format!("paused before F {} at {:.0} s", m.kmax + 1, start.elapsed().as_secs_f64()));
            return Outcome::Paused;
        }
        let src = Layer::new(fdir(root, m.kmax), 1);
        let dst = fdir(root, m.kmax + 1);
        let _ = fs::remove_dir_all(&dst);
        let st = store::step(src, &dst, 0, threads, cap, &bridge, &mut || {});
        m.kmax += 1;
        m.save(root);
        out(&format!(
            "F {:3}  states {:>13}  {:>10.2} GB  {:>8.0} s",
            m.kmax,
            st.states,
            st.bytes as f64 / 1e9,
            start.elapsed().as_secs_f64()
        ));
    }
    let f = |k: usize| Layer::new(fdir(root, k), 1);

    for p in 0..2 {
        let rmax_new = target / 2 + 1;
        if seg == 0 && done[p] == 0 && !gdir(root, p, 0).exists() {
            store::write_states(&gdir(root, p, 0), 0, &finishers(p));
        }
        let g = |r: usize| Layer::new(gdir(root, p, r), seg + 1);
        let value_at = |r: usize, values: &mut BTreeMap<usize, (u128, Option<u128>)>, out: &mut dyn FnMut(&str)| {
            let n = 2 * r + p;
            if n <= target && old.is_none_or(|b| n > b) {
                let c = store::dot(&f(r + p), &g(r), threads);
                values.insert(n, (c, None));
                out(&format!("A({n}) = {c}"));
            }
            if r + p >= 2 && n >= 2 && n - 2 <= target && old.is_none_or(|b| n - 2 > b) {
                let c = store::dot(&f(r + p - 2), &g(r), threads);
                if let Some(v) = values.get_mut(&(n - 2)) {
                    v.1 = Some(c);
                    let ok = if v.0 == c { "agrees" } else { "DISAGREES" };
                    out(&format!("A({}) second split {ok}: {c}", n - 2));
                }
            }
        };
        if done[p] == 0 {
            value_at(0, &mut values, out);
            save_values(root, &values);
        }
        for r in (done[p] + 1)..=rmax_new {
            if pause_requested(root, &opt, out) {
                out(&format!("paused before G{p} {r} at {:.0} s", start.elapsed().as_secs_f64()));
                return Outcome::Paused;
            }
            let lower = old.filter(|_| r <= m.rmax[p]).map(|b| b.saturating_sub(r));
            let upper = target.saturating_sub(r);
            let back = move |k: Key, emit: &mut dyn FnMut(Key)| {
                crate::bits::predecessors(k, upper, |t| {
                    if lower.is_none_or(|lo| crate::bits::depth(t) > lo) {
                        emit(t);
                    }
                });
            };
            let dst = gdir(root, p, r);
            let _ = fs::remove_dir_all(dst.join("tmp"));
            store::remove_segment(&dst, seg);
            let src_dir = gdir(root, p, r - 1);
            let st = store::step(g(r - 1), &dst, seg, threads, cap, &back, &mut || {
                // The source's values were taken when it was built; with discard it is not needed.
                if opt.discard && r >= 2 {
                    let _ = fs::remove_dir_all(&src_dir);
                }
            });
            out(&format!(
                "G{p} {:3}  new states {:>13}  {:>10.2} GB  spilled {:>13}  {:>8.0} s",
                r,
                st.states,
                st.bytes as f64 / 1e9,
                st.spilled_records,
                start.elapsed().as_secs_f64()
            ));
            value_at(r, &mut values, out);
            save_values(root, &values);
            done[p] = r;
            m.partial = Some((target, done));
            m.save(root);
            if opt.discard {
                let _ = fs::remove_dir_all(gdir(root, p, r - 1));
            }
        }
        m.rmax[p] = rmax_new;
    }
    m.horizons.push(target);
    m.partial = None;
    m.save(root);
    out(&format!("horizon {target} complete in {:.0} s", start.elapsed().as_secs_f64()));
    Outcome::Complete
}
