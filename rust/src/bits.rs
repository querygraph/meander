//! Backward steps on the packed 64-bit state, for words without `E`.
//!
//! The key (see `word::narrow`) is `h << 59 | 63 << 53 | 1 << len | brackets`, with bracket `i`
//! at bit `i` (`1 = (`, `0 = )`). Everything here works on those bits directly, with no decoding:
//!
//! * `depth = len − bal(h)`, where `bal(h) = 2·popcount(brackets below bit h) − h` is the excess
//!   of `(` left of the cut (`state::depth`).
//! * The inverse of "close both tops" re-splits one pair of the word at the cut. A pair right of
//!   the cut can be split only if it is at top level there (the letters between the cut and it
//!   are balanced), and likewise on the left, and among the pairs that straddle the cut only the
//!   innermost one qualifies. One scan outward from the cut on each side finds them all.
//!
//! `predecessors` emits exactly the states of `state::predecessors` (checked by a test).

pub type Key = u64;

const NO_END: u64 = 63;
const BITS: u64 = (1 << 53) - 1;

#[inline(always)]
fn parts(k: Key) -> (u64, usize, usize) {
    let h = (k >> 59) as usize;
    let b = k & BITS;
    let len = 63 - b.leading_zeros() as usize;
    (b ^ (1 << len), len, h)
}

#[inline(always)]
fn make(b: u64, len: usize, h: usize) -> Key {
    debug_assert!(len <= 52 && h < 32);
    ((h as u64) << 59) | (NO_END << 53) | (1 << len) | b
}

#[inline(always)]
fn low(b: u64, i: usize) -> u64 {
    b & ((1u64 << i) - 1)
}

/// Insert two letters `x` (at position i) and `y` (at i + 1).
#[inline(always)]
fn insert2(b: u64, i: usize, x: u64, y: u64) -> u64 {
    low(b, i) | (x << i) | (y << (i + 1)) | ((b >> i) << (i + 2))
}

/// The excess of `(` over `)` in positions `0..i`.
#[inline(always)]
fn bal(b: u64, i: usize) -> i32 {
    2 * (low(b, i).count_ones() as i32) - i as i32
}

/// The fewest bridges that build the state from the west (`state::depth`).
#[inline(always)]
pub fn depth(k: Key) -> usize {
    let (b, len, h) = parts(k);
    (len as i32 - bal(b, h)) as usize
}

/// Every predecessor of `k` under a bridge step whose depth is at most `bound`.
#[inline(always)]
pub fn predecessors(k: Key, bound: usize, mut emit: impl FnMut(Key)) {
    let (b, len, h) = parts(k);
    let mut out = |b2: u64, len2: usize, h2: usize| {
        let d = len2 as i32 - bal(b2, h2);
        if d as usize <= bound {
            emit(make(b2, len2, h2));
        }
    };
    // open both: a matched pair `()` at h-1, h.
    if h >= 1 && h < len && (b >> (h - 1)) & 1 == 1 && (b >> h) & 1 == 0 {
        let b2 = low(b, h - 1) | ((b >> (h + 1)) << (h - 1));
        out(b2, len - 2, h - 1);
    }
    // open above, close below.
    if h >= 1 {
        out(b, len, h - 1);
    }
    // close above, open below.
    if h < len {
        out(b, len, h + 1);
    }
    // close both, a pair right of the cut: `((` inserted at h and the pair's `(` at p turned `)`.
    let mut d = 0i32;
    for p in h..len {
        if (b >> p) & 1 == 1 {
            if d == 0 {
                out(insert2(b & !(1 << p), h, 1, 1), len + 2, h + 1);
            }
            d += 1;
        } else {
            d -= 1;
            if d < 0 {
                break;
            }
        }
    }
    // a pair left of the cut: `))` inserted at h and the pair's `)` at q turned `(`.
    // Scanning left, a `)` opens a level and a `(` closes one.
    let mut d = 0i32;
    let mut straddle = None;
    for q in (0..h).rev() {
        if (b >> q) & 1 == 0 {
            if d == 0 {
                out(insert2(b | (1 << q), h, 0, 0), len + 2, h + 1);
            }
            d += 1;
        } else {
            d -= 1;
            if d < 0 {
                straddle = Some(q);
                break;
            }
        }
    }
    // the innermost straddling pair: `)(` inserted at h.
    if straddle.is_some() {
        out(insert2(b, h, 0, 1), len + 2, h + 1);
    }
}
