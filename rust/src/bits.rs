//! The meet-in-the-middle key, and backward steps on it.
//!
//! The states of the meet-in-the-middle layers never contain `E` (forward layers come before the
//! east end, and backward states are what the east end will finish), so their key needs no field
//! for its position: `h << 59 | 1 << len | brackets`, with bracket `i` at bit `i` (`1 = (`,
//! `0 = )`) under a sentinel. That fits words of up to 58 brackets, enough for every horizon up to
//! 58 (the forward layer after `k` bridges has words of up to `2k` brackets). `from_state` and
//! `to_state` convert to and from the two-bit working form in constant time.
//!
//! Everything else here works on those bits directly, with no decoding:
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

const BITS: u64 = (1 << 59) - 1;

#[inline(always)]
fn parts(k: Key) -> (u64, usize, usize) {
    let h = (k >> 59) as usize;
    let b = k & BITS;
    let len = 63 - b.leading_zeros() as usize;
    (b ^ (1 << len), len, h)
}

#[inline(always)]
fn make(b: u64, len: usize, h: usize) -> Key {
    assert!(len <= 58 && h < 32, "a state does not fit in the 64-bit key");
    ((h as u64) << 59) | (1 << len) | b
}

/// The key of a state given in the two-bit form of `word.rs` (which must contain no `E`).
#[inline(always)]
pub fn from_state(k: crate::state::Key) -> Key {
    use crate::word::{EVEN, H_SHIFT, WORD_MASK, compact, len};
    let h = (k >> H_SHIFT) as usize;
    let b = k & WORD_MASK;
    debug_assert!(b & (b >> 1) & EVEN == 0, "a meet-in-the-middle state has no E");
    let n = len(b);
    make(compact(b), n, h)
}

/// The two-bit form of a key.
#[inline(always)]
pub fn to_state(k: Key) -> crate::state::Key {
    use crate::word::{EVEN, H_SHIFT, low, spread};
    let (b, n, h) = parts(k);
    let w = (low(u128::MAX, n) & (EVEN << 1)) - spread(b);
    w | ((h as u128) << H_SHIFT)
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
