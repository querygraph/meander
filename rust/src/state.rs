//! The transfer-matrix state of `Arnold.TM` in a packed encoding.
//!
//! Lean's `St` keeps the open arcs above (`up`) and below (`dn`) the road as two stacks, and
//! each open arc records where its piece of river leads. Read the open arcs along the cut from
//! top to bottom: `up[0], …, up[top], dn[top], …, dn[0]`. The pieces west of the cut never
//! cross, so in that order they form a non-crossing matching, with at most one arc whose piece
//! leads to the east end `E` instead. So a state is a word over `(`, `)` and `E`, plus the
//! number `h` of arcs above the road. Word position `i` takes bits `2i, 2i+1` of a `u128`
//! (`1 = (`, `2 = )`, `3 = E`, `0 = empty`), and `h` takes the top 6 bits.

pub type Key = u128;

pub const OPEN: u8 = 1;
pub const CLOSE: u8 = 2;
pub const END: u8 = 3;

/// The longest word that fits beside `h`.
pub const MAX_LEN: usize = 61;
const H_SHIFT: u32 = 122;

/// A decoded state: the word and the height of the upper stack.
#[derive(Clone, Copy)]
pub struct Word {
    pub w: [u8; 64],
    pub len: usize,
    pub h: usize,
}

#[inline(always)]
pub fn decode(k: Key) -> Word {
    let h = (k >> H_SHIFT) as usize;
    let mut bits = k & ((1u128 << H_SHIFT) - 1);
    let mut w = [0u8; 64];
    let mut len = 0;
    while bits != 0 {
        w[len] = (bits & 3) as u8;
        bits >>= 2;
        len += 1;
    }
    Word { w, len, h }
}

#[inline(always)]
pub fn encode(s: &Word) -> Key {
    debug_assert!(s.len <= MAX_LEN, "state too long");
    let mut k: Key = 0;
    for i in (0..s.len).rev() {
        k = (k << 2) | s.w[i] as Key;
    }
    k | ((s.h as Key) << H_SHIFT)
}

/// The partner of the bracket at position `i`.
#[inline(always)]
fn partner(s: &Word, i: usize) -> usize {
    if s.w[i] == OPEN {
        let mut d = 0i32;
        let mut j = i + 1;
        loop {
            match s.w[j] {
                OPEN => d += 1,
                CLOSE => {
                    if d == 0 {
                        return j;
                    }
                    d -= 1
                }
                _ => {}
            }
            j += 1;
        }
    } else {
        let mut d = 0i32;
        let mut j = i - 1;
        loop {
            match s.w[j] {
                CLOSE => d += 1,
                OPEN => {
                    if d == 0 {
                        return j;
                    }
                    d -= 1
                }
                _ => {}
            }
            j -= 1;
        }
    }
}

#[inline(always)]
fn remove(s: &mut Word, i: usize) {
    s.w.copy_within(i + 1..s.len, i);
    s.len -= 1;
    s.w[s.len] = 0;
}

#[inline(always)]
fn insert(s: &mut Word, i: usize, c: u8) {
    s.w.copy_within(i..s.len, i + 1);
    s.w[i] = c;
    s.len += 1;
}

/// `cap m k σ` of `Arnold.TM`: how many of the points `k, …, m` have an arc on side `σ`.
#[inline(always)]
pub fn cap(m: usize, k: usize, up: bool) -> usize {
    if k <= m {
        (m - k) + usize::from((m % 2 == 1) == up)
    } else {
        0
    }
}

/// `viable m k s` of `Arnold.TM`.
#[inline(always)]
pub fn viable(m: usize, k: usize, s: &Word) -> bool {
    s.h <= cap(m, k, true) && s.len - s.h <= cap(m, k, false) + 1
}

/// `step m x s a` of `Arnold.TM` for every action `a` in `acts m x`: calls `emit` with each
/// successor that is still viable after point `x`.
#[inline(always)]
pub fn successors(m: usize, x: usize, k: Key, mut emit: impl FnMut(Key)) {
    let s = decode(k);
    let h = s.h;
    let dn = s.len - h;
    let mut out = |t: &Word| {
        if viable(m, x + 1, t) {
            emit(encode(t))
        }
    };
    if x < m {
        // (true, true): a new arc on each side, joined at this bridge.
        let mut t = s;
        insert(&mut t, h, OPEN);
        insert(&mut t, h + 1, CLOSE);
        t.h = h + 1;
        out(&t);
        // (true, false): close the lower top, open above; the word is unchanged.
        if dn > 0 {
            let mut t = s;
            t.h = h + 1;
            out(&t);
        }
        // (false, true): close the upper top, open below.
        if h > 0 {
            let mut t = s;
            t.h = h - 1;
            out(&t);
        }
        // (false, false): close both tops and join their pieces, unless that closes a loop.
        if h > 0 && dn > 0 {
            let (i, j) = (h - 1, h);
            let (ci, cj) = (s.w[i], s.w[j]);
            if !(ci == OPEN && cj == CLOSE) {
                let mut t = s;
                if ci == END {
                    let pj = partner(&s, j);
                    t.w[pj] = END;
                } else if cj == END {
                    let pi = partner(&s, i);
                    t.w[pi] = END;
                } else if ci == OPEN && cj == OPEN {
                    let pj = partner(&s, j);
                    t.w[pj] = OPEN;
                } else if ci == CLOSE && cj == CLOSE {
                    let pi = partner(&s, i);
                    t.w[pi] = CLOSE;
                }
                remove(&mut t, j);
                remove(&mut t, i);
                t.h = h - 1;
                out(&t);
            }
        }
    } else {
        // The east end: one arc, on side `m % 2`.
        let up = m % 2 == 1;
        // open: its piece leads to `E`.
        let mut t = s;
        insert(&mut t, h, END);
        if up {
            t.h = h + 1;
        }
        out(&t);
        // close the top arc on that side; its partner's piece now leads to `E`.
        let top = if up { h.checked_sub(1) } else if dn > 0 { Some(h) } else { None };
        if let Some(i) = top
            && s.w[i] != END
        {
            let p = partner(&s, i);
            let mut t = s;
            t.w[p] = END;
            remove(&mut t, i);
            if up {
                t.h = h - 1;
            }
            out(&t);
        }
    }
}

/// The initial state: nothing open.
pub const INIT: Key = 0;

/// `final` of `Arnold.TM`: one arc below the road, leading to `E`.
pub fn final_key() -> Key {
    let mut w = [0u8; 64];
    w[0] = END;
    encode(&Word { w, len: 1, h: 0 })
}

#[cfg(test)]
/// Prefix balances of a word without `E`: `bal[i]` = (number of `(`) − (number of `)`) in
/// positions `0..i`.
fn balances(s: &Word) -> [i32; 65] {
    let mut bal = [0i32; 65];
    for i in 0..s.len {
        bal[i + 1] = bal[i] + if s.w[i] == OPEN { 1 } else { -1 };
    }
    bal
}

#[cfg(test)]
/// The fewest bridges that build state `s` (a word without `E`) from the west: each piece of
/// river west of the cut joins two open arcs, and needs one bridge if they are on opposite sides
/// of the road and two if they are on the same side. The pieces joining opposite sides are the
/// unmatched `(` left of the cut, so this is `len − bal[h]`.
pub fn depth(s: &Word) -> usize {
    s.len - balances(s)[s.h] as usize
}

#[cfg(test)]
/// `emit(t)` for every state `t` with a bridge step `t → s` (the inverse of the bridge cases of
/// `successors`), for words without `E`. Viability is not applied.
pub fn predecessors(s: &Word, mut emit: impl FnMut(Word)) {
    let (h, len) = (s.h, s.len);
    let bal = balances(s);
    // open both: a matched pair `()` was inserted at h-1, h.
    if h >= 1 && h < len && s.w[h - 1] == OPEN && s.w[h] == CLOSE {
        let mut t = *s;
        remove(&mut t, h);
        remove(&mut t, h - 1);
        t.h = h - 1;
        emit(t);
    }
    // open above, close below: same word, one arc fewer above.
    if h >= 1 {
        let mut t = *s;
        t.h = h - 1;
        emit(t);
    }
    // close above, open below: same word, one arc more above.
    if h < len {
        let mut t = *s;
        t.h = h + 1;
        emit(t);
    }
    // close both: two letters were removed at the cut and their partners joined.
    let mut stack = [0usize; 64];
    let mut sp = 0;
    let mut partner = [0usize; 64];
    for i in 0..len {
        if s.w[i] == OPEN {
            stack[sp] = i;
            sp += 1;
        } else {
            sp -= 1;
            partner[stack[sp]] = i;
            partner[i] = stack[sp];
        }
    }
    // Is w[a..b] balanced? (never below its starting level, ending at it)
    let balanced = |a: usize, b: usize| bal[b] == bal[a] && (a..=b).all(|i| bal[i] >= bal[a]);
    for p in 0..len {
        if s.w[p] != OPEN {
            continue;
        }
        let q = partner[p];
        let mut t = *s;
        if p >= h {
            // right of the cut: both removed letters were `(`, and p was `)`.
            if !balanced(h, p) {
                continue;
            }
            t.w[p] = CLOSE;
            insert(&mut t, h, OPEN);
            insert(&mut t, h, OPEN);
        } else if q < h {
            // left of the cut: both were `)`, and q was `(`.
            if !balanced(q + 1, h) {
                continue;
            }
            t.w[q] = OPEN;
            insert(&mut t, h, CLOSE);
            insert(&mut t, h, CLOSE);
        } else {
            // straddling: `)` joined p and `(` joined q.
            if !balanced(p + 1, h) {
                continue;
            }
            insert(&mut t, h, OPEN);
            insert(&mut t, h, CLOSE);
        }
        t.h = h + 1;
        emit(t);
    }
}
