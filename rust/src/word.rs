//! The same transitions as `state.rs`, computed directly on the packed `u128`.
//! Word position `i` is the 2-bit field at bit `2i`; `h` sits in the top 6 bits.

use crate::state::{CLOSE, END, Key, OPEN, cap};

const H_SHIFT: u32 = 122;
const WORD_MASK: u128 = (1u128 << H_SHIFT) - 1;

#[inline(always)]
fn get(b: u128, i: usize) -> u8 {
    ((b >> (2 * i)) & 3) as u8
}

#[inline(always)]
fn set(b: u128, i: usize, c: u8) -> u128 {
    (b & !(3u128 << (2 * i))) | ((c as u128) << (2 * i))
}

#[inline(always)]
fn low(b: u128, i: usize) -> u128 {
    if i == 0 { 0 } else { b & (u128::MAX >> (128 - 2 * i)) }
}

#[inline(always)]
fn insert(b: u128, i: usize, c: u8) -> u128 {
    low(b, i) | ((c as u128) << (2 * i)) | ((b >> (2 * i)) << (2 * i + 2))
}

#[inline(always)]
fn remove(b: u128, i: usize) -> u128 {
    low(b, i) | ((b >> (2 * i + 2)) << (2 * i))
}

#[inline(always)]
fn len(b: u128) -> usize {
    (129 - b.leading_zeros() as usize) / 2
}

#[inline(always)]
fn partner(b: u128, i: usize) -> usize {
    let mut d = 0i32;
    if get(b, i) == OPEN {
        let mut j = i + 1;
        loop {
            match get(b, j) {
                OPEN => d += 1,
                CLOSE if d == 0 => return j,
                CLOSE => d -= 1,
                _ => {}
            }
            j += 1;
        }
    } else {
        let mut j = i - 1;
        loop {
            match get(b, j) {
                CLOSE => d += 1,
                OPEN if d == 0 => return j,
                OPEN => d -= 1,
                _ => {}
            }
            j -= 1;
        }
    }
}

/// Every viable successor of state `k` at point `x` of an `m`-crossing river.
#[inline(always)]
pub fn successors(m: usize, x: usize, k: Key, mut emit: impl FnMut(Key)) {
    let h = (k >> H_SHIFT) as usize;
    let b = k & WORD_MASK;
    let l = len(b);
    let dn = l - h;
    let cu = cap(m, x + 1, true);
    let cd = cap(m, x + 1, false) + 1;
    let mut out = |b2: u128, l2: usize, h2: usize| {
        if h2 <= cu && l2 - h2 <= cd {
            emit(b2 | ((h2 as u128) << H_SHIFT))
        }
    };
    if x < m {
        out(insert(insert(b, h, OPEN), h + 1, CLOSE), l + 2, h + 1);
        if dn > 0 {
            out(b, l, h + 1);
        }
        if h > 0 {
            out(b, l, h - 1);
        }
        if h > 0 && dn > 0 {
            let (i, j) = (h - 1, h);
            let (ci, cj) = (get(b, i), get(b, j));
            if !(ci == OPEN && cj == CLOSE) {
                let t = if ci == END {
                    set(b, partner(b, j), END)
                } else if cj == END {
                    set(b, partner(b, i), END)
                } else if ci == OPEN && cj == OPEN {
                    set(b, partner(b, j), OPEN)
                } else if ci == CLOSE && cj == CLOSE {
                    set(b, partner(b, i), CLOSE)
                } else {
                    b
                };
                out(remove(remove(t, j), i), l - 2, h - 1);
            }
        }
    } else {
        let up = m % 2 == 1;
        out(insert(b, h, END), l + 1, if up { h + 1 } else { h });
        let top = if up { h.checked_sub(1) } else if dn > 0 { Some(h) } else { None };
        if let Some(i) = top
            && get(b, i) != END
        {
            let t = set(b, partner(b, i), END);
            out(remove(t, i), l - 1, if up { h - 1 } else { h });
        }
    }
}

/// A state in 64 bits, for the parallel sweep: bits `59..64` hold `h` (below 32, since a viable
/// state has at most about `n / 2` arcs above the road), bits `53..59` the position of `E` (`63`
/// if none), and bits `0..53` the brackets other than `E` (`1 = (`, `0 = )`) under a leading `1`.
/// Words of up to 52 brackets fit, enough for `n ≤ 52`.
pub type Key64 = u64;

const NO_END: u64 = 63;

/// Spread the bits of `x` to the even bit positions of a `u128` (bit `i` to bit `2i`).
#[inline(always)]
fn spread(x: u64) -> u128 {
    let mut x = x as u128;
    x = (x | (x << 32)) & 0x0000_0000_FFFF_FFFF_0000_0000_FFFF_FFFF;
    x = (x | (x << 16)) & 0x0000_FFFF_0000_FFFF_0000_FFFF_0000_FFFF;
    x = (x | (x << 8)) & 0x00FF_00FF_00FF_00FF_00FF_00FF_00FF_00FF;
    x = (x | (x << 4)) & 0x0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F;
    x = (x | (x << 2)) & 0x3333_3333_3333_3333_3333_3333_3333_3333;
    (x | (x << 1)) & 0x5555_5555_5555_5555_5555_5555_5555_5555
}

/// The inverse of `spread`: gather the even bits of `x`.
#[inline(always)]
fn compact(x: u128) -> u64 {
    let mut x = x & 0x5555_5555_5555_5555_5555_5555_5555_5555;
    x = (x | (x >> 1)) & 0x3333_3333_3333_3333_3333_3333_3333_3333;
    x = (x | (x >> 2)) & 0x0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F;
    x = (x | (x >> 4)) & 0x00FF_00FF_00FF_00FF_00FF_00FF_00FF_00FF;
    x = (x | (x >> 8)) & 0x0000_FFFF_0000_FFFF_0000_FFFF_0000_FFFF;
    x = (x | (x >> 16)) & 0x0000_0000_FFFF_FFFF_0000_0000_FFFF_FFFF;
    (x | (x >> 32)) as u64
}

const EVEN: u128 = 0x5555_5555_5555_5555_5555_5555_5555_5555;

/// Pack a state into 64 bits, in constant time. A field holds `( = 01`, `) = 10`, `E = 11`, so
/// the low bit of a field is set for `(` and `E`, and both bits only for `E`.
#[inline(always)]
pub fn narrow(k: Key) -> Key64 {
    let h = (k >> H_SHIFT) as u64;
    let mut b = k & WORD_MASK;
    let mut e = NO_END;
    let ends = b & (b >> 1) & EVEN;
    if ends != 0 {
        let i = ends.trailing_zeros() as usize / 2;
        b = remove(b, i);
        e = i as u64;
    }
    let n = len(b);
    assert!(n <= 52 && h < 32, "a state does not fit in 64 bits; use a wider key");
    let bits = compact(b) | (1u64 << n);
    (h << 59) | (e << 53) | bits
}

/// Unpack a 64-bit state, in constant time.
#[inline(always)]
pub fn widen(k: Key64) -> Key {
    let h = k >> 59;
    let e = ((k >> 53) & 63) as usize;
    let bits = k & ((1 << 53) - 1);
    let n = 63 - bits.leading_zeros() as usize; // brackets under the sentinel
    let ones = bits ^ (1u64 << n);
    // A field is 2 - bit: `10` for `)`, `01` for `(`.
    let mut b = (low(u128::MAX, n) & (EVEN << 1)) - spread(ones);
    if e != NO_END as usize {
        b = insert(b, e, END);
    }
    b | ((h as u128) << H_SHIFT)
}
