//! A single-threaded reference: `tmCountWith` with a hash-map merge.

use crate::state::{Key, INIT, final_key, successors};
use std::collections::HashMap;

pub fn count(m: usize) -> (u128, usize) {
    let mut layer: HashMap<Key, u128> = HashMap::from([(INIT, 1)]);
    let mut peak = 1;
    for x in 0..=m {
        let mut next: HashMap<Key, u128> = HashMap::with_capacity(layer.len() * 2);
        for (&k, &c) in &layer {
            successors(m, x, k, |k2| *next.entry(k2).or_insert(0) += c);
        }
        layer = next;
        peak = peak.max(layer.len());
    }
    (layer.get(&final_key()).copied().unwrap_or(0), peak)
}
