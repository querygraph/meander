//! `meanders-rs [N] [--from M] [--threads T] [--check] [--two-moduli]`: print Arnold's numbers (OEIS A005316)
//! for `n = M, …, N`, computed by the parallel transfer matrix.

mod par;
mod serial;
mod state;
mod word;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |name: &str| args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)?.parse().ok());
    let n: usize = args.first().and_then(|a| a.parse().ok()).unwrap_or(32);
    let from: usize = flag("--from").unwrap_or(0);
    let threads: usize = flag("--threads")
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |p| p.get()));
    let check = args.iter().any(|a| a == "--check");
    let two = args.iter().any(|a| a == "--two-moduli");
    println!("# n\tcount\tpeak_states\ttotal_states\tseconds\tthreads={threads}");
    for m in from..=n {
        let t = std::time::Instant::now();
        let s = par::count(m, threads, two);
        let secs = t.elapsed().as_secs_f64();
        if check {
            assert_eq!(s.count, serial::count(m).0, "parallel and serial disagree at n = {m}");
        }
        println!("{m}\t{}\t{}\t{}\t{secs:.3}", s.count, s.peak_states, s.total_states);
    }
}

#[cfg(test)]
mod tests {
    /// The values certified in Lean (`Arnold.openMeanderCount_values_native`, n ≤ 24) and the
    /// published OEIS terms up to n = 30.
    const KNOWN: [u128; 31] = [
        1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538, 1828, 3926, 13820, 30694, 110954, 252939, 933458,
        2172830, 8152860, 19304190, 73424650, 176343390, 678390116, 1649008456, 6405031050,
        15730575554, 61606881612, 152663683494, 602188541928, 1503962954930,
    ];

    #[test]
    fn serial_matches_known_values() {
        for (m, &v) in KNOWN.iter().enumerate() {
            assert_eq!(crate::serial::count(m).0, v, "n = {m}");
        }
    }

    #[test]
    fn parallel_matches_known_values_with_both_moduli() {
        for (m, &v) in KNOWN.iter().enumerate() {
            assert_eq!(crate::par::count(m, 4, false).count, v, "n = {m}");
            assert_eq!(crate::par::count(m, 4, true).count, v, "n = {m}, two moduli");
        }
    }

    #[test]
    fn narrow_and_widen_are_inverse() {
        for m in 0..=20 {
            let mut layer = vec![crate::state::INIT];
            for x in 0..=m {
                let mut next = Vec::new();
                for &k in &layer {
                    crate::word::successors(m, x, k, |k2| next.push(k2));
                }
                for &k in &next {
                    assert_eq!(crate::word::widen(crate::word::narrow(k)), k);
                }
                next.sort_unstable();
                next.dedup();
                layer = next;
            }
        }
    }
}
