//! `meanders-rs [N] [--from M] [--threads T] [--check] [--two-moduli] [--presize]
//! [--spill DIR [--cap N | --mem-gb G] [--all]]`. With `--all`, one out-of-core sweep for N
//! also prints A(m) for every m ≤ N.: print Arnold's numbers (OEIS A005316)
//! for `n = M, …, N`, computed by the parallel transfer matrix.

mod ooc;
mod par;
mod serial;
mod state;
mod word;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let arg = |name: &str| args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned());
    let flag = |name: &str| arg(name).and_then(|v| v.parse::<usize>().ok());
    let n: usize = args.first().and_then(|a| a.parse().ok()).unwrap_or(32);
    let from: usize = flag("--from").unwrap_or(0);
    let threads: usize = flag("--threads")
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |p| p.get()));
    let check = args.iter().any(|a| a == "--check");
    let two = args.iter().any(|a| a == "--two-moduli");
    let presize = args.iter().any(|a| a == "--presize");
    let spill: Option<String> = arg("--spill");
    let cap: Option<usize> = flag("--cap");
    let mem_gb: Option<f64> = arg("--mem-gb").and_then(|v| v.parse().ok());
    let all = args.iter().any(|a| a == "--all");
    println!("# n\tcount\tpeak_states\ttotal_states\tseconds\tthreads={threads}");
    for m in from..=n {
        let t = std::time::Instant::now();
        if let Some(dir) = &spill {
            // About 120 bytes per capped entry: table slack and a sorted copy while spilling,
            // for the layer being built and the remainders of the layer being read.
            let cap = cap.unwrap_or_else(|| {
                ((mem_gb.unwrap_or(16.0) * 1e9 / (4096.0 * 120.0)) as usize).max(1024)
            });
            let s = ooc::count(m, threads, cap, std::path::Path::new(dir));
            let secs = t.elapsed().as_secs_f64();
            if check {
                assert_eq!(s.count, serial::count(m).0, "out-of-core and serial disagree at n = {m}");
            }
            println!(
                "{m}\t{}\t{}\t{}\t{secs:.3}\tspilled={} bytes_per_record={:.1} disk_peak_gb={:.2}",
                s.count,
                s.peak_states,
                s.total_states,
                s.spilled_records,
                s.spilled_bytes as f64 / s.spilled_records.max(1) as f64,
                s.spilled_bytes_peak as f64 / 1e9
            );
            if all {
                for (j, a) in s.all.iter().enumerate() {
                    println!("all\t{j}\t{a}");
                }
            }
            continue;
        }
        let s = par::count(m, threads, two, presize);
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
            assert_eq!(crate::par::count(m, 4, false, false).count, v, "n = {m}");
            assert_eq!(crate::par::count(m, 4, true, false).count, v, "n = {m}, two moduli");
            assert_eq!(crate::par::count(m, 3, true, true).count, v, "n = {m}, presized");
        }
    }

    #[test]
    fn out_of_core_matches_known_values() {
        let dir = std::env::temp_dir().join(format!("meanders-ooc-test-{}", std::process::id()));
        for (m, &v) in KNOWN.iter().enumerate().take(27) {
            assert_eq!(crate::ooc::count(m, 3, 4, &dir).count, v, "n = {m}, spilling");
        }
        let s = crate::ooc::count(26, 3, 4, &dir);
        assert_eq!(s.all, KNOWN[..27].to_vec(), "every A(m), m <= 26, from one sweep");
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 0, "run files left behind");
        let _ = std::fs::remove_dir(&dir);
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
