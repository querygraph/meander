//! `meanders-rs [N] [--from M] [--threads T] [--check] [--two-moduli] [--presize]
//! [--spill DIR [--cap N | --mem-gb G] [--all]]
//! [--mitm B] [--store DIR --horizon B [--cap N | --mem-gb G] [--discard] [--min-free-gb G] [--passes P|auto]]`. With `--all`, one out-of-core sweep for N
//! also prints A(m) for every m ≤ N.: print Arnold's numbers (OEIS A005316)
//! for `n = M, …, N`, computed by the parallel transfer matrix.

mod bits;
mod mitm;
mod mitm_store;
mod store;
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
    if let (Some(root), Some(b)) = (arg("--store"), arg("--horizon").and_then(|v| v.parse::<usize>().ok())) {
        let cap = cap.unwrap_or_else(|| ((mem_gb.unwrap_or(16.0) * 1e9 / (4096.0 * 120.0)) as usize).max(1024));
        let opt = mitm_store::Options {
            threads,
            cap,
            discard: args.iter().any(|a| a == "--discard"),
            min_free: (arg("--min-free-gb").and_then(|v| v.parse::<f64>().ok()).unwrap_or(40.0) * 1e9) as u64,
            passes: match arg("--passes").as_deref() {
                Some("auto") => 0,
                Some(v) => v.parse().expect("--passes N or --passes auto"),
                None => 1,
            },
        };
        let outcome = mitm_store::extend(std::path::Path::new(&root), b, opt, &mut |line| {
            println!("{line}");
            use std::io::Write;
            let _ = std::io::stdout().flush();
        });
        if outcome == mitm_store::Outcome::Paused {
            std::process::exit(3);
        }
        return;
    }
    if let Some(b) = arg("--mitm").and_then(|v| v.parse::<usize>().ok()) {
        let t = std::time::Instant::now();
        println!("# n\tcount\tcheck\tforward_states\tbackward_states\tthreads={threads}");
        mitm::run(b, threads, |r| {
            let check = match r.check {
                Some(c) if c == r.count => "ok".to_string(),
                Some(c) => format!("MISMATCH({c})"),
                None => "-".to_string(),
            };
            println!("{}\t{}\t{check}\t{}\t{}", r.n, r.count, r.forward_states, r.backward_states);
        });
        eprintln!("seconds: {:.3}", t.elapsed().as_secs_f64());
        return;
    }
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

    /// The inverse transitions are exact: on every state reachable within 12 bridges, `t` is a
    /// predecessor of `s` exactly when `s` is a bridge successor of `t`; and `depth` is the first
    /// layer where a state appears.
    #[test]
    fn predecessors_invert_bridge_steps() {
        use crate::state::{Word, decode, depth, encode, predecessors};
        use std::collections::{HashMap, HashSet};
        let big = 100; // no viability pruning, and every point is a bridge
        let succ = |k: crate::state::Key| {
            let mut v = Vec::new();
            crate::word::successors(big, 0, k, |k2| v.push(k2));
            v
        };
        let mut first: HashMap<crate::state::Key, usize> = HashMap::from([(crate::state::INIT, 0)]);
        let mut layer = vec![crate::state::INIT];
        for x in 1..=12 {
            let mut next: Vec<_> = layer.iter().flat_map(|&k| succ(k)).collect();
            next.sort_unstable();
            next.dedup();
            for &k in &next {
                first.entry(k).or_insert(x);
            }
            layer = next;
        }
        for (&k, &x) in &first {
            assert_eq!(depth(&decode(k)), x, "depth of a state first reached at layer {x}");
            let mut pre = HashSet::new();
            predecessors(&decode(k), |t: Word| {
                pre.insert(encode(&t));
            });
            for &t in &pre {
                assert!(succ(t).contains(&k), "spurious predecessor");
            }
            if x < 12 {
                for k2 in succ(k) {
                    let mut back = HashSet::new();
                    predecessors(&decode(k2), |t: Word| {
                        back.insert(encode(&t));
                    });
                    assert!(back.contains(&k), "missing predecessor");
                }
            }
        }
    }

    /// The packed-bit backward step equals the reference one on every state within 14 bridges.
    #[test]
    fn packed_predecessors_match_reference() {
        use crate::state::{Word, decode, depth, encode, predecessors};
        use std::collections::BTreeSet;
        let mut layer = vec![crate::state::INIT];
        let mut all = BTreeSet::new();
        for _ in 0..14 {
            let mut next = Vec::new();
            for &k in &layer {
                crate::word::successors(100, 0, k, |k2| next.push(k2));
            }
            next.sort_unstable();
            next.dedup();
            all.extend(next.iter().copied());
            layer = next;
        }
        for &k in &all {
            let w = decode(k);
            assert_eq!(crate::bits::depth(crate::bits::from_state(k)), depth(&w));
            assert_eq!(crate::bits::to_state(crate::bits::from_state(k)), k);
            let mut want = BTreeSet::new();
            predecessors(&w, |t: Word| {
                want.insert(crate::bits::from_state(encode(&t)));
            });
            let mut got = BTreeSet::new();
            crate::bits::predecessors(crate::bits::from_state(k), usize::MAX, |t| {
                assert!(got.insert(t), "duplicate predecessor");
            });
            assert_eq!(got, want, "predecessors of {k:#x}");
            // the depth bound filters exactly
            let bound = depth(&w);
            let mut kept = BTreeSet::new();
            crate::bits::predecessors(crate::bits::from_state(k), bound, |t| {
                kept.insert(t);
            });
            let expect: BTreeSet<_> =
                want.iter().copied().filter(|&t| crate::bits::depth(t) <= bound).collect();
            assert_eq!(kept, expect);
        }
    }

    fn test_opt() -> crate::mitm_store::Options {
        crate::mitm_store::Options { threads: 3, cap: 64, discard: false, min_free: 0, passes: 1 }
    }

    /// A store built to 20 and extended to 24 holds the same values as one built at 24, and
    /// every value matches the known one and its second split.
    #[test]
    fn store_extends_stepwise() {
        let base = std::env::temp_dir().join(format!("meanders-store-test-{}", std::process::id()));
        let (a, b) = (base.join("a"), base.join("b"));
        for (dir, horizons) in [(&a, vec![20, 24]), (&b, vec![24])] {
            for h in horizons {
                crate::mitm_store::extend(dir, h, test_opt(), &mut |_| {});
            }
        }
        let va = std::fs::read_to_string(a.join("values")).unwrap();
        assert_eq!(va, std::fs::read_to_string(b.join("values")).unwrap());
        for line in va.lines().filter(|l| !l.starts_with('#')) {
            let f: Vec<&str> = line.split('\t').collect();
            let n: usize = f[0].parse().unwrap();
            assert_eq!(f[1].parse::<u128>().unwrap(), KNOWN[n], "A({n})");
            if f[2] != "-" {
                assert_eq!(f[2], f[1], "second split of A({n})");
            }
        }
        let _ = std::fs::remove_dir_all(&base);
    }

    /// Discarding used backward layers gives the same values and keeps one layer per family.
    #[test]
    fn store_discard_matches() {
        let base = std::env::temp_dir().join(format!("meanders-discard-test-{}", std::process::id()));
        let (a, b) = (base.join("a"), base.join("b"));
        crate::mitm_store::extend(&a, 24, crate::mitm_store::Options { discard: true, ..test_opt() }, &mut |_| {});
        crate::mitm_store::extend(&b, 24, test_opt(), &mut |_| {});
        assert_eq!(
            std::fs::read_to_string(a.join("values")).unwrap(),
            std::fs::read_to_string(b.join("values")).unwrap()
        );
        for p in ["G0", "G1"] {
            assert_eq!(std::fs::read_dir(a.join(p)).unwrap().count(), 1, "{p} keeps its last layer");
        }
        let _ = std::fs::remove_dir_all(&base);
    }

    /// Building each step in several passes over its source gives the same store as one pass,
    /// whether the passes are forced or chosen from the layer sizes.
    #[test]
    fn store_passes_match() {
        let base = std::env::temp_dir().join(format!("meanders-passes-test-{}", std::process::id()));
        let read = |d: &str| std::fs::read_to_string(base.join(d).join("values")).unwrap();
        for (d, passes) in [("one", 1), ("three", 3), ("auto", 0)] {
            crate::mitm_store::extend(&base.join(d), 24, crate::mitm_store::Options { cap: 2, passes, ..test_opt() }, &mut |_| {});
        }
        assert_eq!(read("one"), read("three"));
        assert_eq!(read("one"), read("auto"));
        let _ = std::fs::remove_dir_all(&base);
    }

    /// Pausing at a layer boundary and resuming gives the same store as an uninterrupted run,
    /// also after an interrupted step left stale runs behind.
    #[test]
    fn store_pauses_and_resumes() {
        use crate::mitm_store::{Outcome, extend};
        let base = std::env::temp_dir().join(format!("meanders-pause-test-{}", std::process::id()));
        let (a, b) = (base.join("a"), base.join("b"));
        extend(&b, 22, test_opt(), &mut |_| {});
        std::fs::create_dir_all(&a).unwrap();
        let pause = a.join("PAUSE");
        let outcome = extend(&a, 22, test_opt(), &mut |line| {
            if line.starts_with("G1   5") {
                std::fs::write(&pause, "").unwrap();
            }
        });
        assert_eq!(outcome, Outcome::Paused);
        // A crash in the middle of the next step leaves runs in its scratch directory.
        let tmp = a.join("G1").join("006").join("tmp");
        std::fs::create_dir_all(&tmp).unwrap();
        std::fs::write(tmp.join("w0.spill"), [1u8, 2, 3]).unwrap();
        std::fs::write(a.join("G1").join("006").join("seg0.dat"), [9u8; 7]).unwrap();
        std::fs::remove_file(&pause).unwrap();
        assert_eq!(extend(&a, 22, test_opt(), &mut |_| {}), Outcome::Complete);
        assert!(!tmp.exists(), "stale runs removed");
        assert_eq!(
            std::fs::read_to_string(a.join("values")).unwrap(),
            std::fs::read_to_string(b.join("values")).unwrap()
        );
        let _ = std::fs::remove_dir_all(&base);
    }

    /// The meet-in-the-middle key holds words of up to 58 brackets.
    #[test]
    fn mitm_key_round_trips_long_words() {
        use crate::state::{CLOSE, OPEN, Word, encode};
        let mut seed = 0x2545_F491_4F6C_DD1Du64;
        for _ in 0..20_000 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            // a random balanced word of length 2·(1..=29), and a cut
            let pairs = 1 + (seed % 29) as usize;
            let mut w = [0u8; 64];
            let (mut open, mut closed, mut i, mut r) = (0, 0, 0, seed);
            while closed < pairs {
                r = r.rotate_left(7) ^ 0x9E37_79B9;
                let can_open = open < pairs;
                let can_close = closed < open;
                let take_open = can_open && (!can_close || r & 1 == 1);
                w[i] = if take_open { OPEN } else { CLOSE };
                if take_open { open += 1 } else { closed += 1 }
                i += 1;
            }
            let h = ((seed >> 8) as usize % (2 * pairs + 1)).min(31);
            let k = encode(&Word { w, len: 2 * pairs, h });
            assert_eq!(crate::bits::to_state(crate::bits::from_state(k)), k);
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
