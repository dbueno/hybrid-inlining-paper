//! Sequential vs. parallel evaluation of the same rules, on a CTADL import.
//!
//! ```text
//! cargo run --features ctadl --release --example ctadl_parallel -- \
//!     backflash.apk --k 1 --repeat 3
//! ```
//!
//! `benches/backends.rs` asks this question of the synthetic families of
//! `src/families.rs`, which are small and regular; this asks it of a real
//! APK, which is neither. Three backends, one rule source
//! (`analysis::hybrid_rules`), so any difference is the evaluator:
//!
//! - `seq` — [`HybridAnalysis`], `ascent!`.
//! - `par` — [`ParallelHybridAnalysis`], `ascent_par!`: intra-rule
//!   parallelism, a parallel iterator over each rule's delta.
//! - `par+ir` — [`InterRuleHybridAnalysis`], the same plus
//!   `#![inter_rule_parallelism]`, so independent rules inside one SCC also
//!   run concurrently. Stratum B is one large SCC, which is the shape that
//!   axis exists for.
//!
//! Every backend's relation sizes are compared against the sequential run's
//! before any speedup is reported: a backend that is fast because it derived
//! less is a bug, not a result. `--backend` runs one of the three alone,
//! which is what to do under `/usr/bin/time -l` — a peak footprint is
//! per-process, so three fixpoints in one process report one peak.

use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::analysis::parallel::ParallelHybridAnalysis;
use hybrid_inlining_paper::analysis::parallel::inter_rule::InterRuleHybridAnalysis;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};
use hybrid_inlining_paper::ir::Program;

/// Relation sizes, parsed out of Ascent's own summary, as `benches/common`
/// does it. Compared by name *and* by count: a backend that drops a relation
/// entirely has to show up as a missing key, not as an unnoticed absence.
fn sizes(summary: &str) -> BTreeMap<String, usize> {
    summary
        .lines()
        .filter_map(|line| {
            let (name, rest) = line.split_once(" size: ")?;
            Some((name.to_string(), rest.trim().parse().ok()?))
        })
        .collect()
}

/// One backend's run: its wall times, and what it derived.
struct Run {
    walls: Vec<Duration>,
    sizes: BTreeMap<String, usize>,
    tuples: usize,
}

impl Run {
    /// The median of the repeats. Wall clock on a machine with other things
    /// on it has a long right tail and no left one, so the median is the
    /// honest summary; every observation is printed anyway.
    fn median(&self) -> Duration {
        let mut v = self.walls.clone();
        v.sort_unstable();
        v[v.len() / 2]
    }
}

fn run_backend(name: &str, prog: &Program, k: usize, repeat: usize) -> Run {
    let mut walls = Vec::with_capacity(repeat);
    let mut sizes_of = BTreeMap::new();
    for i in 0..repeat {
        let start = Instant::now();
        let summary = match name {
            "seq" => {
                let mut a = HybridAnalysis::for_program(prog, k);
                a.run();
                a.relation_sizes_summary()
            }
            "par" => {
                let mut a = ParallelHybridAnalysis::for_program(prog, k);
                a.run();
                a.relation_sizes_summary()
            }
            "par+ir" => {
                let mut a = InterRuleHybridAnalysis::for_program(prog, k);
                a.run();
                a.relation_sizes_summary()
            }
            other => panic!("unknown backend `{other}`"),
        };
        let wall = start.elapsed();
        println!("  {name} run {}: {wall:?}", i + 1);
        walls.push(wall);
        if i == 0 {
            sizes_of = sizes(&summary);
        }
    }
    let tuples = sizes_of.values().sum();
    Run { walls, sizes: sizes_of, tuples }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut k = 1usize;
    let mut max_procs: Option<usize> = None;
    let mut repeat = 3usize;
    let mut backends: Vec<String> = Vec::new();

    let mut opts = Options::default();

    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "--max-procs" => max_procs = Some(args.next().unwrap_or_default().parse()?),
            "--repeat" => repeat = args.next().unwrap_or_default().parse()?,
            "--backend" => backends.push(args.next().unwrap_or_default()),
            "-h" | "--help" => {
                eprintln!(
                    "usage: ctadl_parallel <import>... [--k N] [--max-procs N] \
                     [--repeat N] [--backend seq|par|par+ir]... [--ssa] [--no-preprocess]"
                );
                return Ok(());
            }
            "--ssa" => opts.preprocess = Preprocess::ssa_only(),
            "--ctadl-pre" => opts.preprocess = Preprocess::ctadl(),
            "--no-preprocess" => opts.preprocess = Preprocess::none(),
            _ => imports.push(a),
        }
    }
    if imports.is_empty() {
        eprintln!("no imports given; try --help");
        return Ok(());
    }
    if backends.is_empty() {
        backends = vec!["seq".into(), "par".into(), "par+ir".into()];
    }

    let mut t = Translator::new(opts.clone());
    for name in &imports {
        let (cir, vmt) = read_import(name)?;
        t.add_import(cir, &vmt);
    }
    let mut prog = t.finish();
    if let Some(n) = max_procs {
        prog = restrict(&prog, n);
    }

    // Rayon reads `RAYON_NUM_THREADS` at first use and never again, so the
    // thread count is a property of the whole process; report it next to the
    // times it explains.
    let threads = std::env::var("RAYON_NUM_THREADS")
        .ok()
        .unwrap_or_else(|| {
            std::thread::available_parallelism().map_or("?".into(), |n| n.to_string())
        });

    println!(
        "procs={} stmts={} virtual_call={} direct_call={} k={k} repeat={repeat} threads={threads}",
        prog.procedure.len(),
        prog.in_proc.len(),
        prog.virtual_call.len(),
        prog.direct_call.len(),
    );

    let mut runs: Vec<(String, Run)> = Vec::new();
    for name in &backends {
        let r = run_backend(name, &prog, k, repeat);
        println!("  {name} median: {:?}  ({} tuples)", r.median(), r.tuples);
        runs.push((name.clone(), r));
    }

    // The sizes themselves, from the first backend run — they are the same
    // set for all of them, and the agreement check below is what says so.
    // A converged run at a `k` the sequential binary has only ever timed out
    // at is the one case where this program is the only source of them.
    if let Some((name, r)) = runs.first() {
        println!("\n=== relation sizes ({name}) ===");
        for (rel, n) in &r.sizes {
            println!("{rel} size: {n}");
        }
    }

    // Agreement first, speedup second, and in that order on purpose: a
    // backend that derives less is not faster, it is wrong.
    if let Some((_, seq)) = runs.iter().find(|(n, _)| n == "seq") {
        println!("\n=== agreement with seq ===");
        for (name, r) in &runs {
            if name == "seq" {
                continue;
            }
            let mut bad = Vec::new();
            for (rel, n) in &seq.sizes {
                if r.sizes.get(rel) != Some(n) {
                    bad.push(format!("{rel}: seq {n}, {name} {:?}", r.sizes.get(rel)));
                }
            }
            for rel in r.sizes.keys() {
                if !seq.sizes.contains_key(rel) {
                    bad.push(format!("{rel}: only in {name}"));
                }
            }
            if bad.is_empty() {
                println!("  {name}: all {} relations agree", seq.sizes.len());
            } else {
                println!("  {name}: {} DISAGREE", bad.len());
                for line in &bad {
                    println!("    {line}");
                }
            }
        }

        println!("\n=== speedup over seq ===");
        let base = seq.median().as_secs_f64();
        for (name, r) in &runs {
            let t = r.median().as_secs_f64();
            println!("  {name:<7} {t:>8.3}s   {:.2}x", base / t);
        }
    }

    Ok(())
}
