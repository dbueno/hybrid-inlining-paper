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
//!
//! `--timeout SECS` caps each fixpoint, as `ctadl_profile` does: Ascent
//! checks it *between* iterations, so it declines to start another rather
//! than cutting one short, and a run can overrun its budget by a lot. There
//! is no default — omit it and every backend runs to convergence, which is
//! what the `k = 6` recipe in `backflash-profile.md` wants. A truncated run's
//! relation sizes are a function of the budget, so once anything times out
//! the agreement check and the speedups are no longer claims about the
//! evaluators, and this program says so rather than printing them straight:
//! `seq` timing out at 240s while `par+ir` converges is exactly the shape
//! that would otherwise read as a derivation bug.

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
    /// One per repeat, in step with `walls`: did that repeat reach a
    /// fixpoint, or did `--timeout` stop it?
    converged: Vec<bool>,
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

    /// Did any repeat stop at the budget? One is enough to disqualify the
    /// whole backend from being compared: the sizes come from the first
    /// repeat and the median from all of them.
    fn timed_out(&self) -> bool {
        self.converged.iter().any(|c| !c)
    }
}

/// `timeout` is passed straight to Ascent's generated `run_timeout`, which
/// treats [`Duration::MAX`] as "no budget" and skips reading the clock
/// altogether — so the no-`--timeout` path is the same code, not a branch
/// around it.
fn run_backend(name: &str, prog: &Program, k: usize, repeat: usize, timeout: Duration) -> Run {
    let mut walls = Vec::with_capacity(repeat);
    let mut converged = Vec::with_capacity(repeat);
    let mut sizes_of = BTreeMap::new();
    for i in 0..repeat {
        let start = Instant::now();
        let (done, summary) = match name {
            "seq" => {
                let mut a = HybridAnalysis::for_program(prog, k);
                let done = a.run_timeout(timeout);
                (done, a.relation_sizes_summary())
            }
            "par" => {
                let mut a = ParallelHybridAnalysis::for_program(prog, k);
                let done = a.run_timeout(timeout);
                (done, a.relation_sizes_summary())
            }
            "par+ir" => {
                let mut a = InterRuleHybridAnalysis::for_program(prog, k);
                let done = a.run_timeout(timeout);
                (done, a.relation_sizes_summary())
            }
            other => panic!("unknown backend `{other}`"),
        };
        let wall = start.elapsed();
        println!(
            "  {name} run {}: {wall:?}{}",
            i + 1,
            if done { "" } else { "  (TIMED OUT)" }
        );
        walls.push(wall);
        converged.push(done);
        if i == 0 {
            sizes_of = sizes(&summary);
        }
        // A repeat that hit the budget will hit it again, at the same
        // iteration, for as many minutes as it is given. Measuring is
        // expensive; stop rather than buy the same non-result twice.
        if !done {
            if i + 1 < repeat {
                println!("  {name}: stopping after {} of {repeat} repeats (timed out)", i + 1);
            }
            break;
        }
    }
    let tuples = sizes_of.values().sum();
    Run { walls, converged, sizes: sizes_of, tuples }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut k = 1usize;
    let mut max_procs: Option<usize> = None;
    let mut repeat = 3usize;
    let mut backends: Vec<String> = Vec::new();
    // No budget by default: `Duration::MAX` is what Ascent's generated
    // `run_timeout` reads as "run to convergence".
    let mut timeout = Duration::MAX;

    let mut opts = Options::default();

    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "--max-procs" => max_procs = Some(args.next().unwrap_or_default().parse()?),
            "--repeat" => repeat = args.next().unwrap_or_default().parse()?,
            "--timeout" => {
                timeout = Duration::from_secs(args.next().unwrap_or_default().parse()?);
            }
            "--backend" => backends.push(args.next().unwrap_or_default()),
            "-h" | "--help" => {
                eprintln!(
                    "usage: ctadl_parallel <import>... [--k N] [--max-procs N] \
                     [--repeat N] [--timeout SECS] [--backend seq|par|par+ir]... \
                     [--ssa] [--no-preprocess]"
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

    let timeout_desc = if timeout == Duration::MAX {
        "none".to_string()
    } else {
        format!("{}s", timeout.as_secs())
    };
    println!(
        "procs={} stmts={} virtual_call={} direct_call={} k={k} repeat={repeat} \
         timeout={timeout_desc} threads={threads}",
        prog.procedure.len(),
        prog.in_proc.len(),
        prog.virtual_call.len(),
        prog.direct_call.len(),
    );

    let mut runs: Vec<(String, Run)> = Vec::new();
    for name in &backends {
        let r = run_backend(name, &prog, k, repeat, timeout);
        println!(
            "  {name} median: {:?}  ({} tuples){}",
            r.median(),
            r.tuples,
            if r.timed_out() { "  (partial: timed out)" } else { "" }
        );
        runs.push((name.clone(), r));
    }

    // The sizes themselves, from the first backend run — they are the same
    // set for all of them, and the agreement check below is what says so.
    // A converged run at a `k` the sequential binary has only ever timed out
    // at is the one case where this program is the only source of them.
    if let Some((name, r)) = runs.first() {
        println!(
            "\n=== relation sizes ({name}){} ===",
            if r.timed_out() { ", TRUNCATED — a function of the budget, not of k" } else { "" }
        );
        for (rel, n) in &r.sizes {
            println!("{rel} size: {n}");
        }
    }

    // Agreement first, speedup second, and in that order on purpose: a
    // backend that derives less is not faster, it is wrong.
    if let Some((_, seq)) = runs.iter().find(|(n, _)| n == "seq") {
        println!("\n=== agreement with seq ===");
        if seq.timed_out() {
            println!(
                "  seq stopped at the budget, so its sizes are a snapshot and \
                 nothing below is a check on any backend"
            );
        }
        for (name, r) in &runs {
            if name == "seq" {
                continue;
            }
            // Two runs stopped at different points of the same fixpoint are
            // expected to differ. Report the comparison anyway — the numbers
            // are still worth seeing — but never as evidence of a bug.
            let comparable = !seq.timed_out() && !r.timed_out();
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
                println!(
                    "  {name}: all {} relations agree{}",
                    seq.sizes.len(),
                    if comparable { "" } else { "  (both snapshots; agreement here is luck)" }
                );
            } else if comparable {
                println!("  {name}: {} DISAGREE", bad.len());
                for line in &bad {
                    println!("    {line}");
                }
            } else {
                println!(
                    "  {name}: {} differ, but a truncated run is not comparable — \
                     re-run without --timeout to check the derivation",
                    bad.len()
                );
                for line in &bad {
                    println!("    {line}");
                }
            }
        }

        println!("\n=== speedup over seq ===");
        let base = seq.median().as_secs_f64();
        for (name, r) in &runs {
            let t = r.median().as_secs_f64();
            // A backend that stopped at the budget did less work than one
            // that finished, so their ratio is not a speedup. Print the time
            // and withhold the number rather than print a flattering one.
            if seq.timed_out() || r.timed_out() {
                println!("  {name:<7} {t:>8.3}s   --  (timed out; not a speedup)");
            } else {
                println!("  {name:<7} {t:>8.3}s   {:.2}x", base / t);
            }
        }
    }

    Ok(())
}
