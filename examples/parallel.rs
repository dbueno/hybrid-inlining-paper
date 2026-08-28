//! Sequential vs. parallel evaluation of the same Hybrid Inlining rules.
//!
//! Three backends, one rule source ([`hybrid_inlining_paper::analysis`]'s
//! `hybrid_rules`), so any difference is the evaluator and not the analysis:
//!
//! - `seq`    — [`HybridAnalysis`], `ascent!`.
//! - `par`    — [`ParallelHybridAnalysis`], `ascent_par!`: intra-rule
//!              parallelism, a parallel iterator over each rule's delta.
//! - `par+ir` — [`InterRuleHybridAnalysis`], the same plus
//!              `#![inter_rule_parallelism]`, so independent rules inside one
//!              SCC also run concurrently. Stratum B is one large SCC, which
//!              is the shape that axis exists for.
//!
//! Every run is checked against `seq` relation-by-relation, so this doubles as
//! a correctness test of the parallel backends: a rule edit that makes them
//! disagree fails here loudly.
//!
//! ```text
//! cargo run --release --example parallel
//! RAYON_NUM_THREADS=1 cargo run --release --example parallel   # parallel overhead alone
//! ```

use std::collections::BTreeMap;
use std::io::Write;
use std::time::{Duration, Instant};

use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::analysis::parallel::ParallelHybridAnalysis;
use hybrid_inlining_paper::analysis::parallel::inter_rule::InterRuleHybridAnalysis;
use hybrid_inlining_paper::families::*;
use hybrid_inlining_paper::figure1;
use hybrid_inlining_paper::ir::Program;

/// Relation sizes, parsed out of Ascent's own summary.
fn sizes(summary: &str) -> BTreeMap<String, usize> {
    summary
        .lines()
        .filter_map(|line| {
            let (name, rest) = line.split_once(" size: ")?;
            Some((name.to_string(), rest.trim().parse().ok()?))
        })
        .collect()
}

/// Roughly how long to spend on each (case, backend) pair. The parallel
/// backends are slow enough here that a fixed repetition count would make the
/// whole run unusable; a budget keeps it re-runnable after a rule edit.
const BUDGET: Duration = Duration::from_millis(750);
const MAX_REPS: usize = 20;

/// Best wall time over as many runs as `BUDGET` allows (at least one), plus
/// the resulting relation sizes. Best-of rather than mean: we are after the
/// cost of the fixpoint, not of whatever else the machine was doing.
fn time<T>(build: impl Fn() -> T, run: impl Fn(&mut T), summary: impl Fn(&T) -> String)
    -> (Duration, BTreeMap<String, usize>)
{
    let mut best = Duration::MAX;
    let mut out = BTreeMap::new();
    let start = Instant::now();
    for _ in 0..MAX_REPS {
        let mut a = build();
        let t0 = Instant::now();
        run(&mut a);
        best = best.min(t0.elapsed());
        out = sizes(&summary(&a));
        if start.elapsed() >= BUDGET {
            break;
        }
    }
    (best, out)
}

struct Row {
    label: String,
    edb: usize,
    seq: Duration,
    par: Duration,
    inter: Duration,
    tuples: usize,
    agree: bool,
}

fn bench(label: String, prog: &Program, k: usize) -> Row {
    let (seq, s_sizes) = time(
        || HybridAnalysis::for_program(prog, k),
        |a| a.run(),
        |a| a.relation_sizes_summary(),
    );
    let (par, p_sizes) = time(
        || ParallelHybridAnalysis::for_program(prog, k),
        |a| a.run(),
        |a| a.relation_sizes_summary(),
    );
    let (inter, i_sizes) = time(
        || InterRuleHybridAnalysis::for_program(prog, k),
        |a| a.run(),
        |a| a.relation_sizes_summary(),
    );

    let agree = s_sizes == p_sizes && s_sizes == i_sizes;
    if !agree {
        for (name, n) in &s_sizes {
            let (p, i) = (p_sizes.get(name), i_sizes.get(name));
            if p != Some(n) || i != Some(n) {
                eprintln!("  MISMATCH {name}: seq {n}, par {p:?}, par+ir {i:?}");
            }
        }
    }

    Row {
        label,
        edb: edb_size(prog),
        seq,
        par,
        inter,
        tuples: s_sizes.values().sum(),
        agree,
    }
}

fn header() {
    println!(
        "  {:<26} {:>7} {:>9} {:>11} {:>11} {:>11} {:>7} {:>7}  {}",
        "case", "|P|", "tuples", "seq", "par", "par+ir", "par×", "ir×", "agree"
    );
}

fn show(r: &Row) {
    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    println!(
        "  {:<26} {:>7} {:>9} {:>9.2}ms {:>9.2}ms {:>9.2}ms {:>6.2}x {:>6.2}x  {}",
        r.label,
        r.edb,
        r.tuples,
        ms(r.seq),
        ms(r.par),
        ms(r.inter),
        r.seq.as_secs_f64() / r.par.as_secs_f64(),
        r.seq.as_secs_f64() / r.inter.as_secs_f64(),
        if r.agree { "yes" } else { "NO — see above" }
    );
    // Rows are printed as they are measured, so a run that is taking too long
    // can still be read (and interrupted).
    let _ = std::io::stdout().flush();
}

fn main() {
    println!(
        "rayon threads: {}   (set RAYON_NUM_THREADS to vary)\n",
        ascent::rayon::current_num_threads()
    );

    println!("## Figure 1");
    header();
    show(&bench("figure1, k = 4".into(), &figure1::program(), 4));

    println!("\n## scaled families");
    header();

    let mut cases: Vec<(String, Program, usize)> = vec![];
    for n in [8usize, 32, 128, 512] {
        cases.push((format!("chain({n}), k = n+2"), chain(n, 2), n + 2));
    }
    for m in [8usize, 32, 128, 512] {
        cases.push((format!("fanin({m}), k = 3"), fanin(m, 2), 3));
    }
    for d in [6usize, 8, 10, 12] {
        cases.push((format!("branching({d}), k = d+2"), branching(d, 2), d + 2));
    }
    for n in [64usize, 256, 512] {
        cases.push((format!("alias({n})"), alias(n), 0));
    }
    // `fields` is capped at 64: its access paths reach depth n, and every
    // path comparison is O(depth), so the wall time grows far faster than the
    // tuple count. That divergence is the point — see hi-complexity.md.
    for n in [16usize, 32, 64] {
        cases.push((format!("fields({n})"), fields(n), 0));
    }
    for n in [32usize, 128, 256] {
        cases.push((format!("fields_chain({n})"), fields_chain(n), 0));
    }

    for (label, prog, k) in &cases {
        show(&bench(label.clone(), prog, *k));
    }
}
