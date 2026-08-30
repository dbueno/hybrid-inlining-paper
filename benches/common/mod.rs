//! Case lists shared by the two bench targets.
//!
//! Every case is a `(family, parameter, program, k)` tuple. The family names
//! the criterion group, the parameter names the point within it, so
//! `cargo bench -- wide` re-measures one family and criterion's own report
//! plots wall time against the parameter.
//!
//! Sizes are inherited from the sweeps these benches replaced
//! (`examples/parallel.rs`, and the families in `examples/complexity.rs`):
//! large enough that the fixpoint dominates process startup, small enough
//! that the whole sweep stays re-runnable after a rule edit — about a minute
//! for `families`, about fifteen for `backends`.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::time::Duration;

use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion, Throughput};
use hybrid_inlining_paper::families::*;
use hybrid_inlining_paper::figure1;
use hybrid_inlining_paper::ir::Program;

/// One benchmarked program.
pub struct Case {
    /// Criterion group this case belongs to; also the `cargo bench` filter.
    pub family: &'static str,
    /// Point within the family, e.g. `512` for `wide(512, 8)`.
    pub param: usize,
    pub prog: Program,
    /// The k-limit on call strings, which for several families varies with
    /// the parameter and is therefore part of the case, not of the family.
    pub k: usize,
}

impl Case {
    fn new(family: &'static str, param: usize, prog: Program, k: usize) -> Self {
        Case { family, param, prog, k }
    }

    /// EDB fact count, used as criterion's throughput unit so the reports
    /// read as time per input fact rather than time per opaque parameter.
    pub fn edb(&self) -> u64 {
        edb_size(&self.prog) as u64
    }
}

/// Relation sizes, parsed out of Ascent's own summary. Used to check that the
/// parallel backends derive what the sequential one does before either is
/// timed.
pub fn sizes(summary: &str) -> BTreeMap<String, usize> {
    summary
        .lines()
        .filter_map(|line| {
            let (name, rest) = line.split_once(" size: ")?;
            Some((name.to_string(), rest.trim().parse().ok()?))
        })
        .collect()
}

/// A whole fixpoint is milliseconds of work, not nanoseconds, so criterion's
/// defaults (100 samples, 3s warm-up) would put the sweep out of reach. Ten
/// samples over two seconds is enough to separate the backends; pass
/// `--sample-size`/`--measurement-time` on the command line for a tighter
/// number on one family.
pub fn configure(group: &mut BenchmarkGroup<'_, WallTime>) {
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(300));
    group.measurement_time(Duration::from_secs(2));
}

/// The paper's own example, timed on its own so a rule edit that regresses
/// the small case is visible without reading a sweep. It has no family
/// parameter, so the k-limit stands in for one: the benchmark id is
/// `figure1/4`.
pub fn figure1_case() -> Case {
    Case::new("figure1", 4, figure1::program(), 4)
}

/// The backend comparison: sequential vs. the two parallel evaluators.
///
/// `wide` leads because it is the shape parallelism could pay on — many
/// procedures, real flow in each, a fixpoint whose rounds are wide rather
/// than deep. The rest are there to show what it costs elsewhere.
///
/// Sizes are capped below [`family_cases`]: three backends at ten samples is
/// thirty fixpoints per point, where the budget-driven loop this replaced got
/// through two or three, and the parallel evaluators run one to three orders
/// of magnitude slower than `seq` on everything except `wide`. The largest
/// point of each family therefore lives in the sequential sweep instead,
/// where it costs a fraction as much.
///
/// Measured on an idle 20-core M1 Ultra, the whole sweep is ~15 minutes, and
/// two points account for half of it: `chain(256)` at ~200 s and
/// `fields_chain(128)` at ~200 s, both dominated by `par`/`par+ir`. Raising
/// either cap one step costs roughly another four minutes apiece.
pub fn backend_cases() -> Vec<Case> {
    let mut cases = vec![figure1_case()];
    for m in [32usize, 128, 512, 2048, 8192] {
        cases.push(Case::new("wide", m, wide(m, 8), 0));
    }
    for w in [4usize, 8, 16] {
        cases.push(Case::new("wide-closure", w, wide(128, w), 0));
    }
    for n in [8usize, 32, 128, 256] {
        cases.push(Case::new("chain", n, chain(n, 2), n + 2));
    }
    for m in [8usize, 32, 128, 512] {
        cases.push(Case::new("fanin", m, fanin(m, 2), 3));
    }
    for d in [6usize, 8, 10, 12] {
        cases.push(Case::new("branching", d, branching(d, 2), d + 2));
    }
    for n in [64usize, 128, 256] {
        cases.push(Case::new("alias", n, alias(n), 0));
    }
    // `fields` is capped at 64: its access paths reach depth n and every path
    // comparison is O(depth), so wall time grows far faster than the tuple
    // count. That divergence is the point — see hi-complexity.md.
    for n in [16usize, 32, 64] {
        cases.push(Case::new("fields", n, fields(n), 0));
    }
    for n in [32usize, 128] {
        cases.push(Case::new("fields-chain", n, fields_chain(n), 0));
    }
    cases
}

/// The sequential wall-clock sweep: the same families as
/// `examples/complexity.rs`, which fits exponents over *tuple counts*. These
/// are the same shapes measured in time, so a relation that stays linear in
/// tuples while its wall time does not (access-path depth is the usual
/// culprit) shows up here and nowhere else.
pub fn family_cases() -> Vec<Case> {
    let mut cases = vec![figure1_case()];
    // The k-limit is what contains the call-string explosion, so each family
    // that has one is swept twice: with k tracking the depth, and with k held
    // fixed.
    for n in [16usize, 64, 256, 512] {
        cases.push(Case::new("chain-k-depth", n, chain(n, 2), n + 2));
        cases.push(Case::new("chain-k-2", n, chain(n, 2), 2));
    }
    for d in [6usize, 8, 10, 12] {
        cases.push(Case::new("branching-k-depth", d, branching(d, 2), d + 2));
        cases.push(Case::new("branching-k-3", d, branching(d, 2), 3));
    }
    for m in [16usize, 64, 256, 512] {
        cases.push(Case::new("fanin", m, fanin(m, 2), 3));
    }
    for t in [8usize, 32, 128, 512] {
        cases.push(Case::new("targets", t, targets(t), 2));
    }
    for n in [64usize, 128, 256, 512] {
        cases.push(Case::new("alias", n, alias(n), 0));
    }
    for n in [8usize, 16, 32, 64] {
        cases.push(Case::new("fields", n, fields(n), 0));
    }
    for n in [32usize, 64, 128, 256] {
        cases.push(Case::new("fields-chain", n, fields_chain(n), 0));
    }
    for m in [128usize, 512, 2048, 8192] {
        cases.push(Case::new("wide", m, wide(m, 8), 0));
    }
    for w in [4usize, 8, 16, 32] {
        cases.push(Case::new("wide-closure", w, wide(128, w), 0));
    }
    cases
}

/// Group the flat case list by family, preserving order within each.
pub fn by_family(cases: Vec<Case>) -> Vec<(&'static str, Vec<Case>)> {
    let mut out: Vec<(&'static str, Vec<Case>)> = vec![];
    for case in cases {
        match out.last_mut() {
            Some((family, group)) if *family == case.family => group.push(case),
            _ => out.push((case.family, vec![case])),
        }
    }
    out
}

/// Open a criterion group named for the family, pre-configured.
pub fn group<'a>(c: &'a mut Criterion, family: &str) -> BenchmarkGroup<'a, WallTime> {
    let mut g = c.benchmark_group(family);
    configure(&mut g);
    g
}

/// Declare the input size for the next benchmark in `group`.
pub fn throughput(group: &mut BenchmarkGroup<'_, WallTime>, case: &Case) {
    group.throughput(Throughput::Elements(case.edb()));
}
