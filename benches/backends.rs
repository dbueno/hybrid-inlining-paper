//! Sequential vs. parallel evaluation of the same Hybrid Inlining rules.
//!
//! Three backends, one rule source ([`hybrid_inlining_paper::analysis`]'s
//! `hybrid_rules`), so any difference is the evaluator and not the analysis:
//!
//! - `seq` — [`HybridAnalysis`], `ascent!`.
//! - `par` — [`ParallelHybridAnalysis`], `ascent_par!`: intra-rule
//!   parallelism, a parallel iterator over each rule's delta.
//! - `par+ir` — [`InterRuleHybridAnalysis`], the same plus
//!   `#![inter_rule_parallelism]`, so independent rules inside one SCC also
//!   run concurrently. Stratum B is one large SCC, which is the shape that
//!   axis exists for.
//!
//! Criterion groups the three under each family, so its report plots them
//! against each other over the family's parameter.
//!
//! Before a case is timed, the three backends are run once and their relation
//! sizes compared: a rule edit that makes them disagree fails here rather
//! than being reported as a speedup. (`tests/scaling.rs` pins the same
//! property on small programs, in a debug build.)
//!
//! ```text
//! cargo bench --bench backends
//! RAYON_NUM_THREADS=1 cargo bench --bench backends   # parallel overhead alone
//! cargo bench --bench backends -- wide               # one family only
//! ```

use std::cell::Cell;

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::analysis::parallel::ParallelHybridAnalysis;
use hybrid_inlining_paper::analysis::parallel::inter_rule::InterRuleHybridAnalysis;
use hybrid_inlining_paper::ir::Program;

mod common;

use common::{Case, by_family, group, sizes, throughput};

/// Run all three backends once and require that they derived the same thing.
/// Outside the timed region, and cheap next to the sample count.
fn check_agreement(family: &str, param: usize, prog: &Program, k: usize) {
    let mut seq = HybridAnalysis::for_program(prog, k);
    seq.run();
    let want = sizes(&seq.relation_sizes_summary());

    let mut par = ParallelHybridAnalysis::for_program(prog, k);
    par.run();
    let mut inter = InterRuleHybridAnalysis::for_program(prog, k);
    inter.run();

    for (backend, got) in [
        ("par", sizes(&par.relation_sizes_summary())),
        ("par+ir", sizes(&inter.relation_sizes_summary())),
    ] {
        for (rel, n) in &want {
            assert_eq!(
                got.get(rel),
                Some(n),
                "{family}({param}), k = {k}: {backend} derived {:?} for `{rel}`, seq derived {n}",
                got.get(rel)
            );
        }
    }
}

fn backends(c: &mut Criterion) {
    for (family, cases) in by_family(common::backend_cases()) {
        let mut g = group(c, family);
        for case in &cases {
            let Case { param, prog, k, .. } = case;
            throughput(&mut g, case);

            // Checked lazily, and at most once per case: criterion only calls
            // the routine for a benchmark that survived the command-line
            // filter, so `cargo bench -- wide` does not pay for the families
            // it is not measuring. The call sits outside `iter_batched`, so
            // it is not part of any sample.
            let checked = Cell::new(false);
            let ensure_checked = || {
                if !checked.replace(true) {
                    check_agreement(family, *param, prog, *k);
                }
            };

            // `PerIteration` keeps `for_program` and the drop of the finished
            // relations out of the timed region, so what is measured is the
            // fixpoint alone.
            g.bench_function(BenchmarkId::new("seq", param), |b| {
                ensure_checked();
                b.iter_batched(
                    || HybridAnalysis::for_program(prog, *k),
                    |mut a| {
                        a.run();
                        a
                    },
                    BatchSize::PerIteration,
                );
            });
            g.bench_function(BenchmarkId::new("par", param), |b| {
                ensure_checked();
                b.iter_batched(
                    || ParallelHybridAnalysis::for_program(prog, *k),
                    |mut a| {
                        a.run();
                        a
                    },
                    BatchSize::PerIteration,
                );
            });
            g.bench_function(BenchmarkId::new("par+ir", param), |b| {
                ensure_checked();
                b.iter_batched(
                    || InterRuleHybridAnalysis::for_program(prog, *k),
                    |mut a| {
                        a.run();
                        a
                    },
                    BatchSize::PerIteration,
                );
            });
        }
        g.finish();
    }
}

criterion_group!(benches, backends);
criterion_main!(benches);
