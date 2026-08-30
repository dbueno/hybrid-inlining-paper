//! How long the sequential Hybrid Inlining fixpoint takes, family by family.
//!
//! `examples/complexity.rs` fits `|R| ~ |P|^d` over *tuple counts*. This is
//! the same set of families measured in wall time, which is the axis tuple
//! counts cannot see: access-path depth grows with call depth and every path
//! comparison is `O(depth)`, so `fields(n)` gets slower much faster than it
//! gets bigger.
//!
//! ```text
//! cargo bench --bench families
//! cargo bench --bench families -- fields          # one family
//! cargo bench --bench families -- --quick         # stop at significance
//! ```
//!
//! Criterion reports time per EDB fact alongside total time, and writes a
//! per-family plot under `target/criterion/`.

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use hybrid_inlining_paper::analysis::run_hybrid;

mod common;

use common::{Case, by_family, group, throughput};

fn families(c: &mut Criterion) {
    for (family, cases) in by_family(common::family_cases()) {
        let mut g = group(c, family);
        for case in &cases {
            let Case { param, prog, k, .. } = case;
            throughput(&mut g, case);
            g.bench_function(BenchmarkId::from_parameter(param), |b| {
                // `PerIteration` keeps both the program walk in `for_program`
                // and the drop of the finished relations out of the timed
                // region, so what is measured is the fixpoint alone.
                b.iter_batched(|| (), |()| run_hybrid(prog, *k), BatchSize::PerIteration);
            });
        }
        g.finish();
    }
}

criterion_group!(benches, families);
criterion_main!(benches);
