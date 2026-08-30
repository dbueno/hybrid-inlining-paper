//! Heap held by the finished fixpoint, measured under criterion.
//!
//! Same families and sizes as `benches/families.rs`, same sequential
//! evaluator — the measured quantity is bytes rather than nanoseconds. What
//! that buys over `examples/memory.rs` is criterion's baseline machinery: the
//! comparison against the previous run is done for you, per family point, with
//! the same "improved/regressed" verdict the wall-time benches give.
//!
//! ```text
//! cargo bench --bench memory -- --save-baseline before   # before a rule edit
//! cargo bench --bench memory -- --baseline before        # after it
//! cargo bench --bench memory -- fields                   # one family
//! ```
//!
//! The value is *retained* bytes: live heap at the end of the fixpoint minus
//! live heap at its start, with the finished relations still alive. So it is
//! the size of the derived relations and every index Ascent built over them —
//! the thing that should shrink when a rule stops deriving something, or stops
//! needing a column to join on. Transient peak and the per-relation split live
//! in `examples/memory.rs`; this target is for the one number that a rule edit
//! either moves or does not.
//!
//! Two things to know when reading the output. Criterion labels the value
//! `time:` whatever the measurement is, so the line reads `time: [12.210 MiB
//! ...]`; the unit is the truth, the label is boilerplate. And its statistics
//! assume noise, of which there is very little here — the fixpoint is
//! deterministic, so the ten samples of a point agree to the byte, and a
//! p-value of 0.00 on a 0.1% change is criterion doing as asked rather than a
//! real effect. Read the point estimate.

use std::time::Duration;

use criterion::measurement::{Measurement, ValueFormatter};
use criterion::{
    BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main,
};
use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::mem::Counting;

mod common;

use common::{Case, by_family};

#[global_allocator]
static ALLOC: Counting = Counting;

/// Criterion measurement: bytes still held when the routine returns.
///
/// Criterion calls `end` before dropping the iteration's output (see
/// `Bencher::iter_batched`), so with [`BatchSize::PerIteration`] the delta is
/// taken while the finished analysis is still alive. That is what makes this
/// "what the relations weigh" rather than "what leaked".
struct HeapHeld;

impl Measurement for HeapHeld {
    /// Live bytes when the iteration started.
    type Intermediate = usize;
    type Value = u64;

    fn start(&self) -> usize {
        Counting::live()
    }

    fn end(&self, start: usize) -> u64 {
        Counting::live().saturating_sub(start) as u64
    }

    fn add(&self, a: &u64, b: &u64) -> u64 {
        a + b
    }

    fn zero(&self) -> u64 {
        0
    }

    fn to_f64(&self, v: &u64) -> f64 {
        *v as f64
    }

    fn formatter(&self) -> &dyn ValueFormatter {
        &ByteFormatter
    }
}

struct ByteFormatter;

impl ValueFormatter for ByteFormatter {
    fn scale_values(&self, typical: f64, values: &mut [f64]) -> &'static str {
        let (unit, scale) = if typical >= 1024.0 * 1024.0 * 1024.0 {
            ("GiB", 1024.0 * 1024.0 * 1024.0)
        } else if typical >= 1024.0 * 1024.0 {
            ("MiB", 1024.0 * 1024.0)
        } else if typical >= 1024.0 {
            ("KiB", 1024.0)
        } else {
            ("B", 1.0)
        };
        for v in values.iter_mut() {
            *v /= scale;
        }
        unit
    }

    /// Throughput is the case's EDB size, so the derived figure is bytes of
    /// fixpoint per input fact — the density number, comparable across
    /// families and across sizes within one.
    fn scale_throughputs(
        &self,
        _typical: f64,
        throughput: &Throughput,
        values: &mut [f64],
    ) -> &'static str {
        let (n, unit) = match *throughput {
            Throughput::Elements(n) => (n, "B/fact"),
            Throughput::ElementsAndBytes { elements, .. } => (elements, "B/fact"),
            Throughput::Bytes(n) | Throughput::BytesDecimal(n) => (n, "B/input B"),
            Throughput::Bits(n) => (n, "B/input bit"),
        };
        for v in values.iter_mut() {
            *v /= n.max(1) as f64;
        }
        unit
    }

    fn scale_for_machines(&self, _values: &mut [f64]) -> &'static str {
        "bytes"
    }
}

fn memory(c: &mut Criterion<HeapHeld>) {
    for (family, cases) in by_family(common::family_cases()) {
        // `mem-` prefix, because criterion keys its saved data by benchmark id
        // and this target measures the same families at the same sizes as
        // `benches/families.rs`. Sharing an id would have each target
        // overwrite the other's baseline and then report the difference
        // between bytes and nanoseconds as a change. The prefix is not part of
        // what a filter has to match: `-- fields` still selects `mem-fields`.
        let mut g = c.benchmark_group(format!("mem-{family}"));
        // The measurement is deterministic, so samples are for criterion's
        // benefit rather than ours; the minimum it accepts is plenty, and the
        // sweep then costs about what one wall-time pass costs.
        g.sample_size(10);
        g.warm_up_time(Duration::from_millis(300));
        g.measurement_time(Duration::from_secs(2));

        for case in &cases {
            let Case { param, prog, k, .. } = case;
            g.throughput(Throughput::Elements(case.edb()));
            g.bench_function(BenchmarkId::from_parameter(param), |b| {
                // `PerIteration` both keeps `for_program` out of the measured
                // region and forces criterion's batch size to one, which is
                // what lets `end` see the analysis before it is dropped.
                b.iter_batched(
                    || HybridAnalysis::for_program(prog, *k),
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

criterion_group! {
    name = benches;
    // No plots. The samples of a point are bit-identical — the fixpoint is
    // deterministic and so is the allocation sequence — and criterion's
    // kernel-density estimate panics on a zero-variance sample
    // (`index out of bounds` in `kde.rs`) when it comes to draw the
    // comparison against a baseline. The numbers and the baseline diff are
    // unaffected; only the HTML report is skipped.
    config = Criterion::default().with_measurement(HeapHeld).without_plots();
    targets = memory
}
criterion_main!(benches);
