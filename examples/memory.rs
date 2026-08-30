//! What the Hybrid Inlining fixpoint costs in bytes, family by family.
//!
//! `examples/complexity.rs` fits `|R| ~ |P|^d` over tuple counts and
//! `cargo bench` measures wall time. Neither answers "did that rule edit make
//! the relations leaner": a tuple is not a fixed number of bytes here (access
//! paths and call strings carry `Arc` payloads that grow with the program),
//! and Ascent stores every relation as tuples *plus* private index maps that
//! `relation_sizes_summary()` never mentions. Both are counted at the
//! allocator — see [`hybrid_inlining_paper::mem`].
//!
//! ```text
//! cargo run --release --example memory
//! ```
//!
//! Two columns per family carry the message:
//!
//! - `B/tuple` — retained heap per derived fact, indices included. Rising with
//!   `n` means the tuples themselves are getting fatter, which tuple counts
//!   cannot show.
//! - the `retained ~ |P|^d` fit against the `tuples ~ |P|^d` fit beside it.
//!   Bytes growing with a bigger exponent than tuples is the signature of a
//!   relation whose *elements* grow: `fields_chain` is the worst case, and
//!   the reason `hi-complexity.md` argues for a depth limit on access paths.
//!
//! Re-run after editing the rules and compare against the numbers you kept.
//! `cargo bench --bench memory` measures the same quantity under criterion,
//! where `--save-baseline`/`--baseline` does the comparing for you.

use hybrid_inlining_paper::families::*;
use hybrid_inlining_paper::figure1;
use hybrid_inlining_paper::ir::Program;
use hybrid_inlining_paper::mem::{Counting, Usage, human, idb_tuples, report, run_measured};

#[global_allocator]
static ALLOC: Counting = Counting;

/// Per-relation table for one program, plus what the relations do not explain.
fn breakdown(label: &str, prog: &Program, k: usize) {
    let (h, usage) = run_measured(prog, k);
    println!("\n## {label}");
    report(&h, &usage, edb_size(prog));
}

/// Least-squares slope of `log y` against `log x`. Same fit as
/// `examples/complexity.rs`, so the exponents are comparable.
fn exponent(xs: &[f64], ys: &[f64]) -> f64 {
    let pts: Vec<(f64, f64)> = xs
        .iter()
        .zip(ys)
        .filter(|(_, y)| **y > 0.0)
        .map(|(x, y)| (x.ln(), y.ln()))
        .collect();
    if pts.len() < 2 {
        return 0.0;
    }
    let n = pts.len() as f64;
    let mx = pts.iter().map(|q| q.0).sum::<f64>() / n;
    let my = pts.iter().map(|q| q.1).sum::<f64>() / n;
    let num: f64 = pts.iter().map(|(x, y)| (x - mx) * (y - my)).sum();
    let den: f64 = pts.iter().map(|(x, _)| (x - mx).powi(2)).sum();
    if den == 0.0 { 0.0 } else { num / den }
}

/// The parameter a family is swept over, read off its label: `m` for
/// `fanin(m), k = 3`, `w` for `wide(64, w)` — the first argument that is not a
/// fixed number. The sweep row is labelled with it so the table reads against
/// the heading instead of calling every parameter `n`.
fn param(label: &str) -> &str {
    label
        .split_once('(')
        .and_then(|(_, rest)| rest.split_once(')'))
        .and_then(|(args, _)| {
            args.split(',')
                .map(str::trim)
                .find(|a| a.parse::<usize>().is_err())
        })
        .unwrap_or("n")
}

struct Row {
    n: usize,
    edb: usize,
    tuples: usize,
    usage: Usage,
}

fn sweep(label: &str, note: &str, ns: &[usize], build: impl Fn(usize) -> (Program, usize)) {
    let rows: Vec<Row> = ns
        .iter()
        .map(|&n| {
            let (prog, k) = build(n);
            let edb = edb_size(&prog);
            let (h, usage) = run_measured(&prog, k);
            let tuples = idb_tuples(&h);
            drop(h);
            Row { n, edb, tuples, usage }
        })
        .collect();

    println!("\n\n### {label} — {note}");
    let cell = |s: String| format!("{s:>10}");
    let line = |name: &str, f: &dyn Fn(&Row) -> String| {
        println!(
            "  {name:<12}{}",
            rows.iter().map(|r| cell(f(r))).collect::<Vec<_>>().join("")
        );
    };
    line(param(label), &|r| r.n.to_string());
    line("|P|", &|r| r.edb.to_string());
    line("tuples", &|r| r.tuples.to_string());
    line("retained", &|r| human(r.usage.retained));
    line("peak", &|r| human(r.usage.peak));
    line("B/tuple", &|r| format!("{:.1}", r.usage.bytes_per(r.tuples)));

    let xs: Vec<f64> = rows.iter().map(|r| r.edb as f64).collect();
    let tup = exponent(&xs, &rows.iter().map(|r| r.tuples as f64).collect::<Vec<_>>());
    let bytes = exponent(
        &xs,
        &rows.iter().map(|r| r.usage.retained as f64).collect::<Vec<_>>(),
    );
    println!("  fit:        tuples ~ |P|^{tup:.2}   retained ~ |P|^{bytes:.2}");

    // The exponents are the coarse signal; `B/tuple` is the sensitive one.
    // A family whose tuples stay the same shape holds it flat to about a
    // percent across a sweep spanning an order of magnitude (`wide` goes 816
    // to 824), so a sixth more bytes per tuple at the far end is the
    // access-path suffix — or the call string — growing with the program,
    // not measurement slack.
    let (first, last) = (&rows[0], rows.last().unwrap());
    let growth = last.usage.bytes_per(last.tuples) / first.usage.bytes_per(first.tuples).max(1.0);
    if growth >= 1.15 {
        println!(
            "              <== {growth:.2}x the bytes per tuple over the sweep: \
             the tuples themselves are growing"
        );
    }
}

fn main() {
    println!("# Heap cost of the fixpoint");
    println!(
        "\nBytes are what the program asked the allocator for: no size-class\n\
         rounding, no per-allocation header, so RSS runs above these. Measured\n\
         over `run()` only — building the analysis and copying the EDB in is\n\
         outside the measured region."
    );

    breakdown("Figure 1 (k = 4)", &figure1::program(), 4);
    breakdown("wide(512, 8)", &wide(512, 8), 0);
    breakdown("fields_chain(32)", &fields_chain(32), 0);

    sweep(
        "chain(n), k = n+2",
        "call chain of depth n above one critical virtual call",
        &[2, 4, 8, 16, 32],
        |n| (chain(n, 2), n + 2),
    );
    sweep(
        "chain(n), k = 2",
        "the same chain with the k-limit held fixed",
        &[2, 4, 8, 16, 32],
        |n| (chain(n, 2), 2),
    );
    sweep(
        "fanin(m), k = 3",
        "one critical procedure called from m distinct callers",
        &[2, 4, 8, 16, 32],
        |m| (fanin(m, 2), 3),
    );
    sweep(
        "branching(d), k = d+2",
        "each level calls the one below from two sites",
        &[1, 2, 3, 4, 5, 6, 7, 8],
        |d| (branching(d, 2), d + 2),
    );
    sweep(
        "branching(d), k = 3",
        "the same, with the k-limit capping the call string",
        &[1, 2, 3, 4, 5, 6, 7, 8],
        |d| (branching(d, 2), 3),
    );
    sweep(
        "targets(t), k = 2",
        "one critical call with t CHA implementations, unpinned",
        &[2, 4, 8, 16, 32],
        |t| (targets(t), 2),
    );
    sweep(
        "alias(n)",
        "n allocations merged into a chain of n variables; no calls",
        &[4, 8, 16, 32, 64],
        |n| (alias(n), 0),
    );
    sweep(
        "fields(n)",
        "chain of n distinct field loads off a parameter",
        &[2, 4, 8, 16, 32, 64],
        |n| (fields(n), 0),
    );
    sweep(
        "fields_chain(n)",
        "n procedures, each appending one accessor to the callee's path",
        &[2, 4, 8, 16, 32],
        |n| (fields_chain(n), 0),
    );
    sweep(
        "wide(m, 8)",
        "m procedures with a nontrivial local closure each; nothing critical",
        &[4, 8, 16, 32, 64],
        |m| (wide(m, 8), 0),
    );
    sweep(
        "wide(64, w)",
        "64 procedures, local closure of width w in each",
        &[2, 4, 8, 16],
        |w| (wide(64, w), 0),
    );
}
