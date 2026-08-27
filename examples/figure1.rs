//! Run Hybrid Inlining on Figure 1 and print what it derives.
//!
//! The program itself lives in [`hybrid_inlining_paper::figure1`]. This example
//! runs the analysis twice:
//!
//! - with `k = 0`, which forbids propagation and so forces every critical
//!   statement to be ⊤-summarized where it occurs — the compositional,
//!   context-insensitive analysis of Figure 2; and
//! - with `k = 4`, the real thing, which reproduces Figure 3 and verifies
//!   `service()`'s two assertions.

use std::collections::BTreeSet;

use hybrid_inlining_paper::access_path::PtVal;
use hybrid_inlining_paper::analysis::{HybridAnalysis, render_summary, run_hybrid};
use hybrid_inlining_paper::figure1;
use hybrid_inlining_paper::ir::{Proc, Var};

fn report(label: &str, h: &HybridAnalysis) {
    println!("\n=== {label} ===");

    for (proc_, summary) in h.summaries() {
        let placeholders = h.placeholders(&proc_);
        println!("  {proc_}:");
        for line in render_summary(&summary, &placeholders) {
            println!("    {line}");
        }
    }

    println!("  call edges resolved for critical statements:");
    for (holder, id, callee) in h.dispatches() {
        println!("    in {holder}: {id} → {callee}");
    }
}

fn pt(h: &HybridAnalysis, p: &Proc, v: &str) -> BTreeSet<PtVal> {
    h.points_to(p, Var::from(v))
}

fn main() {
    let prog = figure1::program();

    let insensitive = run_hybrid(&prog, 0);
    report("k = 0: context-insensitive (Figure 2)", &insensitive);

    let hybrid = run_hybrid(&prog, 4);
    report("k = 4: hybrid inlining (Figure 3)", &hybrid);

    let service = figure1::p("FacadeImpl.service");
    let first = pt(&hybrid, &service, "first");
    let second = pt(&hybrid, &service, "second");
    let third = pt(&hybrid, &service, "third");

    let show = |s: &BTreeSet<PtVal>| {
        s.iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    };

    println!("\n=== service() verdicts ===");
    println!("  pt(first)  = {{{}}}", show(&first));
    println!("  pt(second) = {{{}}}", show(&second));
    println!("  pt(third)  = {{{}}}", show(&third));
    println!(
        "  assert(first == second): {}",
        if first == second && !first.is_empty() {
            "possible — the two points-to sets coincide"
        } else {
            "NOT verified"
        }
    );
    println!(
        "  assert(first != third):  {}",
        if first.is_disjoint(&third) {
            "always — the two points-to sets are disjoint"
        } else {
            "NOT verified"
        }
    );
}
