//! Run Hybrid Inlining on Figure 5 and print Figure 6.
//!
//! This is the `lv[v]` half of the paper's illustration: the index of a map
//! access is unknown while `getP`/`setP` are summarized, and — unlike a
//! virtual call — cannot be enumerated, because the values a key may take are
//! unbounded. Only propagating the access into `build`, where the constants
//! live, resolves it.

use hybrid_inlining_poc::analysis::{HybridAnalysis, render_summary, run_hybrid};
use hybrid_inlining_poc::figure5;

fn report(label: &str, h: &HybridAnalysis) {
    println!("\n=== {label} ===");
    for (proc_, summary) in h.summaries() {
        println!("  {proc_}:");
        for line in render_summary(&summary, &h.placeholders(&proc_)) {
            println!("    {line}");
        }
    }
    println!("  index accesses resolved:");
    for (holder, id, acc) in &h.index_acc {
        println!("    in {holder}: {id} → {acc}");
    }
}

fn main() {
    let prog = figure5::program();

    report(
        "k = 0: no propagation, so every index is π (Figure 4, def. 5)",
        &run_hybrid(&prog, 0),
    );
    report(
        "k = 4: hybrid inlining — index- and context-sensitive (Figure 6)",
        &run_hybrid(&prog, 4),
    );
}
