//! How the Hybrid Inlining relations grow with the size of the program.
//!
//! Runs the analysis over the parametric families in
//! [`hybrid_inlining_paper::families`] and reports, for every IDB relation,
//! the fitted exponent `d` in `|R| ~ |P|^d` (least squares on `log|R|` against
//! `log |P|`, where `|P|` is the EDB fact count). A power law cannot express
//! an exponential, so a `last/prev` column is printed beside it: a ratio that
//! stays near 2 while the parameter steps by 1 is a doubling, not a polynomial.
//!
//! ```text
//! cargo run --release --example complexity
//! ```
//!
//! Re-run after editing the rules: the fitted exponents are the regression
//! test. `tests/scaling.rs` pins the ones that matter.

use std::collections::BTreeMap;

use hybrid_inlining_paper::analysis::{HybridAnalysis, run_hybrid};
use hybrid_inlining_paper::families::*;
use hybrid_inlining_paper::figure1;
use hybrid_inlining_paper::ir::Program;

/// Relation sizes, parsed out of Ascent's own summary.
pub fn sizes(summary: &str) -> BTreeMap<String, usize> {
    summary
        .lines()
        .filter_map(|line| {
            let (name, rest) = line.split_once(" size: ")?;
            Some((name.to_string(), rest.trim().parse().ok()?))
        })
        .collect()
}

/// The input relations, excluded from the fits: they grow by construction.
pub const EDB: &[&str] = &[
    "procedure", "proc_type", "proc_sig", "entry", "in_proc", "alloc", "alloc_type",
    "const_assign", "mov", "load_field", "store_field", "load_static", "store_static",
    "load_index_const", "store_index_const", "load_index_var", "store_index_var",
    "direct_call", "virtual_call", "actual_arg", "bind_ret", "formal", "ret",
    "direct_subtype", "lookup", "paths", "k_limit",
];

/// Least-squares slope of `log|R|` against `log|P|`.
pub fn exponent(xs: &[f64], ys: &[f64]) -> Option<f64> {
    let pts: Vec<(f64, f64)> = xs
        .iter()
        .zip(ys)
        .filter(|(_, y)| **y > 0.0)
        .map(|(x, y)| (x.ln(), y.ln()))
        .collect();
    if pts.len() < 2 {
        return None;
    }
    let n = pts.len() as f64;
    let mx = pts.iter().map(|q| q.0).sum::<f64>() / n;
    let my = pts.iter().map(|q| q.1).sum::<f64>() / n;
    let num: f64 = pts.iter().map(|(x, y)| (x - mx) * (y - my)).sum();
    let den: f64 = pts.iter().map(|(x, _)| (x - mx).powi(2)).sum();
    if den == 0.0 { None } else { Some(num / den) }
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

struct Family {
    label: &'static str,
    note: &'static str,
    runs: Vec<(usize, usize, BTreeMap<String, usize>)>,
}

fn measure(
    label: &'static str,
    note: &'static str,
    ns: &[usize],
    build: impl Fn(usize) -> (Program, usize),
) -> Family {
    let runs = ns
        .iter()
        .map(|&n| {
            let (prog, k) = build(n);
            let size = edb_size(&prog);
            let h = run_hybrid(&prog, k);
            (n, size, sizes(&h.relation_sizes_summary()))
        })
        .collect();
    Family { label, note, runs }
}

fn report(f: &Family) {
    println!("\n\n### {} — {}", f.label, f.note);
    let ns: Vec<f64> = f.runs.iter().map(|(_, sz, _)| *sz as f64).collect();
    println!(
        "  {:<18}{}",
        format!("parameter {}:", param(f.label)),
        f.runs.iter().map(|(n, ..)| n.to_string()).collect::<Vec<_>>().join("  ")
    );
    println!(
        "  EDB facts |P|:    {}",
        f.runs.iter().map(|(_, sz, _)| sz.to_string()).collect::<Vec<_>>().join("  ")
    );

    let names: Vec<&String> = f.runs.last().unwrap().2.keys()
        .filter(|k| !EDB.contains(&k.as_str()))
        .filter(|k| f.runs.iter().any(|(_, _, m)| m[*k] > 0))
        .collect();

    let mut rows: Vec<(f64, String, String, f64)> = names.iter().map(|name| {
        let ys: Vec<f64> = f.runs.iter().map(|(_, _, m)| m[*name] as f64).collect();
        let d = exponent(&ns, &ys).unwrap_or(0.0);
        let (last, prev) = (*ys.last().unwrap(), ys[ys.len() - 2]);
        let ratio = if prev > 0.0 { last / prev } else { 0.0 };
        let counts = ys.iter().map(|y| format!("{}", *y as usize)).collect::<Vec<_>>().join(" ");
        (d, (*name).clone(), counts, ratio)
    }).collect();
    rows.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap().then(a.1.cmp(&b.1)));

    println!("  {:<20} {:>8} {:>10}   {}", "relation", "|P|^d", "last/prev", "sizes");
    for (d, name, counts, ratio) in rows {
        let flag = if d >= 1.7 { "  <== superlinear in |P|" } else { "" };
        println!("  {name:<20} {d:>8.2} {ratio:>10.2}   {counts}{flag}");
    }
}

/// Maximum and total accessor depth over `edge`: a domain whose *elements*
/// grow is invisible in tuple counts.
fn path_depths(h: &HybridAnalysis) -> (usize, usize) {
    let (mut max, mut total) = (0usize, 0usize);
    for (_, a, b) in &h.edge {
        for path in [a, b] {
            max = max.max(path.accessors.len());
            total += path.accessors.len();
        }
    }
    (max, total)
}

fn main() {
    println!("## Figure 1 (k = 4)");
    let prog = figure1::program();
    let m = sizes(&run_hybrid(&prog, 4).relation_sizes_summary());
    println!(
        "  |P| = {} EDB facts, {} procedures, {} statements",
        edb_size(&prog), prog.procedure.len(), prog.in_proc.len()
    );
    let mut idb: Vec<(&String, &usize)> =
        m.iter().filter(|(k, n)| !EDB.contains(&k.as_str()) && **n > 0).collect();
    idb.sort_by(|a, b| b.1.cmp(a.1));
    for (k, n) in idb {
        println!("  {k:<20} {n}");
    }

    // What this measures is now the *bound*: `paths` fixes the vocabulary
    // before the fixpoint starts, so these depths are the syntactic set's, not
    // the closure's. `fields_chain` assembles its path across calls and so
    // stops at 1; `fields` spells its chain out in one procedure and does not.
    println!("\n\n## access-path depth (tuple counts alone hide this)");
    println!("  {:>4}  {:>14} {:>16}  {:>14} {:>16}", "n",
             "chain max", "chain accessors", "fields max", "fields accessors");
    for n in [2usize, 4, 8, 16, 32] {
        let (m1, t1) = path_depths(&run_hybrid(&fields_chain(n), 0));
        let (m2, t2) = path_depths(&run_hybrid(&fields(n), 0));
        println!("  {n:>4}  {m1:>14} {t1:>16}  {m2:>14} {t2:>16}");
    }

    println!("\n\n## recursion: does inlining a summary into its own body terminate?");
    let h = run_hybrid(&recursive_field(), 2);
    println!("  recursive_field: reached a fixpoint, edge = {}, points = {}",
             h.edge.len(), h.points.len());
    println!("  summary of P: {:?}",
             h.summaries().get(&hybrid_inlining_paper::figure1::p("P")).map(|s| s.len()));

    let fams = vec![
        measure("chain(n), k = n+2", "call chain of depth n above one critical virtual call",
                &[2, 4, 8, 16, 32], |n| (chain(n, 2), n + 2)),
        measure("chain(n), k = 2", "the same chain with the k-limit held fixed",
                &[2, 4, 8, 16, 32], |n| (chain(n, 2), 2)),
        measure("fanin(m), k = 3", "one critical procedure called from m distinct callers",
                &[2, 4, 8, 16, 32], |m| (fanin(m, 2), 3)),
        measure("branching(d), k = d+2", "each level calls the one below from two sites",
                &[1, 2, 3, 4, 5, 6, 7, 8], |d| (branching(d, 2), d + 2)),
        measure("branching(d), k = 3", "the same, with the k-limit capping the call string",
                &[1, 2, 3, 4, 5, 6, 7, 8], |d| (branching(d, 2), 3)),
        measure("targets(t), k = 2", "one critical call with t CHA implementations, unpinned",
                &[2, 4, 8, 16, 32], |t| (targets(t), 2)),
        measure("alias(n)", "n allocations merged into a chain of n variables; no calls",
                &[4, 8, 16, 32, 64], |n| (alias(n), 0)),
        measure("fields(n)", "chain of n distinct field loads off a parameter",
                &[2, 4, 8, 16, 32, 64], |n| (fields(n), 0)),
        measure("fields_chain(n)", "n procedures, each appending one accessor to the callee's path",
                &[2, 4, 8, 16, 32], |n| (fields_chain(n), 0)),
        measure("wide(m, 8)", "m procedures with a nontrivial local closure each; nothing critical",
                &[4, 8, 16, 32, 64], |m| (wide(m, 8), 0)),
        measure("wide(64, w)", "64 procedures, local closure of width w in each",
                &[2, 4, 8, 16], |w| (wide(64, w), 0)),
    ];
    for f in &fams {
        report(f);
    }
}
