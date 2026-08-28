//! Dump the SCC structure of the [`HybridAnalysis`] Datalog program as a
//! Graphviz graph.
//!
//! Ascent's `scc_times_summary()` reports timings per SCC but never says which
//! relations live where; the generated `summary()` does, as text. This turns
//! that text into a picture.
//!
//! ```text
//! cargo run --example scc_dot | dot -Tsvg -o scc.svg   # relations, clustered by SCC
//! cargo run --example scc_dot -- --no-edb | dot -Tsvg  # ... without the EDB
//! cargo run --example scc_dot -- --sccs | dot -Tsvg    # the condensation DAG
//! cargo run --example scc_dot -- --summary             # Ascent's raw text
//! ```
//!
//! Ascent computes SCCs over *rules*, not relations, so a relation defined by
//! several unrelated rules is finalized in several SCCs (`edge` in 18 of them).
//! Such a relation is drawn in the last SCC that writes it — the point at which
//! it is complete — and its node lists the others.

use std::collections::{BTreeMap, BTreeSet};

use hybrid_inlining_paper::analysis::HybridAnalysis;

/// One strongly connected component of Ascent's rule dependency graph.
struct Scc {
    index: usize,
    /// Whether Ascent evaluates this component to a fixpoint rather than once.
    looping: bool,
    /// The relations this component writes, in Ascent's own order.
    dynamic: Vec<String>,
    /// `(body relation, head relation, is_aggregate)`, deduplicated. Negation
    /// desugars to `agg not()`, so `is_aggregate` marks both.
    deps: BTreeSet<(String, String, bool)>,
}

/// The relation a body item mentions, if it mentions one: `agg` and plain
/// clauses do, `if`/`let`/`for` generators do not.
fn body_relation(item: &str) -> Option<(String, bool)> {
    let item = item.trim();
    let (item, is_agg) = match item.strip_prefix("agg ") {
        Some(rest) => (rest, true),
        None => (item, false),
    };
    // `edge_indices_0_2_delta` -> `edge`. Index and version suffixes are noise.
    let name = item.split("_indices_").next()?;
    if name.is_empty() || name.contains(' ') || name.contains('⋯') {
        return None;
    }
    Some((name.to_string(), is_agg))
}

fn parse(summary: &str) -> Vec<Scc> {
    let mut sccs: Vec<Scc> = vec![];
    for line in summary.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("scc ") {
            let (index, rest) = rest.split_once(',').expect("scc header");
            sccs.push(Scc {
                index: index.trim().parse().expect("scc index"),
                looping: rest.contains("is_looping: true"),
                dynamic: vec![],
                deps: BTreeSet::new(),
            });
        } else if let Some(rels) = trimmed.strip_prefix("dynamic relations:") {
            let scc = sccs.last_mut().expect("relations before any scc");
            scc.dynamic = rels.split(',').map(|r| r.trim().to_string()).filter(|r| !r.is_empty()).collect();
        } else if let Some((heads, body)) = trimmed.split_once(" <-- ") {
            let scc = sccs.last_mut().expect("rule before any scc");
            let body = body.split(" [").next().unwrap_or(body);
            for head in heads.split(',').map(str::trim) {
                for item in body.split(',') {
                    if let Some((rel, is_agg)) = body_relation(item) {
                        scc.deps.insert((rel, head.to_string(), is_agg));
                    }
                }
            }
        }
    }
    sccs
}

/// Every relation Ascent derives, mapped to the SCCs that write it.
fn homes(sccs: &[Scc]) -> BTreeMap<String, Vec<usize>> {
    let mut homes: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for scc in sccs {
        for rel in &scc.dynamic {
            homes.entry(rel.clone()).or_default().push(scc.index);
        }
    }
    homes
}

fn quote(s: &str) -> String { format!("\"{s}\"") }

/// A relation finalized in many SCCs (`edge` in 18) needs its "also scc" list
/// wrapped, or the node comes out wider than the cluster around it.
fn relation_label(rel: &str, also: &[usize]) -> String {
    if also.is_empty() {
        return rel.to_string();
    }
    let mut lines: Vec<String> = vec!["also scc".to_string()];
    for i in also {
        let i = i.to_string();
        let last = lines.last_mut().unwrap();
        if last.len() + 2 + i.len() > 28 {
            lines.push(i);
        } else {
            last.push_str(if last.ends_with("scc") { " " } else { ", " });
            last.push_str(&i);
        }
    }
    format!("{rel}\\n{}", lines.join("\\n"))
}

/// Relation-level graph: a node per relation, clustered by the SCC that
/// finishes it, plus one cluster for the EDB.
fn relation_graph(sccs: &[Scc], with_edb: bool) -> String {
    let homes = homes(sccs);
    // A relation belongs to the last SCC that writes it: before that point it
    // is still growing.
    let owner: BTreeMap<&str, usize> =
        homes.iter().map(|(rel, at)| (rel.as_str(), *at.last().unwrap())).collect();

    let mut out = String::new();
    out.push_str("digraph hybrid_analysis {\n");
    out.push_str("  rankdir=TB;\n  newrank=true;\n  compound=true;\n");
    // `edge` and `points` each attract dozens of edges; mincross needs more
    // than its default four passes to untangle them.
    out.push_str("  ranksep=0.45;\n  nodesep=0.28;\n  mclimit=10;\n");
    out.push_str("  graph [fontname=\"Helvetica\", fontsize=11, style=\"rounded,filled\"];\n");
    out.push_str("  node  [fontname=\"Helvetica\", fontsize=10, shape=box, style=\"rounded,filled\", fillcolor=white];\n");
    out.push_str("  edge  [fontname=\"Helvetica\", fontsize=8, color=\"#555555\"];\n\n");

    let mut edb: BTreeSet<&str> = BTreeSet::new();
    for scc in sccs {
        for (from, _, _) in &scc.deps {
            if !owner.contains_key(from.as_str()) {
                edb.insert(from.as_str());
            }
        }
    }

    if with_edb {
        out.push_str("  subgraph cluster_edb {\n");
        out.push_str("    label=\"EDB\"; fillcolor=\"#f2f2f2\"; color=\"#bbbbbb\";\n");
        out.push_str("    node [fillcolor=\"#ffffff\", color=\"#999999\", shape=box, style=\"filled\"];\n");
        // Every EDB relation is a source. Pinning them to one band across the
        // top (`newrank` makes this bind across clusters) keeps the rest of the
        // drawing flowing downward; left to itself dot spreads them over a
        // dozen ranks and the cluster becomes a wall down one side.
        out.push_str("    rank=same;\n");
        for rel in &edb {
            out.push_str(&format!("    {};\n", quote(rel)));
        }
        out.push_str("  }\n\n");
    }

    for scc in sccs {
        let mine: Vec<&String> =
            scc.dynamic.iter().filter(|r| owner.get(r.as_str()) == Some(&scc.index)).collect();
        if mine.is_empty() {
            continue; // every relation of this SCC is finished in a later one
        }
        let (fill, color) = if scc.looping {
            ("#fde8d0", "#d97706")
        } else {
            ("#e8eef7", "#7189b5")
        };
        let label = |rel: &str| {
            let also: Vec<usize> =
                homes[rel].iter().copied().filter(|&i| i != scc.index).collect();
            relation_label(rel, &also)
        };
        // Most SCCs hold one relation, and a labelled box around a single node
        // is all frame and no content: name the SCC in the node instead.
        if let [rel] = mine[..] {
            out.push_str(&format!(
                "  {} [label=\"{}\\nscc {}\", fillcolor=\"{}\", color=\"{}\"];\n",
                quote(rel),
                label(rel),
                scc.index,
                fill,
                color
            ));
            continue;
        }
        let tag = if scc.looping { " (looping)" } else { "" };
        out.push_str(&format!("  subgraph cluster_scc{} {{\n", scc.index));
        out.push_str(&format!(
            "    label=\"scc {}{}\"; fillcolor=\"{}\"; color=\"{}\";\n",
            scc.index, tag, fill, color
        ));
        for rel in mine {
            out.push_str(&format!("    {} [label=\"{}\"];\n", quote(rel), label(rel)));
        }
        out.push_str("  }\n");
    }
    out.push('\n');

    // `has_agg`/`has_plain` per relation pair: an edge that is only ever an
    // aggregate or negation is the stratification-critical one.
    let mut edges: BTreeMap<(String, String), (bool, bool)> = BTreeMap::new();
    for scc in sccs {
        for (from, to, is_agg) in &scc.deps {
            let e = edges.entry((from.clone(), to.clone())).or_insert((false, false));
            if *is_agg { e.0 = true } else { e.1 = true }
        }
    }
    for ((from, to), (has_agg, has_plain)) in &edges {
        if !with_edb && edb.contains(from.as_str()) {
            continue;
        }
        let recursive = owner.contains_key(from.as_str())
            && owner.get(from.as_str()) == owner.get(to.as_str());
        let style = if *has_agg && !has_plain {
            " [color=\"#c2410c\", style=dashed, label=\"agg/¬\"]"
        } else if recursive {
            " [color=\"#d97706\"]"
        } else if edb.contains(from.as_str()) {
            // Each EDB relation reaches deep into the graph, so these are the
            // longest edges in the drawing. At full strength they bury the IDB
            // structure they are only context for.
            " [color=\"#c8c8c8\"]"
        } else {
            ""
        };
        out.push_str(&format!("  {} -> {}{};\n", quote(from), quote(to), style));
    }
    out.push_str("}\n");
    out
}

/// Condensation DAG: a node per SCC, labelled with the relations it writes.
fn scc_graph(sccs: &[Scc]) -> String {
    let homes = homes(sccs);
    let mut out = String::new();
    out.push_str("digraph hybrid_analysis_sccs {\n");
    out.push_str("  rankdir=TB;\n");
    out.push_str("  node [fontname=\"Helvetica\", fontsize=10, shape=box, style=\"rounded,filled\", fillcolor=\"#e8eef7\", color=\"#7189b5\"];\n");
    out.push_str("  edge [fontname=\"Helvetica\", fontsize=8, color=\"#555555\"];\n\n");

    for scc in sccs {
        let (fill, color) = if scc.looping { ("#fde8d0", "#d97706") } else { ("#e8eef7", "#7189b5") };
        // Wrap the relation list so a 24-relation SCC stays a readable box.
        let mut lines: Vec<String> = vec![String::new()];
        for rel in &scc.dynamic {
            let last = lines.last_mut().unwrap();
            if last.len() + rel.len() > 46 && !last.is_empty() {
                lines.push(rel.clone());
            } else if last.is_empty() {
                last.push_str(rel);
            } else {
                last.push_str(", ");
                last.push_str(rel);
            }
        }
        let tag = if scc.looping { " (looping)" } else { "" };
        let label = format!("scc {}{}\\n{}", scc.index, tag, lines.join("\\n"));
        out.push_str(&format!(
            "  scc{} [label=\"{}\", fillcolor=\"{}\", color=\"{}\"];\n",
            scc.index, label, fill, color
        ));
    }
    out.push('\n');

    // An SCC depends on the last SCC that finishes each relation it reads.
    let mut edges: BTreeMap<(usize, usize), bool> = BTreeMap::new();
    for scc in sccs {
        for (from, _, is_agg) in &scc.deps {
            let Some(at) = homes.get(from) else { continue };
            let Some(&src) = at.iter().rfind(|&&i| i <= scc.index) else { continue };
            if src == scc.index {
                continue;
            }
            let e = edges.entry((src, scc.index)).or_insert(true);
            *e &= *is_agg;
        }
    }
    for ((from, to), only_agg) in &edges {
        let style = if *only_agg { " [color=\"#c2410c\", style=dashed, label=\"agg/¬\"]" } else { "" };
        out.push_str(&format!("  scc{from} -> scc{to}{style};\n"));
    }
    out.push_str("}\n");
    out
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let with_edb = !args.iter().any(|a| a == "--no-edb");
    let mode = args.iter().find(|a| *a != "--no-edb").cloned();

    let summary = HybridAnalysis::summary();
    match mode.as_deref() {
        Some("--summary") => print!("{summary}"),
        Some("--sccs") => print!("{}", scc_graph(&parse(summary))),
        Some("--relations") | None => print!("{}", relation_graph(&parse(summary), with_edb)),
        Some(other) => {
            eprintln!("usage: scc_dot [--relations | --sccs | --summary] [--no-edb]  (unknown: {other})");
            std::process::exit(2);
        }
    }
}
