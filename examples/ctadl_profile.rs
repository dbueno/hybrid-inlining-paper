//! Profile the analysis on a CTADL import: which rules burn the time.
//!
//! ```text
//! cargo run --features ctadl,profile --release --example ctadl_profile -- \
//!     backflash.apk --k 1 --timeout 60 --max-procs 200
//! ```
//!
//! Uses [`analysis::profile::ProfiledHybridAnalysis`], which is the same rules
//! under `#![measure_rule_times]` and `#![generate_run_timeout]`. The timeout
//! is what makes this usable at all: on a real APK the fixpoint does not
//! converge, and `run_timeout` stops between iterations with every rule timer
//! already filled in.
//!
//! `--max-procs N` keeps the N procedures with the most statements and drops
//! the rest of the EDB with them, so the same profile can be taken at a
//! sequence of sizes and the growth read off.

use std::time::Duration;

use hybrid_inlining_paper::analysis::profile::ProfiledHybridAnalysis;
use hybrid_inlining_paper::access_path::AccessPath;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};
use hybrid_inlining_paper::ir::Proc;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut k = 1usize;
    let mut timeout = 60u64;
    let mut max_procs: Option<usize> = None;
    let mut top_paths = 0usize;

    let mut opts = Options::default();

    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "--timeout" => timeout = args.next().unwrap_or_default().parse()?,
            "--max-procs" => max_procs = Some(args.next().unwrap_or_default().parse()?),
            "--top-paths" => top_paths = args.next().unwrap_or_default().parse()?,
            "-h" | "--help" => {
                eprintln!(
                    "usage: ctadl_profile <import>... [--k N] [--timeout SECS] \
                     [--max-procs N] [--top-paths N] [--ssa] [--no-preprocess]"
                );
                return Ok(());
            }
            // The IR passes `ctadl index` runs before codegen are on by
            // default. `--no-preprocess` is the ablation this repo's earlier
            // measurements were taken under; `--ssa` is SSA without the three
            // shrinking passes around it.
            "--ssa" => opts.preprocess = Preprocess::ssa_only(),
            "--ctadl-pre" => opts.preprocess = Preprocess::ctadl(),
            "--no-preprocess" => opts.preprocess = Preprocess::none(),
            _ => imports.push(a),
        }
    }
    if imports.is_empty() {
        eprintln!("no imports given; try --help");
        return Ok(());
    }

    let mut t = Translator::new(opts.clone());
    for name in &imports {
        let (cir, vmt) = read_import(name)?;
        t.add_import(cir, &vmt);
    }
    let mut prog = t.finish();
    if let Some(n) = max_procs {
        prog = restrict(&prog, n);
    }

    println!(
        "procs={} stmts={} virtual_call={} direct_call={} k={} timeout={}s",
        prog.procedure.len(),
        prog.in_proc.len(),
        prog.virtual_call.len(),
        prog.direct_call.len(),
        k,
        timeout
    );

    let mut a = ProfiledHybridAnalysis::for_program(&prog, k);
    let start = std::time::Instant::now();
    let converged = a.run_timeout(Duration::from_secs(timeout));
    let wall = start.elapsed();

    println!(
        "converged={converged} wall={:?}{}",
        wall,
        if converged { "" } else { "  (TIMED OUT — profile below is partial but proportional)" }
    );

    println!("\n=== scc / rule times ===\n{}", a.scc_times_summary());
    println!("=== relation sizes ===\n{}", a.relation_sizes_summary());

    // Suffix congruence materializes a *longer* path from every pair it
    // matches, and the longer path is itself a `used_ext` entry that can
    // match again. If that is what is running away, it shows up here as a
    // long tail: paths far deeper than any the front end wrote down.
    println!("=== access-path depth in `edge` ===");
    let mut hist: Vec<usize> = Vec::new();
    let mut widest: Option<AccessPath> = None;
    for (_, sup, sub) in &a.edge {
        for w in [sup, sub] {
            let d = w.accessors.len();
            if d + 1 > hist.len() {
                hist.resize(d + 1, 0);
            }
            hist[d] += 1;
            if widest.as_ref().is_none_or(|b| b.accessors.len() < d) {
                widest = Some(w.clone());
            }
        }
    }
    let total: usize = hist.iter().sum();
    for (d, n) in hist.iter().enumerate() {
        if *n > 0 {
            println!("  depth {d:>3}: {n:>10}  ({:>5.2}%)", 100.0 * *n as f64 / total as f64);
        }
    }
    if let Some(w) = widest {
        println!("  deepest: {w}");
    }

    // The histogram says how deep the paths are; this says which ones they
    // are. A path's count is how many `edge` tuples mention it on either
    // side, so the head of this list is what the congruence and alias joins
    // actually spend their scans on.
    if top_paths > 0 {
        let mut count: std::collections::HashMap<&AccessPath, usize> = Default::default();
        for (_, sup, sub) in &a.edge {
            for w in [sup, sub] {
                *count.entry(w).or_default() += 1;
            }
        }
        let mut v: Vec<(&AccessPath, usize)> = count.into_iter().collect();
        v.sort_unstable_by_key(|(_, n)| std::cmp::Reverse(*n));
        let n = top_paths.min(v.len());
        // Ties are arbitrary out of the hash map; order the slice we print.
        v[..n].sort_by_cached_key(|(w, n)| (std::cmp::Reverse(*n), w.to_string()));
        println!("\n=== top {n} access paths in `edge`, by occurrences (of {} distinct) ===", v.len());
        for (i, (w, c)) in v[..n].iter().enumerate() {
            println!("{:>4}. {c:>9}  d{}  {w}", i + 1, w.accessors.len());
        }
    }

    // What actually pumps. A path only grows via congruence, and congruence
    // only fires when one path is a strict extension of another with the same
    // base. A *cycle* in the edge graph plus one such extension is enough to
    // extend forever: `a ⊇ b`, `b ⊇ a.f` gives `a.f ⊇ b.f`, then `b.f ⊇ a.f.f`,
    // and so on. Nothing in the rules bounds access-path length, so the only
    // thing that stops it is the clock. Two symptoms, measured here.
    //
    // 1. Cycles: the largest strongly connected component of `edge` viewed as
    //    a graph on access paths, within one procedure.
    let edges: Vec<(&AccessPath, &AccessPath)> =
        a.edge.iter().map(|(_, sup, sub)| (sup, sub)).collect();
    let mut idx: std::collections::HashMap<&AccessPath, usize> = Default::default();
    let mut g: Vec<Vec<usize>> = Vec::new();
    for (sup, sub) in &edges {
        for w in [sup, sub] {
            let n = idx.len();
            idx.entry(w).or_insert_with(|| {
                g.push(Vec::new());
                n
            });
        }
    }
    for (sup, sub) in &edges {
        let (u, v) = (idx[sup], idx[sub]);
        g[u].push(v);
    }
    println!("=== cycles in `edge` (graph on access paths) ===");
    println!("  {} distinct paths, {} edges", g.len(), edges.len());
    let comp = scc_sizes(&g);
    let biggest = comp.iter().copied().max().unwrap_or(0);
    let in_cycle: usize = comp.iter().filter(|c| **c > 1).sum();
    println!("  paths on a cycle: {in_cycle}  (largest SCC: {biggest} paths)");

    // 2. Type-impossible paths. `AdobeUtil.wl` is a WakeLock; a WakeLock has
    //    no `AdobeUtil.wl` field, so `.wl.wl` denotes no heap path that can
    //    exist. Counting paths that repeat an accessor counts the fiction.
    let mut repeated = 0usize;
    let mut distinct = std::collections::HashSet::new();
    for (sup, sub) in &edges {
        for w in [sup, sub] {
            if !distinct.insert(*w) {
                continue;
            }
            let mut seen = std::collections::HashSet::new();
            if w.accessors.iter().any(|acc| !seen.insert(acc)) {
                repeated += 1;
            }
        }
    }
    println!(
        "  paths repeating an accessor: {repeated} of {} distinct ({:.1}%)",
        distinct.len(),
        100.0 * repeated as f64 / distinct.len() as f64
    );

    // 3. The join fan-out. Both congruence rules join `used_ext` against
    //    `edge` on `(proc, path)`, so the work is one retrieval per `used_ext`
    //    tuple and the multiplier is the number of edges hanging off that
    //    exact path — not, as it was when the key was `(proc, base)`, the
    //    number of paths sharing a root.
    let mut per_sup: std::collections::HashMap<(&Proc, &AccessPath), usize> = Default::default();
    let mut per_sub: std::collections::HashMap<(&Proc, &AccessPath), usize> = Default::default();
    for (p, sup, sub) in &a.edge {
        *per_sup.entry((p, sup)).or_default() += 1;
        *per_sub.entry((p, sub)).or_default() += 1;
    }
    let mut fan: Vec<usize> = Vec::with_capacity(a.used_ext.len());
    for (p, w, _, _) in &a.used_ext {
        fan.push(per_sup.get(&(p, w)).copied().unwrap_or(0));
        fan.push(per_sub.get(&(p, w)).copied().unwrap_or(0));
    }
    fan.sort_unstable();
    let sum: usize = fan.iter().sum();
    let pick = |q: f64| fan.get(((fan.len() as f64 - 1.0) * q) as usize).copied().unwrap_or(0);
    println!(
        "  edges per (proc, path) retrieved: n={} mean={:.1} p50={} p99={} max={}",
        fan.len(),
        sum as f64 / fan.len().max(1) as f64,
        pick(0.50),
        pick(0.99),
        fan.last().copied().unwrap_or(0)
    );
    println!(
        "  => congruence considers ~{} (edge, extension) pairs per full pass, from {} \
         indexed lookups; before the join was indexed it rescanned all {} edges every \
         iteration instead",
        sum,
        fan.len(),
        a.edge.len()
    );

    Ok(())
}

/// Sizes of the strongly connected components of `g`, by iterative Tarjan.
fn scc_sizes(g: &[Vec<usize>]) -> Vec<usize> {
    let n = g.len();
    let (mut index, mut low, mut on) = (vec![usize::MAX; n], vec![0usize; n], vec![false; n]);
    let (mut stack, mut out, mut next) = (Vec::new(), Vec::new(), 0usize);
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        let mut work = vec![(root, 0usize)];
        while let Some((v, pi)) = work.pop() {
            if pi == 0 {
                index[v] = next;
                low[v] = next;
                next += 1;
                stack.push(v);
                on[v] = true;
            }
            let mut recursed = false;
            for (i, &w) in g[v].iter().enumerate().skip(pi) {
                if index[w] == usize::MAX {
                    work.push((v, i + 1));
                    work.push((w, 0));
                    recursed = true;
                    break;
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
            }
            if recursed {
                continue;
            }
            if low[v] == index[v] {
                let mut size = 0;
                while let Some(w) = stack.pop() {
                    on[w] = false;
                    size += 1;
                    if w == v {
                        break;
                    }
                }
                out.push(size);
            }
            if let Some(&(u, _)) = work.last() {
                low[u] = low[u].min(low[v]);
            }
        }
    }
    out
}
