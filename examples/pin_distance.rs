//! How far up the call graph is the allocation that would pin each critical
//! receiver?
//!
//! ```text
//! cargo run --features ctadl --release --example pin_distance -- backflash.apk
//! ```
//!
//! `waste-profile.md` measures that no instance created by propagation is
//! answered better than CHA at `k = 1, 2`. That is consistent with two very
//! different worlds: propagation never pays on this app, or the resolvent
//! simply lives further up than `k = 2` can reach. This binary decides
//! between them without needing a deep run.
//!
//! The walk is propagation with the instances taken out. Start at the
//! receiver of a critical statement. At each step ask whether the current
//! path holds a concrete allocation; if not, follow the symbolic paths it
//! does hold outward through every callsite of the holder — the same two
//! kinds of callsite propagation itself crosses, `eff_direct` and a resolved
//! critical statement — and ask again one level up. The depth at which an
//! allocation first appears is the smallest `k` at which Hybrid Inlining
//! could pin that receiver.
//!
//! Two properties make the answer meaningful:
//!
//! - The points-to sets it reads are the **`k = 0`** ones, which are
//!   context-*insensitive*: every caller's values are merged. So a receiver
//!   this walk cannot pin at depth `d` cannot be pinned by the real analysis
//!   at `k = d` either — it is an over-approximation of pinning, and a
//!   negative result is therefore the strong one.
//! - It costs one `k = 0` fixpoint and a breadth-first search, so it answers
//!   at depths the fixpoint itself cannot reach on this program.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use hybrid_inlining_paper::access_path::{AccessPath, Base, PtVal};
use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};
use hybrid_inlining_paper::ir::{ArgIdx, Proc, Stmt};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut max_depth = 16usize;
    let mut max_procs: Option<usize> = None;
    let mut trace = 0usize;
    let mut trace_from = 1usize;
    let mut cha = false;
    let mut pre = Preprocess::default();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--max-depth" => max_depth = args.next().unwrap_or_default().parse()?,
            "--max-procs" => max_procs = Some(args.next().unwrap_or_default().parse()?),
            "--cha" => cha = true,
            "--trace" => trace = args.next().unwrap_or_default().parse()?,
            "--trace-from" => trace_from = args.next().unwrap_or_default().parse()?,
            // The ablation: translate the IR as `ctadl import` cached it, without
            // the four passes `ctadl index` runs and this front end now defaults to.
            "--no-preprocess" => pre = Preprocess::none(),
            _ => imports.push(a),
        }
    }

    let mut t = Translator::new(Options {
        preprocess: pre,
        ..Options::default()
    });
    for name in &imports {
        let (cir, vmt) = read_import(name)?;
        t.add_import(cir, &vmt);
    }
    let mut prog = t.finish();
    if let Some(n) = max_procs {
        prog = restrict(&prog, n);
    }

    // k = 0: no propagation, so every procedure's summary is the
    // context-insensitive one, which is what the walk wants.
    let mut a = HybridAnalysis::for_program(&prog, 0);
    a.run();
    println!(
        "procs={} stmts={} virtual_call={} k=0 fixpoint: points={} edge={}",
        prog.procedure.len(),
        prog.in_proc.len(),
        prog.virtual_call.len(),
        a.points.len(),
        a.edge.len()
    );

    // --- indices -----------------------------------------------------------
    let mut has_alloc: BTreeSet<(Proc, AccessPath)> = BTreeSet::new();
    let mut paths_of: BTreeMap<(Proc, AccessPath), Vec<AccessPath>> = BTreeMap::new();
    for (p, w, v) in &a.points {
        match v {
            PtVal::Alloc(_) => {
                has_alloc.insert((p.clone(), w.clone()));
            }
            PtVal::Path(u) => paths_of
                .entry((p.clone(), w.clone()))
                .or_default()
                .push(u.clone()),
            PtVal::Const(_) => {}
        }
    }
    let mut stmt_proc: BTreeMap<Stmt, Proc> = BTreeMap::new();
    for (s, p, _) in &prog.in_proc {
        stmt_proc.insert(s.clone(), p.clone());
    }
    let mut arg: BTreeMap<(Stmt, ArgIdx), Base> = BTreeMap::new();
    for (s, i, v) in &prog.actual_arg {
        arg.insert((s.clone(), *i), Base::Var(v.clone()));
    }
    // Every callsite propagation crosses: a statically known callee, and a
    // critical statement resolved to one.
    let mut callsites: BTreeMap<Proc, BTreeSet<(Proc, Stmt)>> = BTreeMap::new();
    for (s, callee) in &a.eff_direct {
        if let Some(caller) = stmt_proc.get(s) {
            callsites
                .entry(callee.clone())
                .or_default()
                .insert((caller.clone(), s.clone()));
        }
    }
    if cha {
        // Every callee CHA admits at every virtual callsite, resolved or not.
        // This graph contains the call graph of *any* `k`, so a receiver the
        // walk cannot pin over it cannot be pinned by any run — the negative
        // result stops depending on what `k = 0` managed to resolve.
        let mut targets: BTreeMap<hybrid_inlining_paper::ir::Sig, Vec<Proc>> = BTreeMap::new();
        for (sig, p) in &a.sig_target {
            targets.entry(sig.clone()).or_default().push(p.clone());
        }
        for (s, _, sig) in &prog.virtual_call {
            if let Some(caller) = stmt_proc.get(s) {
                for callee in targets.get(sig).into_iter().flatten() {
                    callsites
                        .entry(callee.clone())
                        .or_default()
                        .insert((caller.clone(), s.clone()));
                }
            }
        }
    } else {
        for (_, id, callee) in &a.resolve {
            if let Some(caller) = stmt_proc.get(&id.stmt) {
                callsites
                    .entry(callee.clone())
                    .or_default()
                    .insert((caller.clone(), id.stmt.clone()));
            }
        }
    }

    // --- the walk ----------------------------------------------------------
    /// Why a receiver's search ran out without finding an allocation.
    #[derive(Default)]
    struct Why {
        no_caller: usize,
        through_unresolved: usize,
        through_ret: usize,
        depth_capped: usize,
        nothing_to_follow: usize,
    }

    let mut pure_hits: BTreeMap<usize, usize> = BTreeMap::new();
    let mut merged_hits: BTreeMap<usize, usize> = BTreeMap::new();
    let mut traced = 0usize;
    let mut hist: BTreeMap<Option<usize>, usize> = BTreeMap::new();
    let mut why = Why::default();
    let mut crit: Vec<(Proc, Stmt, hybrid_inlining_paper::ir::Var)> = Vec::new();
    let critical: BTreeSet<Stmt> = a.critical.iter().map(|(s,)| s.clone()).collect();
    for (s, recv, _) in &prog.virtual_call {
        if critical.contains(s)
            && let Some(p) = stmt_proc.get(s)
        {
            crit.push((p.clone(), s.clone(), recv.clone()));
        }
    }

    for (p0, _s, recv) in &crit {
        let start = AccessPath::var(recv.clone());
        let mut seen: BTreeSet<(Proc, AccessPath)> = BTreeSet::new();
        let mut q: VecDeque<(Proc, AccessPath, usize)> = VecDeque::new();
        q.push_back((p0.clone(), start.clone(), 0));
        seen.insert((p0.clone(), start));
        let mut found: Option<usize> = None;
        let mut parent: BTreeMap<(Proc, AccessPath), (Proc, AccessPath, Stmt)> = BTreeMap::new();
        let mut hit: Option<(Proc, AccessPath)> = None;
        let mut reason = (false, false, false, false); // no_caller, unresolved, ret, capped
        while let Some((p, w, d)) = q.pop_front() {
            if has_alloc.contains(&(p.clone(), w.clone())) {
                found = Some(d);
                hit = Some((p.clone(), w.clone()));
                break;
            }
            if d == max_depth {
                reason.3 = true;
                continue;
            }
            let mut moved = false;
            for u in paths_of.get(&(p.clone(), w.clone())).into_iter().flatten() {
                match &u.base {
                    Base::Param(q0, i) if q0 == &p => {
                        let sites = callsites.get(&p);
                        if sites.is_none_or(|s| s.is_empty()) {
                            reason.0 = true;
                        }
                        for (caller, site) in sites.into_iter().flatten() {
                            let Some(actual) = arg.get(&(site.clone(), *i)) else {
                                continue;
                            };
                            let next = u.rebase(actual.clone());
                            if seen.insert((caller.clone(), next.clone())) {
                                parent.insert(
                                    (caller.clone(), next.clone()),
                                    (p.clone(), w.clone(), site.clone()),
                                );
                                q.push_back((caller.clone(), next, d + 1));
                            }
                            moved = true;
                        }
                    }
                    // The value comes out of a call this analysis has not
                    // resolved, or out of this procedure's own return. Going
                    // outward cannot pin either one.
                    Base::CritSlot(..) | Base::CritRet(_) => reason.1 = true,
                    Base::Ret(_) => reason.2 = true,
                    _ => {}
                }
            }
            let _ = moved;
        }
        if let (Some(d), Some(end)) = (found, hit.clone())
            && d >= trace_from
            && traced < trace
        {
            traced += 1;
            println!("\n  -- {} in {} needs k = {d}", _s, p0);
            let mut chain = vec![end.clone()];
            let mut cur = end;
            while let Some((pp, ww, site)) = parent.get(&cur) {
                chain.push((pp.clone(), ww.clone()));
                println!("     {} : {}   <- through callsite {}", cur.0, cur.1, site);
                cur = (pp.clone(), ww.clone());
            }
            println!("     {} : {}   (the receiver)", cur.0, cur.1);
        }
        if let (Some(d), Some((hp, hw))) = (found, hit.clone()) {
            // `blocked` is a presence test on a *free* root: a param, a
            // return, or a live placeholder. If the receiver still holds one
            // of those where the allocation is, the instance is blocked
            // there, and at the k-limit `top` gives it the whole CHA set
            // back — the allocation buys nothing.
            let merged = paths_of
                .get(&(hp.clone(), hw.clone()))
                .is_some_and(|us| us.iter().any(|u| u.base.is_symbolic()));
            if merged {
                *merged_hits.entry(d).or_default() += 1;
            } else {
                *pure_hits.entry(d).or_default() += 1;
            }
        }
        *hist.entry(found).or_default() += 1;
        if found.is_none() {
            if reason.3 {
                why.depth_capped += 1;
            } else if reason.1 {
                why.through_unresolved += 1;
            } else if reason.0 {
                why.no_caller += 1;
            } else if reason.2 {
                why.through_ret += 1;
            } else {
                why.nothing_to_follow += 1;
            }
        }
    }

    println!(
        "\n=== distance from a critical receiver to an allocation that pins it ({}) ===",
        if cha { "CHA call graph — contains every k's" } else { "k=0 resolved call graph" }
    );
    println!("  critical virtual calls: {}", crit.len());
    let total = crit.len();
    let mut cum = 0usize;
    for (d, n) in &hist {
        match d {
            Some(d) => {
                cum += n;
                println!(
                    "  depth {d:>3}   {n:>6}  {:>6.1}%   cumulative {cum:>6}  {:>6.1}%   (needs k >= {d})",
                    100.0 * *n as f64 / total as f64,
                    100.0 * cum as f64 / total as f64
                );
            }
            None => {}
        }
    }
    println!("\n  at the depth where the allocation appears, is the receiver purely concrete?");
    println!("    {:>5}{:>12}{:>12}", "depth", "pure", "merged");
    for d in 0..=max_depth {
        let (a, b) = (
            pure_hits.get(&d).copied().unwrap_or(0),
            merged_hits.get(&d).copied().unwrap_or(0),
        );
        if a + b > 0 {
            println!("    {d:>5}{a:>12}{b:>12}");
        }
    }
    println!("  a merged receiver is still `blocked` there, so at k = that depth the ⊤");
    println!("  fallback hands back the whole CHA set and the allocation buys nothing.");

    let never = hist.get(&None).copied().unwrap_or(0);
    println!(
        "  never    {never:>6}  {:>6.1}%   (no allocation within depth {max_depth})",
        100.0 * never as f64 / total as f64
    );
    println!("    the search stopped because:");
    println!("      the holder has no caller            {:>6}", why.no_caller);
    println!("      the value is a deferred call's result   {:>3}", why.through_unresolved);
    println!("      the value comes from a return       {:>6}", why.through_ret);
    println!("      the depth cap was reached           {:>6}", why.depth_capped);
    println!("      the receiver's points-to set holds nothing to follow {:>3}", why.nothing_to_follow);

    Ok(())
}
