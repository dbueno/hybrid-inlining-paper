//! How much of the fixpoint is thrown on the floor at the end?
//!
//! ```text
//! cargo run --features ctadl --release --example waste -- backflash.apk --k 1
//! ```
//!
//! Three questions, three sections of output.
//!
//! 1. **Accounting.** Of the tuples the fixpoint derives, how many survive
//!    into what the reporting layer publishes — `summaries()`, `pub_edges()`,
//!    the settled dispatches — and how many are dropped by one of the three
//!    filters that run *after* convergence: the publication filter (a root
//!    that is a local), the settled-placeholder filter
//!    (`HybridAnalysis::is_decided`), and adequacy itself.
//!
//! 2. **The adequacy oracle.** `resolve` fires unless `will_propagate`, a
//!    *syntactic* under-approximation of `blocked`. The exact test is
//!    `blocked`, and it is only known at the fixpoint. So: run once, take
//!    `blocked`, seed it into `will_propagate` and run again. That second run
//!    is what a redesign with a perfect adequacy oracle — available for free,
//!    before the fixpoint — would derive, and it is therefore an upper bound
//!    on what any such redesign can save. The two runs' outputs are compared
//!    tuple for tuple, so a saving that costs an answer is visible as one.
//!
//! 3. **Dead procedures.** Summaries computed for procedures no reachable
//!    call site ever inlines: derived in full, read by nobody.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use hybrid_inlining_paper::access_path::{AccessPath, Base, CritId, PtVal, Summary};
use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};
use hybrid_inlining_paper::ir::{Proc, Program};

fn pct(a: usize, b: usize) -> String {
    if b == 0 {
        return "   -  ".into();
    }
    format!("{:5.1}%", 100.0 * a as f64 / b as f64)
}

/// Every relation size the two runs can be compared on.
fn sizes(a: &HybridAnalysis) -> Vec<(&'static str, usize)> {
    vec![
        ("points", a.points.len()),
        ("edge", a.edge.len()),
        ("used_ext", a.used_ext.len()),
        ("pub_points", a.pub_points.len()),
        ("root_map", a.root_map.len()),
        ("pub_root", a.pub_root.len()),
        ("free_root", a.free_root.len()),
        ("pending", a.pending.len()),
        ("blocked", a.blocked.len()),
        ("resolve", a.resolve.len()),
        ("settled", a.settled.len()),
        ("adequate", a.adequate.len()),
        ("top", a.top.len()),
        ("crit_operand", a.crit_operand.len()),
        ("can_propagate", a.can_propagate.len()),
        ("will_propagate", a.will_propagate.len()),
        ("index_acc", a.index_acc.len()),
    ]
}

fn total(a: &HybridAnalysis) -> usize {
    sizes(a).iter().map(|(_, n)| n).sum()
}

/// The client-visible answer: every procedure's reported summary, and the
/// dispatch decision of every instance that is settled.
fn answer(a: &HybridAnalysis) -> (BTreeMap<Proc, Summary>, BTreeSet<(Proc, CritId, Proc)>) {
    let settled: BTreeSet<(Proc, CritId)> = a.settled.iter().cloned().collect();
    let dispatch = a
        .resolve
        .iter()
        .filter(|(p, id, _)| settled.contains(&((*p).clone(), id.clone())))
        .cloned()
        .collect();
    (a.summaries(), dispatch)
}

fn accounting(a: &HybridAnalysis) {
    let settled: BTreeSet<(Proc, CritId)> = a.settled.iter().cloned().collect();
    let pub_root: BTreeSet<(Proc, Base)> = a.pub_root.iter().cloned().collect();
    let published = |p: &Proc, w: &AccessPath| pub_root.contains(&(p.clone(), w.base.clone()));
    let decided = |p: &Proc, w: &AccessPath| match w.base.crit_id() {
        Some(id) => settled.contains(&(p.clone(), id.clone())),
        None => false,
    };

    // --- `points`, by what becomes of it ------------------------------------
    let (mut path_val, mut conc_val) = (0usize, 0usize);
    let (mut pub_path, mut pub_conc) = (0usize, 0usize);
    let (mut rep_path, mut rep_conc) = (0usize, 0usize);
    let mut local_key = 0usize;
    for (p, w, v) in &a.points {
        let key_pub = published(p, w);
        if !key_pub {
            local_key += 1;
        }
        match v {
            PtVal::Path(b) => {
                path_val += 1;
                if key_pub && published(p, b) {
                    pub_path += 1;
                    if !decided(p, w) && !decided(p, b) {
                        rep_path += 1;
                    }
                }
            }
            _ => {
                conc_val += 1;
                if key_pub {
                    pub_conc += 1;
                    if !decided(p, w) {
                        rep_conc += 1;
                    }
                }
            }
        }
    }
    let n = a.points.len();
    println!("=== what becomes of `points` ({n} tuples) ===");
    println!("  value is a path                {path_val:>10}  {}", pct(path_val, n));
    println!("  value is concrete              {conc_val:>10}  {}", pct(conc_val, n));
    println!("  key rooted at a local          {local_key:>10}  {}   (never publishable)", pct(local_key, n));
    println!("  survives the publication filter{:>10}  {}", pub_path + pub_conc, pct(pub_path + pub_conc, n));
    println!("    of which path half           {pub_path:>10}  {}   (= pub_edges())", pct(pub_path, n));
    println!("    of which concrete half       {pub_conc:>10}  {}   (= pub_points)", pct(pub_conc, n));
    println!("  reaches the reported summary   {:>10}  {}", rep_path + rep_conc, pct(rep_path + rep_conc, n));
    println!("    dropped as settled-placeholder{:>9}  {}", (pub_path + pub_conc) - (rep_path + rep_conc), pct((pub_path + pub_conc) - (rep_path + rep_conc), n));

    // --- `edge`, same question ----------------------------------------------
    let mut edge_pub = 0usize;
    let mut edge_settled = 0usize;
    for (p, sup, sub) in &a.edge {
        if published(p, sup) && published(p, sub) {
            edge_pub += 1;
            if decided(p, sup) || decided(p, sub) {
                edge_settled += 1;
            }
        }
    }
    let e = a.edge.len();
    println!("\n=== what becomes of `edge` ({e} tuples) ===");
    println!("  both endpoints published       {edge_pub:>10}  {}", pct(edge_pub, e));
    println!("    of those, settled placeholder{edge_settled:>10}  {}", pct(edge_settled, e));
    println!("  at least one endpoint local    {:>10}  {}   (eliminated by publication)", e - edge_pub, pct(e - edge_pub, e));

    // --- the placeholder hop ------------------------------------------------
    // A placeholder root exists so that a *deferred* statement has a node in
    // the graph. For an instance that is settled where it stands, nothing is
    // deferred, and the node is one extra hop between the callee's summary
    // and the local the statement writes.
    let ph_root = a.pub_root.iter().filter(|(_, b)| b.crit_id().is_some()).count();
    let ph_root_settled = a
        .pub_root
        .iter()
        .filter(|(p, b)| b.crit_id().is_some_and(|id| settled.contains(&(p.clone(), id.clone()))))
        .count();
    let pts_key_settled = a.points.iter().filter(|(p, w, _)| decided(p, w)).count();
    let edge_any_settled = a
        .edge
        .iter()
        .filter(|(p, sup, sub)| decided(p, sup) || decided(p, sub))
        .count();
    println!("\n=== the placeholder hop ===");
    println!("  pub_root                       {:>10}", a.pub_root.len());
    println!("    a placeholder node           {ph_root:>10}  {}", pct(ph_root, a.pub_root.len()));
    println!("    of a settled instance        {ph_root_settled:>10}  {}   (defers nothing)", pct(ph_root_settled, a.pub_root.len()));
    println!("  points keyed at such a node    {pts_key_settled:>10}  {}", pct(pts_key_settled, n));
    println!("  edge touching such a node      {edge_any_settled:>10}  {}", pct(edge_any_settled, e));

    // --- the instance machinery ---------------------------------------------
    let blocked: BTreeSet<(Proc, CritId)> = a.blocked.iter().cloned().collect();
    let resolve_blocked = a
        .resolve
        .iter()
        .filter(|(p, id, _)| blocked.contains(&((*p).clone(), id.clone())))
        .count();
    let instances_resolved_blocked: BTreeSet<(Proc, CritId)> = a
        .resolve
        .iter()
        .filter(|(p, id, _)| blocked.contains(&((*p).clone(), id.clone())))
        .map(|(p, id, _)| (p.clone(), id.clone()))
        .collect();
    println!("\n=== instances ===");
    println!("  pending                        {:>10}", a.pending.len());
    println!("    blocked (= !adequate)        {:>10}  {}", a.blocked.len(), pct(a.blocked.len(), a.pending.len()));
    println!("    adequate                     {:>10}  {}", a.adequate.len(), pct(a.adequate.len(), a.pending.len()));
    println!("    settled                      {:>10}  {}", a.settled.len(), pct(a.settled.len(), a.pending.len()));
    println!("    top (⊤-summarized)           {:>10}  {}", a.top.len(), pct(a.top.len(), a.pending.len()));
    // A resolution is *redundant* only if the instance both is blocked (so
    // the caller re-derives it) and actually has a caller to propagate to.
    // A blocked instance with nowhere to go is `top`, and its resolution is
    // the ⊤-fallback, which is the only answer available.
    let can_prop: BTreeSet<(Proc, CritId)> = a.can_propagate.iter().cloned().collect();
    let resolve_redundant = a
        .resolve
        .iter()
        .filter(|(p, id, _)| {
            blocked.contains(&((*p).clone(), id.clone())) && can_prop.contains(&((*p).clone(), id.clone()))
        })
        .count();
    let top_set: BTreeSet<(Proc, CritId)> = a.top.iter().cloned().collect();
    let resolve_top = a
        .resolve
        .iter()
        .filter(|(p, id, _)| top_set.contains(&((*p).clone(), id.clone())))
        .count();
    println!("  resolve                        {:>10}", a.resolve.len());
    println!("    at a blocked instance        {resolve_blocked:>10}  {}", pct(resolve_blocked, a.resolve.len()));
    println!("      of those, ⊤-fallback       {resolve_top:>10}  {}   (no other answer exists)", pct(resolve_top, a.resolve.len()));
    println!("      of those, redundant        {resolve_redundant:>10}  {}   <-- blocked AND has a caller: the caller redoes these", pct(resolve_redundant, a.resolve.len()));
    println!("    instances so resolved        {:>10}", instances_resolved_blocked.len());
    println!("  will_propagate (the syntactic guard) {:>4}  of {} blocked  {}",
        a.will_propagate.len(), a.blocked.len(), pct(a.will_propagate.len(), a.blocked.len()));

    // Tuples rooted at a placeholder of an instance that was resolved while
    // blocked: the material a perfect oracle would not have had to build.
    let mut e_at = 0usize;
    for (p, sup, sub) in &a.edge {
        let hit = |w: &AccessPath| {
            w.base
                .crit_id()
                .is_some_and(|id| instances_resolved_blocked.contains(&(p.clone(), id.clone())))
        };
        if hit(sup) || hit(sub) {
            e_at += 1;
        }
    }
    let mut p_at = 0usize;
    for (p, w, v) in &a.points {
        let hit = |w: &AccessPath| {
            w.base
                .crit_id()
                .is_some_and(|id| instances_resolved_blocked.contains(&(p.clone(), id.clone())))
        };
        if hit(w) || matches!(v, PtVal::Path(b) if hit(b)) {
            p_at += 1;
        }
    }
    println!("  tuples mentioning such an instance: edge {e_at} ({}), points {p_at} ({})",
        pct(e_at, e), pct(p_at, n));
}

/// What the context-sensitive machinery actually decides, per critical
/// statement: a callee set smaller than CHA's, or CHA's own set back again.
fn dispatch_precision(a: &HybridAnalysis) {
    use hybrid_inlining_paper::ir::{Sig, Stmt};
    let mut cha: BTreeMap<Sig, BTreeSet<Proc>> = BTreeMap::new();
    for (sig, p) in &a.sig_target {
        cha.entry(sig.clone()).or_default().insert(p.clone());
    }
    let mut sig_of: BTreeMap<CritId, Sig> = BTreeMap::new();
    for (id, sig) in &a.crit_sig {
        sig_of.insert(id.clone(), sig.clone());
    }
    let mut by_inst: BTreeMap<(Proc, CritId), BTreeSet<Proc>> = BTreeMap::new();
    for (p, id, callee) in &a.resolve {
        by_inst.entry((p.clone(), id.clone())).or_default().insert(callee.clone());
    }
    let top: BTreeSet<(Proc, CritId)> = a.top.iter().cloned().collect();

    let (mut empty, mut precise, mut full, mut topped) = (0usize, 0usize, 0usize, 0usize);
    let mut by_stmt: BTreeMap<Stmt, BTreeSet<Proc>> = BTreeMap::new();
    let mut stmts: BTreeSet<Stmt> = BTreeSet::new();
    for (p, id) in &a.pending {
        let key = (p.clone(), id.clone());
        let got = by_inst.get(&key).cloned().unwrap_or_default();
        let n_cha = sig_of.get(id).and_then(|s| cha.get(s)).map_or(0, |s| s.len());
        if top.contains(&key) {
            topped += 1;
        }
        if got.is_empty() {
            empty += 1;
        } else if got.len() < n_cha {
            precise += 1;
        } else {
            full += 1;
        }
        stmts.insert(id.stmt.clone());
        by_stmt.entry(id.stmt.clone()).or_default().extend(got);
    }
    let mut stmt_precise = 0usize;
    let mut stmt_empty = 0usize;
    let mut pairs = 0usize;
    let mut cha_pairs = 0usize;
    for s in &stmts {
        let got = by_stmt.get(s).cloned().unwrap_or_default();
        // every instance of `s` has the same signature, so any one will do
        let n_cha = a
            .crit_sig
            .iter()
            .find(|(id, _)| &id.stmt == s)
            .and_then(|(_, sig)| cha.get(sig))
            .map_or(0, |t| t.len());
        pairs += got.len();
        cha_pairs += n_cha;
        if got.is_empty() {
            stmt_empty += 1;
        } else if got.len() < n_cha {
            stmt_precise += 1;
        }
    }
    println!("\n=== what the dispatch machinery decides ===");
    println!("  instances                      {:>10}", a.pending.len());
    println!("    ⊤-summarized                 {topped:>10}  {}", pct(topped, a.pending.len()));
    println!("    resolved to nothing          {empty:>10}  {}   (dead: no value reaches the receiver)", pct(empty, a.pending.len()));
    println!("    resolved below CHA           {precise:>10}  {}   <-- what context-sensitivity buys", pct(precise, a.pending.len()));
    println!("    resolved to the whole CHA set{full:>10}  {}", pct(full, a.pending.len()));
    // The same, split by call-string depth: an instance at depth d > 0 exists
    // only because some instance at depth d-1 was propagated. If none of them
    // is answered better than CHA, the propagation that made them derived
    // nothing that the origin could not have decided on its own.
    let mut by_depth: BTreeMap<usize, [usize; 4]> = BTreeMap::new();
    for (p, id) in &a.pending {
        let key = (p.clone(), id.clone());
        let got = by_inst.get(&key).cloned().unwrap_or_default();
        let n_cha = sig_of.get(id).and_then(|s| cha.get(s)).map_or(0, |s| s.len());
        let row = by_depth.entry(id.depth()).or_default();
        row[0] += 1;
        if top.contains(&key) {
            row[1] += 1;
        }
        if got.is_empty() {
            row[2] += 1;
        } else if got.len() < n_cha {
            row[3] += 1;
        }
    }
    println!("  by call-string depth:");
    println!("    {:>5}{:>12}{:>12}{:>12}{:>12}", "depth", "instances", "⊤", "nothing", "< CHA");
    for (d, r) in &by_depth {
        println!("    {d:>5}{:>12}{:>12}{:>12}{:>12}", r[0], r[1], r[2], r[3]);
    }
    println!("  critical statements            {:>10}", stmts.len());
    println!("    answered below CHA           {stmt_precise:>10}  {}", pct(stmt_precise, stmts.len()));
    println!("    answered with nothing        {stmt_empty:>10}  {}", pct(stmt_empty, stmts.len()));
    println!("  (stmt, callee) edges           {pairs:>10}   against {cha_pairs} for CHA alone  {}",
        pct(pairs, cha_pairs));
}

/// The cost of the hop, exactly: a tuple at a placeholder node of a settled
/// origin instance whose *local* twin already exists.
///
/// A placeholder node exists so a deferred statement has somewhere to hang
/// its constraints. `CritSlot(id, i)` stands for the `i`-th operand of `id`'s
/// statement and is wired `CritSlot(id,i) ⊇ a_i`; `CritRet(id)` stands for its
/// result and is wired `r ⊇ CritRet(id)`. When the instance is settled at its
/// origin — decided here, never propagated — a design that inlined the
/// resolved callee onto `a_i` and `r` directly, the way `eff_direct` already
/// inlines a static callee, would never build the node. Every tuple at the
/// node whose twin at the local is already derived is then a tuple that
/// design does not derive.
///
/// Twins are only checkable at depth 0: a propagated instance's operands are
/// in the procedure the instance came *from*, so its node has no local twin
/// here and the hop cannot be collapsed the same way.
fn hop_cost(a: &HybridAnalysis, prog: &Program) {
    let settled: BTreeSet<(Proc, CritId)> = a.settled.iter().cloned().collect();
    let mut arg: BTreeMap<(hybrid_inlining_paper::ir::Stmt, usize), Base> = BTreeMap::new();
    for (s, i, v) in &prog.actual_arg {
        arg.insert((s.clone(), *i), Base::Var(v.clone()));
    }
    let mut retv: BTreeMap<hybrid_inlining_paper::ir::Stmt, Base> = BTreeMap::new();
    for (s, v) in &prog.bind_ret {
        retv.insert(s.clone(), Base::Var(v.clone()));
    }
    // The local a settled origin placeholder stands for, if there is one.
    let twin = |p: &Proc, b: &Base| -> Option<Base> {
        let id = b.crit_id()?;
        if id.depth() != 0 || !settled.contains(&(p.clone(), id.clone())) {
            return None;
        }
        match b {
            Base::CritSlot(_, i) => arg.get(&(id.stmt.clone(), *i)).cloned(),
            Base::CritRet(_) => retv.get(&id.stmt).cloned(),
            _ => None,
        }
    };

    let pts: BTreeSet<(Proc, AccessPath, PtVal)> = a.points.iter().cloned().collect();
    let (mut at_node, mut dup, mut deep) = (0usize, 0usize, 0usize);
    for (p, w, v) in &a.points {
        match w.base.crit_id() {
            Some(id) if settled.contains(&(p.clone(), id.clone())) => {
                if id.depth() != 0 {
                    deep += 1;
                    continue;
                }
                at_node += 1;
                if let Some(t) = twin(p, &w.base)
                    && pts.contains(&(p.clone(), w.rebase(t), v.clone()))
                {
                    dup += 1;
                }
            }
            _ => {}
        }
    }
    let n = a.points.len();
    println!("\n=== the hop, priced ===");
    println!("  points keyed at a settled placeholder, depth 0   {at_node:>10}  {}", pct(at_node, n));
    println!("    whose twin at the local already exists         {dup:>10}  {}   <-- derived twice", pct(dup, n));
    println!("  points keyed at a settled placeholder, deeper    {deep:>10}  {}   (no local twin to merge with)", pct(deep, n));

    let edges: BTreeSet<(Proc, AccessPath, AccessPath)> = a.edge.iter().cloned().collect();
    let (mut e_node, mut e_dup) = (0usize, 0usize);
    for (p, sup, sub) in &a.edge {
        let (ts, tb) = (twin(p, &sup.base), twin(p, &sub.base));
        if ts.is_none() && tb.is_none() {
            continue;
        }
        e_node += 1;
        let s2 = ts.map_or_else(|| sup.clone(), |t| sup.rebase(t));
        let b2 = tb.map_or_else(|| sub.clone(), |t| sub.rebase(t));
        if edges.contains(&(p.clone(), s2, b2)) {
            e_dup += 1;
        }
    }
    println!("  edge touching such a node, depth 0               {e_node:>10}  {}", pct(e_node, a.edge.len()));
    println!("    whose local twin already exists               {e_dup:>10}  {}", pct(e_dup, a.edge.len()));
}

/// Procedures no chain of resolved calls from an `entry` ever reaches.
fn dead_procedures(a: &HybridAnalysis, prog: &Program) {
    let mut callees: BTreeMap<Proc, BTreeSet<Proc>> = BTreeMap::new();
    let mut stmt_proc: BTreeMap<_, Proc> = BTreeMap::new();
    for (s, p, _) in &prog.in_proc {
        stmt_proc.insert(s.clone(), p.clone());
    }
    for (s, callee) in &a.eff_direct {
        if let Some(p) = stmt_proc.get(s) {
            callees.entry(p.clone()).or_default().insert(callee.clone());
        }
    }
    for (p, _, callee) in &a.resolve {
        callees.entry(p.clone()).or_default().insert(callee.clone());
    }

    let mut seen: BTreeSet<Proc> = prog.entry.iter().map(|(p,)| p.clone()).collect();
    let mut work: Vec<Proc> = seen.iter().cloned().collect();
    while let Some(p) = work.pop() {
        for q in callees.get(&p).into_iter().flatten() {
            if seen.insert(q.clone()) {
                work.push(q.clone());
            }
        }
    }

    let all: BTreeSet<Proc> = a.known_proc.iter().map(|(p,)| p.clone()).collect();
    let dead: BTreeSet<Proc> = all.difference(&seen).cloned().collect();
    let dead_points = a.points.iter().filter(|(p, _, _)| dead.contains(p)).count();
    let dead_edge = a.edge.iter().filter(|(p, _, _)| dead.contains(p)).count();
    println!("\n=== procedures unreachable from any entry ===");
    println!("  entries {:>6}", prog.entry.len());
    println!("  known procedures {:>6}", all.len());
    let reach_known = seen.intersection(&all).count();
    println!("  reachable        {:>6}  {}   ({} names reached in all, incl. bodyless CHA targets)",
        reach_known, pct(reach_known, all.len()), seen.len());
    println!("  unreachable      {:>6}  {}", dead.len(), pct(dead.len(), all.len()));
    println!("  points in unreachable procedures {dead_points:>10}  {}", pct(dead_points, a.points.len()));
    println!("  edge   in unreachable procedures {dead_edge:>10}  {}", pct(dead_edge, a.edge.len()));
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut k = 1usize;
    let mut max_procs: Option<usize> = None;
    let mut oracle = true;

    let mut pre = Preprocess::default();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "--max-procs" => max_procs = Some(args.next().unwrap_or_default().parse()?),
            "--no-oracle" => oracle = false,
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
    println!(
        "procs={} stmts={} virtual_call={} direct_call={} k={k}",
        prog.procedure.len(),
        prog.in_proc.len(),
        prog.virtual_call.len(),
        prog.direct_call.len(),
    );

    let mut base = HybridAnalysis::for_program(&prog, k);
    let t0 = Instant::now();
    base.run();
    let base_wall = t0.elapsed();
    println!("baseline: {:?}, {} tuples in the relations compared\n", base_wall, total(&base));

    accounting(&base);
    dispatch_precision(&base);
    hop_cost(&base, &prog);
    dead_procedures(&base, &prog);

    if !oracle {
        return Ok(());
    }

    // --- the oracle run -----------------------------------------------------
    // `will_propagate` is a stratum-A relation the SCC negates over. Seeding
    // it with the *exact* `blocked` set of the baseline makes the resolution
    // guard `!will_propagate` into `!blocked` — adequacy, known for free
    // before the fixpoint starts. Ascent unions a rule's output with whatever
    // the relation was seeded with, so the syntactic rule can only add tuples
    // that are already there (`will_propagate ⊆ blocked` is the claim).
    // Everything the comparison needs, so the baseline itself can be dropped
    // before the second fixpoint is built: at k = 8 holding both at once is
    // 36 GiB, and nothing here needs them simultaneously.
    let base_sizes = sizes(&base);
    let base_total = total(&base);
    let (bs, bd) = answer(&base);
    let ball: BTreeSet<_> = base.resolve.iter().cloned().collect();
    let blocked_seed: Vec<_> = base.blocked.iter().cloned().collect();
    drop(base);

    let mut orc = HybridAnalysis::for_program(&prog, k);
    orc.will_propagate = blocked_seed;
    let seeded = orc.will_propagate.len();
    let t1 = Instant::now();
    orc.run();
    let orc_wall = t1.elapsed();

    println!("\n=== the adequacy oracle: resolve only where the fixpoint says adequate ===");
    println!("  seeded will_propagate with {seeded} blocked instances");
    println!("  wall  {:?}  ->  {:?}   ({:+.1}%)", base_wall, orc_wall,
        100.0 * (orc_wall.as_secs_f64() / base_wall.as_secs_f64() - 1.0));
    println!("\n  {:<16}{:>12}{:>12}{:>10}", "relation", "baseline", "oracle", "delta");
    for ((name, b), (_, o)) in base_sizes.into_iter().zip(sizes(&orc)) {
        let d = if b == 0 { 0.0 } else { 100.0 * (o as f64 / b as f64 - 1.0) };
        println!("  {name:<16}{b:>12}{o:>12}{d:>9.1}%");
    }
    let (bt, ot) = (base_total, total(&orc));
    println!("  {:<16}{bt:>12}{ot:>12}{:>9.1}%", "TOTAL", 100.0 * (ot as f64 / bt as f64 - 1.0));

    let (os, od) = answer(&orc);
    println!("\n  outputs:");
    println!("    summaries equal:        {}", bs == os);
    println!("    settled dispatch equal: {}", bd == od);
    if bs != os {
        let bkeys: BTreeSet<_> = bs.keys().cloned().collect();
        let okeys: BTreeSet<_> = os.keys().cloned().collect();
        println!("      procedures with a summary: {} -> {}", bkeys.len(), okeys.len());
        let mut lost = 0usize;
        let mut gained = 0usize;
        for p in bkeys.union(&okeys) {
            let (b, o) = (bs.get(p), os.get(p));
            let empty = Summary::default();
            let b = b.unwrap_or(&empty);
            let o = o.unwrap_or(&empty);
            lost += b.difference(o).count();
            gained += o.difference(b).count();
        }
        println!("      constraints lost by the oracle: {lost}, gained: {gained}");
    }
    if bd != od {
        println!("      settled dispatches: {} -> {}, lost {}, gained {}",
            bd.len(), od.len(), bd.difference(&od).count(), od.difference(&bd).count());
    }
    // The full dispatch set, adequate or not, is what a whole-program client
    // would read as the call graph.
    let oall: BTreeSet<_> = orc.resolve.iter().cloned().collect();
    println!("    all resolve tuples: {} -> {} (lost {}, gained {})",
        ball.len(), oall.len(), ball.difference(&oall).count(), oall.difference(&ball).count());

    Ok(())
}
