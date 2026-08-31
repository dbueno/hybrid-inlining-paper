//! What is actually *in* `points` at the fixpoint.
//!
//! ```text
//! cargo run --features ctadl --release --example points_anatomy -- \
//!     backflash.apk --k 1
//! ```
//!
//! `backflash-profile.md` says `points` is the largest thing in the run
//! (1,061,910 tuples at `k = 1`) and 55% of rule time, but not what the tuples
//! *are*. This binary answers that: it runs the same fixpoint as
//! `HybridAnalysis`, then cross-tabulates every `points(p, ω, v)` tuple by the
//! kind of root `ω` has and the kind of value `v` is, attributes every
//! `PtVal::Alloc` to the procedure that syntactically contains its allocation
//! statement, and reports where the mass sits per procedure.
//!
//! The headline question it exists to answer: what fraction of `points` is a
//! procedure pointing at an allocation made in some *other* procedure — i.e.
//! how much of the relation is inlined foreign material rather than the
//! procedure's own intraprocedural closure.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use hybrid_inlining_paper::access_path::{AccessPath, Base, PtVal};
use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};
use hybrid_inlining_paper::ir::{Alloc, Proc, Stmt};

/// Coarse kind of a root, for the cross-tab.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Kind {
    Local,
    ParamOwn,
    ParamForeign,
    RetOwn,
    RetForeign,
    CritOwn,
    CritPropagated,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Local => "local var",
            Kind::ParamOwn => "par@self",
            Kind::ParamForeign => "par@other",
            Kind::RetOwn => "ret@self",
            Kind::RetForeign => "ret@other",
            Kind::CritOwn => "crit (own stmt)",
            Kind::CritPropagated => "crit (propagated)",
        }
    }
    fn all() -> [Kind; 7] {
        [
            Kind::Local,
            Kind::ParamOwn,
            Kind::ParamForeign,
            Kind::RetOwn,
            Kind::RetForeign,
            Kind::CritOwn,
            Kind::CritPropagated,
        ]
    }
}

fn kind_of(base: &Base, holder: &Proc, stmt_proc: &HashMap<Stmt, Proc>) -> Kind {
    match base {
        Base::Var(_) => Kind::Local,
        Base::Param(q, _) => {
            if q == holder {
                Kind::ParamOwn
            } else {
                Kind::ParamForeign
            }
        }
        Base::Ret(q) => {
            if q == holder {
                Kind::RetOwn
            } else {
                Kind::RetForeign
            }
        }
        Base::CritSlot(id, _) | Base::CritRet(id) => {
            let own = id.chain.is_empty() && stmt_proc.get(&id.stmt) == Some(holder);
            if own { Kind::CritOwn } else { Kind::CritPropagated }
        }
    }
}

fn pct(n: usize, d: usize) -> f64 {
    if d == 0 { 0.0 } else { 100.0 * n as f64 / d as f64 }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut k = 1usize;
    let mut max_procs: Option<usize> = None;
    let mut top = 15usize;

    let mut pre = Preprocess::default();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "--max-procs" => max_procs = Some(args.next().unwrap_or_default().parse()?),
            "--top" => top = args.next().unwrap_or_default().parse()?,
            "-h" | "--help" => {
                eprintln!("usage: points_anatomy <import>... [--k N] [--max-procs N] [--top N]");
                return Ok(());
            }
            // The ablation: translate the IR as `ctadl import` cached it, without
            // the four passes `ctadl index` runs and this front end now defaults to.
            "--no-preprocess" => pre = Preprocess::none(),
            _ => imports.push(a),
        }
    }
    if imports.is_empty() {
        eprintln!("no imports given; try --help");
        return Ok(());
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

    // stmt -> containing procedure, and thence alloc site -> containing
    // procedure. `alloc` is keyed by statement, so this is the only way to ask
    // "whose allocation is this".
    let stmt_proc: HashMap<Stmt, Proc> = prog
        .in_proc
        .iter()
        .map(|(s, p, _)| (s.clone(), p.clone()))
        .collect();
    let mut alloc_home: HashMap<Alloc, BTreeSet<Proc>> = HashMap::new();
    for (s, _v, l) in &prog.alloc {
        if let Some(p) = stmt_proc.get(s) {
            alloc_home.entry(l.clone()).or_default().insert(p.clone());
        }
    }

    println!(
        "procs={} stmts={} alloc_stmts={} distinct_allocs={} k={}",
        prog.procedure.len(),
        prog.in_proc.len(),
        prog.alloc.len(),
        alloc_home.len(),
        k
    );

    let mut a = HybridAnalysis::for_program(&prog, k);
    let start = std::time::Instant::now();
    a.run();
    println!("fixpoint in {:?}\n", start.elapsed());

    let total = a.points.len();

    // ---- the headline: whose allocations is a procedure looking at? -----
    let (mut v_alloc, mut v_const, mut v_path) = (0usize, 0usize, 0usize);
    let (mut own_alloc, mut foreign_alloc, mut unknown_alloc) = (0usize, 0usize, 0usize);
    // the same question restricted to tuples over a *local* key, which is the
    // part of `points` that never leaves the procedure
    let (mut own_alloc_local_key, mut foreign_alloc_local_key) = (0usize, 0usize);

    // key-kind x value-kind cross-tab; value kinds are the 7 root kinds of a
    // `Path` value plus alloc-own / alloc-foreign / const
    let mut xtab: BTreeMap<(Kind, &'static str), usize> = BTreeMap::new();

    let mut depth_key = vec![0usize; 8];
    let mut depth_val = vec![0usize; 8];

    // per-procedure mass
    #[derive(Default, Clone)]
    struct ProcStat {
        tuples: usize,
        alloc_tuples: usize,
        foreign_alloc_tuples: usize,
        paths: BTreeSet<AccessPath>,
        allocs: BTreeSet<Alloc>,
        foreign_allocs: BTreeSet<Alloc>,
        path_vals: usize,
    }
    let mut per_proc: HashMap<Proc, ProcStat> = HashMap::new();
    // how many procedures see each allocation
    let mut alloc_fanout: HashMap<Alloc, BTreeSet<Proc>> = HashMap::new();

    for (p, w, v) in &a.points {
        let kk = kind_of(&w.base, p, &stmt_proc);
        let d = w.accessors.len().min(7);
        depth_key[d] += 1;
        let st = per_proc.entry(p.clone()).or_default();
        st.tuples += 1;
        st.paths.insert(w.clone());

        let vk: &'static str = match v {
            PtVal::Const(_) => {
                v_const += 1;
                "const"
            }
            PtVal::Alloc(l) => {
                v_alloc += 1;
                st.alloc_tuples += 1;
                st.allocs.insert(l.clone());
                alloc_fanout.entry(l.clone()).or_default().insert(p.clone());
                match alloc_home.get(l) {
                    None => {
                        unknown_alloc += 1;
                        "alloc (no home)"
                    }
                    Some(homes) if homes.contains(p) => {
                        own_alloc += 1;
                        if kk == Kind::Local {
                            own_alloc_local_key += 1;
                        }
                        "alloc (own)"
                    }
                    Some(_) => {
                        foreign_alloc += 1;
                        st.foreign_alloc_tuples += 1;
                        st.foreign_allocs.insert(l.clone());
                        if kk == Kind::Local {
                            foreign_alloc_local_key += 1;
                        }
                        "alloc (foreign)"
                    }
                }
            }
            PtVal::Path(b) => {
                v_path += 1;
                st.path_vals += 1;
                depth_val[b.accessors.len().min(7)] += 1;
                match kind_of(&b.base, p, &stmt_proc) {
                    Kind::Local => "path: local var",
                    Kind::ParamOwn => "path: par@self",
                    Kind::ParamForeign => "path: par@other",
                    Kind::RetOwn => "path: ret@self",
                    Kind::RetForeign => "path: ret@other",
                    Kind::CritOwn => "path: crit own",
                    Kind::CritPropagated => "path: crit prop",
                }
            }
        };
        *xtab.entry((kk, vk)).or_default() += 1;
    }

    println!("=== points at the fixpoint: {total} tuples ===\n");
    println!("by value kind");
    for (name, n) in [
        ("PtVal::Path  (symbolic)", v_path),
        ("PtVal::Alloc (an object)", v_alloc),
        ("PtVal::Const", v_const),
    ] {
        println!("  {name:<26} {n:>10}  {:>6.2}%", pct(n, total));
    }

    println!("\nthe allocation-valued tuples, by whose allocation it is");
    for (name, n) in [
        ("same procedure", own_alloc),
        ("another procedure", foreign_alloc),
        ("no home (not in `alloc`)", unknown_alloc),
    ] {
        println!(
            "  {name:<26} {n:>10}  {:>6.2}% of alloc  {:>6.2}% of points",
            pct(n, v_alloc),
            pct(n, total)
        );
    }
    println!(
        "  (of the foreign ones, {} sit under a local-variable key, {} under a symbolic one)",
        foreign_alloc_local_key,
        foreign_alloc - foreign_alloc_local_key
    );
    println!(
        "  (of the own ones,     {} sit under a local-variable key, {} under a symbolic one)",
        own_alloc_local_key,
        own_alloc - own_alloc_local_key
    );

    println!("\nby key root kind");
    let mut key_totals: BTreeMap<Kind, usize> = BTreeMap::new();
    for ((kk, _), n) in &xtab {
        *key_totals.entry(*kk).or_default() += n;
    }
    for kk in Kind::all() {
        let n = key_totals.get(&kk).copied().unwrap_or(0);
        if n > 0 {
            println!("  {:<20} {n:>10}  {:>6.2}%", kk.name(), pct(n, total));
        }
    }

    println!("\ncross-tab (rows: key root; cols: value), tuples and % of all points");
    let cols: Vec<&'static str> = {
        let mut c: BTreeSet<&'static str> = BTreeSet::new();
        for ((_, vk), _) in &xtab {
            c.insert(vk);
        }
        c.into_iter().collect()
    };
    for kk in Kind::all() {
        if key_totals.get(&kk).copied().unwrap_or(0) == 0 {
            continue;
        }
        println!("  {}", kk.name());
        for c in &cols {
            let n = xtab.get(&(kk, *c)).copied().unwrap_or(0);
            if n > 0 {
                println!("      {c:<18} {n:>10}  {:>6.2}%", pct(n, total));
            }
        }
    }

    println!("\naccess-path depth of the key ω");
    for (d, n) in depth_key.iter().enumerate() {
        if *n > 0 {
            println!("  depth {d}: {n:>10}  {:>6.2}%", pct(*n, total));
        }
    }
    println!("access-path depth of a Path value");
    for (d, n) in depth_val.iter().enumerate() {
        if *n > 0 {
            println!("  depth {d}: {n:>10}  {:>6.2}%", pct(*n, v_path));
        }
    }

    // ---- where the mass sits, per procedure -----------------------------
    let mut stats: Vec<(Proc, ProcStat)> = per_proc.into_iter().collect();
    stats.sort_by_key(|(p, s)| (std::cmp::Reverse(s.tuples), p.0.to_string()));
    let nonempty = stats.len();
    println!(
        "\n=== distribution over procedures ===\n{nonempty} procedures have any `points` \
         tuple at all (of {} known)",
        prog.procedure.len()
    );
    let mut cum = 0usize;
    let mut p50 = 0usize;
    let mut p90 = 0usize;
    for (i, (_, s)) in stats.iter().enumerate() {
        cum += s.tuples;
        if p50 == 0 && cum * 2 >= total {
            p50 = i + 1;
        }
        if p90 == 0 && cum * 10 >= total * 9 {
            p90 = i + 1;
        }
    }
    println!("the largest {p50} procedures hold half of `points`; the largest {p90} hold 90%");
    println!(
        "\n  {:<58} {:>8} {:>7} {:>7} {:>8} {:>7}",
        "procedure", "tuples", "paths", "allocs", "foreign", "vals/path"
    );
    for (p, s) in stats.iter().take(top) {
        let name = p.0.to_string();
        let short = if name.len() > 58 { format!("…{}", &name[name.len() - 57..]) } else { name };
        println!(
            "  {:<58} {:>8} {:>7} {:>7} {:>8} {:>7.1}",
            short,
            s.tuples,
            s.paths.len(),
            s.allocs.len(),
            s.foreign_allocs.len(),
            s.tuples as f64 / s.paths.len().max(1) as f64
        );
    }

    let sum_paths: usize = stats.iter().map(|(_, s)| s.paths.len()).sum();
    let sum_allocs: usize = stats.iter().map(|(_, s)| s.allocs.len()).sum();
    let sum_foreign: usize = stats.iter().map(|(_, s)| s.foreign_allocs.len()).sum();
    println!(
        "\n  totals: {sum_paths} (proc, path) keys, {} tuples, {:.1} values per key",
        total,
        total as f64 / sum_paths.max(1) as f64
    );
    println!(
        "  Σ_p |allocs visible in p| = {sum_allocs}, of which foreign {sum_foreign} \
         ({:>.1}%)",
        pct(sum_foreign, sum_allocs.max(1))
    );

    // ---- what the symbolic mass is made of ------------------------------
    //
    // 93% of `points` is a `PtVal::Path`, and most of it hangs off a
    // propagated placeholder. This asks the obvious follow-up: how many
    // distinct *symbols* does one procedure end up carrying, how many pending
    // instances minted them, and how dense the (key x value) square is.
    let mut pending_per: HashMap<Proc, usize> = HashMap::new();
    for (p, _id) in &a.pending {
        *pending_per.entry(p.clone()).or_default() += 1;
    }
    let mut settled_per: HashMap<Proc, usize> = HashMap::new();
    for (p, _id) in &a.settled {
        *settled_per.entry(p.clone()).or_default() += 1;
    }
    let mut vals_per: HashMap<Proc, BTreeSet<PtVal>> = HashMap::new();
    let mut crits_per: HashMap<Proc, BTreeSet<String>> = HashMap::new();
    let mut fanout: Vec<usize> = Vec::new();
    let mut per_key: HashMap<(Proc, AccessPath), usize> = HashMap::new();
    for (p, w, v) in &a.points {
        vals_per.entry(p.clone()).or_default().insert(v.clone());
        *per_key.entry((p.clone(), w.clone())).or_default() += 1;
        for b in [Some(&w.base), match v { PtVal::Path(x) => Some(&x.base), _ => None }]
            .into_iter()
            .flatten()
        {
            if let Some(id) = b.crit_id() {
                crits_per
                    .entry(p.clone())
                    .or_default()
                    .insert(format!("{}|{}", id.stmt, id.chain.len()));
            }
        }
    }
    fanout.extend(per_key.values().copied());
    fanout.sort_unstable();
    let fq = |f: f64| fanout[((fanout.len() as f64 - 1.0) * f) as usize];
    println!(
        "\n=== how dense is each procedure's square? ===\nvalues per (proc, path) key: \
         n={} mean={:.1} p50={} p90={} p99={} max={}",
        fanout.len(),
        total as f64 / fanout.len() as f64,
        fq(0.5),
        fq(0.9),
        fq(0.99),
        fanout.last().copied().unwrap_or(0)
    );
    println!(
        "\n  {:<48} {:>8} {:>7} {:>7} {:>7} {:>7} {:>6}",
        "procedure", "tuples", "keys", "values", "crits", "pending", "dens%"
    );
    for (p, s) in stats.iter().take(top) {
        let name = p.0.to_string();
        let short =
            if name.len() > 48 { format!("\u{2026}{}", &name[name.len() - 47..]) } else { name };
        let nv = vals_per.get(p).map(|v| v.len()).unwrap_or(0);
        println!(
            "  {:<48} {:>8} {:>7} {:>7} {:>7} {:>7} {:>6.1}",
            short,
            s.tuples,
            s.paths.len(),
            nv,
            crits_per.get(p).map(|c| c.len()).unwrap_or(0),
            pending_per.get(p).copied().unwrap_or(0),
            100.0 * s.tuples as f64 / (s.paths.len().max(1) * nv.max(1)) as f64
        );
    }
    let sum_sq: f64 = stats
        .iter()
        .map(|(p, s)| {
            (s.paths.len() * vals_per.get(p).map(|v| v.len()).unwrap_or(0)) as f64
        })
        .sum();
    println!(
        "  Σ_p |keys_p| × |values_p| = {:.0}; `points` fills {:.1}% of it",
        sum_sq,
        100.0 * total as f64 / sum_sq.max(1.0)
    );
    println!(
        "  pending instances: {} in {} procedures; settled: {}",
        a.pending.len(),
        pending_per.len(),
        a.settled.len()
    );

    // ---- how much of it survives into a summary? ------------------------
    //
    // A tuple over a *local* key never leaves the procedure (locals are
    // eliminated before publication), and a tuple mentioning a *settled*
    // placeholder is plumbing for a critical statement that has already been
    // decided — `summaries()` drops both. This is the share of `points` that
    // exists only so the fixpoint can reach the part that is kept.
    let settled: BTreeSet<(Proc, String)> = a
        .settled
        .iter()
        .map(|(p, id)| (p.clone(), format!("{}|{:?}", id.stmt, id.chain)))
        .collect();
    let is_settled = |p: &Proc, b: &Base| match b.crit_id() {
        Some(id) => settled.contains(&(p.clone(), format!("{}|{:?}", id.stmt, id.chain))),
        None => false,
    };
    let (mut local_key, mut settled_key, mut settled_val, mut either_settled, mut keepable) =
        (0usize, 0usize, 0usize, 0usize, 0usize);
    for (p, w, v) in &a.points {
        let lk = matches!(w.base, Base::Var(_));
        let sk = is_settled(p, &w.base);
        let sv = match v {
            PtVal::Path(b) => is_settled(p, &b.base),
            _ => false,
        };
        if lk {
            local_key += 1;
        }
        if sk {
            settled_key += 1;
        }
        if sv {
            settled_val += 1;
        }
        if sk || sv {
            either_settled += 1;
        }
        if !lk && !sk && !sv {
            keepable += 1;
        }
    }
    println!(
        "\n=== how much of `points` reaches a summary? ===\n  \
         key is a local var (eliminated before publication)  {local_key:>9}  {:>6.2}%\n  \
         key roots at a settled placeholder                  {settled_key:>9}  {:>6.2}%\n  \
         value roots at a settled placeholder                {settled_val:>9}  {:>6.2}%\n  \
         either endpoint settled                             {either_settled:>9}  {:>6.2}%\n  \
         neither local nor settled (publishable material)    {keepable:>9}  {:>6.2}%",
        pct(local_key, total),
        pct(settled_key, total),
        pct(settled_val, total),
        pct(either_settled, total),
        pct(keepable, total)
    );
    println!(
        "  for comparison: pub_edges() = {}, pub_points = {}, pub_root = {}, \
         summaries() keeps {} constraints",
        a.pub_edges().len(),
        a.pub_points.len(),
        a.pub_root.len(),
        a.summaries().values().map(|s| s.len()).sum::<usize>()
    );

    // how far does one allocation travel?
    let mut fan: Vec<(usize, Alloc)> = alloc_fanout
        .iter()
        .map(|(l, ps)| (ps.len(), l.clone()))
        .collect();
    fan.sort_by_key(|(n, l)| (std::cmp::Reverse(*n), l.0.to_string()));
    let seen = fan.len();
    let fsum: usize = fan.iter().map(|(n, _)| n).sum();
    println!(
        "\n=== allocation fan-out ===\n{seen} distinct allocations appear in `points`; \
         each is visible in {:.1} procedures on average",
        fsum as f64 / seen.max(1) as f64
    );
    let mut counts: Vec<usize> = fan.iter().map(|(n, _)| *n).collect();
    counts.sort_unstable();
    let q = |f: f64| counts[((counts.len() as f64 - 1.0) * f) as usize];
    println!(
        "  procedures per allocation: p50={} p90={} p99={} max={}",
        q(0.5),
        q(0.9),
        q(0.99),
        counts.last().copied().unwrap_or(0)
    );
    println!("  the most widely-visible allocations:");
    for (n, l) in fan.iter().take(10) {
        let home = alloc_home
            .get(l)
            .map(|h| h.iter().map(|p| p.0.to_string()).collect::<Vec<_>>().join(","))
            .unwrap_or_else(|| "?".into());
        let home = if home.len() > 70 { format!("…{}", &home[home.len() - 69..]) } else { home };
        println!("    {n:>5} procedures  {l}  home={home}");
    }

    Ok(())
}
