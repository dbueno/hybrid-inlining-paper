//! Does eager (per-allocation) resolution cost more than the paper's
//! adequacy-gated resolution? Measured on a family the existing ones miss:
//! a receiver that is *partially* pinned — one local allocation merged with
//! the symbolic parameter — under `n` levels of callers.

use hybrid_inlining_paper::analysis::run_hybrid;
use hybrid_inlining_paper::ir::*;

fn p(x: &str) -> Proc { x.into() }
fn s(x: &str) -> Stmt { x.into() }
fn v(x: &str) -> Var { x.into() }
fn l(x: &str) -> Alloc { x.into() }
fn t(x: &str) -> Type { x.into() }
fn g(x: &str) -> Sig { x.into() }

/// `P0(this, x, obj) { y = x; y = new C1; return y.poly(obj) }` with `n`
/// direct callers above it and `Entry` pinning a `C0` receiver at the top.
///
/// At every holder the deciding operand holds *both* `Alloc(l@local)` and
/// `Path(par_1@P0)`, so the instance is blocked all the way up — and eager
/// resolution fires `C1.poly` at every one of the `n+1` holders, where the
/// paper would fire it once, at `Entry`.
fn partial(n: usize, targets: usize) -> Program { partial_ext(n, targets, true, false) }

/// `pinned = false` removes the local allocation, so the receiver is purely
/// symbolic and no holder below `Entry` can resolve anything: the control for
/// the measurement above.
///
/// `nested = true` gives `C1.poly` a critical statement of its own, so every
/// redundant resolution of it also spawns a *nested* placeholder.
fn partial_ext(n: usize, targets: usize, pinned: bool, nested: bool) -> Program {
    let mut prog = Program::default();
    let mut line = std::collections::BTreeMap::<String, usize>::new();
    let mut stmt = |prog: &mut Program, st: &str, owner: &str| {
        let c = line.entry(owner.to_string()).or_insert(0);
        prog.in_proc.push((s(st), p(owner), *c));
        *c += 1;
    };

    for j in 0..targets {
        let (ty, imp) = (format!("C{j}"), format!("C{j}.poly"));
        prog.direct_subtype.push((t(&ty), t("I")));
        prog.lookup.push((t(&ty), g("poly(Obj)"), p(&imp)));
        prog.proc_sig.push((p(&imp), g("poly(Obj)")));
        prog.procedure.push((p(&imp),));
        prog.proc_type.push((p(&imp), t("K")));
        prog.formal.push((p(&imp), 0, v(&format!("this@{imp}"))));
        prog.formal.push((p(&imp), 1, v(&format!("obj@{imp}"))));
        if j == 0 {
            prog.ret.push((p(&imp), v(&format!("obj@{imp}"))));
        } else {
            stmt(&mut prog, &format!("A@{imp}"), &imp);
            prog.alloc.push((s(&format!("A@{imp}")), v(&format!("t@{imp}")), l(&format!("l@{imp}"))));
            prog.alloc_type.push((l(&format!("l@{imp}")), t("Obj")));
            prog.ret.push((p(&imp), v(&format!("t@{imp}"))));
        }
    }

    if nested {
        // `C1.poly` becomes critical itself: `q = obj.poly(obj)`, whose
        // receiver is `C1.poly`'s own parameter and so always blocked there.
        stmt(&mut prog, "N@C1.poly", "C1.poly");
        prog.virtual_call.push((s("N@C1.poly"), v("obj@C1.poly"), g("poly(Obj)")));
        prog.actual_arg.push((s("N@C1.poly"), 0, v("obj@C1.poly")));
        prog.actual_arg.push((s("N@C1.poly"), 1, v("obj@C1.poly")));
        prog.bind_ret.push((s("N@C1.poly"), v("q@C1.poly")));
    }

    // The critical leaf, with a *partially* pinned receiver.
    prog.procedure.push((p("P0"),));
    prog.proc_type.push((p("P0"), t("K")));
    for (i, f) in ["this@P0", "x@P0", "obj@P0"].iter().enumerate() {
        prog.formal.push((p("P0"), i, v(f)));
    }
    stmt(&mut prog, "S0m", "P0");
    prog.mov.push((s("S0m"), v("y@P0"), v("x@P0")));      // symbolic half
    if pinned {
        stmt(&mut prog, "S0a", "P0");
        prog.alloc.push((s("S0a"), v("y@P0"), l("l@P0")));    // pinned half
        prog.alloc_type.push((l("l@P0"), t("C1")));
    }
    stmt(&mut prog, "S0", "P0");
    prog.virtual_call.push((s("S0"), v("y@P0"), g("poly(Obj)")));
    prog.actual_arg.push((s("S0"), 0, v("y@P0")));
    prog.actual_arg.push((s("S0"), 1, v("obj@P0")));
    prog.bind_ret.push((s("S0"), v("r@P0")));
    prog.ret.push((p("P0"), v("r@P0")));

    for i in 1..=n {
        let (me, below) = (format!("P{i}"), format!("P{}", i - 1));
        prog.procedure.push((p(&me),));
        prog.proc_type.push((p(&me), t("K")));
        for (j, f) in [format!("this@{me}"), format!("x@{me}"), format!("obj@{me}")].iter().enumerate() {
            prog.formal.push((p(&me), j, v(f)));
        }
        stmt(&mut prog, &format!("S{i}"), &me);
        prog.direct_call.push((s(&format!("S{i}")), p(&below)));
        for (j, a) in [format!("this@{me}"), format!("x@{me}"), format!("obj@{me}")].iter().enumerate() {
            prog.actual_arg.push((s(&format!("S{i}")), j, v(a)));
        }
        prog.bind_ret.push((s(&format!("S{i}")), v(&format!("r@{me}"))));
        prog.ret.push((p(&me), v(&format!("r@{me}"))));
    }

    prog.procedure.push((p("Entry"),));
    prog.proc_type.push((p("Entry"), t("K")));
    prog.formal.push((p("Entry"), 0, v("this@Entry")));
    stmt(&mut prog, "E0", "Entry");
    prog.alloc.push((s("E0"), v("first"), l("lfirst")));
    prog.alloc_type.push((l("lfirst"), t("Obj")));
    stmt(&mut prog, "E1", "Entry");
    prog.alloc.push((s("E1"), v("recv"), l("lrecv")));
    prog.alloc_type.push((l("lrecv"), t("C0")));
    stmt(&mut prog, "E2", "Entry");
    prog.direct_call.push((s("E2"), p(&format!("P{n}"))));
    for (j, a) in ["this@Entry", "recv", "first"].iter().enumerate() {
        prog.actual_arg.push((s("E2"), j, v(a)));
    }
    prog.bind_ret.push((s("E2"), v("res")));
    prog.entry.push((p("Entry"),));
    prog
}

fn fit(xs: &[f64], ys: &[f64]) -> f64 {
    let pts: Vec<(f64, f64)> = xs.iter().zip(ys).filter(|(_, y)| **y > 0.0)
        .map(|(x, y)| (x.ln(), y.ln())).collect();
    let n = pts.len() as f64;
    let (mx, my) = (pts.iter().map(|q| q.0).sum::<f64>() / n, pts.iter().map(|q| q.1).sum::<f64>() / n);
    let num: f64 = pts.iter().map(|(x, y)| (x - mx) * (y - my)).sum();
    let den: f64 = pts.iter().map(|(x, _)| (x - mx).powi(2)).sum();
    num / den
}

type H = hybrid_inlining_paper::analysis::HybridAnalysis;

fn sweep(tag: &str, ns: &[usize], pinned: bool, nested: bool) {
    let hs: Vec<H> = ns.iter().map(|&n| run_hybrid(&partial_ext(n, 3, pinned, nested), n + 2)).collect();
    let xs: Vec<f64> = ns.iter().map(|&n| n as f64).collect();
    println!("  {tag}");
    let cols: [(&str, fn(&H) -> usize); 5] = [
        ("pending", |h| h.pending.len()),
        ("resolve", |h| h.resolve.len()),
        ("crit_map", |h| h.crit_map.len()),
        ("points", |h| h.points.len()),
        ("edge", |h| h.edge.len()),
    ];
    for (name, f) in cols {
        let ys: Vec<f64> = hs.iter().map(|h| f(h) as f64).collect();
        let sizes = ys.iter().map(|y| format!("{y:.0}")).collect::<Vec<_>>().join(" ");
        println!("    {name:<10} n^{:>4.2}   {sizes}", fit(&xs, &ys));
    }
    println!();
}

fn main() {
    let ns = [2usize, 4, 8, 16, 32];
    println!("one critical call under n callers, k = n+2, 3 CHA targets; fits vs n\n");
    sweep("symbolic  (receiver purely symbolic — nothing resolves below Entry)", &ns, false, false);
    sweep("partial   (receiver = local C1 alloc + parameter)", &ns, true, false);
    sweep("sym+nest  (symbolic, and C1.poly is itself critical)", &ns, false, true);
    sweep("part+nest (partial, and C1.poly is itself critical)", &ns, true, true);

    println!("resolve tuples for partial(4, 3), holder by holder:");
    let h = run_hybrid(&partial(4, 3), 6);
    let mut rows: Vec<String> = h.resolve.iter()
        .map(|(q, id, callee)| {
            let tag = if h.blocked.contains(&(q.clone(), id.clone())) { "BLOCKED" } else { "adequate" };
            format!("  {q} :: {id:?} -> {callee}   [{tag}]")
        })
        .collect();
    rows.sort();
    for r in rows { println!("{r}"); }
}
