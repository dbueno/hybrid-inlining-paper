//! The shape `will_propagate` cannot see, and what an exact adequacy test
//! would save on it.
//!
//! `will_propagate` is the syntactic under-approximation of `blocked` that
//! gates resolution: an instance whose deciding operand is fed from a formal
//! *by a chain of moves* is certainly blocked and certainly has somewhere to
//! go, so resolving it here only duplicates what the caller will redo.
//! `carries` follows moves and nothing else, so a receiver blocked through a
//! **field load** — `y = x.f`, with `x` a formal — is invisible to it: the
//! instance is blocked, it does propagate, and it is resolved here anyway.
//!
//! That is the residual class the exact test would remove. This program is
//! the smallest thing in it, and the run below prices it: baseline against a
//! run whose `will_propagate` is seeded with the baseline's own `blocked`,
//! which is adequacy known for free.
//!
//! ```text
//! cargo run --release --example redundant_shape
//! ```

use std::collections::BTreeMap;

use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::ir::*;

fn p(x: &str) -> Proc { x.into() }
fn s(x: &str) -> Stmt { x.into() }
fn v(x: &str) -> Var { x.into() }
fn l(x: &str) -> Alloc { x.into() }
fn t(x: &str) -> Type { x.into() }
fn g(x: &str) -> Sig { x.into() }
fn f(x: &str) -> Field { x.into() }

/// `P0(this, x, obj) { y = x.f; y = new C1; r = y.poly(obj); return r }` under
/// `n` direct callers, with `Entry` pinning a `C0` receiver at the top.
///
/// `via_load = false` writes `y = x` instead, which is the move chain
/// `carries` does follow — the control.
fn prog(n: usize, targets: usize, via_load: bool) -> Program {
    let mut prog = Program::default();
    let mut line = BTreeMap::<String, usize>::new();
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
        stmt(&mut prog, &format!("A@{imp}"), &imp);
        prog.alloc.push((s(&format!("A@{imp}")), v(&format!("t@{imp}")), l(&format!("l@{imp}"))));
        prog.alloc_type.push((l(&format!("l@{imp}")), t("Obj")));
        prog.ret.push((p(&imp), v(&format!("t@{imp}"))));
    }

    prog.procedure.push((p("P0"),));
    prog.proc_type.push((p("P0"), t("K")));
    for (i, fm) in ["this@P0", "x@P0", "obj@P0"].iter().enumerate() {
        prog.formal.push((p("P0"), i, v(fm)));
    }
    stmt(&mut prog, "S0m", "P0");
    if via_load {
        prog.load_field.push((s("S0m"), v("y@P0"), v("x@P0"), f("fld")));
    } else {
        prog.mov.push((s("S0m"), v("y@P0"), v("x@P0")));
    }
    stmt(&mut prog, "S0a", "P0");
    prog.alloc.push((s("S0a"), v("y@P0"), l("l@P0")));
    prog.alloc_type.push((l("l@P0"), t("C1")));
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
        for (j, fm) in [format!("this@{me}"), format!("x@{me}"), format!("obj@{me}")].iter().enumerate() {
            prog.formal.push((p(&me), j, v(fm)));
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

fn run(prog: &Program, k: usize, oracle: Option<&Vec<(Proc, hybrid_inlining_paper::access_path::CritId)>>) -> HybridAnalysis {
    let mut a = HybridAnalysis::for_program(prog, k);
    if let Some(b) = oracle {
        a.will_propagate = b.clone();
    }
    a.run();
    a
}

fn main() {
    println!("one critical call under n callers, k = n+2, 3 CHA targets\n");
    for via_load in [false, true] {
        println!("  receiver blocked through a {}", if via_load { "FIELD LOAD (will_propagate is blind to it)" } else { "move chain (will_propagate sees it)" });
        println!("    {:>4}{:>10}{:>10}{:>10}{:>12}{:>10}{:>10}{:>10}",
            "n", "resolve", "redundant", "pending", "points", "edge", "pts/orc", "edge/orc");
        for n in [2usize, 4, 8, 16, 32] {
            let pr = prog(n, 3, via_load);
            let k = n + 2;
            let a = run(&pr, k, None);
            let blocked: Vec<_> = a.blocked.iter().cloned().collect();
            let can: std::collections::BTreeSet<_> = a.can_propagate.iter().cloned().collect();
            let bset: std::collections::BTreeSet<_> = blocked.iter().cloned().collect();
            let redundant = a
                .resolve
                .iter()
                .filter(|(q, id, _)| bset.contains(&((*q).clone(), id.clone())) && can.contains(&((*q).clone(), id.clone())))
                .count();
            let o = run(&pr, k, Some(&blocked));
            println!("    {n:>4}{:>10}{redundant:>10}{:>10}{:>12}{:>10}{:>10}{:>10}",
                a.resolve.len(), a.pending.len(), a.points.len(), a.edge.len(), o.points.len(), o.edge.len());
            // The answers must not move: same summaries, same settled dispatch.
            let (bs, os) = (a.summaries(), o.summaries());
            if bs != os {
                let mut msg = Vec::new();
                for q in bs.keys().chain(os.keys()).collect::<std::collections::BTreeSet<_>>() {
                    let d = std::collections::BTreeSet::new();
                    let (b, oo) = (bs.get(q).unwrap_or(&d), os.get(q).unwrap_or(&d));
                    if b != oo {
                        msg.push(format!("{q}: {} -> {} ({} lost, {} gained)", b.len(), oo.len(),
                            b.difference(oo).count(), oo.difference(b).count()));
                    }
                }
                println!("      summaries differ: {}", msg.join("; "));
            }
            let sd = |h: &HybridAnalysis| -> std::collections::BTreeSet<_> {
                let st: std::collections::BTreeSet<_> = h.settled.iter().cloned().collect();
                h.resolve.iter().filter(|(q, id, _)| st.contains(&((*q).clone(), id.clone())))
                    .map(|(q, id, c)| (q.clone(), id.clone(), c.clone())).collect()
            };
            if sd(&a) != sd(&o) {
                println!("      !! settled dispatch differs: {} -> {}", sd(&a).len(), sd(&o).len());
            }
        }
        println!();
    }
}
