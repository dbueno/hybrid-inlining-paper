//! Parametric families of programs, for measuring how the analysis scales.
//!
//! Each generator turns one integer knob into a program of the same shape, so
//! that fitting |R| against the program's EDB size says something about the
//! relation's complexity rather than about one hand-written example. They live
//! in the library, not in an example, because both `examples/complexity.rs`
//! (relation sizes) and `examples/parallel.rs` (backend timings) run them, and
//! `tests/scaling.rs` guards the results against rule edits.
//!
//! The families are chosen to separate the axes the analysis can blow up
//! along:
//!
//! | family | axis it stresses |
//! |--------|------------------|
//! | [`chain`] | propagation depth: one critical statement, `n` callers above it |
//! | [`fanin`] | call-graph fan-in: one critical procedure, `m` distinct callers |
//! | [`branching`] | call-string count: every level reachable by two paths |
//! | [`targets`] | CHA width: one critical call with `t` implementations |
//! | [`alias`] | points-to pressure: `n` allocations merged into `n` variables |
//! | [`fields`] | access-path suffix congruence inside one procedure |
//! | [`fields_chain`] | access-path *length* growing through inlining |
//! | [`recursive_field`] | termination when inlining feeds its own summary |
//! | [`dead_receiver`] | the vacuous corner of adequacy: an empty deciding operand |
//! | [`wide`] | many procedures × real data flow, with nothing critical |

use std::collections::BTreeMap;

use crate::ir::*;

fn p(x: &str) -> Proc { x.into() }
fn s(x: &str) -> Stmt { x.into() }
fn v(x: &str) -> Var { x.into() }
fn l(x: &str) -> Alloc { x.into() }
fn t(x: &str) -> Type { x.into() }
fn g(x: &str) -> Sig { x.into() }

/// Small builder, so the generators below read like the IR and not like a pile
/// of vector pushes. It also keeps `in_proc`'s line numbers consistent.
#[derive(Default)]
struct B {
    prog: Program,
    line: BTreeMap<String, usize>,
}

impl B {
    fn proc_(&mut self, name: &str, formals: &[&str]) {
        self.prog.procedure.push((p(name),));
        self.prog.proc_type.push((p(name), t("K")));
        for (i, f) in formals.iter().enumerate() {
            self.prog.formal.push((p(name), i, v(f)));
        }
    }

    fn stmt(&mut self, st: &str, owner: &str) {
        let n = self.line.entry(owner.to_string()).or_insert(0);
        self.prog.in_proc.push((s(st), p(owner), *n));
        *n += 1;
    }

    fn alloc(&mut self, st: &str, owner: &str, var: &str, site: &str, ty: &str) {
        self.stmt(st, owner);
        self.prog.alloc.push((s(st), v(var), l(site)));
        self.prog.alloc_type.push((l(site), t(ty)));
    }

    fn mov(&mut self, st: &str, owner: &str, to: &str, from: &str) {
        self.stmt(st, owner);
        self.prog.mov.push((s(st), v(to), v(from)));
    }

    fn load_field(&mut self, st: &str, owner: &str, to: &str, base: &str, f: &str) {
        self.stmt(st, owner);
        self.prog.load_field.push((s(st), v(to), v(base), Field::from(f)));
    }

    fn call(&mut self, st: &str, owner: &str, callee: &str, args: &[&str], ret: Option<&str>) {
        self.stmt(st, owner);
        self.prog.direct_call.push((s(st), p(callee)));
        for (i, a) in args.iter().enumerate() {
            self.prog.actual_arg.push((s(st), i, v(a)));
        }
        if let Some(r) = ret {
            self.prog.bind_ret.push((s(st), v(r)));
        }
    }

    fn vcall(&mut self, st: &str, owner: &str, recv: &str, sig: &str, args: &[&str], ret: &str) {
        self.stmt(st, owner);
        self.prog.virtual_call.push((s(st), v(recv), g(sig)));
        for (i, a) in args.iter().enumerate() {
            self.prog.actual_arg.push((s(st), i, v(a)));
        }
        self.prog.bind_ret.push((s(st), v(ret)));
    }

    fn ret(&mut self, owner: &str, var: &str) {
        self.prog.ret.push((p(owner), v(var)));
    }

    fn entry(&mut self, owner: &str) {
        self.prog.entry.push((p(owner),));
    }

    /// `targets` implementations of `poly(Obj)`, on types `C0..C{targets-1}`.
    /// `C0.poly` is the identity, the rest each allocate, so the callees are
    /// distinguishable in the points-to sets.
    fn hierarchy(&mut self, targets: usize) {
        for j in 0..targets {
            let ty = format!("C{j}");
            let imp = format!("C{j}.poly");
            self.prog.direct_subtype.push((t(&ty), t("I")));
            self.prog.lookup.push((t(&ty), g("poly(Obj)"), p(&imp)));
            self.prog.proc_sig.push((p(&imp), g("poly(Obj)")));
            self.proc_(&imp, &[&format!("this@{imp}"), &format!("obj@{imp}")]);
            if j == 0 {
                self.ret(&imp, &format!("obj@{imp}"));
            } else {
                let st = format!("A@{imp}");
                self.alloc(&st, &imp, &format!("t@{imp}"), &format!("l@{imp}"), "Obj");
                self.ret(&imp, &format!("t@{imp}"));
            }
        }
    }

    /// The critical procedure every call-shaped family is built around:
    /// `P0(this, x, obj) { return x.poly(obj) }`, where `poly` has `targets`
    /// implementations and so is critical.
    fn critical_leaf(&mut self) {
        self.proc_("P0", &["this@P0", "x@P0", "obj@P0"]);
        self.vcall("S0", "P0", "x@P0", "poly(Obj)", &["x@P0", "obj@P0"], "r@P0");
        self.ret("P0", "r@P0");
    }

    fn done(self) -> Program {
        self.prog
    }
}

/// EDB fact count — the stand-in for "size of the program" in the fits.
pub fn edb_size(prog: &Program) -> usize {
    prog.procedure.len()
        + prog.in_proc.len()
        + prog.alloc.len()
        + prog.mov.len()
        + prog.load_field.len()
        + prog.store_field.len()
        + prog.direct_call.len()
        + prog.virtual_call.len()
        + prog.actual_arg.len()
        + prog.bind_ret.len()
        + prog.formal.len()
        + prog.ret.len()
        + prog.lookup.len()
}

/// A linear call chain of `n` procedures above one critical virtual call —
/// Figure 1's `foo ← mid ← bar ← service`, with the chain made as long as we
/// like. The receiver is pinned at the top, so with `k ≥ n` the placeholder
/// propagates the whole way and is resolved exactly once.
pub fn chain(n: usize, targets: usize) -> Program {
    let mut b = B::default();
    b.hierarchy(targets);
    b.critical_leaf();

    for i in 1..=n {
        let (me, below) = (format!("P{i}"), format!("P{}", i - 1));
        b.proc_(&me, &[&format!("this@{me}"), &format!("x@{me}"), &format!("obj@{me}")]);
        b.call(
            &format!("S{i}"),
            &me,
            &below,
            &[&format!("this@{me}"), &format!("x@{me}"), &format!("obj@{me}")],
            Some(&format!("r@{me}")),
        );
        b.ret(&me, &format!("r@{me}"));
    }

    b.proc_("Entry", &["this@Entry"]);
    b.alloc("E0", "Entry", "first", "lfirst", "Obj");
    b.alloc("E1", "Entry", "recv", "lrecv", "C0");
    b.call("E2", "Entry", &format!("P{n}"), &["this@Entry", "recv", "first"], Some("res"));
    b.entry("Entry");
    b.done()
}

/// One critical call with `t` CHA implementations, never pinned by a context:
/// the ⊤-summarization path. `chain(1, t)` with a small `k`.
pub fn targets(t: usize) -> Program {
    chain(1, t)
}

/// `m` distinct callers of one critical procedure, each pinning a different
/// receiver type: fan-in rather than depth.
pub fn fanin(m: usize, targets: usize) -> Program {
    let mut b = B::default();
    b.hierarchy(targets);
    b.critical_leaf();

    b.proc_("Entry", &["this@Entry"]);
    b.alloc("E0", "Entry", "first", "lfirst", "Obj");
    for i in 0..m {
        let bi = format!("B{i}");
        b.proc_(&bi, &[&format!("this@{bi}"), &format!("obj@{bi}")]);
        b.alloc(
            &format!("A@{bi}"),
            &bi,
            &format!("t@{bi}"),
            &format!("l@{bi}"),
            &format!("C{}", i % targets),
        );
        b.call(
            &format!("C@{bi}"),
            &bi,
            "P0",
            &[&format!("this@{bi}"), &format!("t@{bi}"), &format!("obj@{bi}")],
            Some(&format!("r@{bi}")),
        );
        b.ret(&bi, &format!("r@{bi}"));
        b.call(&format!("E@{i}"), "Entry", &bi, &["this@Entry", "first"], Some(&format!("res{i}")));
    }
    b.entry("Entry");
    b.done()
}

/// A chain of depth `d` in which every level calls the level below it from
/// *two* statements. The program grows linearly in `d`, but the number of call
/// strings of length `d` — and so the number of pending instances — doubles
/// per level. This is the k-CFA call-string explosion, and the k-limit is the
/// only thing standing between it and the analysis.
pub fn branching(d: usize, targets: usize) -> Program {
    let mut b = B::default();
    b.hierarchy(targets);
    b.critical_leaf();

    for i in 1..=d {
        let (me, below) = (format!("P{i}"), format!("P{}", i - 1));
        b.proc_(&me, &[&format!("this@{me}"), &format!("x@{me}"), &format!("obj@{me}")]);
        for side in ["a", "b"] {
            b.call(
                &format!("S{i}{side}"),
                &me,
                &below,
                &[&format!("this@{me}"), &format!("x@{me}"), &format!("obj@{me}")],
                Some(&format!("r{side}@{me}")),
            );
            b.ret(&me, &format!("r{side}@{me}"));
        }
    }

    b.proc_("Entry", &["this@Entry"]);
    b.alloc("E0", "Entry", "first", "lfirst", "Obj");
    b.alloc("E1", "Entry", "recv", "lrecv", "C0");
    b.call("E2", "Entry", &format!("P{d}"), &["this@Entry", "recv", "first"], Some("res"));
    b.entry("Entry");
    b.done()
}

/// No calls and no critical statements: `n` allocations merged into a chain of
/// `n` variables, so that `pt(c_i) = {l_0..l_i}`. Pure points-to pressure —
/// the classic |vars| × |allocs| product, with nothing of Hybrid Inlining in
/// the way.
pub fn alias(n: usize) -> Program {
    let mut b = B::default();
    b.proc_("M", &["this@M"]);
    for i in 0..n {
        b.alloc(&format!("A{i}"), "M", &format!("a{i}"), &format!("l{i}"), "Obj");
    }
    b.mov("M0", "M", "c0", "a0");
    for i in 1..n {
        b.mov(&format!("Mc{i}"), "M", &format!("c{i}"), &format!("c{}", i - 1));
        b.mov(&format!("Ma{i}"), "M", &format!("c{i}"), &format!("a{i}"));
    }
    b.ret("M", &format!("c{}", n.saturating_sub(1)));
    b.entry("M");
    b.done()
}

/// A chain of `n` *distinct* field loads off a parameter, all inside one
/// procedure: stresses the suffix-congruence rules and `used_ext`. Distinct
/// fields, because repeating one would let congruence extend a path by a
/// suffix it already carries and grow it without bound.
pub fn fields(n: usize) -> Program {
    let mut b = B::default();
    b.proc_("F", &["this@F", "x@F"]);
    b.mov("F0", "F", "y0", "x@F");
    for i in 1..=n {
        b.load_field(&format!("F{i}"), "F", &format!("y{i}"), &format!("y{}", i - 1), &format!("f{i}"));
    }
    b.ret("F", &format!("y{n}"));
    b.entry("F");
    b.done()
}

/// `P0(x) { return x.f0 }`, `Pi(x) { t = P_{i-1}(x); return t.fi }`. Every
/// summary is a single constraint, but its access path is one accessor longer
/// than the callee's — so this measures whether path *length* (as opposed to
/// tuple count) grows through inlining. It does: linearly in call depth, with
/// no limit of its own.
pub fn fields_chain(n: usize) -> Program {
    let mut b = B::default();
    b.proc_("P0", &["this@P0", "x@P0"]);
    b.load_field("S0", "P0", "y@P0", "x@P0", "f0");
    b.ret("P0", "y@P0");
    for i in 1..=n {
        let (me, below) = (format!("P{i}"), format!("P{}", i - 1));
        b.proc_(&me, &[&format!("this@{me}"), &format!("x@{me}")]);
        b.call(&format!("C{i}"), &me, &below, &[&format!("this@{me}"), &format!("x@{me}")], Some(&format!("t@{me}")));
        b.load_field(&format!("S{i}"), &me, &format!("y@{me}"), &format!("t@{me}"), &format!("f{i}"));
        b.ret(&me, &format!("y@{me}"));
    }
    b.proc_("Entry", &["this@Entry"]);
    b.alloc("E0", "Entry", "o", "lo", "Obj");
    b.call("E1", "Entry", &format!("P{n}"), &["this@Entry", "o"], Some("res"));
    b.entry("Entry");
    b.done()
}

/// A critical statement whose deciding operand has *no* reaching definition:
/// `x@V` is never assigned, so `pt(x@V)` is empty and the receiver of
/// `x.poly(obj)` is decided by nothing at all.
///
/// This is the vacuous corner of adequacy. `blocked` is a presence test, so an
/// empty points-to set makes the instance *un*blocked — not because the
/// context pinned it, but because there is nothing to pin. `V` has a caller,
/// so the instance could propagate; the point of the family is that
/// propagating it would only manufacture equally vacuous copies.
pub fn dead_receiver() -> Program {
    let mut b = B::default();
    b.hierarchy(2);
    b.proc_("V", &["this@V", "obj@V"]);
    // `x@V` is a local of `V` that no statement ever writes.
    b.vcall("S", "V", "x@V", "poly(Obj)", &["x@V", "obj@V"], "r@V");
    b.ret("V", "r@V");

    b.proc_("Entry", &["this@Entry"]);
    b.alloc("E0", "Entry", "o", "lo", "Obj");
    b.call("E1", "Entry", "V", &["this@Entry", "o"], Some("res"));
    b.entry("Entry");
    b.done()
}

/// `P(x) { y = x.f; return P(y) }`: direct recursion whose summary, inlined
/// into itself, would append `.f` on every round. The termination question for
/// the access-path domain, in its smallest form.
pub fn recursive_field() -> Program {
    let mut b = B::default();
    b.proc_("P", &["this@P", "x@P"]);
    b.load_field("S1", "P", "y@P", "x@P", "f");
    b.call("S2", "P", "P", &["this@P", "y@P"], Some("r@P"));
    b.ret("P", "r@P");
    b.proc_("Entry", &["this@Entry"]);
    b.alloc("E0", "Entry", "o", "lo", "Obj");
    b.call("E1", "Entry", "P", &["this@Entry", "o"], Some("res"));
    b.entry("Entry");
    b.done()
}

/// Many procedures, wide interprocedural data flow, **nothing critical**.
///
/// The families above each isolate one axis, and between them they leave a
/// gap: the shapes with many procedures ([`chain`], [`fanin`],
/// [`fields_chain`]) give each procedure a body of one or two statements, and
/// the shape with a real intraprocedural closure ([`alias`]) is a single
/// procedure with no calls at all. Nothing measures the ordinary case — a
/// program that is large because it has *many* procedures, each doing a
/// nontrivial amount of pointer flow, with dispatch essentially free.
///
/// `wide(m, w)` is that case: `m` leaf procedures, each an [`alias`]-style
/// merge of `w` allocations into `w` variables with the parameter seeded into
/// the chain, so every leaf has an `Θ(w²)` local `points` closure *and* a
/// summary its callers must inline. The leaves are grouped four at a time
/// under mid-level callers that merge their results, and `Entry` merges the
/// mids. No `virtual_call`, no `load_index_var`/`store_index_var`: there is
/// not one critical statement in the program, so `pending` stays empty and
/// `k` is irrelevant.
///
/// Depth is fixed at 3 while `m` grows, which is the point. The other
/// families grow the *length* of the dependency chain the fixpoint has to walk
/// (`alias(n)` needs `n` semi-naive rounds to push `l_0` to `c_n`); this one
/// grows its *width*, so each round has `Θ(m)` independent procedures to work
/// on. That is the shape most favourable to a parallel evaluator, and so the
/// honest test of whether parallelism can ever pay here.
pub fn wide(m: usize, w: usize) -> Program {
    const GROUP: usize = 4;
    let mut b = B::default();

    for i in 0..m {
        let wi = format!("W{i}");
        b.proc_(&wi, &[&format!("this@{wi}"), &format!("x@{wi}")]);
        for j in 0..w {
            b.alloc(&format!("A{j}@{wi}"), &wi, &format!("a{j}@{wi}"), &format!("l{j}@{wi}"), "Obj");
        }
        // The parameter seeds the merge chain, so the summary is `ret ⊇ par_1`
        // as well as `ret ⊇ {l_j}` — a caller inlining it gets real flow, not
        // just a set of allocation sites.
        b.mov(&format!("M0@{wi}"), &wi, &format!("c0@{wi}"), &format!("x@{wi}"));
        for j in 1..w {
            b.mov(&format!("Mc{j}@{wi}"), &wi, &format!("c{j}@{wi}"), &format!("c{}@{wi}", j - 1));
            b.mov(&format!("Ma{j}@{wi}"), &wi, &format!("c{j}@{wi}"), &format!("a{j}@{wi}"));
        }
        b.ret(&wi, &format!("c{}@{wi}", w.saturating_sub(1)));
    }

    let mids = m.div_ceil(GROUP);
    for j in 0..mids {
        let mj = format!("D{j}");
        b.proc_(&mj, &[&format!("this@{mj}"), &format!("x@{mj}")]);
        for i in (j * GROUP)..((j + 1) * GROUP).min(m) {
            b.call(
                &format!("C{i}@{mj}"),
                &mj,
                &format!("W{i}"),
                &[&format!("this@{mj}"), &format!("x@{mj}")],
                Some(&format!("r{i}@{mj}")),
            );
            b.mov(&format!("Mr{i}@{mj}"), &mj, &format!("acc@{mj}"), &format!("r{i}@{mj}"));
        }
        b.ret(&mj, &format!("acc@{mj}"));
    }

    b.proc_("Entry", &["this@Entry"]);
    b.alloc("E0", "Entry", "o", "lo", "Obj");
    for j in 0..mids {
        b.call(&format!("E@{j}"), "Entry", &format!("D{j}"), &["this@Entry", "o"], Some(&format!("r{j}")));
        b.mov(&format!("Em@{j}"), "Entry", "res", &format!("r{j}"));
    }
    b.entry("Entry");
    b.done()
}
