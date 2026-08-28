//! End-to-end tests for the Hybrid Inlining analysis.
//!
//! The headline acceptance test is Figure 1: the analysis must compute
//! `pt(second) = {l37} = pt(first)` and `pt(third) = {l14}` in `service()`,
//! and must *not* admit the spurious call edge `bar1 → … → Z.poly`.

use std::collections::{BTreeMap, BTreeSet};

use hybrid_inlining_paper::access_path::{
    AccessPath, Accessor, Base, Constraint, CritId, PtVal, Summary,
};
use hybrid_inlining_paper::analysis::{HybridAnalysis, run_hybrid};
use hybrid_inlining_paper::ir::*;
use hybrid_inlining_paper::{families, figure1, figure5};

fn p(x: &str) -> Proc {
    x.into()
}

/// `pt(v)` for a local of `p`, rendered for readable assertions.
fn pt(h: &HybridAnalysis, proc_: &str, v: &str) -> BTreeSet<String> {
    h.points_to(&p(proc_), Var::from(v))
        .iter()
        .map(ToString::to_string)
        .collect()
}

fn rendered(summaries: &BTreeMap<Proc, Summary>, proc_: &str) -> Vec<String> {
    summaries
        .get(&p(proc_))
        .map(|s| s.iter().map(ToString::to_string).collect())
        .unwrap_or_default()
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|s| s.to_string()).collect()
}

// =========================================================================
// Milestone 3: the monotone core, before any critical statement is involved
// =========================================================================

#[test]
fn id_publishes_exactly_figure_2b() {
    // `X id(X x) { X tv = x; return tv; }` — both locals eliminated.
    let h = run_hybrid(&figure1::program(), 4);
    assert_eq!(
        rendered(&h.summaries(), "FacadeImpl.id"),
        ["ret@FacadeImpl.id ⊇ par_1@FacadeImpl.id"]
    );
}

#[test]
fn published_summaries_never_mention_a_local() {
    let h = run_hybrid(&figure1::program(), 4);
    for (owner, summary) in h.summaries() {
        for constraint in &summary {
            for path in constraint.paths() {
                assert!(
                    path.base.is_symbolic(),
                    "local root in summary of {owner}: {constraint}"
                );
            }
        }
    }
}

// =========================================================================
// Milestone 4: the k = 0 baseline is the context-insensitive analysis
// =========================================================================

#[test]
fn k_zero_reproduces_figure_2_exactly() {
    // With no propagation allowed, every critical statement is
    // ⊤-summarized where it occurs — which is precisely what a
    // compositional, context-insensitive analysis does. The oracle is the
    // hand-written Figure 2 already in the repo.
    let h = run_hybrid(&figure1::program(), 0);
    assert_eq!(h.summaries(), figure1::figure2_summaries());
}

#[test]
fn k_zero_top_summarizes_the_critical_call_at_its_origin() {
    let h = run_hybrid(&figure1::program(), 0);
    let c0 = CritId::origin("L25");
    assert_eq!(
        h.callees_of(&p("FacadeImpl.foo"), &c0),
        BTreeSet::from([p("Y.poly"), p("Z.poly")]),
        "without context both implementations must be admitted"
    );
    // And nothing was deferred: the hybrid summary degenerates to a plain one.
    assert!(h.placeholders(&p("FacadeImpl.foo")).is_empty());
}

// =========================================================================
// Milestone 5: the full pipeline on Figure 1
// =========================================================================

/// The `L25` instance as it reaches each holder, per §5 of the plan.
fn c(chain: &[&str]) -> CritId {
    let mut id = CritId::origin("L25");
    for site in chain {
        id = id.push(&Stmt::from(*site));
    }
    id
}

#[test]
fn service_verifies_both_assertions() {
    let h = run_hybrid(&figure1::program(), 4);

    let first = pt(&h, "FacadeImpl.service", "first");
    let second = pt(&h, "FacadeImpl.service", "second");
    let third = pt(&h, "FacadeImpl.service", "third");

    assert_eq!(first, set(&["{l37}"]));
    assert_eq!(second, set(&["{l37}"]), "assert(first == second)");
    assert_eq!(third, set(&["{l14}"]), "assert(first != third)");
    assert!(first.is_disjoint(&third));
}

#[test]
fn foo_and_mid_defer_the_critical_call() {
    // Figure 3(a) and 3(b): the summary keeps the virtual call as a
    // placeholder wired to the operands it accesses, instead of inlining
    // both implementations under ⊤.
    let h = run_hybrid(&figure1::program(), 4);
    let summaries = h.summaries();

    assert_eq!(
        rendered(&summaries, "FacadeImpl.foo"),
        [
            "ret@FacadeImpl.foo ⊇ ⟨L25⟩:res",
            "⟨L25⟩:arg0 ⊇ par_1@FacadeImpl.foo",
            "⟨L25⟩:arg1 ⊇ par_2@FacadeImpl.foo",
        ]
    );
    assert_eq!(
        h.placeholders(&p("FacadeImpl.foo")),
        BTreeSet::from([c(&[])])
    );

    assert_eq!(
        rendered(&summaries, "FacadeImpl.mid"),
        [
            "ret@FacadeImpl.mid ⊇ ⟨L25@L28⟩:res",
            "⟨L25@L28⟩:arg0 ⊇ par_1@FacadeImpl.mid",
            "⟨L25@L28⟩:arg1 ⊇ par_2@FacadeImpl.mid",
        ]
    );
    assert_eq!(
        h.placeholders(&p("FacadeImpl.mid")),
        BTreeSet::from([c(&["L28"])])
    );
}

#[test]
fn bar1_and_bar2_match_figures_3c_and_3f() {
    // Once the receiver is pinned, the placeholder is resolved *precisely*
    // and disappears from the summary. This is the whole point: bar1 is the
    // identity, bar2 always returns l14.
    let h = run_hybrid(&figure1::program(), 4);
    let summaries = h.summaries();

    assert_eq!(
        rendered(&summaries, "FacadeImpl.bar1"),
        ["ret@FacadeImpl.bar1 ⊇ par_1@FacadeImpl.bar1"]
    );
    assert_eq!(
        rendered(&summaries, "FacadeImpl.bar2"),
        ["ret@FacadeImpl.bar2 ⊇ {l14}"]
    );
    assert!(h.placeholders(&p("FacadeImpl.bar1")).is_empty());
    assert!(h.placeholders(&p("FacadeImpl.bar2")).is_empty());
}

#[test]
fn the_spurious_call_edge_is_never_derived() {
    // The precision claim of Figure 1: no path from bar1 reaches Z.poly, and
    // none from bar2 reaches Y.poly.
    let h = run_hybrid(&figure1::program(), 4);

    assert_eq!(
        h.callees_of(&p("FacadeImpl.bar1"), &c(&["L28", "L31b"])),
        BTreeSet::from([p("Y.poly")])
    );
    assert_eq!(
        h.callees_of(&p("FacadeImpl.bar2"), &c(&["L28", "L34b"])),
        BTreeSet::from([p("Z.poly")])
    );

    for (holder, id, callee) in h.dispatches() {
        let via_bar1 =
            holder.as_ref() == "FacadeImpl.bar1" || id.chain.iter().any(|s| s.as_ref() == "L31b");
        assert!(
            !(via_bar1 && callee.as_ref() == "Z.poly"),
            "spurious edge {holder}: {id} → {callee}"
        );
    }
}

#[test]
fn the_receiver_is_what_blocks_propagation() {
    // foo and mid cannot decide the call: `pt(recv)` still contains a path
    // rooted at a parameter, i.e. `pt(recv) ∩ free(𝔞) ≠ ∅`. bar1 can.
    let h = run_hybrid(&figure1::program(), 4);
    let blocked: BTreeSet<(String, String)> = h
        .blocked
        .iter()
        .map(|(q, id)| (q.to_string(), id.to_string()))
        .collect();

    assert!(blocked.contains(&("FacadeImpl.foo".into(), "⟨L25⟩".into())));
    assert!(blocked.contains(&("FacadeImpl.mid".into(), "⟨L25@L28⟩".into())));
    assert!(
        !blocked
            .iter()
            .any(|(q, _)| q == "FacadeImpl.bar1" || q == "FacadeImpl.bar2")
    );
}

#[test]
fn resolution_happens_inside_the_one_fixpoint() {
    // There is no driver: `resolve` is ordinary IDB, derived in the same
    // stratum as the `points` fixpoint it reads and feeds. So the callee's
    // summary must already be inlined at the placeholder in the very model
    // `resolve` was derived in — one `run()`, no replay.
    let h = run_hybrid(&figure1::program(), 4);
    let c2 = c(&["L28", "L31b"]);

    assert!(
        h.resolve
            .contains(&(p("FacadeImpl.bar1"), c2.clone(), p("Y.poly")))
    );
    // σ_crit put `ret@Y.poly ⊇ par_1@Y.poly` onto the placeholder ...
    assert!(h.edge.contains(&(
        p("FacadeImpl.bar1"),
        AccessPath::crit_ret(c2.clone()),
        AccessPath::crit_slot(c2.clone(), 1),
    )));
    // ... and the result reached bar1's published summary in the same run.
    assert_eq!(
        rendered(&h.summaries(), "FacadeImpl.bar1"),
        ["ret@FacadeImpl.bar1 ⊇ par_1@FacadeImpl.bar1"]
    );
}

#[test]
fn a_tight_k_limit_still_gets_the_right_answer() {
    // bar1/bar2 resolve at call-string depth 2, so k = 2 suffices; the
    // duplicated depth-3 instances the plan notes at `service` simply never
    // come into existence. Theorem 3.3: resolving early is no less precise.
    let h = run_hybrid(&figure1::program(), 2);
    assert_eq!(pt(&h, "FacadeImpl.service", "second"), set(&["{l37}"]));
    assert_eq!(pt(&h, "FacadeImpl.service", "third"), set(&["{l14}"]));
    assert_eq!(h.dispatches().len(), 2, "no depth-3 duplicates at k = 2");
}

// =========================================================================
// N1: a virtual call with a single CHA target is not critical
// =========================================================================

#[test]
fn a_monomorphic_virtual_call_is_devirtualized_not_deferred() {
    // Same shape as Figure 1's foo, but the interface has one implementor,
    // so `|dispatch(⊤, proc)| = 1` and the site is an ordinary direct call.
    let mut prog = Program::default();
    prog.procedure = vec![(p("Y.poly"),), (p("caller"),)];
    prog.entry = vec![(p("caller"),)];
    prog.lookup = vec![(Type::from("Y"), Sig::from("poly(Obj)"), p("Y.poly"))];

    prog.formal = vec![
        (p("Y.poly"), 0, Var::from("this@Y.poly")),
        (p("Y.poly"), 1, Var::from("obj@Y.poly")),
        (p("caller"), 0, Var::from("this@caller")),
        (p("caller"), 1, Var::from("recv")),
        (p("caller"), 2, Var::from("arg")),
    ];
    prog.ret = vec![
        (p("Y.poly"), Var::from("obj@Y.poly")),
        (p("caller"), Var::from("r")),
    ];
    prog.in_proc = vec![(Stmt::from("C1"), p("caller"), 0)];
    prog.virtual_call = vec![(Stmt::from("C1"), Var::from("recv"), Sig::from("poly(Obj)"))];
    prog.actual_arg = vec![
        (Stmt::from("C1"), 0, Var::from("recv")),
        (Stmt::from("C1"), 1, Var::from("arg")),
    ];
    prog.bind_ret = vec![(Stmt::from("C1"), Var::from("r"))];

    let h = run_hybrid(&prog, 4);
    assert!(h.critical.is_empty(), "single-target site is not critical");
    assert_eq!(h.eff_direct.len(), 1, "it is an effectively direct call");
    assert!(h.placeholders(&p("caller")).is_empty());
    assert_eq!(
        rendered(&h.summaries(), "caller"),
        ["ret@caller ⊇ par_2@caller"],
        "the callee was inlined outright"
    );
}

// =========================================================================
// Recursion: the k-limit is what bounds pending call strings
// =========================================================================

/// A recursive identity, with no critical statement in sight:
/// `Obj rid(Obj x) { if (..) return x; Obj t = rid(x); return t; }`.
///
/// The summary of `rid` is defined by a cycle through `rid`'s own published
/// summary. Nothing special is needed for that: S2 is monotone, so the
/// Ascent fixpoint handles recursive summaries natively.
#[test]
fn a_recursive_summary_is_just_a_fixpoint() {
    let mut prog = Program::default();
    prog.procedure = vec![(p("rid"),)];
    prog.entry = vec![(p("rid"),)];
    prog.formal = vec![(p("rid"), 0, Var::from("x"))];
    prog.ret = vec![(p("rid"), Var::from("x")), (p("rid"), Var::from("t"))];
    prog.in_proc = vec![(Stmt::from("D1"), p("rid"), 0)];
    prog.direct_call = vec![(Stmt::from("D1"), p("rid"))];
    prog.actual_arg = vec![(Stmt::from("D1"), 0, Var::from("x"))];
    prog.bind_ret = vec![(Stmt::from("D1"), Var::from("t"))];

    let h = run_hybrid(&prog, 4);
    assert_eq!(rendered(&h.summaries(), "rid"), ["ret@rid ⊇ par_0@rid"]);
    assert!(
        h.pending.is_empty(),
        "no critical statements, so nothing to defer"
    );
}

/// ```text
/// Obj rec(X x, Obj o) {
///   R0:  if (..) return o;          // base case
///   R1:  Obj t = rec(x, o);
///   R2:  Obj r = x.poly(t);         // critical
///   R3:  return r;
/// }
/// main() { y = new Y(); o = new Obj(); res = rec(y, o); }
/// ```
///
/// The receiver of the critical call is `rec`'s own parameter, so the pending
/// instance is blocked at every depth and the recursive call at `R1` grows its
/// call string without bound. Only the k-limit stops it.
fn recursive_program() -> Program {
    let mut prog = Program::default();
    prog.procedure = vec![(p("Y.poly"),), (p("Z.poly"),), (p("rec"),), (p("main"),)];
    prog.entry = vec![(p("main"),)];
    prog.lookup = vec![
        (Type::from("Y"), Sig::from("poly(Obj)"), p("Y.poly")),
        (Type::from("Z"), Sig::from("poly(Obj)"), p("Z.poly")),
    ];
    prog.alloc_type = vec![
        (Alloc::from("ly"), Type::from("Y")),
        (Alloc::from("lo"), Type::from("Obj")),
        (Alloc::from("l14"), Type::from("Obj")),
    ];

    prog.formal = vec![
        (p("Y.poly"), 0, Var::from("this@Y")),
        (p("Y.poly"), 1, Var::from("obj@Y")),
        (p("Z.poly"), 0, Var::from("this@Z")),
        (p("Z.poly"), 1, Var::from("obj@Z")),
        (p("rec"), 0, Var::from("x@rec")),
        (p("rec"), 1, Var::from("o@rec")),
        (p("main"), 0, Var::from("this@main")),
    ];
    prog.ret = vec![
        (p("Y.poly"), Var::from("obj@Y")),
        (p("Z.poly"), Var::from("z14")),
        (p("rec"), Var::from("o@rec")), // the base case
        (p("rec"), Var::from("r")),
    ];

    prog.in_proc = vec![
        (Stmt::from("Z1"), p("Z.poly"), 0),
        (Stmt::from("R1"), p("rec"), 0),
        (Stmt::from("R2"), p("rec"), 1),
        (Stmt::from("M1"), p("main"), 0),
        (Stmt::from("M2"), p("main"), 1),
        (Stmt::from("M3"), p("main"), 2),
    ];
    prog.alloc = vec![
        (Stmt::from("Z1"), Var::from("z14"), Alloc::from("l14")),
        (Stmt::from("M1"), Var::from("y"), Alloc::from("ly")),
        (Stmt::from("M2"), Var::from("o"), Alloc::from("lo")),
    ];

    prog.direct_call = vec![(Stmt::from("R1"), p("rec")), (Stmt::from("M3"), p("rec"))];
    prog.virtual_call = vec![(Stmt::from("R2"), Var::from("x@rec"), Sig::from("poly(Obj)"))];
    prog.actual_arg = vec![
        (Stmt::from("R1"), 0, Var::from("x@rec")),
        (Stmt::from("R1"), 1, Var::from("o@rec")),
        (Stmt::from("R2"), 0, Var::from("x@rec")),
        (Stmt::from("R2"), 1, Var::from("t")),
        (Stmt::from("M3"), 0, Var::from("y")),
        (Stmt::from("M3"), 1, Var::from("o")),
    ];
    prog.bind_ret = vec![
        (Stmt::from("R1"), Var::from("t")),
        (Stmt::from("R2"), Var::from("r")),
        (Stmt::from("M3"), Var::from("res")),
    ];
    prog
}

#[test]
fn the_k_limit_bounds_the_call_strings_of_a_recursive_program() {
    // Termination is the claim under test: without the k-limit, `R1` would
    // push a new callsite onto the same instance forever.
    for k in 0..=4 {
        let h = run_hybrid(&recursive_program(), k);
        for (_, id) in &h.pending {
            assert!(id.depth() <= k, "k = {k} but {id} has depth {}", id.depth());
        }
        assert!(
            h.pending.iter().any(|(_, id)| id.depth() == k),
            "k = {k}: the recursion should reach the limit"
        );
        // Sound at every k: `o` reaches the result via the base case.
        assert!(pt(&h, "main", "res").contains("{lo}"));
    }
}

#[test]
fn a_receiver_the_recursion_never_pins_falls_back_to_top() {
    // `rec`'s receiver is its own parameter, so the instance is blocked at
    // every depth of the recursion. The deepest one can neither be resolved
    // nor propagated, so it must be ⊤-summarized — which admits Z.poly and
    // leaks `l14` into the answer. This is the documented cost of the
    // k-limit inside recursion, not a bug: dropping the instance instead
    // would be unsound.
    let h = run_hybrid(&recursive_program(), 3);

    let reached: BTreeSet<String> = h
        .dispatches()
        .iter()
        .map(|(_, _, callee)| callee.to_string())
        .collect();
    assert!(reached.contains("Y.poly"));
    assert!(
        reached.contains("Z.poly"),
        "the k-limit forces ⊤ inside rec"
    );
    assert_eq!(pt(&h, "main", "res"), set(&["{l14}", "{lo}"]));

    // The instance `main` holds, by contrast, *is* pinned: `y = new Y()`.
    let at_main: BTreeSet<String> = h
        .dispatches()
        .iter()
        .filter(|(holder, ..)| holder.as_ref() == "main")
        .map(|(_, _, callee)| callee.to_string())
        .collect();
    assert_eq!(at_main, set(&["Y.poly"]));
}

// =========================================================================
// Field and constant-index constraints (Figure 4 definitions 6-8)
// =========================================================================

/// `Obj through(Obj a, Obj x) { Obj b = a; a.f = x; return b.f; }` — reading
/// the result back through an *alias* of the base needs suffix congruence,
/// `b ⊇ a ⟹ b.f ⊇ a.f`.
#[test]
fn suffix_congruence_carries_a_store_through_an_alias() {
    let mut prog = Program::default();
    prog.procedure = vec![(p("through"),)];
    prog.entry = vec![(p("through"),)];
    prog.formal = vec![
        (p("through"), 0, Var::from("this")),
        (p("through"), 1, Var::from("a")),
        (p("through"), 2, Var::from("x")),
    ];
    prog.ret = vec![(p("through"), Var::from("y"))];
    prog.in_proc = vec![
        (Stmt::from("F1"), p("through"), 0),
        (Stmt::from("F2"), p("through"), 1),
        (Stmt::from("F3"), p("through"), 2),
    ];
    prog.mov = vec![(Stmt::from("F1"), Var::from("b"), Var::from("a"))];
    prog.store_field = vec![(
        Stmt::from("F2"),
        Var::from("a"),
        Field::from("f"),
        Var::from("x"),
    )];
    prog.load_field = vec![(
        Stmt::from("F3"),
        Var::from("y"),
        Var::from("b"),
        Field::from("f"),
    )];

    // Weak updates: after `a.f = x` the field may still hold whatever the
    // caller left in it, so the summary names both sources.
    let h = run_hybrid(&prog, 4);
    assert_eq!(
        rendered(&h.summaries(), "through"),
        [
            "ret@through ⊇ par_1@through.f",
            "ret@through ⊇ par_2@through"
        ],
    );
}

#[test]
fn a_constant_index_behaves_like_a_field() {
    let mut prog = Program::default();
    prog.procedure = vec![(p("cell"),)];
    prog.entry = vec![(p("cell"),)];
    prog.formal = vec![
        (p("cell"), 0, Var::from("this")),
        (p("cell"), 1, Var::from("arr")),
        (p("cell"), 2, Var::from("x")),
    ];
    prog.ret = vec![(p("cell"), Var::from("y"))];
    prog.in_proc = vec![
        (Stmt::from("I1"), p("cell"), 0),
        (Stmt::from("I2"), p("cell"), 1),
    ];
    prog.store_index_const = vec![(
        Stmt::from("I1"),
        Var::from("arr"),
        Const::from("0"),
        Var::from("x"),
    )];
    prog.load_index_const = vec![(
        Stmt::from("I2"),
        Var::from("y"),
        Var::from("arr"),
        Const::from("0"),
    )];

    let h = run_hybrid(&prog, 4);
    assert_eq!(
        rendered(&h.summaries(), "cell"),
        ["ret@cell ⊇ par_1@cell[0]", "ret@cell ⊇ par_2@cell"],
    );

    // The path the value took really is `par_1@cell[0]`, not a bare root.
    let indexed = AccessPath::param("cell", 1).index("0");
    assert!(h.points.iter().any(|(q, w, v)| q == &p("cell")
        && w == &AccessPath::var("y")
        && v == &PtVal::Path(indexed.clone())));
    assert_eq!(indexed.to_string(), "par_1@cell[0]");
}

// =========================================================================
// The published summaries really are set constraints
// =========================================================================

#[test]
fn every_published_constraint_is_well_formed() {
    let h = run_hybrid(&figure1::program(), 4);
    let prog = figure1::program();
    let sites: BTreeSet<&Alloc> = prog.alloc.iter().map(|(_, _, l)| l).collect();

    for (owner, summary) in h.summaries() {
        assert!(
            prog.procedure.iter().any(|(q,)| *q == owner),
            "summary for unknown proc {owner}"
        );
        for constraint in &summary {
            if let Constraint::Alloc { sub, .. } = constraint {
                assert!(sites.contains(sub), "unknown allocation site {sub}");
            }
        }
    }
}

// =========================================================================
// Milestone 7: `lv[v]` criticals and N4 — Figure 5, reproducing Figure 6
// =========================================================================

#[test]
fn getp_and_setp_defer_their_map_access() {
    // Figure 6(a): the critical statement is a node of the constraint graph,
    // connected to `map`, `key` and `ret`. It cannot be summarized, because
    // `pt(key)` contains the free variable `par_2@getP`.
    let h = run_hybrid(&figure5::program(), 4);
    let summaries = h.summaries();

    assert_eq!(
        rendered(&summaries, "getP"),
        [
            "ret@getP ⊇ ⟨L2⟩:res",
            "⟨L2⟩:arg0 ⊇ par_1@getP",
            "⟨L2⟩:arg1 ⊇ par_2@getP",
        ]
    );
    assert_eq!(
        rendered(&summaries, "setP"),
        [
            "⟨L5⟩:arg0 ⊇ par_1@setP",
            "⟨L5⟩:arg1 ⊇ par_2@setP",
            "⟨L5⟩:arg2 ⊇ par_3@setP",
        ]
    );
    assert_eq!(
        h.placeholders(&p("getP")),
        BTreeSet::from([CritId::origin("L2")])
    );
    assert_eq!(
        h.placeholders(&p("setP")),
        BTreeSet::from([CritId::origin("L5")])
    );

    // Both are blocked on the *index*, not the base — that is N4's decisive
    // operand, and it is what §4.1.3 intersects against `free(𝔞)`.
    let blocked: BTreeSet<String> = h
        .blocked
        .iter()
        .map(|(q, id)| format!("{q}: {id}"))
        .collect();
    assert!(blocked.contains("getP: ⟨L2⟩"));
    assert!(blocked.contains("setP: ⟨L5⟩"));
}

#[test]
fn build_is_index_and_context_sensitive() {
    // Figure 6(d). Once `build` supplies the constants, both accesses resolve
    // to concrete accessors and the summary relates `par_1@build["cur"]` to
    // `ret@build["old"]` — the precise, index-sensitive answer.
    let h = run_hybrid(&figure5::program(), 4);

    assert_eq!(
        rendered(&h.summaries(), "build"),
        [
            "ret@build[\"old\"] ⊇ par_1@build[\"cur\"]",
            "ret@build ⊇ {l8}",
        ]
    );
    assert!(h.placeholders(&p("build")).is_empty());

    assert_eq!(
        h.accessors_of(&p("build"), &CritId::origin("L2").push(&Stmt::from("L9b"))),
        BTreeSet::from([Accessor::Index(Const::from("\"cur\""))])
    );
    assert_eq!(
        h.accessors_of(&p("build"), &CritId::origin("L5").push(&Stmt::from("L9d"))),
        BTreeSet::from([Accessor::Index(Const::from("\"old\""))])
    );
}

#[test]
fn k_zero_loses_index_sensitivity_to_pi() {
    // The contrast the paper draws: with no propagation, `key` is never
    // pinned, so Definition (5) of Figure 4 falls back to the undecidable
    // index `[π]` and every map slot is merged.
    let h = run_hybrid(&figure5::program(), 0);

    assert_eq!(
        rendered(&h.summaries(), "getP"),
        ["ret@getP ⊇ par_1@getP[π]"]
    );
    assert_eq!(
        rendered(&h.summaries(), "build"),
        ["ret@build[π] ⊇ par_1@build[π]", "ret@build ⊇ {l8}"]
    );
    assert!(
        h.index_acc
            .iter()
            .all(|(_, _, acc)| *acc == Accessor::IndexUnknown)
    );
}

#[test]
fn an_index_that_is_not_a_constant_is_undecidable() {
    // N4 proper: the context *is* adequate — nothing free reaches the index —
    // but `pt(key)` holds an allocation site rather than constants, so the
    // index still cannot be decided and `[π]` is used.
    let mut prog = figure5::program();
    prog.const_assign.retain(|(s, ..)| s.as_ref() != "L9a");
    prog.alloc
        .push((Stmt::from("L9a"), Var::from("c_cur"), Alloc::from("lk")));
    prog.alloc_type.push((Alloc::from("lk"), Type::from("Obj")));

    let get = CritId::origin("L2").push(&Stmt::from("L9b"));
    let h = run_hybrid(&prog, 4);

    // Adequacy is no longer a gate, so both classifications stay readable in
    // the finished model rather than only in the round that discovered them.
    assert!(
        h.adequate.contains(&(p("build"), get.clone())),
        "no free variable reaches the index, so the context is adequate"
    );
    assert!(
        h.index_undecidable.contains(&(p("build"), get.clone())),
        "but the index is an allocation site, so it still cannot be pinned"
    );

    assert_eq!(
        h.accessors_of(&p("build"), &get),
        BTreeSet::from([Accessor::IndexUnknown])
    );

    // The write still resolves precisely: `"old"` is untouched.
    assert_eq!(
        h.accessors_of(&p("build"), &CritId::origin("L5").push(&Stmt::from("L9d"))),
        BTreeSet::from([Accessor::Index(Const::from("\"old\""))])
    );
}

// =========================================================================
// The EDB schema is shared; the facts still have to be copied
// =========================================================================

/// `include_source!` guarantees `Program` and `HybridAnalysis` *declare* the
/// same relations, but [`HybridAnalysis::for_program`] still copies the facts
/// one relation at a time, and a forgotten line would leave one silently
/// empty. So: build a program in which every EDB relation holds a tuple, and
/// check every one of them survives the copy.
///
/// The facts are nonsense — this program is never run, only copied.
#[test]
fn every_edb_relation_is_copied_into_the_analysis() {
    let mut prog = Program::default();

    prog.procedure = vec![(p("q"),)];
    prog.proc_type = vec![(p("q"), Type::from("T"))];
    prog.proc_sig = vec![(p("q"), Sig::from("g"))];
    prog.entry = vec![(p("q"),)];
    prog.in_proc = vec![(Stmt::from("s"), p("q"), 0)];
    prog.alloc = vec![(Stmt::from("s"), Var::from("x"), Alloc::from("l"))];
    prog.alloc_type = vec![(Alloc::from("l"), Type::from("T"))];
    prog.const_assign = vec![(Stmt::from("s"), Var::from("x"), Const::from("c"))];
    prog.mov = vec![(Stmt::from("s"), Var::from("x"), Var::from("y"))];
    prog.load_field = vec![(
        Stmt::from("s"),
        Var::from("x"),
        Var::from("y"),
        Field::from("f"),
    )];
    prog.store_field = vec![(
        Stmt::from("s"),
        Var::from("x"),
        Field::from("f"),
        Var::from("y"),
    )];
    prog.load_static = vec![(
        Stmt::from("s"),
        Var::from("x"),
        Type::from("T"),
        Field::from("f"),
    )];
    prog.store_static = vec![(
        Stmt::from("s"),
        Type::from("T"),
        Field::from("f"),
        Var::from("y"),
    )];
    prog.load_index_const = vec![(
        Stmt::from("s"),
        Var::from("x"),
        Var::from("y"),
        Const::from("c"),
    )];
    prog.store_index_const = vec![(
        Stmt::from("s"),
        Var::from("x"),
        Const::from("c"),
        Var::from("y"),
    )];
    prog.load_index_var = vec![(
        Stmt::from("s"),
        Var::from("x"),
        Var::from("y"),
        Var::from("i"),
    )];
    prog.store_index_var = vec![(
        Stmt::from("s"),
        Var::from("x"),
        Var::from("i"),
        Var::from("y"),
    )];
    prog.direct_call = vec![(Stmt::from("s"), p("q"))];
    prog.virtual_call = vec![(Stmt::from("s"), Var::from("x"), Sig::from("g"))];
    prog.actual_arg = vec![(Stmt::from("s"), 0, Var::from("x"))];
    prog.bind_ret = vec![(Stmt::from("s"), Var::from("x"))];
    prog.formal = vec![(p("q"), 0, Var::from("x"))];
    prog.ret = vec![(p("q"), Var::from("x"))];
    prog.direct_subtype = vec![(Type::from("T"), Type::from("U"))];
    prog.lookup = vec![(Type::from("T"), Sig::from("g"), p("q"))];

    fn sizes(summary: &str) -> BTreeMap<&str, usize> {
        summary
            .lines()
            .filter_map(|line| line.split_once(" size: "))
            .map(|(name, n)| (name.trim(), n.trim().parse().unwrap()))
            .collect()
    }

    let analysis = HybridAnalysis::for_program(&prog, 4);
    let (declared, copied) = (
        prog.relation_sizes_summary(),
        analysis.relation_sizes_summary(),
    );
    let (declared, copied) = (sizes(&declared), sizes(&copied));

    assert_eq!(
        declared.len(),
        25,
        "the edb schema changed; update this test"
    );
    for (name, n) in &declared {
        assert_eq!(
            copied.get(name),
            Some(n),
            "{name} is in the shared schema but HybridAnalysis::for_program does not copy it"
        );
    }
}

// =========================================================================
// Chained criticals: what the single fixpoint buys, and where it still pays
// =========================================================================

/// ```text
/// main() {                       // entry, and nothing calls it
///   M1: g   = new P();
///   M2: r   = g.get();           // critical A: get() has two CHA targets
///   M3: o   = new Obj();
///   M4: res = r.poly(o);         // critical B: its receiver *is* A's result
/// }
/// P.get()  { return new Y(); }   Q.get()  { return new Z(); }
/// Y.poly(o){ return o; }         Z.poly(o){ return new Obj(); }  // l14
/// ```
///
/// Both instances are stuck at `main`, and B's receiver is fed by A's
/// placeholder. The round-based analysis had to treat that placeholder as
/// part of `free(𝔞)` — "unresolved" was a state, and A was unresolved in the
/// round B was classified in — so B was blocked, then forced, and admitted
/// *both* `poly` implementations.
///
/// In one fixpoint there is no such state. A is stuck, so it will be decided
/// here from values that are already in `main`; its placeholder is therefore
/// not free. A pins `P.get`, `P.get`'s `new Y()` flows through the
/// placeholder into B's receiver, and B dispatches on what actually arrives.
#[test]
fn a_chained_critical_resolves_from_what_actually_flows() {
    let mut prog = Program::default();
    prog.procedure = [
        (p("P.get"),),
        (p("Q.get"),),
        (p("Y.poly"),),
        (p("Z.poly"),),
        (p("main"),),
    ]
    .to_vec();
    prog.entry = vec![(p("main"),)];
    prog.lookup = vec![
        (Type::from("P"), Sig::from("get()"), p("P.get")),
        (Type::from("Q"), Sig::from("get()"), p("Q.get")),
        (Type::from("Y"), Sig::from("poly(Obj)"), p("Y.poly")),
        (Type::from("Z"), Sig::from("poly(Obj)"), p("Z.poly")),
    ];
    prog.alloc_type = vec![
        (Alloc::from("lp"), Type::from("P")),
        (Alloc::from("ly"), Type::from("Y")),
        (Alloc::from("lz"), Type::from("Z")),
        (Alloc::from("lo"), Type::from("Obj")),
        (Alloc::from("l14"), Type::from("Obj")),
    ];

    prog.formal = vec![
        (p("P.get"), 0, Var::from("this@P")),
        (p("Q.get"), 0, Var::from("this@Q")),
        (p("Y.poly"), 0, Var::from("this@Y")),
        (p("Y.poly"), 1, Var::from("obj@Y")),
        (p("Z.poly"), 0, Var::from("this@Z")),
        (p("Z.poly"), 1, Var::from("obj@Z")),
        (p("main"), 0, Var::from("this@main")),
    ];
    prog.ret = vec![
        (p("P.get"), Var::from("gy")),
        (p("Q.get"), Var::from("gz")),
        (p("Y.poly"), Var::from("obj@Y")),
        (p("Z.poly"), Var::from("z14")),
    ];
    prog.in_proc = vec![
        (Stmt::from("G1"), p("P.get"), 0),
        (Stmt::from("G2"), p("Q.get"), 0),
        (Stmt::from("Z1"), p("Z.poly"), 0),
        (Stmt::from("M1"), p("main"), 0),
        (Stmt::from("M2"), p("main"), 1),
        (Stmt::from("M3"), p("main"), 2),
        (Stmt::from("M4"), p("main"), 3),
    ];
    prog.alloc = vec![
        (Stmt::from("G1"), Var::from("gy"), Alloc::from("ly")),
        (Stmt::from("G2"), Var::from("gz"), Alloc::from("lz")),
        (Stmt::from("Z1"), Var::from("z14"), Alloc::from("l14")),
        (Stmt::from("M1"), Var::from("g"), Alloc::from("lp")),
        (Stmt::from("M3"), Var::from("o"), Alloc::from("lo")),
    ];
    prog.virtual_call = vec![
        (Stmt::from("M2"), Var::from("g"), Sig::from("get()")),
        (Stmt::from("M4"), Var::from("r"), Sig::from("poly(Obj)")),
    ];
    prog.actual_arg = vec![
        (Stmt::from("M2"), 0, Var::from("g")),
        (Stmt::from("M4"), 0, Var::from("r")),
        (Stmt::from("M4"), 1, Var::from("o")),
    ];
    prog.bind_ret = vec![
        (Stmt::from("M2"), Var::from("r")),
        (Stmt::from("M4"), Var::from("res")),
    ];

    let h = run_hybrid(&prog, 4);
    let a = CritId::origin("M2");
    let b = CritId::origin("M4");

    assert_eq!(h.callees_of(&p("main"), &a), BTreeSet::from([p("P.get")]));
    assert_eq!(
        h.callees_of(&p("main"), &b),
        BTreeSet::from([p("Y.poly")]),
        "the feeder is stuck here too, so it is not free: no ⊤ fallback"
    );
    // And so `Z.poly`'s l14 never enters the answer.
    assert_eq!(pt(&h, "main", "res"), set(&["{lo}"]));
}

/// The one corner §10.3 keeps conservative: a critical statement at the
/// k-limit whose receiver is fed by another critical statement that is *not*
/// at the limit.
///
/// ```text
/// main()          { M1: y = new P(); M2: res = mid(y); }   // entry
/// mid(g)          { A: a = g.get();  N: t = helper(a); return t; }
/// helper(z)       { H1: ho = new Obj(); B: b = z.poly(ho); return b; }
/// ```
///
/// At `k = 1` the `B` instance reaches `mid` at depth 1 and can go no
/// further, while `A` originates in `mid` at depth 0 and still can. `A`'s
/// resolution will therefore happen in `main`, a holder `B` never reaches, so
/// `B` cannot wait for it: `A`'s placeholder counts as free, `B` is blocked,
/// and — being stuck — it must ⊤-summarize. Raising the limit to `k = 2`
/// lets both travel together and the imprecision disappears.
#[test]
fn a_feeder_that_outlives_the_k_limit_forces_top() {
    let mut prog = Program::default();
    prog.procedure = [
        (p("P.get"),),
        (p("Q.get"),),
        (p("Y.poly"),),
        (p("Z.poly"),),
        (p("helper"),),
        (p("mid"),),
        (p("main"),),
    ]
    .to_vec();
    prog.entry = vec![(p("main"),)];
    prog.lookup = vec![
        (Type::from("P"), Sig::from("get()"), p("P.get")),
        (Type::from("Q"), Sig::from("get()"), p("Q.get")),
        (Type::from("Y"), Sig::from("poly(Obj)"), p("Y.poly")),
        (Type::from("Z"), Sig::from("poly(Obj)"), p("Z.poly")),
    ];
    prog.alloc_type = vec![
        (Alloc::from("lp"), Type::from("P")),
        (Alloc::from("ly"), Type::from("Y")),
        (Alloc::from("lz"), Type::from("Z")),
        (Alloc::from("lho"), Type::from("Obj")),
        (Alloc::from("l14"), Type::from("Obj")),
    ];

    prog.formal = vec![
        (p("P.get"), 0, Var::from("this@P")),
        (p("Q.get"), 0, Var::from("this@Q")),
        (p("Y.poly"), 0, Var::from("this@Y")),
        (p("Y.poly"), 1, Var::from("obj@Y")),
        (p("Z.poly"), 0, Var::from("this@Z")),
        (p("Z.poly"), 1, Var::from("obj@Z")),
        (p("helper"), 0, Var::from("this@helper")),
        (p("helper"), 1, Var::from("z@helper")),
        (p("mid"), 0, Var::from("this@mid")),
        (p("mid"), 1, Var::from("g@mid")),
        (p("main"), 0, Var::from("this@main")),
    ];
    prog.ret = vec![
        (p("P.get"), Var::from("gy")),
        (p("Q.get"), Var::from("gz")),
        (p("Y.poly"), Var::from("obj@Y")),
        (p("Z.poly"), Var::from("z14")),
        (p("helper"), Var::from("b")),
        (p("mid"), Var::from("t")),
    ];
    prog.in_proc = vec![
        (Stmt::from("G1"), p("P.get"), 0),
        (Stmt::from("G2"), p("Q.get"), 0),
        (Stmt::from("Z1"), p("Z.poly"), 0),
        (Stmt::from("H1"), p("helper"), 0),
        (Stmt::from("B"), p("helper"), 1),
        (Stmt::from("A"), p("mid"), 0),
        (Stmt::from("N"), p("mid"), 1),
        (Stmt::from("M1"), p("main"), 0),
        (Stmt::from("M2"), p("main"), 1),
    ];
    prog.alloc = vec![
        (Stmt::from("G1"), Var::from("gy"), Alloc::from("ly")),
        (Stmt::from("G2"), Var::from("gz"), Alloc::from("lz")),
        (Stmt::from("Z1"), Var::from("z14"), Alloc::from("l14")),
        (Stmt::from("H1"), Var::from("ho"), Alloc::from("lho")),
        (Stmt::from("M1"), Var::from("y"), Alloc::from("lp")),
    ];
    prog.virtual_call = vec![
        (
            Stmt::from("B"),
            Var::from("z@helper"),
            Sig::from("poly(Obj)"),
        ),
        (Stmt::from("A"), Var::from("g@mid"), Sig::from("get()")),
    ];
    prog.direct_call = vec![(Stmt::from("N"), p("helper")), (Stmt::from("M2"), p("mid"))];
    prog.actual_arg = vec![
        (Stmt::from("B"), 0, Var::from("z@helper")),
        (Stmt::from("B"), 1, Var::from("ho")),
        (Stmt::from("A"), 0, Var::from("g@mid")),
        (Stmt::from("N"), 0, Var::from("this@mid")),
        (Stmt::from("N"), 1, Var::from("a")),
        (Stmt::from("M2"), 0, Var::from("this@main")),
        (Stmt::from("M2"), 1, Var::from("y")),
    ];
    prog.bind_ret = vec![
        (Stmt::from("B"), Var::from("b")),
        (Stmt::from("A"), Var::from("a")),
        (Stmt::from("N"), Var::from("t")),
        (Stmt::from("M2"), Var::from("res")),
    ];

    // k = 1: B is at the limit in `mid` while its feeder A is not, so B has
    // to give up and take every CHA target.
    let tight = run_hybrid(&prog, 1);
    let b_at_mid = CritId::origin("B").push(&Stmt::from("N"));
    assert_eq!(
        tight.callees_of(&p("mid"), &b_at_mid),
        BTreeSet::from([p("Y.poly"), p("Z.poly")]),
        "the depth mismatch is the one place §10.3 stays conservative"
    );
    assert!(tight.top.contains(&(p("mid"), b_at_mid.clone())));
    // A itself still travels to `main` and is pinned there.
    assert_eq!(
        tight.callees_of(&p("main"), &CritId::origin("A").push(&Stmt::from("M2"))),
        BTreeSet::from([p("P.get")])
    );
    assert_eq!(pt(&tight, "main", "res"), set(&["{l14}", "{lho}"]));

    // k = 2: both instances reach `main` together, A pins the receiver, and
    // Z.poly is never admitted.
    let loose = run_hybrid(&prog, 2);
    let b_at_main = b_at_mid.push(&Stmt::from("M2"));
    assert!(loose.top.is_empty(), "nothing has to ⊤-summarize at k = 2");
    assert_eq!(
        loose.callees_of(&p("main"), &b_at_main),
        BTreeSet::from([p("Y.poly")])
    );
    assert_eq!(pt(&loose, "main", "res"), set(&["{lho}"]));
}

// =========================================================================
// Milestone 6: derivation cost no longer scales with the decision count
// =========================================================================

/// A cascade of `n` critical statements, each one's receiver being the
/// previous one's result:
///
/// ```text
/// main() { M0: g0 = new T0(); S0: g1 = g0.step(); ... S<n-1>: gn = ...; }
/// T<i>.step() { A<i>: return new T<i+1>(); }        // plus a decoy D.step
/// ```
///
/// Every `S<i>` can only be decided once `S<i-1>` has been, so the
/// round-based driver needed `n + 1` complete re-derivations of the whole
/// IDB. Resolution is now ordinary positive recursion, so one semi-naive
/// fixpoint discovers the entire cascade.
fn cascade_program(n: usize) -> Program {
    let mut prog = Program::default();
    let step = Sig::from("step()");

    // A decoy implementor keeps every callsite genuinely critical: with a
    // single CHA target the site would be devirtualized instead (N1).
    prog.procedure.push((p("D.step"),));
    prog.lookup
        .push((Type::from("D"), step.clone(), p("D.step")));
    prog.formal.push((p("D.step"), 0, Var::from("this@D")));

    for i in 0..n {
        let proc_ = p(&format!("T{i}.step"));
        let site = Stmt::from(format!("A{i}"));
        let result = Var::from(format!("r@T{i}"));
        let site_alloc = Alloc::from(format!("l{}", i + 1));

        prog.procedure.push((proc_.clone(),));
        prog.lookup
            .push((Type::from(format!("T{i}")), step.clone(), proc_.clone()));
        prog.formal
            .push((proc_.clone(), 0, Var::from(format!("this@T{i}"))));
        prog.ret.push((proc_.clone(), result.clone()));
        prog.in_proc.push((site.clone(), proc_, 0));
        prog.alloc.push((site, result, site_alloc.clone()));
        prog.alloc_type
            .push((site_alloc, Type::from(format!("T{}", i + 1))));
    }

    prog.procedure.push((p("main"),));
    prog.entry.push((p("main"),));
    prog.formal.push((p("main"), 0, Var::from("this@main")));
    prog.in_proc.push((Stmt::from("M0"), p("main"), 0));
    prog.alloc
        .push((Stmt::from("M0"), Var::from("g0"), Alloc::from("l0")));
    prog.alloc_type.push((Alloc::from("l0"), Type::from("T0")));
    for i in 0..n {
        let site = Stmt::from(format!("S{i}"));
        prog.in_proc.push((site.clone(), p("main"), i + 1));
        prog.virtual_call
            .push((site.clone(), Var::from(format!("g{i}")), step.clone()));
        prog.actual_arg
            .push((site.clone(), 0, Var::from(format!("g{i}"))));
        prog.bind_ret.push((site, Var::from(format!("g{}", i + 1))));
    }
    prog
}

#[test]
fn a_cascade_of_decisions_is_one_fixpoint() {
    const N: usize = 24;
    let h = run_hybrid(&cascade_program(N), 4);

    for i in 0..N {
        assert_eq!(
            h.callees_of(&p("main"), &CritId::origin(format!("S{i}"))),
            BTreeSet::from([p(&format!("T{i}.step"))]),
            "S{i} should be pinned by the allocation S{} produced",
            i.wrapping_sub(1)
        );
    }
    assert_eq!(
        h.dispatches().len(),
        N,
        "exactly one callee per site: no ⊤ fan-out anywhere in the cascade"
    );
}

// =========================================================================
// The vacuous corner of adequacy: a deciding operand with no values at all
// =========================================================================

/// `blocked` is a *presence* test — "some path the caller controls reaches the
/// deciding operand" — so a deciding operand whose points-to set is **empty**
/// is vacuously unblocked, and propagation's `blocked` guard keeps the
/// instance where it is.
///
/// That is the right answer, and this test pins why. By the `is_symbolic`
/// seeding rule (`points(p, sup, Path(sub)) <-- edge(p, sup, sub)` when `sub`
/// is symbolic), an operand fed by a parameter, or by a field of one, or by
/// any other caller-reachable path, carries a symbolic member and so *is*
/// blocked. An empty set therefore means no reaching definition of any kind:
/// dead code. Propagating it would produce an equally empty placeholder in
/// every caller — `V`'s summary publishes nothing for the operand, so the
/// child would have nothing to decide with either.
#[test]
fn a_receiver_with_no_values_stays_put_and_dispatches_nothing() {
    let h = run_hybrid(&families::dead_receiver(), 4);
    let id = CritId::origin("S");

    // The premise: nothing whatsoever reaches the deciding operand.
    assert!(
        h.points_to_path(&p("V"), &AccessPath::crit_slot(id.clone(), 0))
            .is_empty(),
        "premise: pt(receiver) should be empty"
    );

    // So the instance is adequate — vacuously — and stays in `V`.
    assert!(
        h.pending.contains(&(p("V"), id.clone())),
        "the instance should still be pending in V"
    );
    assert!(
        !h.blocked.contains(&(p("V"), id.clone())),
        "an empty deciding operand cannot be blocked"
    );
    assert!(
        h.pending.iter().all(|(owner, _)| owner == &p("V")),
        "nothing should propagate to Entry: {:?}",
        h.pending
    );

    // Nothing is claimed about it: no callee, and no ⊤ fan-out either.
    assert!(
        h.dispatches().is_empty(),
        "dead code must not admit call edges: {:?}",
        h.dispatches()
    );
    assert!(
        h.top.is_empty(),
        "an unblocked instance is never ⊤-summarized: {:?}",
        h.top
    );

    // And it is reported honestly: still deferred in `V`, invisible in `Entry`.
    assert_eq!(h.placeholders(&p("V")), BTreeSet::from([id]));
    assert!(h.placeholders(&p("Entry")).is_empty());
}

/// The guard on propagation and the guard on the placeholder renaming in
/// `root_map` must agree, or a caller ends up holding constraint-graph nodes
/// rooted at a placeholder it never lists as pending — an obligation with no
/// owner, invisible to `placeholders()` and unreachable by `resolve`.
///
/// This is the structural invariant, checked over every family that has
/// critical statements at all: if a callsite in `q` renames a placeholder into
/// `q`, then `q` holds the renamed instance as pending.
#[test]
fn every_renamed_placeholder_is_pending_in_the_procedure_it_lands_in() {
    let cases: Vec<(&str, Program, usize)> = vec![
        ("figure1", figure1::program(), 4),
        ("figure5", figure5::program(), 4),
        ("chain(4)", families::chain(4, 2), 6),
        ("fanin(4)", families::fanin(4, 2), 3),
        ("branching(3)", families::branching(3, 2), 5),
        ("dead_receiver", families::dead_receiver(), 4),
    ];
    for (label, prog, k) in &cases {
        let h = run_hybrid(prog, *k);
        let pending: BTreeSet<(Proc, CritId)> = h.pending.iter().cloned().collect();
        for (site, _, to) in &h.root_map {
            let Some(id) = to.crit_id() else { continue };
            for (s, owner, _) in &h.in_proc {
                if s != site {
                    continue;
                }
                assert!(
                    pending.contains(&(owner.clone(), id.clone())),
                    "{label}: {site} renames a placeholder to {id} in {owner}, \
                     but {owner} does not hold it as pending"
                );
            }
        }
    }
}

// =========================================================================
// Milestone 7: the corners a rule-by-rule mutation sweep found uncovered
// =========================================================================
//
// Each test here is pinned to rules that could be deleted outright without
// any other test noticing. They are written against the *observable* answer
// — a dispatch set, a points-to set, a propagation — rather than against the
// rule, so they keep their meaning if the derivation is rearranged.

/// Hybrid-in-hybrid: a resolved critical statement whose callee still carries
/// a placeholder of its own.
///
/// ```text
/// main()      { M1: g = new P(); M2: y = new Y(); M3: r = g.get(y); }  // entry
/// P.get(x)    { G1: h = x.hop(); return h; }
/// Q.get(x)    { return x; }                      // decoy: makes get() critical
/// Y.hop()     { H1: yo = new Obj(); return yo; } // lyo
/// Z.hop()     { H2: zo = new Obj(); return zo; } // lzo
/// warm()      { W0: wo = new Obj(); W1: wt = P.get(wo); }  // gives P.get a caller
/// ```
///
/// `M3`'s receiver is a local allocation, so it is pinned to `P.get` outright.
/// `P.get` cannot decide `G1` for itself — its receiver is `par_1@P.get` — so
/// its summary is genuinely hybrid, and inlining it at `M3` has to rename
/// `⟨G1⟩` into `main` as `⟨G1@M3⟩`: the placeholder's slots, its result, and
/// the pending obligation itself. Only then does `main`'s own `new Y()` reach
/// the renamed receiver and pin `Y.hop`.
///
/// `warm` exists so that `P.get` is not `uncalled`: an implementation reached
/// only through virtual calls has nowhere to propagate to, and would
/// ⊤-summarize `G1` in place instead of publishing it as a placeholder.
#[test]
fn a_callee_placeholder_is_renamed_into_the_resolving_caller() {
    let mut prog = Program::default();
    prog.procedure = [
        (p("P.get"),),
        (p("Q.get"),),
        (p("Y.hop"),),
        (p("Z.hop"),),
        (p("warm"),),
        (p("main"),),
    ]
    .to_vec();
    prog.entry = vec![(p("main"),), (p("warm"),)];
    prog.lookup = vec![
        (Type::from("P"), Sig::from("get(Obj)"), p("P.get")),
        (Type::from("Q"), Sig::from("get(Obj)"), p("Q.get")),
        (Type::from("Y"), Sig::from("hop()"), p("Y.hop")),
        (Type::from("Z"), Sig::from("hop()"), p("Z.hop")),
    ];
    prog.alloc_type = vec![
        (Alloc::from("lp"), Type::from("P")),
        (Alloc::from("ly"), Type::from("Y")),
        (Alloc::from("lyo"), Type::from("Obj")),
        (Alloc::from("lzo"), Type::from("Obj")),
        (Alloc::from("lw"), Type::from("Obj")),
    ];
    prog.formal = vec![
        (p("P.get"), 0, Var::from("this@P")),
        (p("P.get"), 1, Var::from("x@P")),
        (p("Q.get"), 0, Var::from("this@Q")),
        (p("Q.get"), 1, Var::from("x@Q")),
        (p("Y.hop"), 0, Var::from("this@Y")),
        (p("Z.hop"), 0, Var::from("this@Z")),
        (p("warm"), 0, Var::from("this@warm")),
        (p("main"), 0, Var::from("this@main")),
    ];
    prog.ret = vec![
        (p("P.get"), Var::from("h")),
        (p("Q.get"), Var::from("x@Q")),
        (p("Y.hop"), Var::from("yo")),
        (p("Z.hop"), Var::from("zo")),
        (p("warm"), Var::from("wt")),
    ];
    prog.in_proc = vec![
        (Stmt::from("G1"), p("P.get"), 0),
        (Stmt::from("H1"), p("Y.hop"), 0),
        (Stmt::from("H2"), p("Z.hop"), 0),
        (Stmt::from("W0"), p("warm"), 0),
        (Stmt::from("W1"), p("warm"), 1),
        (Stmt::from("M1"), p("main"), 0),
        (Stmt::from("M2"), p("main"), 1),
        (Stmt::from("M3"), p("main"), 2),
    ];
    prog.alloc = vec![
        (Stmt::from("H1"), Var::from("yo"), Alloc::from("lyo")),
        (Stmt::from("H2"), Var::from("zo"), Alloc::from("lzo")),
        (Stmt::from("W0"), Var::from("wo"), Alloc::from("lw")),
        (Stmt::from("M1"), Var::from("g"), Alloc::from("lp")),
        (Stmt::from("M2"), Var::from("y"), Alloc::from("ly")),
    ];
    prog.virtual_call = vec![
        (Stmt::from("G1"), Var::from("x@P"), Sig::from("hop()")),
        (Stmt::from("M3"), Var::from("g"), Sig::from("get(Obj)")),
    ];
    prog.direct_call = vec![(Stmt::from("W1"), p("P.get"))];
    prog.actual_arg = vec![
        (Stmt::from("G1"), 0, Var::from("x@P")),
        (Stmt::from("W1"), 0, Var::from("this@warm")),
        (Stmt::from("W1"), 1, Var::from("wo")),
        (Stmt::from("M3"), 0, Var::from("g")),
        (Stmt::from("M3"), 1, Var::from("y")),
    ];
    prog.bind_ret = vec![
        (Stmt::from("G1"), Var::from("h")),
        (Stmt::from("W1"), Var::from("wt")),
        (Stmt::from("M3"), Var::from("r")),
    ];

    let h = run_hybrid(&prog, 4);
    let outer = CritId::origin("M3");
    let inner = CritId::origin("G1");
    let nested = inner.nest(&outer); // ⟨G1@M3⟩

    // The premise: `P.get` publishes `G1` rather than deciding it.
    assert_eq!(
        h.placeholders(&p("P.get")),
        BTreeSet::from([inner.clone()]),
        "P.get's summary must still defer G1"
    );
    assert!(
        h.top.iter().all(|(owner, _)| owner != &p("P.get")),
        "G1 must not be ⊤-summarized inside P.get: {:?}",
        h.top
    );

    // The outer statement is pinned by a local allocation.
    assert_eq!(
        h.callees_of(&p("main"), &outer),
        BTreeSet::from([p("P.get")])
    );

    // ... and inlining P.get renames its placeholder into `main`.
    assert!(
        h.pending.contains(&(p("main"), nested.clone())),
        "⟨G1@M3⟩ must be pending in main: {:?}",
        h.pending
    );

    // Now `main` has the context P.get lacked: `new Y()` reaches the renamed
    // receiver, so `Z.hop` is never admitted.
    assert_eq!(
        h.callees_of(&p("main"), &nested),
        BTreeSet::from([p("Y.hop")]),
        "the nested instance must dispatch on what main actually passes"
    );

    // And the value comes back out through the renamed result node.
    assert_eq!(pt(&h, "main", "r"), set(&["{lyo}"]));
}

/// The two non-k-limit ways of being [`stuck`]: an entry procedure, whose
/// callers the analysis cannot see, and a procedure with no callers at all.
///
/// ```text
/// launcher()      { L1: a = new Obj(); L2: t = root(a); }   // entry
/// root(arg)       { R1: q = arg.poly(); return q; }         // entry *and* called
/// orphan(o)       { O1: s = o.poly();  return s; }          // neither
/// Y.poly() { Y1: yv = new Obj(); return yv; }
/// Z.poly() { Z1: zv = new Obj(); return zv; }
/// ```
///
/// Both `R1` and `O1` are blocked — their receivers are formals, so a caller
/// still controls them — and both are far from the k-limit. What forces them
/// to ⊤-summarize on the spot is the other half of `stuck`: `root` is an
/// entry, so the caller that would pin `R1` may not be in the program at all;
/// `orphan` has no callers, so a placeholder propagated out of it would never
/// come back. The two procedures separate the two rules: `root` is called and
/// so is not `uncalled`, `orphan` is not an entry.
#[test]
fn an_entry_and_an_uncalled_procedure_both_top_summarize_in_place() {
    let mut prog = Program::default();
    prog.procedure = [
        (p("launcher"),),
        (p("root"),),
        (p("orphan"),),
        (p("Y.poly"),),
        (p("Z.poly"),),
    ]
    .to_vec();
    prog.entry = vec![(p("launcher"),), (p("root"),)];
    prog.lookup = vec![
        (Type::from("Y"), Sig::from("poly()"), p("Y.poly")),
        (Type::from("Z"), Sig::from("poly()"), p("Z.poly")),
    ];
    prog.alloc_type = vec![
        (Alloc::from("lo"), Type::from("Obj")),
        (Alloc::from("lyv"), Type::from("Obj")),
        (Alloc::from("lzv"), Type::from("Obj")),
    ];
    prog.formal = vec![
        (p("launcher"), 0, Var::from("this@launcher")),
        (p("root"), 0, Var::from("this@root")),
        (p("root"), 1, Var::from("arg@root")),
        (p("orphan"), 0, Var::from("this@orphan")),
        (p("orphan"), 1, Var::from("o@orphan")),
        (p("Y.poly"), 0, Var::from("this@Y")),
        (p("Z.poly"), 0, Var::from("this@Z")),
    ];
    prog.ret = vec![
        (p("root"), Var::from("q")),
        (p("orphan"), Var::from("s")),
        (p("Y.poly"), Var::from("yv")),
        (p("Z.poly"), Var::from("zv")),
    ];
    prog.in_proc = vec![
        (Stmt::from("L1"), p("launcher"), 0),
        (Stmt::from("L2"), p("launcher"), 1),
        (Stmt::from("R1"), p("root"), 0),
        (Stmt::from("O1"), p("orphan"), 0),
        (Stmt::from("Y1"), p("Y.poly"), 0),
        (Stmt::from("Z1"), p("Z.poly"), 0),
    ];
    prog.alloc = vec![
        (Stmt::from("L1"), Var::from("a"), Alloc::from("lo")),
        (Stmt::from("Y1"), Var::from("yv"), Alloc::from("lyv")),
        (Stmt::from("Z1"), Var::from("zv"), Alloc::from("lzv")),
    ];
    prog.virtual_call = vec![
        (Stmt::from("R1"), Var::from("arg@root"), Sig::from("poly()")),
        (Stmt::from("O1"), Var::from("o@orphan"), Sig::from("poly()")),
    ];
    prog.direct_call = vec![(Stmt::from("L2"), p("root"))];
    prog.actual_arg = vec![
        (Stmt::from("R1"), 0, Var::from("arg@root")),
        (Stmt::from("O1"), 0, Var::from("o@orphan")),
        (Stmt::from("L2"), 0, Var::from("this@launcher")),
        (Stmt::from("L2"), 1, Var::from("a")),
    ];
    prog.bind_ret = vec![
        (Stmt::from("R1"), Var::from("q")),
        (Stmt::from("O1"), Var::from("s")),
        (Stmt::from("L2"), Var::from("t")),
    ];

    let k = 3;
    let h = run_hybrid(&prog, k);
    let r1 = CritId::origin("R1");
    let o1 = CritId::origin("O1");
    let both = BTreeSet::from([p("Y.poly"), p("Z.poly")]);

    // Neither instance is anywhere near the k-limit, so that branch of
    // `stuck` cannot be what decides either of them.
    assert!(r1.depth() < k && o1.depth() < k);

    // `root` is an entry that also has a visible caller: being called is not
    // enough, because the callers an entry has are not all visible.
    assert!(
        !h.uncalled.contains(&(p("root"),)),
        "launcher calls root, so root is not uncalled"
    );
    assert!(h.blocked.contains(&(p("root"), r1.clone())));
    assert!(
        h.top.contains(&(p("root"), r1.clone())),
        "an entry's blocked placeholder must ⊤-summarize where it stands"
    );
    assert_eq!(h.callees_of(&p("root"), &r1), both);

    // `orphan` is not an entry, but nothing calls it either, so a propagated
    // placeholder would never find a caller to pin it.
    assert!(h.uncalled.contains(&(p("orphan"),)));
    assert!(h.blocked.contains(&(p("orphan"), o1.clone())));
    assert!(
        h.top.contains(&(p("orphan"), o1.clone())),
        "a procedure with no callers must ⊤-summarize its blocked placeholders"
    );
    assert_eq!(h.callees_of(&p("orphan"), &o1), both);
}

/// A procedure the EDB only mentions in passing still gets summarized.
///
/// `procedure` is the front end's list of bodies it chose to declare; the
/// analysis takes `in_proc` as equally good evidence that a procedure exists,
/// so that a partial or hand-written EDB cannot silently lose a summary. Here
/// `hidden` is absent from `procedure` but has a body, and without it the
/// caller would see nothing come back.
#[test]
fn a_procedure_only_in_proc_names_still_publishes_a_summary() {
    let mut prog = Program::default();
    prog.procedure = vec![(p("main"),)]; // deliberately omits `hidden`
    prog.entry = vec![(p("main"),)];
    prog.alloc_type = vec![(Alloc::from("lo"), Type::from("Obj"))];
    prog.formal = vec![
        (p("main"), 0, Var::from("this@main")),
        (p("hidden"), 0, Var::from("this@hidden")),
        (p("hidden"), 1, Var::from("x@hidden")),
    ];
    prog.ret = vec![(p("hidden"), Var::from("t"))];
    prog.in_proc = vec![
        (Stmt::from("H1"), p("hidden"), 0),
        (Stmt::from("M1"), p("main"), 0),
        (Stmt::from("M2"), p("main"), 1),
    ];
    prog.mov = vec![(Stmt::from("H1"), Var::from("t"), Var::from("x@hidden"))];
    prog.alloc = vec![(Stmt::from("M1"), Var::from("o"), Alloc::from("lo"))];
    prog.direct_call = vec![(Stmt::from("M2"), p("hidden"))];
    prog.actual_arg = vec![
        (Stmt::from("M2"), 0, Var::from("this@main")),
        (Stmt::from("M2"), 1, Var::from("o")),
    ];
    prog.bind_ret = vec![(Stmt::from("M2"), Var::from("r"))];

    let h = run_hybrid(&prog, 2);

    assert!(
        h.known_proc.contains(&(p("hidden"),)),
        "in_proc names `hidden`, which is enough to make it a known procedure"
    );
    assert_eq!(
        rendered(&h.summaries(), "hidden"),
        ["ret@hidden ⊇ par_1@hidden"]
    );
    assert_eq!(pt(&h, "main", "r"), set(&["{lo}"]));
}

/// The value slot of a pending `lv[v]` *store* is part of `free(𝔞)`, and so
/// blocks anything downstream of it, for as long as that store can still
/// propagate.
///
/// ```text
/// p() {                       // called from main, so its pendings can propagate
///   P0: m = new Arr();
///   P1: k = "key";
///   Pv: v = new Y();
///   P2: m[k] = v;             // critical store ⟨P2⟩ — a variable index
///   P3: t = m["key"];         // a *constant* index: not critical
///   P4: r = t.poly();         // critical call ⟨P4⟩
///   return r;
/// }
/// main() { M1: out = p(); }   // entry
/// ```
///
/// `t` is read back out of the array the store wrote, so the only symbolic
/// member of `⟨P4⟩`'s receiver set is `⟨P2⟩:arg2` — the store's value slot.
/// That is the one root `free_root` can supply here, and it is what makes
/// `⟨P4⟩` blocked and sends it up to `main`.
///
/// # OPEN QUESTION — this test pins behaviour that may be wrong
///
/// Note what the guard is: `can_propagate` (`analysis.rs:278`), not adequacy.
/// `⟨P2⟩`'s index is a local constant, so the store is adequate, settled, and
/// will never move — the propagation rules (`:267`, `:377`, `:380`) all carry a
/// `blocked` guard that `can_propagate` never picked up. So `⟨P2⟩:arg2` is
/// declared caller-influenced even though everything it holds is local, and
/// `⟨P4⟩` is blocked as a result.
///
/// Measured on this program, with `free_root`'s `CritSlot` rule
/// (`analysis.rs:335`) removed and nothing else changed:
///
/// ```text
///                     with :335                without :335
///   ⟨P4⟩ blocked      true                     false
///   ⟨P4⟩ settled      false                    true
///   pending           p:⟨P2⟩ p:⟨P4⟩             p:⟨P2⟩ p:⟨P4⟩
///                     main:⟨P4@M1⟩              (no copy in main)
///   placeholders(p)   [⟨P4⟩]                   []
///   summary(p)        ret@p ⊇ ⟨P4⟩:res         ret@p ⊇ {lyv}
///                     ret@p ⊇ {lyv}
///                     ⟨P4⟩:arg0 ⊇ {ly}
///                     ⟨P4⟩:res ⊇ {lyv}
/// ```
///
/// Dispatch is `Y.poly` either way — `resolve` (`:424`) fires on the
/// allocation regardless of `blocked`. What the rule costs is a spurious
/// pending in every caller, a placeholder reported as deferred that isn't, and
/// three constraints of placeholder plumbing kept in the published summary
/// instead of collapsed away.
///
/// Two neighbouring shapes, measured, suggest the rule may never do necessary
/// work — that it adds blocking only where blocking is wrong:
///
/// - `P2: m[k] = par` (value from a parameter): `⟨P4⟩` is blocked, and
///   rightly, but `pt(t) = {par_1@p}` — the parameter arrives in the receiver's
///   set by ordinary closure, so `free_root`'s *`Param`* rule (`:333`) already
///   blocks it. `:335` fires redundantly.
/// - `P2: m[par] = v` (index from a parameter): an unpinned index yields no
///   `index_acc`, so `:496`/`:511` never fire, nothing reaches `t`, and `⟨P4⟩`
///   is untouched. `⟨P2⟩` itself is blocked and propagates, as it should.
///
/// The conjecture, *not proven*: whatever a slot holds reaches its readers by
/// closure (`:187`), so genuinely caller-influenced content always arrives as a
/// `Param`-rooted path (blocks via `:333`) or a `CritRet`-rooted one (blocks
/// via `:337`) on its own. `:335` contributes only the placeholder root, which
/// carries no caller influence the closure has not already delivered. Settling
/// it means enumerating what can reach a decisive slot from the only base case
/// that puts a `CritSlot` on the sub side of an edge — the `lv[v]` store
/// resolution `:496`/`:511`, slot 2 specifically; every other occurrence is
/// renaming (`:377`, `:466`) — the way `rule-57-to-check.md` does for `Ret`.
///
/// The candidate fix is to give `can_propagate` the guard its siblings have:
///
/// ```text
/// can_propagate(p, id) <-- pending(p, id), blocked(p, id), eff_direct(s, p),
///                          in_proc(s, _, _), k_limit(k), if id.depth() < *k;
/// ```
///
/// It stays positive and monotone, so it remains legal inside the SCC. The
/// thing to watch is the cycle it introduces —
/// `blocked → can_propagate → free_root → blocked`. The least fixpoint is
/// still well defined and the bootstrap survives (`:333`/`:334` are
/// unconditional), but a blocking chain grounded *only* in placeholder slots
/// would then collapse to nothing. That is the intended effect, and the part
/// worth a deliberate test of its own.
///
/// Until that is settled, this test pins the guard as written, so that
/// tightening it is a visible change rather than a silent one.
#[test]
fn a_pending_stores_value_slot_blocks_what_reads_it_back() {
    let mut prog = Program::default();
    prog.procedure = [(p("p"),), (p("main"),), (p("Y.poly"),), (p("Z.poly"),)].to_vec();
    prog.entry = vec![(p("main"),)];
    prog.lookup = vec![
        (Type::from("Y"), Sig::from("poly()"), p("Y.poly")),
        (Type::from("Z"), Sig::from("poly()"), p("Z.poly")),
    ];
    prog.alloc_type = vec![
        (Alloc::from("lm"), Type::from("Arr")),
        (Alloc::from("ly"), Type::from("Y")),
        (Alloc::from("lyv"), Type::from("Obj")),
        (Alloc::from("lzv"), Type::from("Obj")),
    ];
    prog.formal = vec![
        (p("p"), 0, Var::from("this@p")),
        (p("main"), 0, Var::from("this@main")),
        (p("Y.poly"), 0, Var::from("this@Y")),
        (p("Z.poly"), 0, Var::from("this@Z")),
    ];
    prog.ret = vec![
        (p("p"), Var::from("r")),
        (p("Y.poly"), Var::from("yv")),
        (p("Z.poly"), Var::from("zv")),
    ];
    prog.in_proc = vec![
        (Stmt::from("P0"), p("p"), 0),
        (Stmt::from("P1"), p("p"), 1),
        (Stmt::from("Pv"), p("p"), 2),
        (Stmt::from("P2"), p("p"), 3),
        (Stmt::from("P3"), p("p"), 4),
        (Stmt::from("P4"), p("p"), 5),
        (Stmt::from("M1"), p("main"), 0),
        (Stmt::from("Y1"), p("Y.poly"), 0),
        (Stmt::from("Z1"), p("Z.poly"), 0),
    ];
    prog.alloc = vec![
        (Stmt::from("P0"), Var::from("m"), Alloc::from("lm")),
        (Stmt::from("Pv"), Var::from("v"), Alloc::from("ly")),
        (Stmt::from("Y1"), Var::from("yv"), Alloc::from("lyv")),
        (Stmt::from("Z1"), Var::from("zv"), Alloc::from("lzv")),
    ];
    prog.const_assign = vec![(Stmt::from("P1"), Var::from("k"), Const::from("key"))];
    prog.store_index_var = vec![(
        Stmt::from("P2"),
        Var::from("m"),
        Var::from("k"),
        Var::from("v"),
    )];
    prog.load_index_const = vec![(
        Stmt::from("P3"),
        Var::from("t"),
        Var::from("m"),
        Const::from("key"),
    )];
    prog.virtual_call = vec![(Stmt::from("P4"), Var::from("t"), Sig::from("poly()"))];
    prog.direct_call = vec![(Stmt::from("M1"), p("p"))];
    prog.actual_arg = vec![
        (Stmt::from("P4"), 0, Var::from("t")),
        (Stmt::from("M1"), 0, Var::from("this@main")),
    ];
    prog.bind_ret = vec![
        (Stmt::from("P4"), Var::from("r")),
        (Stmt::from("M1"), Var::from("out")),
    ];

    let h = run_hybrid(&prog, 3);
    let call = CritId::origin("P4");
    let store = CritId::origin("P2");

    // The premise: the store's value slot is what the receiver reads back.
    assert!(
        h.points.contains(&(
            p("p"),
            AccessPath::crit_slot(call.clone(), 0),
            PtVal::Path(AccessPath::crit_slot(store.clone(), 2)),
        )),
        "the receiver should see the store's value slot"
    );
    assert!(
        h.can_propagate.contains(&(p("p"), store.clone())),
        "premise: the store instance can still travel"
    );

    // So the call is blocked, even though nothing symbolic reaches it by any
    // other route, and it travels to `main` instead of settling in `p`.
    assert!(
        h.blocked.contains(&(p("p"), call.clone())),
        "a free placeholder slot in the receiver's set must block"
    );
    assert!(
        h.pending
            .contains(&(p("main"), call.push(&Stmt::from("M1")))),
        "a blocked instance propagates: {:?}",
        h.pending
    );
    assert!(
        h.placeholders(&p("p")).contains(&call),
        "and it is still reported as deferred in p"
    );
}

/// Suffix congruence keys off the suffixes a procedure *mentions*, not off the
/// suffixes that happen to carry values.
///
/// ```text
/// p(par) { S1: a = par; S2: a.f = c; return a; }   // `c` is opaque: nothing
///                                                  // in the EDB defines it
/// ```
///
/// `a.f` is written and never read, and what is written to it has no
/// points-to set at all — the shape a front end produces for a value it
/// cannot model, such as the result of a native call. So `a.f` is nowhere on
/// the receiving end of a constraint and holds nothing: the only evidence
/// that `.f` is a suffix worth closing over is that a constraint *mentions*
/// it on the left.
///
/// That is enough. `ret@p ⊇ a` and `a ⊇ par_1@p`, closed under `.f`, give
/// `ret@p.f ⊇ par_1@p.f`, and the caller needs it: `p` hands back the very
/// object it was given, so a field of the result is a field of the argument.
#[test]
fn a_store_of_an_opaque_value_still_publishes_the_congruent_suffix() {
    let mut prog = Program::default();
    prog.procedure = vec![(p("p"),)];
    prog.formal = vec![
        (p("p"), 0, Var::from("this@p")),
        (p("p"), 1, Var::from("par@p")),
    ];
    prog.ret = vec![(p("p"), Var::from("a"))];
    prog.in_proc = vec![(Stmt::from("S1"), p("p"), 0), (Stmt::from("S2"), p("p"), 1)];
    prog.mov = vec![(Stmt::from("S1"), Var::from("a"), Var::from("par@p"))];
    prog.store_field = vec![(
        Stmt::from("S2"),
        Var::from("a"),
        Field::from("f"),
        Var::from("c"),
    )];

    let h = run_hybrid(&prog, 2);

    // The premise: what is stored has no points-to set of its own, so `a.f`
    // has no content except whatever congruence gives it.
    assert!(
        h.points_to(&p("p"), "c").is_empty(),
        "premise: the stored value is opaque"
    );

    assert_eq!(
        rendered(&h.summaries(), "p"),
        ["ret@p ⊇ par_1@p", "ret@p.f ⊇ par_1@p.f"],
        "the mention of `.f` is what makes the congruent constraint publishable"
    );
}

// ---------------------------------------------------------------------------
// `free(𝔞) ∋ ret@p` — `analysis.rs:334`
//
// §4.1.3 defines `free(𝔞)` as "the set of variables that are accessible
// outside the current procedure", and §2 introduces `ret@p` as one of the
// symbolic variables that make up exactly that vocabulary. So the rule is the
// paper's definition read literally, and `free_root` is `pub_root` modulo the
// `can_propagate` refinement on placeholders.
//
// No rule in the current program ever puts a `Base::Ret` on the *sub* side of
// an `edge`: `:182` puts `ret@p` on the sup side, and `root_map` (`:371`) and
// `crit_map` (`:463`) have it only as a substitution *source*, never a target.
// So `blocked` never queries `free_root` at a `Ret` base, and a rule-by-rule
// mutation sweep finds `:334` removable with the whole suite still green.
//
// It is not removable, and these two tests are what say so. The first pins the
// paper's definition; the second pins the consequence, by seeding the one
// constraint shape the rest of the rules do not currently produce.
//
// Do not confuse `Base::Ret` with the paper's `ret@poly` in Figure 3(a), where
// `foo()`'s hybrid summary is `{tx ⊇ par₁@foo, obj ⊇ par₂@foo, ret ⊇ ret@poly}`.
// That `ret@poly` is the critical statement's *result placeholder* — this
// analysis's `Base::CritRet` — and it does sit on the sub side (`:186`). The
// `Ret`/`CritRet` split is the whole reason `:334` looks dead.
// ---------------------------------------------------------------------------

/// `free(𝔞)` contains `ret@p` for every procedure, per §4.1.3.
///
/// `ret@p` is accessible outside `p` by construction — it is the name §2 gives
/// the value the caller receives — so it belongs to `free(𝔞)` under the
/// paper's definition, whether or not the current rule set ever asks.
#[test]
fn free_root_lists_the_return_value_of_every_procedure() {
    for prog in [figure1::program(), figure5::program()] {
        let h = run_hybrid(&prog, 2);
        assert!(
            !h.known_proc.is_empty(),
            "premise: the program has procedures"
        );
        for (proc_,) in &h.known_proc {
            assert!(
                h.free_root
                    .contains(&(proc_.clone(), Base::Ret(proc_.clone()))),
                "free(𝔞) must contain ret@{proc_} (§4.1.3: the variables \
                 accessible outside the current procedure)"
            );
        }
    }
}

/// A `ret@·`-rooted path in a deciding operand must block — the safety net
/// `:334` actually is.
///
/// `:193` manufactures a `PtVal::Path` for *any* symbolic sub base, and
/// `Base::Ret` is symbolic (`access_path.rs:139`). So the roots `blocked` can
/// be queried at are `{Param, Ret, CritSlot, CritRet}`, and `free_root` has to
/// be total over them. `:334` is what keeps the two sets aligned; without it,
/// the day some rule puts `ret@q` on a sub side, the failure is silent.
///
/// The current rules never produce that shape, so this test seeds it directly
/// — one extra `edge` tuple before `run()`, standing in for a future rule that
/// models a callee's return as a symbolic value rather than substituting it
/// away:
///
/// ```text
/// q() {                    // uncalled, so its pendings are `stuck`
///   Q0: m = new Arr();
///   Q1: t = m[i];          // critical lv[v]; `i` is otherwise opaque
/// }
/// seeded:  i ⊇ ret@q
/// ```
///
/// Nothing else symbolic reaches the index, so `⟨Q1⟩` is blocked on the
/// strength of `ret@q` alone. Being stuck as well, it must be ⊤-summarized:
/// `top` fires and the access resolves to `[π]`.
///
/// Delete `:334` and every one of those goes the other way — the instance is
/// declared *adequate*, `index_acc` stays empty, and the load resolves to
/// nothing at all. The analysis would silently treat a caller-visible index as
/// dead code instead of widening it, which is the unsound direction.
#[test]
fn a_ret_rooted_index_blocks_the_access_it_decides() {
    let mut prog = Program::default();
    prog.procedure = vec![(p("q"),)];
    prog.formal = vec![(p("q"), 0, Var::from("this@q"))];
    prog.alloc_type = vec![(Alloc::from("lm"), Type::from("Arr"))];
    prog.in_proc = vec![(Stmt::from("Q0"), p("q"), 0), (Stmt::from("Q1"), p("q"), 1)];
    prog.alloc = vec![(Stmt::from("Q0"), Var::from("m"), Alloc::from("lm"))];
    prog.load_index_var = vec![(
        Stmt::from("Q1"),
        Var::from("t"),
        Var::from("m"),
        Var::from("i"),
    )];

    let mut h = HybridAnalysis::for_program(&prog, 2);
    // The one shape no current rule derives: `ret@q` on the sub side.
    h.edge
        .push((p("q"), AccessPath::var("i"), AccessPath::ret(p("q"))));
    h.run();

    let id = CritId::origin("Q1");
    let index = AccessPath::crit_slot(id.clone(), 1);

    // Premise: the index sees `ret@q` and nothing else symbolic, so `:333`,
    // `:335` and `:337` cannot be what blocks here.
    let symbolic: BTreeSet<Base> = h
        .points
        .iter()
        .filter(|(proc_, w, _)| proc_ == &p("q") && w == &index)
        .filter_map(|(_, _, v)| match v {
            PtVal::Path(w) => Some(w.base.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(
        symbolic,
        BTreeSet::from([Base::Ret(p("q"))]),
        "premise: `ret@q` is the only free root reaching the index"
    );
    assert!(
        h.stuck.contains(&(p("q"), id.clone())),
        "premise: `q` has no callers, so `⟨Q1⟩` has nowhere to propagate"
    );

    assert!(
        h.blocked.contains(&(p("q"), id.clone())),
        "`ret@q` is in `free(𝔞)`, so the index it reaches is not yet decided"
    );
    assert!(
        !h.adequate.contains(&(p("q"), id.clone())),
        "and `Φ_a` must therefore not hold"
    );
    assert!(
        h.top.contains(&(p("q"), id.clone())),
        "blocked and stuck: the instance has to be ⊤-summarized here"
    );
    assert_eq!(
        h.accessors_of(&p("q"), &id),
        BTreeSet::from([Accessor::IndexUnknown]),
        "so the access widens to `[π]` rather than resolving to nothing"
    );
}
