//! End-to-end tests for the Hybrid Inlining analysis.
//!
//! The headline acceptance test is Figure 1: the analysis must compute
//! `pt(second) = {l37} = pt(first)` and `pt(third) = {l14}` in `service()`,
//! and must *not* admit the spurious call edge `bar1 → … → Z.poly`.

use std::collections::{BTreeMap, BTreeSet};

use hybrid_inlining_poc::access_path::{AccessPath, Accessor, Constraint, CritId, PtVal, Summary};
use hybrid_inlining_poc::analysis::{Decisions, Hybrid, Round, run_hybrid};
use hybrid_inlining_poc::ir::*;
use hybrid_inlining_poc::{figure1, figure5};

fn p(x: &str) -> Proc {
    x.into()
}

/// `pt(v)` for a local of `p`, rendered for readable assertions.
fn pt(h: &Hybrid, proc_: &str, v: &str) -> BTreeSet<String> {
    h.round
        .points_to(&p(proc_), Var::from(v))
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
        rendered(&h.round.summaries(), "FacadeImpl.id"),
        ["ret@FacadeImpl.id ⊇ par_1@FacadeImpl.id"]
    );
}

#[test]
fn published_summaries_never_mention_a_local() {
    let h = run_hybrid(&figure1::program(), 4);
    for (owner, summary) in h.round.summaries() {
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
    assert_eq!(h.round.summaries(), figure1::figure2_summaries());
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
    assert!(h.round.placeholders(&p("FacadeImpl.foo")).is_empty());
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
    let summaries = h.round.summaries();

    assert_eq!(
        rendered(&summaries, "FacadeImpl.foo"),
        [
            "ret@FacadeImpl.foo ⊇ ⟨L25⟩:res",
            "⟨L25⟩:arg0 ⊇ par_1@FacadeImpl.foo",
            "⟨L25⟩:arg1 ⊇ par_2@FacadeImpl.foo",
        ]
    );
    assert_eq!(
        h.round.placeholders(&p("FacadeImpl.foo")),
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
        h.round.placeholders(&p("FacadeImpl.mid")),
        BTreeSet::from([c(&["L28"])])
    );
}

#[test]
fn bar1_and_bar2_match_figures_3c_and_3f() {
    // Once the receiver is pinned, the placeholder is resolved *precisely*
    // and disappears from the summary. This is the whole point: bar1 is the
    // identity, bar2 always returns l14.
    let h = run_hybrid(&figure1::program(), 4);
    let summaries = h.round.summaries();

    assert_eq!(
        rendered(&summaries, "FacadeImpl.bar1"),
        ["ret@FacadeImpl.bar1 ⊇ par_1@FacadeImpl.bar1"]
    );
    assert_eq!(
        rendered(&summaries, "FacadeImpl.bar2"),
        ["ret@FacadeImpl.bar2 ⊇ {l14}"]
    );
    assert!(h.round.placeholders(&p("FacadeImpl.bar1")).is_empty());
    assert!(h.round.placeholders(&p("FacadeImpl.bar2")).is_empty());
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
        .round
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
fn resolution_is_the_only_feedback_between_rounds() {
    // Figure 1 needs exactly one round of discovery plus one round to reach
    // the fixpoint. If this ever grows, the driver is doing more work than
    // §5 of the plan predicts.
    assert_eq!(run_hybrid(&figure1::program(), 4).rounds, 2);
    assert_eq!(run_hybrid(&figure1::program(), 0).rounds, 2);
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
    assert!(
        h.round.critical.is_empty(),
        "single-target site is not critical"
    );
    assert_eq!(
        h.round.eff_direct.len(),
        1,
        "it is an effectively direct call"
    );
    assert!(h.round.placeholders(&p("caller")).is_empty());
    assert_eq!(
        rendered(&h.round.summaries(), "caller"),
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
    assert_eq!(
        rendered(&h.round.summaries(), "rid"),
        ["ret@rid ⊇ par_0@rid"]
    );
    assert_eq!(h.rounds, 1, "no critical statements, so nothing to resolve");
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
        for (_, id) in &h.round.pending {
            assert!(id.depth() <= k, "k = {k} but {id} has depth {}", id.depth());
        }
        assert!(
            h.round.pending.iter().any(|(_, id)| id.depth() == k),
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
        rendered(&h.round.summaries(), "through"),
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
        rendered(&h.round.summaries(), "cell"),
        ["ret@cell ⊇ par_1@cell[0]", "ret@cell ⊇ par_2@cell"],
    );

    // The path the value took really is `par_1@cell[0]`, not a bare root.
    let indexed = AccessPath::param("cell", 1).index("0");
    assert!(h.round.points.iter().any(|(q, w, v)| q == &p("cell")
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

    for (owner, summary) in h.round.summaries() {
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
    let summaries = h.round.summaries();

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
        h.round.placeholders(&p("getP")),
        BTreeSet::from([CritId::origin("L2")])
    );
    assert_eq!(
        h.round.placeholders(&p("setP")),
        BTreeSet::from([CritId::origin("L5")])
    );

    // Both are blocked on the *index*, not the base — that is N4's decisive
    // operand, and it is what §4.1.3 intersects against `free(𝔞)`.
    let blocked: BTreeSet<String> = h
        .round
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
        rendered(&h.round.summaries(), "build"),
        [
            "ret@build[\"old\"] ⊇ par_1@build[\"cur\"]",
            "ret@build ⊇ {l8}",
        ]
    );
    assert!(h.round.placeholders(&p("build")).is_empty());

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
        rendered(&h.round.summaries(), "getP"),
        ["ret@getP ⊇ par_1@getP[π]"]
    );
    assert_eq!(
        rendered(&h.round.summaries(), "build"),
        ["ret@build[π] ⊇ par_1@build[π]", "ret@build ⊇ {l8}"]
    );
    assert!(
        h.decisions
            .indices
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

    // Adequacy and N4 are gated on `!resolved`, so they are only visible in
    // the round that discovers them — replay the first one to see both.
    let mut first = Round::for_program(&prog, 4, &Decisions::default());
    first.run();
    assert!(
        first.adequate.contains(&(p("build"), get.clone())),
        "no free variable reaches the index, so the context is adequate"
    );
    assert!(
        first.index_undecidable.contains(&(p("build"), get.clone())),
        "but the index is an allocation site, so it still cannot be pinned"
    );

    let h = run_hybrid(&prog, 4);
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

/// `include_source!` guarantees `Program` and `Round` *declare* the same
/// relations, but [`Round::for_program`] still copies the facts one relation
/// at a time, and a forgotten line would leave one silently empty. So: build a
/// program in which every EDB relation holds a tuple, and check every one of
/// them survives the copy.
///
/// The facts are nonsense — this program is never run, only copied.
#[test]
fn every_edb_relation_is_copied_into_the_round() {
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

    let round = Round::for_program(&prog, 4, &Decisions::default());
    let (declared, copied) = (
        prog.relation_sizes_summary(),
        round.relation_sizes_summary(),
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
            "{name} is in the shared schema but Round::for_program does not copy it"
        );
    }
}
