//! Complexity regression guards.
//!
//! `examples/complexity.rs` and `cargo bench` produce the full picture; this
//! file pins the handful of facts that a rule edit must not change silently.
//! Each test states the shape it is defending and why, so a failure says what
//! was given up rather than just which number moved.
//!
//! Sizes are kept small deliberately: these run in a debug build.

use std::collections::BTreeMap;

use hybrid_inlining_paper::analysis::parallel::ParallelHybridAnalysis;
use hybrid_inlining_paper::analysis::parallel::inter_rule::InterRuleHybridAnalysis;
use hybrid_inlining_paper::analysis::run_hybrid;
use hybrid_inlining_paper::families::*;
use hybrid_inlining_paper::figure1;
use hybrid_inlining_paper::ir::{Field, Proc, Program, Stmt, Var};
use hybrid_inlining_paper::path_bound::{self, Bound};

fn sizes(summary: &str) -> BTreeMap<String, usize> {
    summary
        .lines()
        .filter_map(|line| {
            let (name, rest) = line.split_once(" size: ")?;
            Some((name.to_string(), rest.trim().parse().ok()?))
        })
        .collect()
}

fn run_sizes(prog: &Program, k: usize) -> BTreeMap<String, usize> {
    sizes(&run_hybrid(prog, k).relation_sizes_summary())
}

/// Least-squares slope of `log|R|` against `log|P|`.
fn exponent(xs: &[f64], ys: &[f64]) -> f64 {
    let pts: Vec<(f64, f64)> = xs
        .iter()
        .zip(ys)
        .filter(|(_, y)| **y > 0.0)
        .map(|(x, y)| (x.ln(), y.ln()))
        .collect();
    let n = pts.len() as f64;
    let mx = pts.iter().map(|q| q.0).sum::<f64>() / n;
    let my = pts.iter().map(|q| q.1).sum::<f64>() / n;
    let num: f64 = pts.iter().map(|(x, y)| (x - mx) * (y - my)).sum();
    let den: f64 = pts.iter().map(|(x, _)| (x - mx).powi(2)).sum();
    num / den
}

/// Fit one relation over a family, against EDB size.
fn fit(rel: &str, points: &[(Program, usize)]) -> f64 {
    let xs: Vec<f64> = points.iter().map(|(p, _)| edb_size(p) as f64).collect();
    let ys: Vec<f64> = points
        .iter()
        .map(|(p, k)| run_sizes(p, *k)[rel] as f64)
        .collect();
    exponent(&xs, &ys)
}

/// The reference point for everything else. If these move, the analysis
/// derives a different amount of work on the paper's own example.
///
/// `resolve = 2` is worth reading twice: it is exactly the two call edges the
/// paper reports (`bar1 → Y.poly`, `bar2 → Z.poly`), one tuple each. Before
/// propagation was guarded on `blocked`, each adequate instance also spawned a
/// child in `service` that re-derived the same decision, and this pinned 4.
#[test]
fn figure1_relation_sizes_are_stable() {
    let m = run_sizes(&figure1::program(), 4);
    for (rel, want) in [
        ("edge", 40),
        ("points", 53),
        ("path_used", 65),
        ("pending", 4),
        ("pub_edge", 16),
        ("pub_points", 5),
        ("resolve", 2),
        ("settled", 2),
        ("root_map", 30),
        ("crit_map", 6),
    ] {
        assert_eq!(m[rel], want, "figure1 k=4: {rel} changed");
    }
}

/// Propagation up a linear call chain must cost a constant per level. Every
/// relation stays essentially linear in `|P|`; the fit is allowed a little
/// slack for the constant terms that dominate at these sizes.
#[test]
fn a_linear_call_chain_costs_a_constant_per_level() {
    let pts: Vec<(Program, usize)> =
        [4usize, 8, 16, 32].iter().map(|&n| (chain(n, 2), n + 2)).collect();
    for rel in ["edge", "points", "pending", "pub_edge", "root_map", "path_used"] {
        let d = fit(rel, &pts);
        assert!(d < 1.35, "chain: {rel} grows as |P|^{d:.2}, expected ~linear");
    }
    // One critical statement, one holder per level, and exactly one resolution
    // at the top where the receiver is finally pinned.
    assert_eq!(run_sizes(&chain(16, 2), 18)["pending"], 18);
    assert_eq!(run_sizes(&chain(16, 2), 18)["resolve"], 1);
}

/// The k-CFA call-string explosion, and the k-limit as the only thing that
/// contains it. `pending` counts call strings, and there are `2^d` of length
/// `d` here while the program grows linearly in `d`.
#[test]
fn call_strings_double_per_level_unless_k_caps_them() {
    for d in 1..=7usize {
        assert_eq!(
            run_sizes(&branching(d, 2), d + 2)["pending"],
            3 * (1 << d) - 1,
            "branching({d}) with k = d+2"
        );
    }
    // With k fixed, the same programs plateau.
    let capped: Vec<usize> =
        (3..=7).map(|d| run_sizes(&branching(d, 2), 3)["pending"]).collect();
    assert!(
        capped.windows(2).all(|w| w[0] == w[1]),
        "k = 3 should bound pending, got {capped:?}"
    );
}

/// `points` is the |paths| x |values| product, and nothing in Hybrid Inlining
/// changes that: a procedure with no calls at all is already quadratic.
#[test]
fn points_is_quadratic_in_a_single_procedure() {
    let pts: Vec<(Program, usize)> = [8usize, 16, 32, 64].iter().map(|&n| (alias(n), 0)).collect();
    let d = fit("points", &pts);
    assert!(d > 1.5, "alias: points grows as |P|^{d:.2}, expected ~quadratic");

    // pt(c_i) = {l_0..l_i}, so the c-chain alone contributes n(n+1)/2.
    let n = 32usize;
    let got = run_sizes(&alias(n), 0)["points"];
    assert!(
        got >= n * (n + 1) / 2,
        "alias({n}): points = {got}, expected at least n(n+1)/2"
    );
}

/// Suffix congruence is the other quadratic: within one procedure it pairs
/// every path prefix with every observed suffix.
#[test]
fn suffix_congruence_is_quadratic_within_a_procedure() {
    let pts: Vec<(Program, usize)> = [4usize, 8, 16, 32].iter().map(|&n| (fields(n), 0)).collect();
    for rel in ["edge", "points", "path_used"] {
        let d = fit(rel, &pts);
        assert!(d > 1.5, "fields: {rel} grows as |P|^{d:.2}, expected ~quadratic");
    }
}

/// The ordinary large program: many procedures, real pointer flow in each,
/// and nothing critical. The property worth pinning is that the two costs
/// stay separate — cost per procedure is a constant in `m`, and the local
/// quadratic in `w` does not escape into the published summary.
#[test]
fn many_procedures_cost_a_constant_each_when_nothing_is_critical() {
    let pts: Vec<(Program, usize)> =
        [8usize, 16, 32, 64].iter().map(|&m| (wide(m, 8), 0)).collect();
    for rel in ["edge", "points", "path_used", "pub_edge", "pub_points", "root_map"] {
        let d = fit(rel, &pts);
        assert!(d < 1.15, "wide: {rel} grows as |P|^{d:.2}, expected ~linear in m");
    }

    // No virtual call and no variable index, so none of the critical-statement
    // machinery is reachable at all — this is the family that isolates the
    // rest of the analysis from it.
    let m = run_sizes(&wide(32, 8), 0);
    for rel in ["critical", "pending", "resolve", "top", "adequate"] {
        assert_eq!(m[rel], 0, "wide: {rel} should be empty with nothing critical");
    }

    // Widening the local closure is quadratic inside each procedure, and the
    // published summary is one `pub_edge` per procedure regardless.
    let wpts: Vec<(Program, usize)> =
        [2usize, 4, 8, 16].iter().map(|&w| (wide(64, w), 0)).collect();
    assert!(fit("points", &wpts) > 1.5, "wide: local points should be quadratic in w");
    let flat: Vec<usize> =
        [2usize, 4, 8, 16].iter().map(|&w| run_sizes(&wide(64, w), 0)["pub_edge"]).collect();
    assert!(
        flat.windows(2).all(|x| x[0] == x[1]),
        "wide: pub_edge should not depend on the local closure, got {flat:?}"
    );
}

/// The deepest access path in `edge`.
fn deepest(h: &hybrid_inlining_paper::analysis::HybridAnalysis) -> usize {
    h.edge
        .iter()
        .flat_map(|(_, a, b)| [a.accessors.len(), b.accessors.len()])
        .max()
        .unwrap()
}

/// Access-path depth used to have no limit of its own: inlining appended one
/// accessor per call level, and `fields_chain(n)` reached depth `n + 1` with
/// nothing to stop it at any `n`. The `paths` bound is what stops it, and this
/// is where that shows.
///
/// `P_i` is `t = P_{i-1}(x); return t.f_i` — one accessor, and no procedure
/// spells two of them in a row — so the default vocabulary reaches depth 1,
/// and so does the analysis. The precision that buys termination is exactly
/// this: `ret@P_i ⊇ par_1@P_i.f0.f1…fi` is no longer derived.
#[test]
fn the_path_bound_holds_depth_where_the_syntax_puts_it() {
    for n in [2usize, 4, 8, 16] {
        assert_eq!(deepest(&run_hybrid(&fields_chain(n), 0)), 1, "fields_chain({n})");
    }
}

/// The depth is the *vocabulary's*, not a constant baked into the rules.
/// Folding admits concatenations no single procedure spells, and the analysis
/// follows the set up as far as it goes — to `fields_chain`'s exact answer,
/// `n + 1`, once the fold reaches it.
///
/// This is also the cost of asking: each fold level multiplies the vocabulary
/// by its own size, so `|paths|` here goes 10, 91, 820, 7381.
#[test]
fn folding_the_bound_buys_back_the_depth_it_gave_up() {
    for fold in [1usize, 2, 3] {
        let mut prog = fields_chain(8);
        path_bound::install(&mut prog, &Bound { fold, ..Bound::default() });
        assert_eq!(deepest(&run_hybrid(&prog, 0)), fold, "fields_chain(8), fold {fold}");
    }

    // `fields_chain(2)`'s deepest path is 3, and a deep enough fold reaches
    // it: the bound stops constraining before the analysis does.
    let mut prog = fields_chain(2);
    path_bound::install(&mut prog, &Bound { fold: 4, ..Bound::default() });
    assert_eq!(deepest(&run_hybrid(&prog, 0)), 3);
}

/// The generator `backflash-profile.md` identifies, in its smallest form:
/// `a = b` and `b = a.f` put a cycle in `edge` under a strict extension, so
/// congruence derives `a.f ⊇ b.f`, then `b.f ⊇ a.f.f`, then `a.f.f ⊇ b.f.f`,
/// forever. Two statements are enough, and no `k` and no call graph are
/// involved.
///
/// The program names `.f` and nothing longer, so that is where it stops. The
/// test terminating at all is half of what it asserts.
#[test]
fn a_cycle_under_a_field_load_no_longer_generates_paths_forever() {
    let mut prog = Program::default();
    prog.procedure = vec![(Proc::from("p"),)];
    prog.formal = vec![(Proc::from("p"), 1, Var::from("b"))];
    prog.ret = vec![(Proc::from("p"), Var::from("a"))];
    prog.in_proc = vec![
        (Stmt::from("S1"), Proc::from("p"), 0),
        (Stmt::from("S2"), Proc::from("p"), 1),
    ];
    prog.mov = vec![(Stmt::from("S1"), Var::from("a"), Var::from("b"))];
    prog.load_field = vec![(
        Stmt::from("S2"),
        Var::from("b"),
        Var::from("a"),
        Field::from("f"),
    )];

    assert_eq!(path_bound::for_program(&prog).len(), 2, "the vocabulary is ε and .f");
    assert_eq!(deepest(&run_hybrid(&prog, 2)), 1);
}

/// Direct recursion through a field load reaches a fixpoint rather than
/// appending `.f` forever. (It does so by deriving nothing for the recursive
/// call — a precision question, not a termination one.)
#[test]
fn recursion_through_a_field_load_terminates() {
    let h = run_hybrid(&recursive_field(), 2);
    assert!(h.edge.len() < 32, "recursive_field: edge = {}", h.edge.len());
    let deepest = h
        .edge
        .iter()
        .flat_map(|(_, a, b)| [a.accessors.len(), b.accessors.len()])
        .max()
        .unwrap();
    assert!(deepest <= 1, "recursive_field: access path grew to depth {deepest}");
}

/// The two parallel backends must derive exactly what the sequential one
/// does. This is what lets `benches/backends.rs` be read as a timing
/// comparison rather than a comparison of two different analyses. That bench
/// re-checks the same property at its own (much larger) sizes; this test
/// pins it cheaply, in a debug build, on every `cargo test`.
#[test]
fn parallel_backends_derive_the_same_relations() {
    let cases: Vec<(&str, Program, usize)> = vec![
        ("figure1", figure1::program(), 4),
        ("chain(4)", chain(4, 2), 6),
        ("fanin(4)", fanin(4, 2), 3),
        ("branching(3)", branching(3, 2), 5),
        ("fields(4)", fields(4), 0),
    ];
    for (label, prog, k) in &cases {
        let want = run_sizes(prog, *k);

        let mut par = ParallelHybridAnalysis::for_program(prog, *k);
        par.run();
        assert_eq!(sizes(&par.relation_sizes_summary()), want, "{label}: ascent_par disagrees");

        let mut inter = InterRuleHybridAnalysis::for_program(prog, *k);
        inter.run();
        assert_eq!(
            sizes(&inter.relation_sizes_summary()),
            want,
            "{label}: inter_rule_parallelism disagrees"
        );
    }
}
