//! The default access-path bound: which suffixes a program's *syntax* asks for.
//!
//! [`crate::ir::edb`]'s `paths` relation is the analysis's whole access-path
//! vocabulary, and the analysis does not care where it comes from. This module
//! is the answer used when a program does not supply one.
//!
//! # Why there has to be a bound
//!
//! The abstract domain of §4.1.1 is `𝕍 × (𝔽 ∪ ℂ)*` — access paths of
//! unbounded length — and suffix congruence closes over it:
//!
//! ```text
//! ω ⊇ ω′   and   ω·ρ observed   ⟹   ω·ρ ⊇ ω′·ρ
//! ```
//!
//! The observed path `ω·ρ` may itself be one congruence invented a moment
//! ago, so the rule feeds itself. One cycle in the constraint graph plus one
//! strict extension is then enough to generate paths forever: given `a ⊇ b`
//! and `b ⊇ a.f`, congruence derives `a.f ⊇ b.f`, then `b.f ⊇ a.f.f`, then
//! `a.f.f ⊇ b.f.f`, without limit. Such cycles are ordinary — on
//! `backflash.apk` a single 2039-statement procedure has 25,410 paths sitting
//! on one, and 85% of the paths the closure invents repeat an accessor
//! (`x.wl.wl.wl.wl.length[]`), which no heap object can satisfy. There is no
//! fixpoint to reach.
//!
//! # The bound
//!
//! The vocabulary is the set of suffixes the program's own statements spell
//! out, *concatenated along local data flow*. If `t = x.foo` and then
//! `u = t.bar`, the program has named the compound path `x.foo.bar`, and the
//! analysis may build it. Nothing has named `x.wl.wl`, so it may not.
//!
//! One statement contributes one accessor. A chain of statements contributes
//! their concatenation, in the order data flows through them:
//!
//! ```text
//! S1: t = x.foo        step   t --.foo@1--> x
//! S2: u = t.bar        step   u --.bar@2--> t
//!
//! ε hangs off u;  S2 hangs  .bar     off t
//!                 S1 hangs  .foo.bar off x
//! ```
//!
//! Read a step `v --α@ℓ--> w` as: whatever suffix `ρ` the program hangs off
//! `v`, statement `ℓ` also hangs `α·ρ` off `w`. Loads, stores and moves each
//! give one:
//!
//! | statement | step |
//! |---|---|
//! | `to = base.f` | `to --.f--> base` |
//! | `base.f = from` | `from --.f--> base` |
//! | `to = base[c]` | `to --[c]--> base` |
//! | `base[c] = from` | `from --[c]--> base` |
//! | `to = base[i]` | `to --α--> base`, α over every index the program can decide to |
//! | `base[i] = from` | `from --α--> base`, likewise |
//! | `to = from` | `to --ε--> from` |
//!
//! Two conditions gate a step, and between them they say "this is the same
//! value". A suffix discovered at line `ℓ''` attaches at line `ℓ` only if
//!
//! 1. `ℓ < ℓ''` — the statement being extended comes first, and
//! 2. the variable linking them is not redefined anywhere in `(ℓ, ℓ'')`.
//!
//! # Why it terminates
//!
//! Condition 1 alone is the termination argument: `ℓ` strictly decreases
//! along a chain, so a chain visits each statement of a procedure at most
//! once and the longest suffix is bounded by the procedure's length. No
//! control-flow graph is needed for that — `in_proc`'s statement order is
//! enough, and a loop's back edge is simply not a step, because it would use
//! a variable before the statement that defines it.
//!
//! Condition 2 is what makes the result *small*. Without it, "the variable
//! `v` at line 3" and "the variable `v` at line 500" are the same node, and
//! on register-machine IR — where a Dalvik method reuses `v0` dozens of times
//! for unrelated values — every later use chains to every earlier statement
//! that named the register. The fan multiplies along a chain and the set
//! stops being computable: on `backflash.apk` the set without condition 2
//! does not finish. With it, a use reaches exactly the one definition that
//! reaches *it*, and the whole 2375-procedure program has a vocabulary of a
//! few dozen suffixes.
//!
//! # What it gives up
//!
//! Concatenation is local to a procedure, so a suffix assembled *across a
//! call* is not in the set. [`crate::families::fields_chain`] is that shape —
//! `P_i(x) { t = P_{i-1}(x); return t.f_i }`, whose exact summary is
//! `ret@P_i ⊇ par_1@P_i.f0.f1…fi` — and under this bound its paths stop at
//! depth 1, because no single procedure spells `.f0.f1`. That is the same
//! restriction that makes the set finite: chaining across calls is chaining
//! around the call graph, and the call graph has cycles.
//!
//! [`Bound::fold`] buys levels of it back, at a cost: folding closes the set
//! under concatenation, so `fold = 2` admits `σ·τ` for any two locally-derived
//! `σ`, `τ` and squares the vocabulary. It defaults to 1, i.e. off.

use std::collections::{BTreeMap, BTreeSet};

use crate::access_path::{Accessor, Suffix};
use crate::ir::{Const, Line, Proc, Program, Var};

/// Knobs on [`syntactic`].
#[derive(Clone, Debug)]
pub struct Bound {
    /// Drop any suffix longer than this. `None` lets the syntax decide, which
    /// it always does — chains are bounded by procedure length — but a cap is
    /// the cheap way to sweep precision against cost.
    pub max_depth: Option<usize>,
    /// How many locally-derived suffixes may be concatenated. `1` is the
    /// syntactic set itself; `2` also admits every `σ·τ`, and so on. Each
    /// level multiplies the vocabulary by its own size, so raise it with care.
    pub fold: usize,
}

impl Default for Bound {
    fn default() -> Self {
        Self {
            max_depth: None,
            fold: 1,
        }
    }
}

/// One link of local data flow, labelled with what it prepends.
///
/// `accessors` is empty for a move, which passes a suffix through unchanged,
/// and holds more than one entry for a variable index, which the analysis may
/// decide to any of several accessors.
struct Step {
    line: Line,
    src: Var,
    dst: Var,
    accessors: Vec<Accessor>,
}

/// One procedure's statements, as the two things the walk needs: the steps,
/// and where each variable is overwritten.
#[derive(Default)]
struct Body {
    steps: Vec<Step>,
    /// `defines[ℓ]` is the variables statement `ℓ` assigns. Crossing one ends
    /// every chain through that variable: what a later line hung off it
    /// belonged to a different value.
    defines: BTreeMap<Line, Vec<Var>>,
}

/// The access-path bound to run `prog` under: whatever it carries in
/// `paths`, and otherwise [`syntactic`] under the default [`Bound`].
///
/// A program with an empty `paths` is taken to mean "no bound was chosen",
/// not "no path is admissible" — the latter would forbid every field access,
/// and is spelled by supplying just `ε`.
pub fn for_program(prog: &Program) -> BTreeSet<Suffix> {
    if prog.paths.is_empty() {
        syntactic(prog, &Bound::default())
    } else {
        prog.paths.iter().map(|(s,)| s.clone()).collect()
    }
}

/// Compute the bound and store it on the program, so that later runs (and
/// anything that inspects the EDB) see the same set.
pub fn install(prog: &mut Program, bound: &Bound) {
    prog.paths = syntactic(prog, bound).into_iter().map(|s| (s,)).collect();
}

/// The suffixes `prog`'s statements spell out, concatenated along local data
/// flow. Always contains `ε`, and is prefix-closed.
pub fn syntactic(prog: &Program, bound: &Bound) -> BTreeSet<Suffix> {
    let mut out = BTreeSet::from([Suffix::empty()]);
    let indices = decidable_indices(prog);

    for (_, body) in bodies(prog, &indices) {
        collect(body, bound, &mut out);
    }
    fold(&mut out, bound);
    out
}

/// The accessors a variable-index access may be decided to: `[π]`, plus `[c]`
/// for every constant the program mentions.
///
/// A `[c]` is chosen from the index's points-to set, which no syntactic pass
/// can predict — Figure 5's `getP(map, key)` resolves `map[key]` to
/// `par_1@getP["cur"]` only once a *caller* pins `key`. So the whole constant
/// vocabulary is admitted at an index position. It costs nothing on a program
/// with no variable indices, which is every program a CTADL front end
/// produces.
fn decidable_indices(prog: &Program) -> Vec<Accessor> {
    let mut consts: BTreeSet<Const> = BTreeSet::new();
    consts.extend(prog.const_assign.iter().map(|(_, _, c)| c.clone()));
    consts.extend(prog.load_index_const.iter().map(|(_, _, _, c)| c.clone()));
    consts.extend(prog.store_index_const.iter().map(|(_, _, c, _)| c.clone()));

    std::iter::once(Accessor::IndexUnknown)
        .chain(consts.into_iter().map(Accessor::Index))
        .collect()
}

/// Every procedure's body, as steps plus definition sites. A statement with no
/// `in_proc` fact has no place in the order and so contributes nothing.
fn bodies(prog: &Program, indices: &[Accessor]) -> BTreeMap<Proc, Body> {
    let mut at: BTreeMap<&str, (Proc, Line)> = BTreeMap::new();
    for (s, p, n) in &prog.in_proc {
        at.insert(s.as_ref(), (p.clone(), *n));
    }

    let mut out: BTreeMap<Proc, Body> = BTreeMap::new();
    let locate = |stmt: &crate::ir::Stmt| at.get(stmt.as_ref()).cloned();

    let mut steps: Vec<(Proc, Step)> = Vec::new();
    let mut defs: Vec<(Proc, Line, Var)> = Vec::new();

    {
        let mut step = |stmt, src: &Var, dst: &Var, accessors: Vec<Accessor>| {
            if let Some((p, line)) = locate(stmt) {
                steps.push((
                    p,
                    Step {
                        line,
                        src: src.clone(),
                        dst: dst.clone(),
                        accessors,
                    },
                ));
            }
        };

        for (s, to, from) in &prog.mov {
            step(s, to, from, Vec::new());
        }
        for (s, to, base, f) in &prog.load_field {
            step(s, to, base, vec![Accessor::Field(f.clone())]);
        }
        for (s, base, f, from) in &prog.store_field {
            step(s, from, base, vec![Accessor::Field(f.clone())]);
        }
        for (s, to, base, c) in &prog.load_index_const {
            step(s, to, base, vec![Accessor::Index(c.clone())]);
        }
        for (s, base, c, from) in &prog.store_index_const {
            step(s, from, base, vec![Accessor::Index(c.clone())]);
        }
        for (s, to, base, _) in &prog.load_index_var {
            step(s, to, base, indices.to_vec());
        }
        for (s, base, _, from) in &prog.store_index_var {
            step(s, from, base, indices.to_vec());
        }
    }

    // Everything that overwrites a variable, whether or not it carries a
    // suffix: an allocation or a call result ends a chain just as a load does.
    {
        let mut define = |stmt, v: &Var| {
            if let Some((p, line)) = locate(stmt) {
                defs.push((p, line, v.clone()));
            }
        };
        for (s, to, _) in &prog.mov {
            define(s, to);
        }
        for (s, v, _) in &prog.alloc {
            define(s, v);
        }
        for (s, v, _) in &prog.const_assign {
            define(s, v);
        }
        for (s, to, _, _) in &prog.load_field {
            define(s, to);
        }
        for (s, to, _, _) in &prog.load_static {
            define(s, to);
        }
        for (s, to, _, _) in &prog.load_index_const {
            define(s, to);
        }
        for (s, to, _, _) in &prog.load_index_var {
            define(s, to);
        }
        for (s, v) in &prog.bind_ret {
            define(s, v);
        }
    }

    for (p, st) in steps {
        out.entry(p).or_default().steps.push(st);
    }
    for (p, line, v) in defs {
        out.entry(p)
            .or_default()
            .defines
            .entry(line)
            .or_default()
            .push(v);
    }
    out
}

/// Walk one procedure from its last statement to its first, accumulating what
/// each variable may carry.
///
/// The descending order is the termination argument: when line `ℓ` is
/// processed, `carried` holds exactly the suffixes produced at lines above
/// `ℓ`, so extending one takes a strictly decreasing step and no chain can
/// close a cycle. Steps that share a line are resolved against the state
/// *before* the line, so they cannot chain to each other either.
///
/// Crossing a definition of `v` clears `carried[v]`: below that line, `v`
/// holds a different value, and what the lines above hung off it says nothing
/// about this one. The clearing happens between reading `carried` and writing
/// the batch back, which is what makes `v = v.f` come out right — the read
/// sees the value being defined, the write lands on the base.
fn collect(body: Body, bound: &Bound, out: &mut BTreeSet<Suffix>) {
    let Body { mut steps, defines } = body;
    steps.sort_by_key(|s| std::cmp::Reverse(s.line));
    let mut carried: BTreeMap<Var, BTreeSet<Suffix>> = BTreeMap::new();
    let empty = BTreeSet::new();

    let mut i = 0;
    while i < steps.len() {
        let line = steps[i].line;
        let mut batch: Vec<(Var, Suffix)> = Vec::new();

        while i < steps.len() && steps[i].line == line {
            let step = &steps[i];
            let below = carried.get(&step.src).unwrap_or(&empty);
            // `ε` is carried by every variable and is never stored, so it is
            // supplied here rather than held in `carried`.
            for rho in std::iter::once(&Suffix::empty()).chain(below) {
                if step.accessors.is_empty() {
                    if !rho.is_empty() {
                        batch.push((step.dst.clone(), rho.clone()));
                    }
                    continue;
                }
                if bound.max_depth.is_some_and(|d| rho.len() >= d) {
                    continue;
                }
                for a in &step.accessors {
                    batch.push((step.dst.clone(), rho.prepended(a)));
                }
            }
            i += 1;
        }

        for v in defines.get(&line).into_iter().flatten() {
            carried.remove(v);
        }
        for (v, suffix) in batch {
            out.insert(suffix.clone());
            carried.entry(v).or_default().insert(suffix);
        }
    }
}

/// Close the set under concatenation, [`Bound::fold`] factors deep.
fn fold(out: &mut BTreeSet<Suffix>, bound: &Bound) {
    if bound.fold <= 1 {
        return;
    }
    let base: Vec<Suffix> = out.iter().filter(|s| !s.is_empty()).cloned().collect();
    let mut frontier = base.clone();
    for _ in 1..bound.fold {
        let mut next = Vec::new();
        for head in &frontier {
            for tail in &base {
                if bound.max_depth.is_some_and(|d| head.len() + tail.len() > d) {
                    continue;
                }
                let joined = head.extended(tail.as_slice());
                if out.insert(joined.clone()) {
                    next.push(joined);
                }
            }
        }
        if next.is_empty() {
            break;
        }
        frontier = next;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Field, Stmt};

    fn v(s: &str) -> Var {
        Var::from(s)
    }

    fn shown(set: &BTreeSet<Suffix>) -> Vec<String> {
        set.iter().map(ToString::to_string).collect()
    }

    /// `t = x.foo; u = t.bar` names `x.foo.bar`, and every prefix of it.
    #[test]
    fn consecutive_loads_are_concatenated() {
        let mut prog = Program::default();
        prog.in_proc = vec![
            (Stmt::from("S1"), Proc::from("p"), 0),
            (Stmt::from("S2"), Proc::from("p"), 1),
        ];
        prog.load_field = vec![
            (Stmt::from("S1"), v("t"), v("x"), Field::from("foo")),
            (Stmt::from("S2"), v("u"), v("t"), Field::from("bar")),
        ];

        assert_eq!(
            shown(&syntactic(&prog, &Bound::default())),
            ["ε", ".bar", ".foo", ".foo.bar"]
        );
    }

    /// The same two statements in the other order are a *use before def*: `t`
    /// is read at line 0 and written at line 1, which only a back edge can
    /// arrange. The step is not taken, so `.foo.bar` is not admitted — this is
    /// what keeps a loop from generating suffixes forever.
    #[test]
    fn a_use_before_its_definition_does_not_concatenate() {
        let mut prog = Program::default();
        prog.in_proc = vec![
            (Stmt::from("S1"), Proc::from("p"), 1),
            (Stmt::from("S2"), Proc::from("p"), 0),
        ];
        prog.load_field = vec![
            (Stmt::from("S1"), v("t"), v("x"), Field::from("foo")),
            (Stmt::from("S2"), v("u"), v("t"), Field::from("bar")),
        ];

        assert_eq!(
            shown(&syntactic(&prog, &Bound::default())),
            ["ε", ".bar", ".foo"]
        );
    }

    /// Between the two, `t` is overwritten, so the `.h` hung off the second
    /// `t` says nothing about the first. Without this condition every later
    /// use of a register chains to every earlier statement that named it, and
    /// on real IR the set stops being computable.
    #[test]
    fn a_redefinition_ends_the_chain_through_a_variable() {
        let mut prog = Program::default();
        prog.in_proc = (0..3)
            .map(|n| (Stmt::from(format!("S{n}")), Proc::from("p"), n))
            .collect();
        prog.load_field = vec![
            (Stmt::from("S0"), v("t"), v("x"), Field::from("f")),
            (Stmt::from("S1"), v("t"), v("y"), Field::from("g")),
            (Stmt::from("S2"), v("u"), v("t"), Field::from("h")),
        ];

        // `.g.h` is the live chain; `.f.h` is the one the reused name would
        // have manufactured.
        assert_eq!(
            shown(&syntactic(&prog, &Bound::default())),
            ["ε", ".f", ".g", ".g.h", ".h"]
        );
    }

    /// `x.f = t` with `t` loaded from later: the store's own suffix extends by
    /// whatever is hung off what it stores, which is how a write through a
    /// local reaches the published summary.
    #[test]
    fn a_store_carries_the_suffixes_of_what_it_stores() {
        let mut prog = Program::default();
        prog.in_proc = vec![
            (Stmt::from("S1"), Proc::from("p"), 0),
            (Stmt::from("S2"), Proc::from("p"), 1),
        ];
        prog.store_field = vec![(Stmt::from("S1"), v("x"), Field::from("f"), v("t"))];
        prog.load_field = vec![(Stmt::from("S2"), v("u"), v("t"), Field::from("g"))];

        assert_eq!(
            shown(&syntactic(&prog, &Bound::default())),
            ["ε", ".f", ".f.g", ".g"]
        );
    }

    /// A move is a step that prepends nothing, so it lengthens no path but
    /// lets one pass through.
    #[test]
    fn a_move_relays_a_suffix_without_growing_it() {
        let mut prog = Program::default();
        prog.in_proc = vec![
            (Stmt::from("S1"), Proc::from("p"), 0),
            (Stmt::from("S2"), Proc::from("p"), 1),
            (Stmt::from("S3"), Proc::from("p"), 2),
        ];
        prog.load_field = vec![
            (Stmt::from("S1"), v("t"), v("x"), Field::from("foo")),
            (Stmt::from("S3"), v("u"), v("s"), Field::from("bar")),
        ];
        prog.mov = vec![(Stmt::from("S2"), v("s"), v("t"))];

        assert!(shown(&syntactic(&prog, &Bound::default())).contains(&".foo.bar".to_string()));
    }

    /// Two procedures do not concatenate with each other, whatever their line
    /// numbers say.
    #[test]
    fn concatenation_does_not_cross_a_procedure() {
        let mut prog = Program::default();
        prog.in_proc = vec![
            (Stmt::from("S1"), Proc::from("p"), 0),
            (Stmt::from("S2"), Proc::from("q"), 1),
        ];
        prog.load_field = vec![
            (Stmt::from("S1"), v("t"), v("x"), Field::from("foo")),
            (Stmt::from("S2"), v("u"), v("t"), Field::from("bar")),
        ];

        assert_eq!(
            shown(&syntactic(&prog, &Bound::default())),
            ["ε", ".bar", ".foo"]
        );
    }

    /// A repeated field is admitted only where the program actually writes it
    /// twice in a row — which is the case the profile of `backflash.apk` says
    /// never happens, and where 85% of that run's paths came from.
    #[test]
    fn a_field_does_not_repeat_unless_the_program_repeats_it() {
        let mut prog = Program::default();
        prog.in_proc = vec![
            (Stmt::from("S1"), Proc::from("p"), 0),
            (Stmt::from("S2"), Proc::from("p"), 1),
        ];
        prog.load_field = vec![
            (Stmt::from("S1"), v("t"), v("x"), Field::from("wl")),
            (Stmt::from("S2"), v("u"), v("y"), Field::from("wl")),
        ];

        let set = syntactic(&prog, &Bound::default());
        assert_eq!(shown(&set), ["ε", ".wl"]);
        assert!(!set.contains(&Suffix::from(vec![
            Accessor::Field(Field::from("wl")),
            Accessor::Field(Field::from("wl")),
        ])));
    }

    /// `max_depth` truncates the set; `fold` widens it.
    #[test]
    fn the_knobs_move_the_set_in_the_directions_they_claim() {
        let mut prog = Program::default();
        prog.in_proc = (0..3)
            .map(|n| (Stmt::from(format!("S{n}")), Proc::from("p"), n))
            .collect();
        prog.load_field = vec![
            (Stmt::from("S0"), v("a"), v("x"), Field::from("f0")),
            (Stmt::from("S1"), v("b"), v("a"), Field::from("f1")),
            (Stmt::from("S2"), v("c"), v("b"), Field::from("f2")),
        ];

        let all = syntactic(&prog, &Bound::default());
        assert!(all.contains(&Suffix::from(vec![
            Accessor::Field(Field::from("f0")),
            Accessor::Field(Field::from("f1")),
            Accessor::Field(Field::from("f2")),
        ])));

        let capped = syntactic(
            &prog,
            &Bound {
                max_depth: Some(2),
                ..Bound::default()
            },
        );
        assert!(capped.iter().all(|s| s.len() <= 2));
        assert!(capped.len() < all.len());

        // `.f2.f0` is two locally-derived suffixes back to back, and no
        // procedure spells it: only folding admits it.
        let joined = Suffix::from(vec![
            Accessor::Field(Field::from("f2")),
            Accessor::Field(Field::from("f0")),
        ]);
        assert!(!all.contains(&joined));
        assert!(
            syntactic(
                &prog,
                &Bound {
                    fold: 2,
                    ..Bound::default()
                }
            )
            .contains(&joined)
        );
    }

    /// A program that supplies its own set is taken at its word.
    #[test]
    fn a_supplied_set_is_used_verbatim() {
        let mut prog = Program::default();
        prog.in_proc = vec![(Stmt::from("S1"), Proc::from("p"), 0)];
        prog.load_field = vec![(Stmt::from("S1"), v("t"), v("x"), Field::from("foo"))];
        prog.paths = vec![(Suffix::empty(),)];

        assert_eq!(shown(&for_program(&prog)), ["ε"]);
        prog.paths.clear();
        assert_eq!(shown(&for_program(&prog)), ["ε", ".foo"]);
    }
}
