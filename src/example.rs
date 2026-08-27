//! Figure 1 of the paper, encoded in the [`crate::ir`] schema.
//!
//! ```java
//!  1 public class Obj{}
//!  2 public interface X{
//!  3   Obj poly(Obj obj);
//!  4 }
//!  5 public class Y implements X{
//!  7   public Obj poly(Obj obj){
//!  8     return obj;
//!  9   }
//! 10 }
//! 11 public class Z implements X{
//! 13   public Obj poly(Obj obj){
//! 14     return new Obj();
//! 15   }
//! 16 }
//! 17 public class FacadeImpl{
//! 18   public X id(X x){
//! 19     X tv = x;
//! 20     return tv;
//! 21   }
//! 22   public Obj foo(X x, Obj obj){
//! 24     X tx = id(x);
//! 25     return tx.poly(obj);
//! 26   }
//! 27   public Obj mid(X x, Obj obj){
//! 28     return foo(x, obj);
//! 29   }
//! 30   public Obj bar1(Obj obj){
//! 31     return mid(new Y(), obj);
//! 32   }
//! 33   public Obj bar2(Obj obj){
//! 34     return mid(new Z(), obj);
//! 35   }
//! 36   public void service(){
//! 37     Obj first = new Obj();
//! 38     Obj second = bar1(first);
//! 39     Obj third = bar2(first);
//! 40     assert(first == second);
//! 41     assert(first != third);
//! 42   }
//! 43 }
//! ```
//!
//! Nested expressions are flattened into temporaries (`t31`, `r25`, ...) and
//! every statement gets a label naming its source line. `service()` is the
//! entry procedure; the interesting statement is `L25`, the virtual call whose
//! callee is only pinned down once the context fixes `tx`'s type.

use crate::ir::*;

fn p(x: &str) -> Proc {
    x.into()
}
fn s(x: &str) -> Stmt {
    x.into()
}
fn v(x: &str) -> Var {
    x.into()
}
fn l(x: &str) -> Alloc {
    x.into()
}
fn t(x: &str) -> Type {
    x.into()
}
fn g(x: &str) -> Sig {
    x.into()
}

/// Build the EDB for Figure 1.
pub fn figure1() -> Program {
    let mut prog = Program::default();

    // -- types ------------------------------------------------------------
    prog.direct_subtype = vec![(t("Y"), t("X")), (t("Z"), t("X"))];

    prog.lookup = vec![
        (t("Y"), g("poly(Obj)"), p("Y.poly")),
        (t("Z"), g("poly(Obj)"), p("Z.poly")),
    ];

    // -- procedures -------------------------------------------------------
    prog.procedure = [
        "Y.poly",
        "Z.poly",
        "FacadeImpl.id",
        "FacadeImpl.foo",
        "FacadeImpl.mid",
        "FacadeImpl.bar1",
        "FacadeImpl.bar2",
        "FacadeImpl.service",
    ]
    .map(|n| (p(n),))
    .to_vec();

    prog.proc_type = vec![
        (p("Y.poly"), t("Y")),
        (p("Z.poly"), t("Z")),
        (p("FacadeImpl.id"), t("FacadeImpl")),
        (p("FacadeImpl.foo"), t("FacadeImpl")),
        (p("FacadeImpl.mid"), t("FacadeImpl")),
        (p("FacadeImpl.bar1"), t("FacadeImpl")),
        (p("FacadeImpl.bar2"), t("FacadeImpl")),
        (p("FacadeImpl.service"), t("FacadeImpl")),
    ];

    prog.proc_sig = vec![(p("Y.poly"), g("poly(Obj)")), (p("Z.poly"), g("poly(Obj)"))];

    prog.entry = vec![(p("FacadeImpl.service"),)];

    // Parameter 0 is the receiver (`this`).
    prog.formal = vec![
        (p("Y.poly"), 0, v("this@Y.poly")),
        (p("Y.poly"), 1, v("obj@Y.poly")),
        (p("Z.poly"), 0, v("this@Z.poly")),
        (p("Z.poly"), 1, v("obj@Z.poly")),
        (p("FacadeImpl.id"), 0, v("this@id")),
        (p("FacadeImpl.id"), 1, v("x@id")),
        (p("FacadeImpl.foo"), 0, v("this@foo")),
        (p("FacadeImpl.foo"), 1, v("x@foo")),
        (p("FacadeImpl.foo"), 2, v("obj@foo")),
        (p("FacadeImpl.mid"), 0, v("this@mid")),
        (p("FacadeImpl.mid"), 1, v("x@mid")),
        (p("FacadeImpl.mid"), 2, v("obj@mid")),
        (p("FacadeImpl.bar1"), 0, v("this@bar1")),
        (p("FacadeImpl.bar1"), 1, v("obj@bar1")),
        (p("FacadeImpl.bar2"), 0, v("this@bar2")),
        (p("FacadeImpl.bar2"), 1, v("obj@bar2")),
        (p("FacadeImpl.service"), 0, v("this@service")),
    ];

    prog.ret = vec![
        (p("Y.poly"), v("obj@Y.poly")),   // 8
        (p("Z.poly"), v("t14")),          // 14
        (p("FacadeImpl.id"), v("tv")),    // 20
        (p("FacadeImpl.foo"), v("r25")),  // 25
        (p("FacadeImpl.mid"), v("r28")),  // 28
        (p("FacadeImpl.bar1"), v("r31")), // 31
        (p("FacadeImpl.bar2"), v("r34")), // 34
    ];

    // -- statements -------------------------------------------------------
    prog.in_proc = vec![
        (s("L14"), p("Z.poly"), 0),
        (s("L19"), p("FacadeImpl.id"), 0),
        (s("L24"), p("FacadeImpl.foo"), 0),
        (s("L25"), p("FacadeImpl.foo"), 1),
        (s("L28"), p("FacadeImpl.mid"), 0),
        (s("L31a"), p("FacadeImpl.bar1"), 0),
        (s("L31b"), p("FacadeImpl.bar1"), 1),
        (s("L34a"), p("FacadeImpl.bar2"), 0),
        (s("L34b"), p("FacadeImpl.bar2"), 1),
        (s("L37"), p("FacadeImpl.service"), 0),
        (s("L38"), p("FacadeImpl.service"), 1),
        (s("L39"), p("FacadeImpl.service"), 2),
    ];

    prog.alloc = vec![
        (s("L14"), v("t14"), l("l14")),   // new Obj() in Z.poly
        (s("L31a"), v("t31"), l("l31")),  // new Y()
        (s("L34a"), v("t34"), l("l34")),  // new Z()
        (s("L37"), v("first"), l("l37")), // new Obj()
    ];

    prog.alloc_type = vec![
        (l("l14"), t("Obj")),
        (l("l31"), t("Y")),
        (l("l34"), t("Z")),
        (l("l37"), t("Obj")),
    ];

    prog.mov = vec![(s("L19"), v("tv"), v("x@id"))]; // X tv = x;

    prog.direct_call = vec![
        (s("L24"), p("FacadeImpl.id")),
        (s("L28"), p("FacadeImpl.foo")),
        (s("L31b"), p("FacadeImpl.mid")),
        (s("L34b"), p("FacadeImpl.mid")),
        (s("L38"), p("FacadeImpl.bar1")),
        (s("L39"), p("FacadeImpl.bar2")),
    ];

    // The one critical call: tx.poly(obj).
    prog.virtual_call = vec![(s("L25"), v("tx"), g("poly(Obj)"))];

    prog.actual_arg = vec![
        (s("L24"), 0, v("this@foo")),
        (s("L24"), 1, v("x@foo")),
        (s("L25"), 0, v("tx")),
        (s("L25"), 1, v("obj@foo")),
        (s("L28"), 0, v("this@mid")),
        (s("L28"), 1, v("x@mid")),
        (s("L28"), 2, v("obj@mid")),
        (s("L31b"), 0, v("this@bar1")),
        (s("L31b"), 1, v("t31")),
        (s("L31b"), 2, v("obj@bar1")),
        (s("L34b"), 0, v("this@bar2")),
        (s("L34b"), 1, v("t34")),
        (s("L34b"), 2, v("obj@bar2")),
        (s("L38"), 0, v("this@service")),
        (s("L38"), 1, v("first")),
        (s("L39"), 0, v("this@service")),
        (s("L39"), 1, v("first")),
    ];

    prog.bind_ret = vec![
        (s("L24"), v("tx")),
        (s("L25"), v("r25")),
        (s("L28"), v("r28")),
        (s("L31b"), v("r31")),
        (s("L34b"), v("r34")),
        (s("L38"), v("second")),
        (s("L39"), v("third")),
    ];

    prog
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn every_statement_is_in_exactly_one_procedure() {
        let prog = figure1();
        let declared: HashSet<&Stmt> = prog.in_proc.iter().map(|(s, _, _)| s).collect();
        assert_eq!(
            declared.len(),
            prog.in_proc.len(),
            "duplicate statement label"
        );

        let mentioned = prog
            .alloc
            .iter()
            .map(|(s, ..)| s)
            .chain(prog.mov.iter().map(|(s, ..)| s))
            .chain(prog.direct_call.iter().map(|(s, ..)| s))
            .chain(prog.virtual_call.iter().map(|(s, ..)| s))
            .chain(prog.actual_arg.iter().map(|(s, ..)| s))
            .chain(prog.bind_ret.iter().map(|(s, ..)| s));
        for st in mentioned {
            assert!(declared.contains(st), "{st} has no in_proc fact");
        }
    }

    #[test]
    fn callsite_arities_match_the_callee() {
        let prog = figure1();
        let arity = |proc: &Proc| prog.formal.iter().filter(|(q, ..)| q == proc).count();
        for (site, callee) in &prog.direct_call {
            let args = prog.actual_arg.iter().filter(|(s, ..)| s == site).count();
            assert_eq!(args, arity(callee), "arity mismatch at {site} -> {callee}");
        }
    }

    #[test]
    fn the_virtual_callsite_dispatches_to_both_implementations() {
        let prog = figure1();
        let (_, _, sig) = &prog.virtual_call[0];
        let targets: Vec<_> = prog
            .lookup
            .iter()
            .filter(|(_, g, _)| g == sig)
            .map(|(_, _, p)| p.to_string())
            .collect();
        assert_eq!(targets, vec!["Y.poly", "Z.poly"]);
    }

    #[test]
    fn running_the_empty_program_changes_nothing() {
        let mut prog = figure1();
        let calls = prog.direct_call.len();
        prog.run(); // no rules yet
        assert_eq!(prog.direct_call.len(), calls);
    }
}
