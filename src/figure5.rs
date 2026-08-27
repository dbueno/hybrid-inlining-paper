//! Figure 5 of the paper — the `lv[v]` half of Hybrid Inlining.
//!
//! ```java
//!  1 getP(map, key){
//!  2   return map[key];
//!  3 }
//!  4 setP(map, key, v){
//!  5   map[key] = v;
//!  6 }
//!  7 build(u){
//!  8   v = new;
//!  9   setP(v, "old",
//! 10     getP(u, "cur"));
//! 11   return v;
//! 12 }
//! ```
//!
//! Neither map access can be summarized under ⊤: the index lives in `key`,
//! whose points-to set contains the free variable `par_2` while `getP`/`setP`
//! are being summarized. The paper notes that disjunction is not an option
//! here either, since the values `key` may take are unbounded — so this is a
//! case only Hybrid Inlining handles.
//!
//! Nested expressions are flattened into temporaries, and parameter 0 is the
//! receiver, so `map` is `par_1`, `key` is `par_2` and `u` is `par_1@build`,
//! matching the labels in Figure 6.

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

/// Build the EDB for Figure 5.
pub fn program() -> Program {
    let mut prog = Program::default();

    prog.procedure = ["getP", "setP", "build"].map(|n| (p(n),)).to_vec();
    prog.entry = vec![(p("build"),)];

    prog.formal = vec![
        (p("getP"), 0, v("this@getP")),
        (p("getP"), 1, v("map@getP")),
        (p("getP"), 2, v("key@getP")),
        (p("setP"), 0, v("this@setP")),
        (p("setP"), 1, v("map@setP")),
        (p("setP"), 2, v("key@setP")),
        (p("setP"), 3, v("val@setP")),
        (p("build"), 0, v("this@build")),
        (p("build"), 1, v("u@build")),
    ];

    prog.ret = vec![(p("getP"), v("t2")), (p("build"), v("v"))];

    prog.in_proc = vec![
        (s("L2"), p("getP"), 0),
        (s("L5"), p("setP"), 0),
        (s("L8"), p("build"), 0),
        (s("L9a"), p("build"), 1),
        (s("L9b"), p("build"), 2),
        (s("L9c"), p("build"), 3),
        (s("L9d"), p("build"), 4),
    ];

    // L2: return map[key] — a critical read, the index is a variable.
    prog.load_index_var = vec![(s("L2"), v("t2"), v("map@getP"), v("key@getP"))];
    // L5: map[key] = v — a critical write.
    prog.store_index_var = vec![(s("L5"), v("map@setP"), v("key@setP"), v("val@setP"))];

    prog.alloc = vec![(s("L8"), v("v"), Alloc::from("l8"))];
    prog.alloc_type = vec![(Alloc::from("l8"), Type::from("Obj"))];

    prog.const_assign = vec![
        (s("L9a"), v("c_cur"), Const::from("\"cur\"")),
        (s("L9c"), v("c_old"), Const::from("\"old\"")),
    ];

    prog.direct_call = vec![(s("L9b"), p("getP")), (s("L9d"), p("setP"))];

    prog.actual_arg = vec![
        (s("L9b"), 0, v("this@build")),
        (s("L9b"), 1, v("u@build")),
        (s("L9b"), 2, v("c_cur")),
        (s("L9d"), 0, v("this@build")),
        (s("L9d"), 1, v("v")),
        (s("L9d"), 2, v("c_old")),
        (s("L9d"), 3, v("t9")),
    ];

    prog.bind_ret = vec![(s("L9b"), v("t9"))];

    prog
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn every_statement_is_in_exactly_one_procedure() {
        let prog = program();
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
            .chain(prog.const_assign.iter().map(|(s, ..)| s))
            .chain(prog.load_index_var.iter().map(|(s, ..)| s))
            .chain(prog.store_index_var.iter().map(|(s, ..)| s))
            .chain(prog.direct_call.iter().map(|(s, ..)| s))
            .chain(prog.actual_arg.iter().map(|(s, ..)| s))
            .chain(prog.bind_ret.iter().map(|(s, ..)| s));
        for st in mentioned {
            assert!(declared.contains(st), "{st} has no in_proc fact");
        }
    }

    #[test]
    fn callsite_arities_match_the_callee() {
        let prog = program();
        let arity = |proc: &Proc| prog.formal.iter().filter(|(q, ..)| q == proc).count();
        for (site, callee) in &prog.direct_call {
            let args = prog.actual_arg.iter().filter(|(s, ..)| s == site).count();
            assert_eq!(args, arity(callee), "arity mismatch at {site} -> {callee}");
        }
    }
}
