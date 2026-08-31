//! The CTADL front end, end to end.
//!
//! Rather than reading an import off disk — which would make the test depend on
//! whatever happens to be in the developer's CTADL store — this builds Figure 1
//! *in CTADL IR*, using `ctadl-ir`'s own builder, and then asserts that
//! translating it and running Hybrid Inlining reproduces the paper's result:
//! `bar1` reaches only `Y.poly`, `bar2` only `Z.poly`, and so `second` is
//! `first` while `third` is not.
//!
//! It is the same acceptance test as `hybrid_inlining::figure1_*`, entered
//! through the front end instead of a hand-written EDB, so it pins the parts of
//! the translation the schema cannot check on its own: receiver-at-slot-0,
//! formal indices, return values, allocation types, and CHA.
#![cfg(feature = "ctadl")]

use std::collections::{BTreeMap, BTreeSet};

use ctadl_ir::mir::builder::FunctionBuilder;
use ctadl_ir::mir::call::{
    CallEdges, CallObject, CallStyle, JavaClass, JavaMethod, JavaSignature, JavaSimpleName,
    VirtualMethodTable,
};
use ctadl_ir::mir::{Exp, FunctionData, ParameterType, Program as CirProgram, Symbol};

use hybrid_inlining_paper::analysis::run_hybrid;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator};
use hybrid_inlining_paper::ir::{Proc, Program, Var};

const OBJ: &str = "LObj;";
const X: &str = "LX;";
const Y: &str = "LY;";
const Z: &str = "LZ;";

const Y_POLY: &str = "LY;->poly(LObj;)LObj;";
const Z_POLY: &str = "LZ;->poly(LObj;)LObj;";
const ID: &str = "LFacade;->id(LX;)LX;";
const FOO: &str = "LFacade;->foo(LX;LObj;)LObj;";
const MID: &str = "LFacade;->mid(LX;LObj;)LObj;";
const BAR1: &str = "LFacade;->bar1(LObj;)LObj;";
const BAR2: &str = "LFacade;->bar2(LObj;)LObj;";
const SERVICE: &str = "LFacade;->service()V";

/// `poly`'s descriptor, as it appears at the callsite and in the method table.
const POLY: (&str, &str) = ("poly", "(LObj;)LObj;");

/// A function with `n` by-value parameters (index 0 being `this`) and one
/// block, filled in by `body`.
fn func(name: &str, n: usize, body: impl FnOnce(&mut FunctionBuilder<'_>)) -> FunctionData {
    let mut f = FunctionData::default();
    let mut b = FunctionBuilder::new(&mut f);
    b.set_name(name);
    for _ in 0..n {
        b.add_param(ParameterType::ByVal);
    }
    b.set_return_arity(1);
    b.add_block();
    body(&mut b);
    f
}

fn direct(callee: &str) -> CallStyle {
    CallStyle::DirectCall {
        call_edges: CallEdges::Explicit(ctadl_ir::thin_vec![callee.to_string()]),
    }
}

/// Figure 1, in CTADL IR.
fn figure1_cir() -> (CirProgram, VirtualMethodTable) {
    let mut fns = Vec::new();

    // Obj poly(Obj obj) { return obj; }
    fns.push(func(Y_POLY, 2, |f| {
        let mut bb = f.at_block(0u32.into());
        let obj = bb.new_param_var(1u16.into());
        bb.create_ret([Exp::Variable(obj)]);
    }));

    // Obj poly(Obj obj) { return new Obj(); }
    fns.push(func(Z_POLY, 2, |f| {
        let mut bb = f.at_block(0u32.into());
        let t = bb.new_local_var("t14");
        bb.create_assign(
            t.clone(),
            [Exp::ObjectRef(CallObject::JavaObject(JavaClass(
                Symbol::from(OBJ),
            )))],
        );
        bb.create_ret([Exp::Variable(t)]);
    }));

    // X id(X x) { X tv = x; return tv; }
    fns.push(func(ID, 2, |f| {
        let mut bb = f.at_block(0u32.into());
        let x = bb.new_param_var(1u16.into());
        let tv = bb.new_local_var("tv");
        bb.create_assign(tv.clone(), [Exp::Variable(x)]);
        bb.create_ret([Exp::Variable(tv)]);
    }));

    // Obj foo(X x, Obj obj) { X tx = id(x); return tx.poly(obj); }
    fns.push(func(FOO, 3, |f| {
        let mut bb = f.at_block(0u32.into());
        let this = bb.new_param_var(0u16.into());
        let x = bb.new_param_var(1u16.into());
        let obj = bb.new_param_var(2u16.into());
        let tx = bb.new_local_var("tx");
        bb.create_call(
            direct(ID),
            [tx.clone()],
            [Exp::Variable(this), Exp::Variable(x)],
        );
        let r25 = bb.new_local_var("r25");
        // The critical statement: the receiver is not an argument in CIR.
        bb.create_call(
            CallStyle::JavaCall {
                receiver: tx,
                cls: Symbol::from(X),
                simple_name: Symbol::from(POLY.0),
                descriptor: Symbol::from(POLY.1),
            },
            [r25.clone()],
            [Exp::Variable(obj)],
        );
        bb.create_ret([Exp::Variable(r25)]);
    }));

    // Obj mid(X x, Obj obj) { return foo(x, obj); }
    fns.push(func(MID, 3, |f| {
        let mut bb = f.at_block(0u32.into());
        let this = bb.new_param_var(0u16.into());
        let x = bb.new_param_var(1u16.into());
        let obj = bb.new_param_var(2u16.into());
        let r28 = bb.new_local_var("r28");
        bb.create_call(
            direct(FOO),
            [r28.clone()],
            [Exp::Variable(this), Exp::Variable(x), Exp::Variable(obj)],
        );
        bb.create_ret([Exp::Variable(r28)]);
    }));

    // Obj bar1(Obj obj) { return mid(new Y(), obj); }  (and bar2, with Z)
    for (name, cls, temp, res) in [(BAR1, Y, "t31", "r31"), (BAR2, Z, "t34", "r34")] {
        fns.push(func(name, 2, |f| {
            let mut bb = f.at_block(0u32.into());
            let this = bb.new_param_var(0u16.into());
            let obj = bb.new_param_var(1u16.into());
            let t = bb.new_local_var(temp);
            bb.create_assign(
                t.clone(),
                [Exp::ObjectRef(CallObject::JavaObject(JavaClass(
                    Symbol::from(cls),
                )))],
            );
            let r = bb.new_local_var(res);
            bb.create_call(
                direct(MID),
                [r.clone()],
                [Exp::Variable(this), Exp::Variable(t), Exp::Variable(obj)],
            );
            bb.create_ret([Exp::Variable(r)]);
        }));
    }

    // void service() { Obj first = new Obj(); second = bar1(first); third = bar2(first); }
    fns.push(func(SERVICE, 1, |f| {
        let mut bb = f.at_block(0u32.into());
        let this = bb.new_param_var(0u16.into());
        let first = bb.new_local_var("first");
        bb.create_assign(
            first.clone(),
            [Exp::ObjectRef(CallObject::JavaObject(JavaClass(
                Symbol::from(OBJ),
            )))],
        );
        let second = bb.new_local_var("second");
        bb.create_call(
            direct(BAR1),
            [second],
            [Exp::Variable(this.clone()), Exp::Variable(first.clone())],
        );
        let third = bb.new_local_var("third");
        bb.create_call(
            direct(BAR2),
            [third],
            [Exp::Variable(this), Exp::Variable(first)],
        );
        bb.create_ret([]);
    }));

    let mut vmt = VirtualMethodTable::new_java();
    if let VirtualMethodTable::Java {
        methods, hierarchy, ..
    } = &mut vmt
    {
        for (cls, imp) in [(Y, Y_POLY), (Z, Z_POLY)] {
            methods.push((
                JavaClass(Symbol::from(cls)),
                JavaSimpleName(Symbol::from(POLY.0)),
                JavaSignature(Symbol::from(POLY.1)),
                JavaMethod(Symbol::from(imp)),
            ));
            hierarchy
                .entry(JavaClass(Symbol::from(cls)))
                .or_default()
                .push(JavaClass(Symbol::from(X)));
        }
    }

    (CirProgram::new(ctadl_ir::mir::Functions::new(fns)), vmt)
}

fn translate_with(pre: Preprocess) -> Program {
    let (cir, vmt) = figure1_cir();
    let mut t = Translator::new(Options {
        preprocess: pre,
        ..Options::default()
    });
    t.add_import(cir, &vmt);
    t.finish()
}

/// A local of `proc`, under the front end's naming scheme.
fn v(local: &str, proc: &str) -> Var {
    Var::from(format!("{local}@{proc}"))
}

/// The one SSA version of `local` in `proc`. Under [`Preprocess::none`] that
/// is `v(local, proc)` itself; with SSA on, the name carries a version this
/// test has no way to predict, so it is found rather than spelled — and the
/// finding doubles as an assertion, since every local named here is assigned
/// exactly once and must therefore have exactly one version.
fn sole_version(prog: &Program, local: &str, proc: &str) -> Var {
    let plain = v(local, proc);
    let versioned = format!("{local}#");
    let suffix = format!("@{proc}");

    // Every relation that can define a variable. `second` and `third` are
    // defined by `bind_ret`, not by an assignment, so that one matters.
    let mut found: BTreeSet<Var> = prog
        .mov
        .iter()
        .map(|(_, to, _)| to.clone())
        .chain(prog.alloc.iter().map(|(_, to, _)| to.clone()))
        .chain(prog.const_assign.iter().map(|(_, to, _)| to.clone()))
        .chain(prog.bind_ret.iter().map(|(_, to)| to.clone()))
        .filter(|var| {
            let n = var.to_string();
            *var == plain || (n.starts_with(&versioned) && n.ends_with(&suffix))
        })
        .collect();
    assert_eq!(
        found.len(),
        1,
        "`{local}` in {proc} should have exactly one definition, found {found:?}"
    );
    found.pop_first().unwrap()
}

#[test]
fn structure_survives_the_translation() {
    // Exact variable names, so this one is pinned to the raw translation;
    // `the_default_preprocessing_preserves_the_result` covers the shipped
    // configuration.
    let prog = translate_with(Preprocess::none());

    let procs: BTreeSet<String> = prog.procedure.iter().map(|(p,)| p.to_string()).collect();
    assert_eq!(procs.len(), 8, "every function with a body is a procedure");
    assert!(procs.contains(SERVICE));

    // Only `service` is uncalled, so it is the only entry.
    let entries: Vec<String> = prog.entry.iter().map(|(p,)| p.to_string()).collect();
    assert_eq!(entries, [SERVICE.to_string()]);

    // The receiver is not a CIR argument, but it is `par_0` here.
    let (vcall, recv, sig) = {
        assert_eq!(prog.virtual_call.len(), 1, "one virtual call: tx.poly(obj)");
        let (s, r, g) = prog.virtual_call[0].clone();
        (s, r, g)
    };
    assert_eq!(recv, v("tx", FOO));
    assert!(
        prog.actual_arg.contains(&(vcall.clone(), 0, recv)),
        "the receiver occupies argument slot 0"
    );
    assert!(
        prog.actual_arg
            .contains(&(vcall, 1, Var::from(format!("par2@{FOO}")))),
        "`obj`, foo's par_2, shifts up to slot 1 to make room for it"
    );

    // CHA over `LX;` finds exactly the two implementations, which is what
    // makes the call critical rather than a direct call in disguise.
    let targets: BTreeSet<String> = prog
        .lookup
        .iter()
        .filter(|(_, s, _)| *s == sig)
        .map(|(_, _, p)| p.to_string())
        .collect();
    assert_eq!(
        targets,
        BTreeSet::from([Y_POLY.to_string(), Z_POLY.to_string()])
    );

    // Two allocation types reach the analysis: Y and Z, plus the two Objs.
    let allocated: BTreeSet<String> = prog.alloc_type.iter().map(|(_, t)| t.to_string()).collect();
    assert_eq!(
        allocated,
        BTreeSet::from([OBJ.to_string(), Y.to_string(), Z.to_string()])
    );
}

#[test]
fn figure1_result_survives_the_translation() {
    check_figure1_result(Preprocess::none());
}

/// The same acceptance test under the shipped default — CTADL's four IR
/// passes. SSA renames every local, so the paper's result has to survive a
/// translation whose variable names this test cannot predict; that it does is
/// the property the default rests on.
#[test]
fn the_default_preprocessing_preserves_the_result() {
    assert_eq!(Options::default().preprocess, Preprocess::ctadl());
    check_figure1_result(Preprocess::ctadl());
}

fn check_figure1_result(pre: Preprocess) {
    let prog = translate_with(pre);
    let h = run_hybrid(&prog, 4);

    let pt = |local: &str| -> BTreeSet<String> {
        h.points_to(&Proc::from(SERVICE), sole_version(&prog, local, SERVICE))
            .iter()
            .map(ToString::to_string)
            .collect()
    };

    let first = pt("first");
    assert_eq!(first.len(), 1, "one allocation site: new Obj() at line 37");

    // `assert(first == second)`: bar1 pins the receiver to Y, whose poly is
    // the identity, so the result is the object that went in.
    assert_eq!(pt("second"), first);

    // `assert(first != third)`: bar2 pins it to Z, whose poly allocates.
    let third = pt("third");
    assert_eq!(third.len(), 1);
    assert!(
        third.is_disjoint(&first),
        "third = {third:?} must not contain first = {first:?}"
    );

    // The spurious edge the paper is about: neither bar must reach both.
    let mut by_holder: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (holder, _, callee) in h.dispatches() {
        by_holder
            .entry(holder.to_string())
            .or_default()
            .insert(callee.to_string());
    }
    assert_eq!(
        by_holder.get(BAR1),
        Some(&BTreeSet::from([Y_POLY.to_string()])),
        "bar1 resolves poly to Y only"
    );
    assert_eq!(
        by_holder.get(BAR2),
        Some(&BTreeSet::from([Z_POLY.to_string()])),
        "bar2 resolves poly to Z only"
    );
}
