//! Does CTADL's pre-codegen pipeline lose dispatch edges, or only spurious ones?
//!
//! ```text
//! cargo run --features ctadl --release --example dispatch_diff -- backflash.apk --k 1
//! ```
//!
//! `resolve` is keyed on [`CritId`], whose `Stmt` names are `{fn}#{block}.{i}`
//! — and SSA renumbers blocks and shifts statement indices, so the same
//! callsite has a different `CritId` on either side. Nothing about the tuples
//! can be compared directly.
//!
//! What *is* stable across the passes is the semantic content of a resolution:
//! the procedure holding the instance, the procedure the critical statement
//! syntactically lives in, the signature being dispatched, and the callee
//! selected. This keys on that quadruple and diffs the sets.
//!
//! The prediction, if version-splitting is doing what the theory says: SSA's
//! set is a *subset* of the non-SSA set. Merging every version of a variable
//! can only add flow, so it can only add resolutions — never remove a real one.
//! Anything the SSA run finds that the baseline does not would falsify that,
//! and is what this example exists to catch.
use std::collections::{BTreeMap, BTreeSet};

use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};
use hybrid_inlining_paper::ir::{Proc, Program, Sig, Stmt};

/// (holder, procedure the critical statement is in, signature, callee).
type Key = (Proc, Proc, Sig, Proc);

fn dispatch_set(prog: &Program, k: usize) -> (BTreeSet<Key>, usize) {
    let owner: BTreeMap<&Stmt, &Proc> = prog.in_proc.iter().map(|(s, p, _)| (s, p)).collect();
    let sig: BTreeMap<&Stmt, &Sig> = prog.virtual_call.iter().map(|(s, _, g)| (s, g)).collect();

    let mut a = HybridAnalysis::for_program(prog, k);
    a.run();
    let n = a.resolve.len();
    let mut out = BTreeSet::new();
    for (p, id, callee) in &a.resolve {
        // A critical statement that is not a virtual call (an `lv[v]` index)
        // has no signature; none are generated from a CTADL front end.
        let (Some(o), Some(g)) = (owner.get(&id.stmt), sig.get(&id.stmt)) else {
            continue;
        };
        out.insert((p.clone(), (*o).clone(), (*g).clone(), callee.clone()));
    }
    (out, n)
}

fn build(imports: &[String], pre: Preprocess, max_procs: Option<usize>) -> Program {
    let mut t = Translator::new(Options {
        preprocess: pre,
        ..Options::default()
    });
    for name in imports {
        let (cir, vmt) = read_import(name).expect("read import");
        t.add_import(cir, &vmt);
    }
    let p = t.finish();
    match max_procs {
        Some(n) => restrict(&p, n),
        None => p,
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut k = 1usize;
    let mut max_procs: Option<usize> = None;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "--max-procs" => max_procs = Some(args.next().unwrap_or_default().parse()?),
            _ => imports.push(a),
        }
    }

    let base = build(&imports, Preprocess::none(), max_procs);
    let (b, bn) = dispatch_set(&base, k);
    drop(base);
    println!("baseline   resolve={bn:>6}  distinct (holder, proc, sig, callee)={}", b.len());

    for (name, pre) in [
        ("ssa", Preprocess::ssa_only()),
        ("ctadl-pre", Preprocess::ctadl()),
    ] {
        let prog = build(&imports, pre, max_procs);
        let (s, sn) = dispatch_set(&prog, k);
        drop(prog);
        let lost: Vec<&Key> = b.difference(&s).collect();
        let gained: Vec<&Key> = s.difference(&b).collect();
        println!(
            "\n{name:<10} resolve={sn:>6}  distinct={}\n  \
             kept    {:>6}\n  dropped {:>6}  (present without the passes, absent with them)\n  \
             gained  {:>6}  (absent without, present with — should be 0)",
            s.len(),
            s.intersection(&b).count(),
            lost.len(),
            gained.len()
        );
        for key in gained.iter().take(10) {
            println!("    GAINED {} @ {} : {} -> {}", key.1, key.0, key.2, key.3);
        }
        for key in lost.iter().take(5) {
            println!("    dropped {} @ {} : {} -> {}", key.1, key.0, key.2, key.3);
        }
    }
    Ok(())
}
