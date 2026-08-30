//! Translate a CTADL import into the EDB, and optionally run the analysis on it.
//!
//! ```text
//! cargo run --features ctadl --release --example ctadl_import -- hello_jni
//! cargo run --features ctadl --release --example ctadl_import -- hello_jni --run --k 2
//! ```
//!
//! The argument is an import name in CTADL's store (`ctadl import --name ...`)
//! or a path to an import directory. Several may be given, which is how a
//! project that co-indexes artifacts — a dex and its native libraries — is
//! translated into one fact base.

use hybrid_inlining_paper::analysis::run_hybrid;
use hybrid_inlining_paper::ctadl::{Options, Translator, read_import};
use hybrid_inlining_paper::ir::Program;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut opts = Options::default();
    let mut imports: Vec<String> = Vec::new();
    let mut run = false;
    let mut k = 2usize;

    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--ssa" => opts.ssa = true,
            "--compact" => opts.compact_names = true,
            "--no-cha-fallback" => opts.cha_fallback = false,
            "--run" => run = true,
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "-h" | "--help" => {
                eprintln!(
                    "usage: ctadl_import <import|dir>... [--ssa] [--compact] \
                     [--no-cha-fallback] [--run] [--k N]"
                );
                return Ok(());
            }
            _ => imports.push(a),
        }
    }
    if imports.is_empty() {
        eprintln!("no imports given; try --help");
        return Ok(());
    }

    let mut t = Translator::new(opts);
    for name in &imports {
        let (cir, vmt) = read_import(name)?;
        eprintln!("{name}: {} function(s)", cir.functions.len());
        t.add_import(cir, &vmt);
    }
    let prog = t.finish();

    println!("=== EDB ===");
    for (name, n) in sizes(&prog) {
        if n > 0 {
            println!("{n:>10}  {name}");
        }
    }

    if run {
        println!("\n=== running hybrid inlining, k = {k} ===");
        let h = run_hybrid(&prog, k);
        println!("{:>10}  critical statements", h.critical.len());
        println!("{:>10}  pending instances", h.pending.len());
        println!("{:>10}  settled", h.settled.len());
        println!("{:>10}  dispatches resolved", h.dispatches().len());
    }

    Ok(())
}

fn sizes(p: &Program) -> Vec<(&'static str, usize)> {
    vec![
        ("procedure", p.procedure.len()),
        ("proc_type", p.proc_type.len()),
        ("proc_sig", p.proc_sig.len()),
        ("entry", p.entry.len()),
        ("in_proc", p.in_proc.len()),
        ("alloc", p.alloc.len()),
        ("alloc_type", p.alloc_type.len()),
        ("const_assign", p.const_assign.len()),
        ("mov", p.mov.len()),
        ("load_field", p.load_field.len()),
        ("store_field", p.store_field.len()),
        ("load_static", p.load_static.len()),
        ("store_static", p.store_static.len()),
        ("load_index_const", p.load_index_const.len()),
        ("store_index_const", p.store_index_const.len()),
        ("load_index_var", p.load_index_var.len()),
        ("store_index_var", p.store_index_var.len()),
        ("direct_call", p.direct_call.len()),
        ("virtual_call", p.virtual_call.len()),
        ("actual_arg", p.actual_arg.len()),
        ("bind_ret", p.bind_ret.len()),
        ("formal", p.formal.len()),
        ("ret", p.ret.len()),
        ("direct_subtype", p.direct_subtype.len()),
        ("lookup", p.lookup.len()),
    ]
}
