//! What the fixpoint costs in bytes on a real artifact.
//!
//! ```text
//! cargo run --features ctadl --release --example ctadl_memory -- \
//!     backflash.apk --k 1
//! ```
//!
//! `examples/memory.rs` asks this question of the synthetic families, where
//! the shape of the input is known and a sweep can be fitted. This asks it of
//! an import, where the shape is whatever the app turned out to be, and the
//! only thing to compare against is the same app before a rule edit. Same
//! measurement either way — [`hybrid_inlining_paper::mem::report`] — so the
//! two tables read alike.
//!
//! The counting allocator is a global, so this is a separate binary from
//! `examples/ctadl_profile.rs`: rule timings must not be taken with an atomic
//! increment on every allocation.
//!
//! `--max-procs N`, repeatable, keeps the N procedures with the most
//! statements. Give it several times for a growth table:
//!
//! ```text
//! cargo run --features ctadl --release --example ctadl_memory -- \
//!     backflash.apk --k 1 --max-procs 100 --max-procs 400 --max-procs 1000
//! ```
//!
//! The whole program is always measured as well, last, unless `--no-whole`
//! says otherwise — which is what a sweep over `k` at a fixed, small size
//! wants, since the whole program does not converge at `k >= 3`.

use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};
use hybrid_inlining_paper::families::edb_size;
use hybrid_inlining_paper::ir::Program;
use hybrid_inlining_paper::mem::{Counting, Usage, human, idb_tuples, report, run_measured};

#[global_allocator]
static ALLOC: Counting = Counting;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut k = 1usize;
    let mut sizes: Vec<usize> = Vec::new();
    let mut whole_too = true;

    let mut opts = Options::default();

    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "--max-procs" => sizes.push(args.next().unwrap_or_default().parse()?),
            "--no-whole" => whole_too = false,
            "-h" | "--help" => {
                eprintln!(
                    "usage: ctadl_memory <import>... [--k N] [--max-procs N]... \
                     [--no-whole] [--ssa] [--no-preprocess]"
                );
                return Ok(());
            }
            // The IR passes `ctadl index` runs before codegen are on by
            // default. `--no-preprocess` is the ablation this repo's earlier
            // measurements were taken under; `--ssa` is SSA without the three
            // shrinking passes around it.
            "--ssa" => opts.preprocess = Preprocess::ssa_only(),
            "--ctadl-pre" => opts.preprocess = Preprocess::ctadl(),
            "--no-preprocess" => opts.preprocess = Preprocess::none(),
            _ => imports.push(a),
        }
    }
    if imports.is_empty() {
        eprintln!("no imports given; try --help");
        return Ok(());
    }

    let mut t = Translator::new(opts.clone());
    for name in &imports {
        let (cir, vmt) = read_import(name)?;
        t.add_import(cir, &vmt);
    }
    let whole = t.finish();
    sizes.sort_unstable();

    println!("# Heap cost of the fixpoint on {}", imports.join(", "));
    println!(
        "\nBytes are what the program asked the allocator for: no size-class\n\
         rounding, no per-allocation header, so RSS runs above these. Measured\n\
         over `run()` only — translating the import and copying the EDB in is\n\
         outside the measured region.  k = {k}"
    );

    // One breakdown per size, largest last so the final table is the one the
    // eye lands on.
    let mut rows: Vec<Row> = Vec::new();
    for n in sizes.iter().copied() {
        rows.push(one(&n.to_string(), &format!("{n} largest procedures"), &restrict(&whole, n), k));
    }
    // At a large `k` the whole-program run is the expensive one by orders of
    // magnitude, and it is not always the one being measured: a `k` sweep wants
    // a size that converges at every `k`, not the biggest size that fits.
    if whole_too {
        rows.push(one("whole", "whole program", &whole, k));
    }

    if rows.len() > 1 {
        println!("\n\n## growth");
        let line = |name: &str, f: &dyn Fn(&Row) -> String| {
            println!(
                "  {name:<12}{}",
                rows.iter().map(|r| format!("{:>12}", f(r))).collect::<Vec<_>>().join("")
            );
        };
        line("procs", &|r| r.procs.clone());
        line("|P|", &|r| r.edb.to_string());
        line("tuples", &|r| r.tuples.to_string());
        line("retained", &|r| human(r.usage.retained));
        line("peak", &|r| human(r.usage.peak));
        line("B/tuple", &|r| format!("{:.1}", r.usage.bytes_per(r.tuples)));
    }

    Ok(())
}

/// One run's figures, for the growth table at the end.
struct Row {
    /// The column heading: how many procedures were kept.
    procs: String,
    edb: usize,
    tuples: usize,
    usage: Usage,
}

/// Run and report one program, and keep the figures the growth table wants.
fn one(procs: &str, label: &str, prog: &Program, k: usize) -> Row {
    let (h, usage) = run_measured(prog, k);
    let (edb, tuples) = (edb_size(prog), idb_tuples(&h));
    println!(
        "\n\n## {label} — {} procedures, {} statements",
        prog.procedure.len(),
        prog.in_proc.len()
    );
    report(&h, &usage, edb);
    Row { procs: procs.to_string(), edb, tuples, usage }
}
