//! Break `points` down by what kind of value it holds, and `edge`/paths by base kind.
use hybrid_inlining_paper::access_path::{Base, PtVal};
use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut imports: Vec<String> = Vec::new();
    let mut k = 1usize;
    let mut max_procs: Option<usize> = None;
    let mut opts = Options::default();

    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--k" => k = args.next().unwrap_or_default().parse()?,
            "--max-procs" => max_procs = Some(args.next().unwrap_or_default().parse()?),
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
    let mut t = Translator::new(opts.clone());
    for name in &imports {
        let (cir, vmt) = read_import(name)?;
        t.add_import(cir, &vmt);
    }
    let mut prog = t.finish();
    if let Some(n) = max_procs { prog = restrict(&prog, n); }
    let mut a = HybridAnalysis::for_program(&prog, k);
    a.run();

    let (mut sym, mut alloc, mut kon) = (0usize, 0, 0);
    // how many points tuples mention a placeholder (CritSlot/CritRet) anywhere
    let mut ph = 0usize;
    let base_is_ph = |b: &Base| matches!(b, Base::CritSlot(..) | Base::CritRet(..));
    for (_, w, v) in &a.points {
        match v { PtVal::Path(_) => sym += 1, PtVal::Alloc(_) => alloc += 1, PtVal::Const(_) => kon += 1 }
        let vph = match v { PtVal::Path(p) => base_is_ph(&p.base), _ => false };
        if base_is_ph(&w.base) || vph { ph += 1; }
    }
    let n = a.points.len();
    println!("points = {n}");
    println!("  PtVal::Path  (symbolic)  {sym:>9}  {:>5.1}%", 100.0*sym as f64/n as f64);
    println!("  PtVal::Alloc (concrete)  {alloc:>9}  {:>5.1}%", 100.0*alloc as f64/n as f64);
    println!("  PtVal::Const             {kon:>9}  {:>5.1}%", 100.0*kon as f64/n as f64);
    println!("  mentions a placeholder   {ph:>9}  {:>5.1}%", 100.0*ph as f64/n as f64);

    let mut eph = 0usize;
    for (_, sup, sub) in &a.edge {
        if base_is_ph(&sup.base) || base_is_ph(&sub.base) { eph += 1; }
    }
    println!("edge = {}\n  mentions a placeholder   {eph:>9}  {:>5.1}%",
        a.edge.len(), 100.0*eph as f64/a.edge.len() as f64);

    let mut pph = 0usize;
    for (_, b) in &a.pub_root { if base_is_ph(b) { pph += 1; } }
    println!("pub_root = {}  placeholders {pph}", a.pub_root.len());
    Ok(())
}
