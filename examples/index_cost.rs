//! What Ascent's indices cost, priced index by index, and what one shared
//! store would cost instead.
//!
//! ```text
//! cargo run --features ctadl --release --example index_cost -- \
//!     backflash.apk --k 1
//! ```
//!
//! `examples/ctadl_memory.rs` reports the index bill as a *subtraction*: the
//! allocator's retained total, less the tuple `Vec`s and the `Arc` payloads,
//! is "indices" — 78% of the run, and no way to see inside it. This binary
//! computes the same quantity from the other end, by modelling Ascent 0.8's
//! generated storage exactly:
//!
//! - the relation itself, `Vec<Tuple>`, grown by doubling;
//! - one `RelFullIndexType<Tuple, ()> = HashMap<Tuple, ()>` per relation —
//!   `ascent_hir.rs:249` makes it unconditionally, for insert-time dedup, and
//!   its key is the *whole tuple*, so it is a second full copy;
//! - one `ToRelIndexType<K, V> = HashMap<K, Vec<V>>` per binding pattern the
//!   rules join on, where `V` is the **non-key columns stored inline**
//!   (`IndexValType::Direct`, `ascent_hir.rs:191-198`) — so each of those is
//!   another full copy of the relation, split between key and value;
//! - the `indices_none` pattern is that with an empty key: one `Vec` holding
//!   every tuple of the relation, verbatim.
//!
//! Every `Vec<V>` in an index is born `Vec::with_capacity(4)`
//! (`internal.rs:index_insert`), so an index whose keys are mostly unique
//! pays four value slots for one value.
//!
//! The counterfactual is the thing worth having: if an index stored a **row
//! id** into one shared `Vec<Tuple>` rather than a copy of the columns —
//! which is what CTADL's `#[ds(locals_trie)]` BYODS store does, and what
//! `ctadl-comparison.md` item 4 proposes here — what would the same run cost?
//! Two variants are reported, `ids` (keys still materialised, values become
//! `u32`) and `ideal` (a lower bound: one copy of the data, every index a
//! pure row-id structure).
//!

use std::collections::HashMap;

use hybrid_inlining_paper::access_path::{AccessPath, Accessor, Base, CritId, PtVal, Suffix};
use hybrid_inlining_paper::analysis::HybridAnalysis;
use hybrid_inlining_paper::ctadl::{Options, Preprocess, Translator, read_import, restrict};
use hybrid_inlining_paper::ir::*;
use hybrid_inlining_paper::mem::human;

/// One generated index: what Ascent stores for it, in the units the model
/// prices.
struct Index {
    rel: &'static str,
    pat: &'static str,
    /// Tuples in the relation — the number of (key, value) pairs the index
    /// holds, since every tuple is indexed exactly once.
    n: usize,
    /// Distinct keys: the entry count of the `HashMap`.
    keys: usize,
    /// Summed capacity of the per-key `Vec<V>`s, at Ascent's `with_capacity(4)`
    /// then doubling.
    vec_slots: usize,
    /// `size_of` the key tuple and the value tuple, as generated.
    ksz: usize,
    vsz: usize,
    /// Is this the full index — key is the whole tuple, value is `()`?
    full: bool,
}

/// `Vec` capacity for `m` pushes into a `Vec::with_capacity(4)`.
fn cap4(m: usize) -> usize {
    if m <= 4 { 4 } else { m.next_power_of_two() }
}

/// Buckets a hashbrown table ends up with holding `m` entries: powers of two,
/// grown at 7/8 load.
fn buckets(m: usize) -> usize {
    if m == 0 {
        return 0;
    }
    let mut b = 4usize;
    while b * 7 / 8 < m {
        b *= 2;
    }
    b
}

/// Bytes a `HashMap<K, V>` of `m` entries occupies: the bucket array of
/// `(K, V)` pairs plus one control byte each.
fn table(m: usize, kv: usize) -> usize {
    let b = buckets(m);
    b * kv + b
}

impl Index {
    /// What Ascent actually allocates for this index today.
    fn now(&self) -> usize {
        if self.full {
            // HashMap<Tuple, ()>: the whole tuple, a second time.
            table(self.keys, self.ksz)
        } else {
            // HashMap<K, Vec<V>> plus one heap Vec per key.
            table(self.keys, self.ksz + 24) + self.vec_slots * self.vsz
        }
    }

    /// Values become 4-byte row ids into the relation's own `Vec`; keys are
    /// still materialised in the table.
    fn ids(&self) -> usize {
        if self.full {
            // Dedup needs only "is this tuple present": a raw table of row
            // ids hashed by the tuple they point at.
            table(self.keys, 4)
        } else {
            table(self.keys, self.ksz + 24) + self.vec_slots * 4
        }
    }

    /// The lower bound: one copy of the data, every index a pure row-id
    /// structure, keys reached through the store.
    fn ideal(&self) -> usize {
        if self.full {
            table(self.keys, 4)
        } else {
            // A key entry costs a hash-table slot pointing at a run of row
            // ids; the ids themselves are one per tuple, packed.
            table(self.keys, 4 + 8) + self.n * 4
        }
    }
}

macro_rules! ix {
    ($out:expr, $rel:expr, $pat:expr, $data:expr, $kty:ty, $vty:ty, $full:expr,
     [$($i:tt),*]) => {{
        let mut counts: HashMap<$kty, usize> = HashMap::new();
        for t in $data.iter() {
            let _ = &t;
            *counts.entry(($(t.$i.clone(),)*)).or_insert(0) += 1;
        }
        $out.push(Index {
            rel: $rel,
            pat: $pat,
            n: $data.len(),
            keys: counts.len(),
            vec_slots: counts.values().map(|&m| cap4(m)).sum::<usize>(),
            ksz: std::mem::size_of::<$kty>(),
            vsz: std::mem::size_of::<$vty>(),
            full: $full,
        });
    }};
}

fn inventory(a: &HybridAnalysis) -> Vec<Index> {
    let mut out = Vec::new();
    include!("index_cost_inventory.inc");
    out
}

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
            "--ssa" => opts.preprocess = Preprocess::ssa_only(),
            "--no-preprocess" => opts.preprocess = Preprocess::none(),
            "-h" | "--help" => {
                eprintln!("usage: index_cost <import>... [--k N] [--max-procs N]");
                return Ok(());
            }
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
    let prog = match max_procs {
        Some(n) => restrict(&t.finish(), n),
        None => t.finish(),
    };

    let mut a = HybridAnalysis::for_program(&prog, k);
    a.run();

    // The generated plan is the authority on which indices exist. Check the
    // hardcoded inventory against it before pricing anything: a rule edit that
    // adds a binding pattern would otherwise be silently unpriced.
    let summary = HybridAnalysis::summary();
    let mut want: std::collections::BTreeSet<String> = Default::default();
    for tok in summary.split(|c: char| !(c.is_alphanumeric() || c == '_')) {
        if let Some((rel, pat)) = tok.split_once("_indices_") {
            let pat = pat
                .strip_suffix("_delta")
                .or_else(|| pat.strip_suffix("_total"))
                .or_else(|| pat.strip_suffix("_new"))
                .unwrap_or(pat);
            want.insert(format!("{rel}_indices_{pat}"));
        }
    }
    let idx = inventory(&a);
    let have: std::collections::BTreeSet<String> =
        idx.iter().map(|i| format!("{}_indices_{}", i.rel, i.pat)).collect();
    let missing: Vec<_> = want.difference(&have).collect();
    if missing.is_empty() {
        println!(
            "inventory: {} indices over {} relations; every index named by the \
             generated plan is priced",
            idx.len(),
            idx.iter().map(|i| i.rel).collect::<std::collections::BTreeSet<_>>().len()
        );
    } else {
        println!("inventory: MISSING {} indices from the plan: {missing:?}", missing.len());
    }

    // The relation `Vec`s: the only part `relation_sizes_summary()` can see.
    let mut vecs: HashMap<&str, (usize, usize)> = HashMap::new();
    for i in &idx {
        if i.full {
            let cap = if i.n == 0 { 0 } else { i.n.next_power_of_two().max(4) };
            vecs.insert(i.rel, (i.n, cap * i.ksz));
        }
    }

    let mut per: HashMap<&str, (usize, usize, usize)> = HashMap::new();
    for i in &idx {
        let e = per.entry(i.rel).or_default();
        e.0 += i.now();
        e.1 += i.ids();
        e.2 += i.ideal();
    }

    let mut rows: Vec<_> = per
        .iter()
        .map(|(&rel, &(now, ids, ideal))| {
            let (n, vb) = vecs[rel];
            (rel, n, vb, now, ids, ideal)
        })
        .filter(|r| r.1 > 0)
        .collect();
    rows.sort_by_key(|r| std::cmp::Reverse(r.2 + r.3));

    println!("\n=== per relation: the Vec, the indices, and two counterfactuals ===");
    println!(
        "{:<14}{:>10}{:>11}{:>11}{:>8}{:>11}{:>11}",
        "relation", "tuples", "Vec", "indices now", "copies", "ids", "ideal"
    );
    for (rel, n, vb, now, ids, ideal) in &rows {
        // "copies" is what the index bill amounts to in units of the tuple
        // data itself: how many extra times the relation is materialised.
        let copies = if *vb == 0 { 0.0 } else { *now as f64 / *vb as f64 };
        println!(
            "{rel:<14}{n:>10}{:>11}{:>11}{copies:>8.1}{:>11}{:>11}",
            human(*vb),
            human(*now),
            human(*ids),
            human(*ideal)
        );
    }

    let tv: usize = rows.iter().map(|r| r.2).sum();
    let tn: usize = rows.iter().map(|r| r.3).sum();
    let ti: usize = rows.iter().map(|r| r.4).sum();
    let td: usize = rows.iter().map(|r| r.5).sum();
    println!(
        "{:<14}{:>10}{:>11}{:>11}{:>8.1}{:>11}{:>11}",
        "-- total",
        rows.iter().map(|r| r.1).sum::<usize>(),
        human(tv),
        human(tn),
        tn as f64 / tv as f64,
        human(ti),
        human(td)
    );

    println!("\n=== the whole modelled store ===");
    for (name, idxb) in [("now", tn), ("row ids", ti), ("ideal", td)] {
        println!(
            "  {name:<10}{:>11}  = {:>10} Vec + {:>10} indices   ({:.2}x of now)",
            human(tv + idxb),
            human(tv),
            human(idxb),
            (tv + idxb) as f64 / (tv + tn) as f64
        );
    }

    println!("\n=== the ten most expensive indices, as they are stored now ===");
    let mut top: Vec<&Index> = idx.iter().filter(|i| i.n > 0).collect();
    top.sort_by_key(|i| std::cmp::Reverse(i.now()));
    println!(
        "{:<14}{:>8}{:>10}{:>10}{:>10}{:>10}{:>7}",
        "index", "pattern", "tuples", "keys", "bytes", "ideal", "val/key"
    );
    for i in top.iter().take(14) {
        println!(
            "{:<14}{:>8}{:>10}{:>10}{:>10}{:>10}{:>7.1}",
            i.rel,
            i.pat,
            i.n,
            i.keys,
            human(i.now()),
            human(i.ideal()),
            i.n as f64 / i.keys.max(1) as f64
        );
    }

    Ok(())
}
