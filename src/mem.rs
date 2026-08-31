//! Heap accounting for the fixpoint: a counting global allocator.
//!
//! Tuple counts are the wrong unit for "did that rule edit make the relations
//! leaner". Two things they cannot see:
//!
//! - **Per-tuple size is not constant.** An `AccessPath` carries an `Arc<[Accessor]>`
//!   whose length grows with call depth (see the access-path section of
//!   `hi-complexity.md`), and a `CritId` carries an `Arc<[Stmt]>` call string
//!   bounded only by `k`. `fields_chain(n)` keeps every relation linear in
//!   tuples while the accessors behind them go quadratic.
//! - **Ascent's indices are not tuples.** Each relation is stored as a public
//!   `Vec` of tuples *plus* private index maps, one per binding pattern the
//!   rules use. Dropping a join column or adding one changes the index side
//!   and not the `Vec`, so `relation_sizes_summary()` reports no change at
//!   all. The indices are routinely the larger half.
//!
//! Counting at the allocator sees both, plus the interned `Arc<str>` symbols
//! that several relations share. It is the only place that sees them once
//! rather than once per referent.
//!
//! A binary opts in — the counters cost an atomic increment per allocation,
//! so the wall-time benches must not:
//!
//! ```ignore
//! #[global_allocator]
//! static ALLOC: hybrid_inlining_paper::mem::Counting = hybrid_inlining_paper::mem::Counting;
//! ```
//!
//! and then [`measure`] brackets the work. `examples/memory.rs` reports a
//! sweep, `benches/memory.rs` puts the same number under criterion so
//! `--save-baseline` can compare two versions of the rules.
//!
//! Caveats worth keeping in mind when reading a number:
//!
//! - Counters are process-wide, so a measurement is only as clean as the
//!   thread that takes it. [`measure`] is meaningful under `ascent_par!` for
//!   `peak` (a true high-water mark across the rayon pool) but `retained`
//!   assumes nothing else on the process is allocating in the meantime.
//! - What is counted is what the program asked for, not what the allocator
//!   reserved: no size-class rounding, no per-allocation header. Real RSS runs
//!   above this, by a factor that depends on the allocation size mix. It is a
//!   like-for-like measure across two versions of the rules, not a prediction
//!   of the process footprint.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static ALLOCATED: AtomicUsize = AtomicUsize::new(0);

/// A pass-through [`System`] allocator that keeps running totals.
///
/// Install it with `#[global_allocator]` in the binary that wants the numbers.
pub struct Counting;

impl Counting {
    /// Bytes currently allocated and not yet freed.
    pub fn live() -> usize {
        LIVE.load(Relaxed)
    }

    /// High-water mark of [`Counting::live`] since the last
    /// [`Counting::reset_peak`].
    pub fn peak() -> usize {
        PEAK.load(Relaxed)
    }

    /// Total allocation calls since process start. A rule edit that leaves
    /// `live` alone but halves this one traded churn for nothing else, which
    /// is usually visible in wall time too.
    pub fn allocs() -> usize {
        ALLOCS.load(Relaxed)
    }

    /// Total bytes ever handed out, freed or not.
    pub fn allocated() -> usize {
        ALLOCATED.load(Relaxed)
    }

    /// Drop the high-water mark back to the current live figure.
    pub fn reset_peak() {
        PEAK.store(LIVE.load(Relaxed), Relaxed);
    }
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            note_alloc(layout.size());
        }
        p
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            note_alloc(layout.size());
        }
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Relaxed);
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            // Ascent's relations grow by doubling, so most of the bytes a
            // sweep moves come through here rather than `alloc`.
            LIVE.fetch_sub(layout.size(), Relaxed);
            note_alloc(new_size);
        }
        p
    }
}

/// Record one allocation of `size` bytes and raise the high-water mark.
fn note_alloc(size: usize) {
    let live = LIVE.fetch_add(size, Relaxed) + size;
    PEAK.fetch_max(live, Relaxed);
    ALLOCS.fetch_add(1, Relaxed);
    ALLOCATED.fetch_add(size, Relaxed);
}

/// What one piece of work cost, in bytes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Usage {
    /// Bytes still held when the work finished — for a fixpoint, the size of
    /// the finished relations and their indices. This is the number to watch
    /// when the question is whether the relations got leaner.
    pub retained: usize,
    /// High-water mark over the work, above the baseline. Exceeds `retained`
    /// by whatever the evaluation allocated transiently (deltas, index
    /// rebuilds, the doubling of a `Vec` that is about to be handed back).
    /// This is the number that decides whether a run fits in RAM.
    pub peak: usize,
    /// Allocation calls made during the work.
    pub allocs: usize,
}

impl Usage {
    /// `retained` per tuple, for a relation total. Guards the empty case so a
    /// report can print it unconditionally.
    pub fn bytes_per(&self, tuples: usize) -> f64 {
        if tuples == 0 {
            0.0
        } else {
            self.retained as f64 / tuples as f64
        }
    }
}

/// Run `f` and report what it cost, with the result still alive.
///
/// `retained` is measured *before* `f`'s value is returned (and so before it
/// can be dropped), which is what makes it "what the finished analysis holds"
/// rather than "what leaked".
pub fn measure<T>(f: impl FnOnce() -> T) -> (T, Usage) {
    let (live0, allocs0) = (Counting::live(), Counting::allocs());
    Counting::reset_peak();

    let value = f();

    let usage = Usage {
        retained: Counting::live().saturating_sub(live0),
        peak: Counting::peak().saturating_sub(live0),
        allocs: Counting::allocs() - allocs0,
    };
    (value, usage)
}

/// Bytes the `Vec` backing one relation holds: its tuples, flat.
///
/// Deliberately shallow — no `Arc` suffix, no interned symbol, no index. What
/// the sum of these misses is split out by [`Payload`] and by subtraction from
/// [`Usage::retained`], so a report can name the three parts instead of
/// implying the flat number is the whole story.
///
/// Capacity, not length: this is the allocation, and Ascent's relations grow
/// by doubling, so the two differ by up to a factor of two on any given
/// relation. `retained` sees the capacity, and these figures have to add up
/// against it.
pub fn reserved_bytes<T>(rel: &Vec<T>) -> usize {
    rel.capacity() * std::mem::size_of::<T>()
}

/// `n` bytes as a human-readable string.
pub fn human(n: usize) -> String {
    const UNITS: [(&str, f64); 4] = [
        ("GiB", 1024.0 * 1024.0 * 1024.0),
        ("MiB", 1024.0 * 1024.0),
        ("KiB", 1024.0),
        ("B", 1.0),
    ];
    for (unit, scale) in UNITS {
        if n as f64 >= scale {
            return format!("{:.1} {unit}", n as f64 / scale);
        }
    }
    format!("{n} B")
}

// -- what is behind the tuples ------------------------------------------------
//
// [`Usage::retained`] is one number for three different things: the `Vec`
// spines Ascent exposes, the `Arc` payloads the tuples point at, and the index
// maps Ascent keeps beside every relation. The first is trivial to compute and
// the third cannot be reached at all from outside — the codegen emits
// `pub <rel>: Vec<Tuple>` but leaves each `<rel>_index_...` field private. So
// the split is done by subtraction: walk what *is* reachable, and whatever
// `retained` has left over is the indices.
//
// The walk has to skip allocations that predate the fixpoint. Cloning an
// `Arc<str>` symbol out of an EDB tuple does not allocate, so counting every
// symbol a derived tuple points at would charge the fixpoint for the front
// end's strings. Walking the EDB first with [`Payload::restart`] in between
// marks those as seen without counting them, which leaves exactly the `Arc`s
// the derivation itself created: new access-path suffixes and new call
// strings.

use std::collections::HashSet;
use std::sync::Arc;

use crate::access_path::{AccessPath, Accessor, Base, CritId, PtVal, Suffix};
use crate::ir::{Alloc, Const, Field, Proc, Sig, Stmt, Type, Var};

/// Strong count plus weak count, the header every `Arc` allocation carries.
const ARC_HEADER: usize = 2 * std::mem::size_of::<usize>();

/// Sums the heap behind a set of tuples, counting each shared allocation once.
#[derive(Default)]
pub struct Payload {
    /// Allocations already counted, by address. An `Arc` reached from two
    /// relations — or from two tuples of one relation, which is the common
    /// case for a suffix — is one allocation, not two.
    seen: HashSet<usize>,
    bytes: usize,
}

impl Payload {
    /// Bytes counted since the last [`Payload::restart`].
    pub fn bytes(&self) -> usize {
        self.bytes
    }

    /// Zero the byte count and keep the seen set: everything walked so far
    /// stops counting but still suppresses double-counting later.
    pub fn restart(&mut self) {
        self.bytes = 0;
    }

    /// Count one allocation, once. Returns whether it was new, which is the
    /// signal to walk its interior.
    fn allocation(&mut self, ptr: usize, bytes: usize) -> bool {
        let new = self.seen.insert(ptr);
        if new {
            self.bytes += ARC_HEADER + bytes;
        }
        new
    }

    /// Walk every tuple of one relation.
    pub fn walk_all<T: HeapWalk>(&mut self, rel: &[T]) {
        for tuple in rel {
            tuple.walk(self);
        }
    }
}

/// A value that may own heap beyond its own size.
pub trait HeapWalk {
    fn walk(&self, p: &mut Payload);
}

/// The interned symbols: one `Arc<str>` each, shared across every tuple that
/// names the same procedure, variable, field or statement.
macro_rules! symbol_walk {
    ($($t:ty),* $(,)?) => {$(
        impl HeapWalk for $t {
            fn walk(&self, p: &mut Payload) {
                p.allocation(Arc::as_ptr(&self.0) as *const u8 as usize, self.0.len());
            }
        }
    )*};
}
symbol_walk!(Proc, Stmt, Var, Field, Const, Alloc, Type, Sig);

impl HeapWalk for usize {
    fn walk(&self, _: &mut Payload) {}
}

impl HeapWalk for Accessor {
    fn walk(&self, p: &mut Payload) {
        match self {
            Accessor::Field(f) => f.walk(p),
            Accessor::Index(c) => c.walk(p),
            Accessor::IndexUnknown => {}
        }
    }
}

/// Every path allocates a suffix, including the empty one: `Arc<[T]>` has to
/// put its counts somewhere. A bare root therefore costs the header alone, and
/// a deep path costs the header plus its accessors.
fn walk_suffix(accessors: &Arc<[Accessor]>, p: &mut Payload) {
    let ptr = Arc::as_ptr(accessors) as *const Accessor as usize;
    if p.allocation(ptr, std::mem::size_of_val(&**accessors)) {
        for a in accessors.iter() {
            a.walk(p);
        }
    }
}

impl HeapWalk for AccessPath {
    fn walk(&self, p: &mut Payload) {
        self.base.walk(p);
        walk_suffix(&self.accessors, p);
    }
}

impl HeapWalk for Suffix {
    fn walk(&self, p: &mut Payload) {
        walk_suffix(&self.0, p);
    }
}

impl HeapWalk for Base {
    fn walk(&self, p: &mut Payload) {
        match self {
            Base::Var(v) => v.walk(p),
            Base::Param(proc_, _) | Base::Ret(proc_) => proc_.walk(p),
            Base::CritSlot(id, _) | Base::CritRet(id) => id.walk(p),
        }
    }
}

impl HeapWalk for CritId {
    fn walk(&self, p: &mut Payload) {
        self.stmt.walk(p);
        let ptr = Arc::as_ptr(&self.chain) as *const Stmt as usize;
        if p.allocation(ptr, std::mem::size_of_val(&*self.chain)) {
            for site in self.chain.iter() {
                site.walk(p);
            }
        }
    }
}

impl HeapWalk for PtVal {
    fn walk(&self, p: &mut Payload) {
        match self {
            PtVal::Path(w) => w.walk(p),
            PtVal::Alloc(l) => l.walk(p),
            PtVal::Const(c) => c.walk(p),
        }
    }
}

/// Relations are tuples; arity 4 is the widest in either schema.
macro_rules! tuple_walk {
    ($(($($n:tt $t:ident),*)),* $(,)?) => {$(
        impl<$($t: HeapWalk),*> HeapWalk for ($($t,)*) {
            fn walk(&self, p: &mut Payload) {
                $(self.$n.walk(p);)*
            }
        }
    )*};
}
tuple_walk![
    (0 A),
    (0 A, 1 B),
    (0 A, 1 B, 2 C),
    (0 A, 1 B, 2 C, 3 D),
];

// -- the report, against the analysis's own schema ----------------------------
//
// Everything above is schema-agnostic: an allocator and a walk. What follows
// names the relations of [`HybridAnalysis`] once, so that the two reports that
// want a per-relation breakdown — `examples/memory.rs` over the synthetic
// families, `examples/ctadl_memory.rs` over an imported APK — cannot drift
// apart from the schema or from each other.

use crate::analysis::HybridAnalysis;
use crate::ir::Program;

/// The IDB relations, named once. Counting tuples, sizing the `Vec`, and
/// walking the `Arc`s behind the tuples all go through this list.
macro_rules! idb {
    ($h:expr, $each:ident) => {
        $each![
            $h, sig_target, sig_size, mono_target, eff_direct, critical, known_proc,
            is_called, uncalled, edge, points, path_used, crit_origin, pending,
            can_propagate, carries, decisive_var, slot_from_formal, will_propagate, stuck,
            crit_operand, call_crit, load_crit, store_crit, index_crit, decisive_slot,
            crit_sig, free_root, pub_root, pub_edge, pub_points, root_map, blocked, top,
            resolve, index_undecidable, index_acc, adequate, settled,
        ]
    };
}

/// The EDB relations, likewise. Walked only to mark what the front end already
/// allocated, never counted — see [`split`].
macro_rules! edb {
    ($h:expr, $each:ident) => {
        $each![
            $h, procedure, proc_type, proc_sig, entry, in_proc, alloc, alloc_type,
            const_assign, mov, load_field, store_field, load_static, store_static,
            load_index_const, store_index_const, load_index_var, store_index_var,
            direct_call, virtual_call, actual_arg, bind_ret, formal, ret, direct_subtype,
            lookup, paths, k_limit,
        ]
    };
}

/// Every IDB relation, as `(name, tuples, bytes the `Vec` holds)`.
///
/// The byte figure is the `Vec` alone: no `Arc` suffix, no interned symbol, no
/// index. [`split`] accounts for the rest.
pub fn idb_relations(h: &HybridAnalysis) -> Vec<(&'static str, usize, usize)> {
    macro_rules! sizes {
        ($h:expr, $($name:ident),* $(,)?) => {
            vec![$((stringify!($name), $h.$name.len(), reserved_bytes(&$h.$name))),*]
        };
    }
    idb!(h, sizes)
}

/// Total IDB tuples — the denominator for `B/tuple`.
pub fn idb_tuples(h: &HybridAnalysis) -> usize {
    idb_relations(h).iter().map(|(_, n, _)| n).sum()
}

/// Where [`Usage::retained`] went, as `(vecs, payload, indices)`.
///
/// `vecs` and `payload` are measured; `indices` is what is left, because
/// Ascent's index fields are private and cannot be sized from outside. The
/// EDB is walked first and discarded so that symbols the front end allocated
/// — which a derived tuple only clones an `Arc` handle to — are not charged to
/// the fixpoint.
pub fn split(h: &HybridAnalysis, usage: &Usage) -> (usize, usize, usize) {
    macro_rules! walk {
        ($h:expr, $($name:ident),* $(,)?) => {{
            let mut p = Payload::default();
            $(p.walk_all(&$h.$name);)*
            p
        }};
    }
    let mut p = edb!(h, walk);
    p.restart();
    macro_rules! walk_into {
        ($h:expr, $($name:ident),* $(,)?) => {{ $(p.walk_all(&$h.$name);)* }};
    }
    idb!(h, walk_into);
    let payload = p.bytes();

    let vecs: usize = idb_relations(h).iter().map(|(_, _, b)| b).sum();
    let indices = usage.retained.saturating_sub(vecs + payload);
    (vecs, payload, indices)
}

/// Run the fixpoint over `prog`, measuring only `run()`.
///
/// `for_program` — which copies the EDB in — happens outside the measured
/// region, so what is reported is the derivation: the IDB tuples, their `Arc`
/// payloads, and every index Ascent builds along the way (including the ones
/// over the EDB, which it builds lazily once the fixpoint starts).
pub fn run_measured(prog: &Program, k: usize) -> (HybridAnalysis, Usage) {
    let mut h = HybridAnalysis::for_program(prog, k);
    let ((), usage) = measure(|| h.run());
    (h, usage)
}

/// Print the per-relation table for one finished analysis, plus the three-way
/// split of what the relations do not explain.
///
/// The `Vec`s in the table are the part `relation_sizes_summary()` can see;
/// the two lines below it are the part it cannot, and between them they are
/// usually the majority of the memory. A rule edit that changes which columns
/// a relation is joined on moves the index line and leaves every tuple count
/// where it was.
pub fn report(h: &HybridAnalysis, usage: &Usage, edb_facts: usize) {
    let mut rels = idb_relations(h);
    rels.retain(|(_, n, _)| *n > 0);
    rels.sort_by(|a, b| b.2.cmp(&a.2).then(a.0.cmp(b.0)));

    let tuples: usize = rels.iter().map(|(_, n, _)| n).sum();
    let vec_bytes: usize = rels.iter().map(|(_, _, b)| b).sum();

    println!(
        "  |P| = {edb_facts} EDB facts;  retained {}, peak {}, {} allocations",
        human(usage.retained),
        human(usage.peak),
        usage.allocs
    );
    println!("\n  {:<20} {:>8} {:>12} {:>8}", "relation", "tuples", "Vec bytes", "B/tuple");
    for (name, n, bytes) in &rels {
        println!(
            "  {name:<20} {n:>8} {:>12} {:>8.1}",
            human(*bytes),
            *bytes as f64 / *n as f64
        );
    }
    println!(
        "  {:<20} {tuples:>8} {:>12} {:>8.1}",
        "-- total",
        human(vec_bytes),
        vec_bytes as f64 / tuples as f64
    );

    let (vecs, payload, indices) = split(h, usage);
    let pct = |n: usize| 100.0 * n as f64 / usage.retained.max(1) as f64;
    println!("\n  where `retained` went");
    println!("    tuple Vecs         {:>10}  {:>4.0}%", human(vecs), pct(vecs));
    println!(
        "    Arc payloads       {:>10}  {:>4.0}%   suffixes and call strings the fixpoint built",
        human(payload),
        pct(payload)
    );
    println!(
        "    Ascent indices     {:>10}  {:>4.0}%   by subtraction: the index fields are private",
        human(indices),
        pct(indices)
    );
}
