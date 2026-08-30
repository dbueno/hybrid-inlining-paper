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

use crate::access_path::{AccessPath, Accessor, Base, CritId, PtVal};
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

impl HeapWalk for AccessPath {
    fn walk(&self, p: &mut Payload) {
        self.base.walk(p);
        // Every path allocates a suffix, including the empty one: `Arc<[T]>`
        // has to put its counts somewhere. A bare root therefore costs the
        // header alone, and a deep path costs the header plus its accessors.
        let ptr = Arc::as_ptr(&self.accessors) as *const Accessor as usize;
        if p.allocation(ptr, std::mem::size_of_val(&*self.accessors)) {
            for a in self.accessors.iter() {
                a.walk(p);
            }
        }
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
