//! Front end: read CTADL's IR and translate it into the [`crate::ir`] EDB.
//!
//! [CTADL](https://github.com/sandialabs/ctadl) (`../ctadl-rs`) has an
//! ingestion pipeline for real artifacts — dex/APK, JVM, Ghidra pcode, Lua, C —
//! that lowers them into `ctadl_ir::mir`, a data-flow-oriented IR. That work is
//! worth reusing: this module is the *only* thing this crate borrows from it.
//! We depend on `ctadl-ir` alone (a leaf crate: no datafusion, no ghidra, no
//! ascent), read the IR that `ctadl import` already cached on disk, and write
//! our own translation. Nothing in ctadl's own Datalog codegen is involved.
//!
//! # Where the IR comes from
//!
//! `ctadl import` parses an artifact into a `ctadl_ir::mir::Program`, encodes
//! it with `bitcode`, and drops it in the store:
//!
//! ```text
//! $XDG_STATE_HOME/ctadl/imports/<name>/ir-program.bitcode   # the IR
//! $XDG_STATE_HOME/ctadl/imports/<name>/ir-vmt.bitcode       # class hierarchy + method table
//! ```
//!
//! So the expensive part is already done and cached; [`read_import`] just
//! decodes it. A project that co-indexes several artifacts (the JNI case: dex
//! plus its native libraries) is several imports, which is why [`Translator`]
//! accumulates across [`Translator::add_import`] calls rather than translating
//! one program at a time. IR names are fully qualified, so imports merge by
//! name with no renaming.
//!
//! # The mapping
//!
//! | CTADL IR | EDB |
//! |----------|-----|
//! | `FunctionData` with a non-empty body | [`procedure`](crate::ir::edb), [`formal`](crate::ir::edb) |
//! | `Assign { dest, sources }` | one [`mov`](crate::ir::edb)/[`const_assign`](crate::ir::edb)/[`alloc`](crate::ir::edb) per source |
//! | `Exp::ObjectRef` | [`alloc`](crate::ir::edb) + [`alloc_type`](crate::ir::edb) |
//! | `Load`/`Store` with a symbolic field | [`load_field`](crate::ir::edb)/[`store_field`](crate::ir::edb) |
//! | offsets in an `AccessPath` (`x.[8]`) | [`load_index_const`](crate::ir::edb)/[`store_index_const`](crate::ir::edb) |
//! | either, based at `Variable::GlobalHeap` | [`load_static`](crate::ir::edb)/[`store_static`](crate::ir::edb) |
//! | `CallStyle::DirectCall` | [`direct_call`](crate::ir::edb) |
//! | `CallStyle::JavaCall`/`LuaCall`/`FuncPtrCall` | [`virtual_call`](crate::ir::edb) |
//! | `VirtualMethodTable` hierarchy | [`direct_subtype`](crate::ir::edb), [`lookup`](crate::ir::edb) |
//! | `TerminatorKind::Return` | [`ret`](crate::ir::edb) |
//!
//! `Phi` becomes one `mov` per operand (only reachable with [`Options::ssa`]);
//! `ParamFlow` and `Nop` are dropped.
//!
//! # Where the two IRs disagree
//!
//! Four places, all decided here rather than left to the caller:
//!
//! 1. **Multiple returns.** A CIR call returns a tuple (`rets`), and dex gives
//!    every call arity 2 — a value and an exception slot. We keep `rets[0]` and
//!    the first operand of each `Return`, and drop the rest. Exception flow is
//!    therefore invisible.
//!
//! 2. **Parameter passing is by value.** CTADL passes parameters by reference:
//!    a callee writing through a parameter flows back out to the caller's
//!    argument, which is what `ParamFlow` anchors. This EDB is the paper's
//!    Java-shaped `call proc(lv_0..n)`, so only the forward half is emitted.
//!    Faithful for dex/JVM; lossy for pcode and C.
//!
//! 3. **Statement identity.** CIR statements have no ids, so one is synthesized
//!    from `(function, block, index)`. A CIR statement that needs temporaries
//!    (a constant argument, a multi-offset access path) expands into several
//!    EDB statements sharing that prefix.
//!
//! 4. **Entries** are the procedures with a body that nothing calls — no
//!    `direct_call` names them and no [`lookup`](crate::ir::edb) target
//!    reaches them.
//!
//! One more approximation, in `FuncPtrCall`. This EDB dispatches a virtual call
//! on argument slot 0, and inlining binds slot *i* to the callee's formal *i*.
//! For Java that is exactly right — the receiver *is* `par_0`. For a C indirect
//! call the pointer is not a parameter at all, so we put the pointer at slot 0
//! *in addition to* the real arguments at their own indices, rather than
//! shifting them. Dispatch sees the pointer where it needs it, every real
//! argument still lands on the right formal, and the cost is one spurious edge
//! into the callee's `par_0`. (The Lua front end already passes the callee as
//! `args[0]`, so there the extra fact is a duplicate.)
//!
//! # A note on what this makes critical
//!
//! No CTADL front end emits a variable-index access: `FieldAccess` is
//! offset-only, and dex lowers `aget`/`aput` to a symbolic `[]` field, losing
//! the index. So [`load_index_var`](crate::ir::edb) and
//! [`store_index_var`](crate::ir::edb) are never populated from here, and the
//! critical statements of §4.1.3 reduce to *unresolved dispatch* —
//! multi-target virtual calls, Lua method calls, and indirect calls.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use ctadl_ir::index::idx::Idx;
use ctadl_ir::mir::call::{CallEdges, CallObject, CallStyle, VirtualMethodTable};
use ctadl_ir::mir::{
    AccessPath as CirPath, Exp, FunctionData, Program as CirProgram, Statement, StatementKind,
    TerminatorKind, Variable, VariableRef,
};

use crate::ir::*;

// =========================================================================
// Reading the store
// =========================================================================

/// Anything that can go wrong getting the IR off disk.
#[derive(Debug)]
pub enum Error {
    Io(PathBuf, std::io::Error),
    Decode(PathBuf, bitcode::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Io(p, e) => write!(f, "reading {}: {e}", p.display()),
            Error::Decode(p, e) => write!(f, "decoding {}: {e}", p.display()),
        }
    }
}

impl std::error::Error for Error {}

/// CTADL's store root: `$XDG_STATE_HOME/ctadl`, defaulting to
/// `~/.local/state/ctadl`.
pub fn store_root() -> PathBuf {
    let state = std::env::var_os("XDG_STATE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".local/state")))
        .unwrap_or_else(|| PathBuf::from("."));
    state.join("ctadl")
}

/// The directory `ctadl import --name <name>` wrote.
pub fn import_dir(name: &str) -> PathBuf {
    store_root().join("imports").join(name)
}

/// Decode the IR and virtual method table an import directory holds.
///
/// `dir` is either a path to an import directory or, if it has no separator and
/// does not exist, an import *name* to look up in the store.
pub fn read_import(dir: impl AsRef<Path>) -> Result<(CirProgram, VirtualMethodTable), Error> {
    let dir = dir.as_ref();
    let dir = if dir.is_dir() {
        dir.to_path_buf()
    } else {
        import_dir(&dir.to_string_lossy())
    };

    let path = dir.join("ir-program.bitcode");
    let bytes = std::fs::read(&path).map_err(|e| Error::Io(path.clone(), e))?;
    let program = ctadl_ir::encode::decode_program(&bytes).map_err(|e| Error::Decode(path, e))?;

    // The VMT is written by `bitcode::serialize` directly, with no helper in
    // `ctadl_ir::encode` to mirror.
    let path = dir.join("ir-vmt.bitcode");
    let bytes = std::fs::read(&path).map_err(|e| Error::Io(path.clone(), e))?;
    let vmt = bitcode::deserialize(&bytes).map_err(|e| Error::Decode(path, e))?;

    Ok((program, vmt))
}

/// Read one import and translate it, the common case.
pub fn import_edb(dir: impl AsRef<Path>, opts: Options) -> Result<Program, Error> {
    let (cir, vmt) = read_import(dir)?;
    let mut t = Translator::new(opts);
    t.add_import(cir, &vmt);
    Ok(t.finish())
}

// =========================================================================
// Options
// =========================================================================

/// The IR-to-IR passes `ctadl index` runs between reading an import and
/// generating facts, in its order (`ctadl-ascent/src/cli/mod.rs:301-304`).
///
/// They are exposed one at a time rather than as a single switch because the
/// comparison in `ctadl-comparison.md` wants the ablation: SSA *grows* the
/// program, the other three shrink it, and lumping them together hides which
/// way the fact count moves. [`Preprocess::ctadl`] is the whole pipeline, and
/// is what "the same front end as `ctadl index`" means.
///
/// All four preserve taint-flow semantics, and all four are documented as
/// no-ops on IR that is already in SSA form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Preprocess {
    /// Delete assigned-but-never-read temporaries. Runs first: a dead temp has
    /// no use for coalescing to fuse it into.
    pub dead_temps: bool,

    /// Fuse single-use copy temporaries into their use.
    pub coalesce: bool,

    /// `ctadl_ir::ssa::transform_program`, so every variable is versioned and
    /// `Phi` nodes appear. The analysis here is flow-insensitive, so this only
    /// buys the extra precision of not merging a variable's versions — at the
    /// cost of a larger variable space. It also gives the function a single
    /// exit block, which collapses [`ret`](crate::ir::edb) to one fact.
    pub ssa: bool,

    /// Propagate the copies SSA introduced but coalescing could not fuse.
    /// Post-SSA, so it is the one pass that must follow `ssa` to do anything.
    pub copy_prop: bool,
}

/// CTADL's pipeline. This is the default because running it is worth 3.7× in
/// time and 3.9× in memory on `backflash.apk` at `k = 1`, for no lost dispatch
/// precision — see `ctadl-comparison.md`. Translating the IR exactly as
/// `ctadl import` cached it is the ablation, [`Preprocess::none`], not the
/// baseline.
impl Default for Preprocess {
    fn default() -> Self {
        Preprocess::ctadl()
    }
}

impl Preprocess {
    /// Every pass `ctadl index` runs, which is all four. The default.
    pub fn ctadl() -> Self {
        Preprocess {
            dead_temps: true,
            coalesce: true,
            ssa: true,
            copy_prop: true,
        }
    }

    /// No preprocessing: the IR as `ctadl import` cached it. Kept for the
    /// ablation in `examples/dispatch_diff.rs` and for front ends that have
    /// already run their own passes.
    pub fn none() -> Self {
        Preprocess {
            dead_temps: false,
            coalesce: false,
            ssa: false,
            copy_prop: false,
        }
    }

    /// SSA alone, with none of the shrinking passes around it.
    pub fn ssa_only() -> Self {
        Preprocess {
            ssa: true,
            ..Preprocess::none()
        }
    }
}

#[derive(Clone, Debug)]
pub struct Options {
    /// Which of CTADL's pre-codegen IR passes to run. Defaults to all four,
    /// matching `ctadl index`; [`Preprocess::none`] translates the IR exactly
    /// as `ctadl import` cached it.
    pub preprocess: Preprocess,

    /// When the declared class at a virtual call is unknown to the hierarchy —
    /// routine for library types an APK does not ship — fall back to every
    /// class that declares the same (name, descriptor). Without it such a call
    /// resolves to nothing and its arguments flow nowhere.
    pub cha_fallback: bool,

    /// Name statements and variables by position (`0:12#3.1`) rather than by
    /// the procedure they sit in (`Lcom/x/Y;->f()V#3.1`). Unreadable, but a
    /// large APK has millions of statements and the qualified form is what
    /// dominates the fact base's memory.
    pub compact_names: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            preprocess: Preprocess::default(),
            cha_fallback: true,
            compact_names: false,
        }
    }
}

// =========================================================================
// The translator
// =========================================================================

/// The type standing for the global heap, so that `Variable::GlobalHeap`
/// accesses become ordinary static field accesses.
const GLOBALS: &str = "$globals";

/// A virtual callsite's dispatch key, collected as the functions go by and
/// turned into [`lookup`](crate::ir::edb) tuples once every import's method
/// table has been seen.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Dispatch {
    /// `cls`, `simple_name`, `descriptor` — the Java/JVM key.
    Class(String, String, String),
    /// A Lua method name; there is no declared receiver class and no
    /// descriptor.
    Lua(String),
    /// An indirect call, keyed by whatever signature the front end recovered.
    FnPtr(String),
}

/// Accumulates an EDB across one or more imports.
///
/// Every relation is collected into a set: a CIR statement can legitimately
/// produce the same tuple twice (a `DirectCall` listing a target twice, an
/// argument that is also the receiver), and duplicate EDB tuples would be
/// wasted work in the analysis.
pub struct Translator {
    opts: Options,
    imports: usize,

    procedure: BTreeSet<Proc>,
    proc_type: BTreeSet<(Proc, Type)>,
    entry: BTreeSet<Proc>,
    in_proc: Vec<(Stmt, Proc, Line)>,
    alloc: BTreeSet<(Stmt, Var, Alloc)>,
    alloc_type: BTreeSet<(Alloc, Type)>,
    const_assign: BTreeSet<(Stmt, Var, Const)>,
    mov: BTreeSet<(Stmt, Var, Var)>,
    load_field: BTreeSet<(Stmt, Var, Var, Field)>,
    store_field: BTreeSet<(Stmt, Var, Field, Var)>,
    load_static: BTreeSet<(Stmt, Var, Type, Field)>,
    store_static: BTreeSet<(Stmt, Type, Field, Var)>,
    load_index_const: BTreeSet<(Stmt, Var, Var, Const)>,
    store_index_const: BTreeSet<(Stmt, Var, Const, Var)>,
    direct_call: BTreeSet<(Stmt, Proc)>,
    virtual_call: BTreeSet<(Stmt, Var, Sig)>,
    actual_arg: BTreeSet<(Stmt, ArgIdx, Var)>,
    bind_ret: BTreeSet<(Stmt, Var)>,
    formal: BTreeSet<(Proc, ArgIdx, Var)>,
    ret: BTreeSet<(Proc, Var)>,

    /// Class hierarchy and method tables, merged over every import.
    cha: Cha,
    /// The dispatch keys actually used at some callsite. Only these get
    /// `lookup` tuples: the method table describes the whole world, and
    /// `sig_size` counts targets per signature.
    sites: BTreeSet<Dispatch>,
    /// Every function whose address is taken (`Exp::ObjectRef(FunctionPtr)`) —
    /// the target set of an indirect call.
    funcptrs: BTreeSet<Proc>,

    // -- per-function scratch --------------------------------------------
    /// The procedure being translated.
    proc: Proc,
    /// The suffix that makes this function's variable and statement names
    /// unique: either its name or its position.
    scope: String,
    /// Label prefix of the CIR statement being translated.
    base: String,
    /// Temporaries emitted under `base` so far.
    sub: usize,
    /// Next `in_proc` line number.
    line: Line,
}

impl Translator {
    pub fn new(opts: Options) -> Self {
        Translator {
            opts,
            imports: 0,
            procedure: BTreeSet::new(),
            proc_type: BTreeSet::new(),
            entry: BTreeSet::new(),
            in_proc: Vec::new(),
            alloc: BTreeSet::new(),
            alloc_type: BTreeSet::new(),
            const_assign: BTreeSet::new(),
            mov: BTreeSet::new(),
            load_field: BTreeSet::new(),
            store_field: BTreeSet::new(),
            load_static: BTreeSet::new(),
            store_static: BTreeSet::new(),
            load_index_const: BTreeSet::new(),
            store_index_const: BTreeSet::new(),
            direct_call: BTreeSet::new(),
            virtual_call: BTreeSet::new(),
            actual_arg: BTreeSet::new(),
            bind_ret: BTreeSet::new(),
            formal: BTreeSet::new(),
            ret: BTreeSet::new(),
            cha: Cha::default(),
            sites: BTreeSet::new(),
            funcptrs: BTreeSet::new(),
            proc: Proc::from(""),
            scope: String::new(),
            base: String::new(),
            sub: 0,
            line: 0,
        }
    }

    /// Translate one import's IR, merging it into what is already here.
    pub fn add_import(&mut self, mut cir: CirProgram, vmt: &VirtualMethodTable) {
        // CTADL's order, and its `prune_unreachable_cfg_nodes` default of
        // `true`. Each guard is separate so an ablation can run one pass.
        let pre = self.opts.preprocess;
        if pre.dead_temps {
            ctadl_ir::ssa::eliminate_dead_temps(&mut cir);
        }
        if pre.coalesce {
            ctadl_ir::ssa::coalesce_copies(&mut cir);
        }
        if pre.ssa {
            ctadl_ir::ssa::transform_program(&mut cir, true);
        }
        if pre.copy_prop {
            ctadl_ir::ssa::propagate_copies(&mut cir);
        }
        self.cha.add_vmt(vmt);

        let tag = self.imports;
        self.imports += 1;

        for (idx, f) in cir.functions.iter_enumerated() {
            // A function with no blocks is a declaration, not a definition —
            // an extern, or a body the front end dropped. It has no summary to
            // compute, so it stays out of `procedure`; calls still name it.
            if f.blocks.is_empty() {
                continue;
            }
            self.scope = if self.opts.compact_names {
                format!("{tag}:{}", idx.index())
            } else {
                f.name.clone()
            };
            self.add_function(f);
        }
    }

    /// Materialize the EDB: run CHA over the collected callsites, work out the
    /// entries, and pour every relation into a [`Program`].
    #[allow(clippy::field_reassign_with_default)]
    pub fn finish(mut self) -> Program {
        self.resolve_dispatch();
        self.find_entries();

        let mut prog = Program::default();
        prog.procedure = self.procedure.into_iter().map(|p| (p,)).collect();
        prog.proc_type = self.proc_type.into_iter().collect();
        prog.entry = self.entry.into_iter().map(|p| (p,)).collect();
        prog.in_proc = self.in_proc;
        prog.alloc = self.alloc.into_iter().collect();
        prog.alloc_type = self.alloc_type.into_iter().collect();
        prog.const_assign = self.const_assign.into_iter().collect();
        prog.mov = self.mov.into_iter().collect();
        prog.load_field = self.load_field.into_iter().collect();
        prog.store_field = self.store_field.into_iter().collect();
        prog.load_static = self.load_static.into_iter().collect();
        prog.store_static = self.store_static.into_iter().collect();
        prog.load_index_const = self.load_index_const.into_iter().collect();
        prog.store_index_const = self.store_index_const.into_iter().collect();
        prog.direct_call = self.direct_call.into_iter().collect();
        prog.virtual_call = self.virtual_call.into_iter().collect();
        prog.actual_arg = self.actual_arg.into_iter().collect();
        prog.bind_ret = self.bind_ret.into_iter().collect();
        prog.formal = self.formal.into_iter().collect();
        prog.ret = self.ret.into_iter().collect();
        prog.direct_subtype = self.cha.subtype_edges();
        prog.proc_sig = self.cha.proc_sigs.into_iter().collect();
        prog.lookup = self.cha.lookup.into_iter().collect();
        prog
    }

    // ---------------------------------------------------------------------
    // Functions
    // ---------------------------------------------------------------------

    fn add_function(&mut self, f: &FunctionData) {
        self.proc = Proc::from(f.name.as_str());
        self.line = 0;
        self.procedure.insert(self.proc.clone());
        if let Some(ty) = declaring_type(&f.name) {
            self.proc_type.insert((self.proc.clone(), ty));
        }

        // CIR parameter 0 is `this` for an instance method, which is also this
        // schema's convention, so the indices carry over unchanged.
        for i in 0..f.params.parameters.len() {
            let v = self.param_var(i);
            self.formal.insert((self.proc.clone(), i, v));
        }

        for (bb, block) in f.blocks.iter_enumerated() {
            for (si, stmt) in block.statements.iter_enumerated() {
                self.begin(format!("{}#{}.{}", self.scope, bb.index(), si.index()));
                self.add_statement(f, stmt);
            }
            if let Some(term) = &block.terminator
                && let TerminatorKind::Return { args } = &term.kind
            {
                self.begin(format!("{}#{}.ret", self.scope, bb.index()));
                // Decision 1: the 0th value only. dex gives every return arity
                // 2, the second being an exception slot.
                if let Some(e) = args.first() {
                    let v = self.exp_var(f, e);
                    self.ret.insert((self.proc.clone(), v));
                }
            }
        }
    }

    // ---------------------------------------------------------------------
    // Statements
    // ---------------------------------------------------------------------

    fn add_statement(&mut self, f: &FunctionData, stmt: &Statement) {
        match &stmt.kind {
            StatementKind::Assign { dest, sources } => {
                let to = self.var(f, dest);
                // Resolve first: an access-path source emits its own statements,
                // and they should precede the assignment that consumes them.
                let srcs: Vec<Rhs> = sources.iter().map(|e| self.rhs(f, e)).collect();
                let s = self.site();
                for (i, rhs) in srcs.into_iter().enumerate() {
                    match rhs {
                        Rhs::Var(v) => {
                            self.mov.insert((s.clone(), to.clone(), v));
                        }
                        Rhs::Const(c) => {
                            self.const_assign.insert((s.clone(), to.clone(), c));
                        }
                        Rhs::Object(ty) => {
                            // One site per (statement, operand): a parallel
                            // assignment can allocate more than once.
                            let site = Alloc::from(format!("l:{s}:{i}"));
                            self.alloc.insert((s.clone(), to.clone(), site.clone()));
                            self.alloc_type.insert((site, ty));
                        }
                    }
                }
            }

            // `dest = source.field`, where `source` is an offset-only address.
            StatementKind::Load {
                dest,
                source,
                field,
            } => {
                let to = self.var(f, dest);
                if is_global(source) {
                    let s = self.site();
                    self.load_static.insert((
                        s,
                        to,
                        Type::from(GLOBALS),
                        Field::from(field.as_str()),
                    ));
                    return;
                }
                let base = self.address(f, source);
                let s = self.site();
                self.load_field
                    .insert((s, to, base, Field::from(field.as_str())));
            }

            // `dest.field := value`. `dest` is an address, read but never
            // defined; `field` is empty for a pure pointer-arithmetic store.
            StatementKind::Store { dest, field, value } => {
                let from = self.exp_var(f, value);
                if is_global(dest) && !field.as_str().is_empty() {
                    let s = self.site();
                    self.store_static.insert((
                        s,
                        Type::from(GLOBALS),
                        Field::from(field.as_str()),
                        from,
                    ));
                    return;
                }
                if field.as_str().is_empty() {
                    // `store x.[8] := v`: the last offset is the accessor.
                    let Some((base, off)) = self.address_split(f, dest) else {
                        return;
                    };
                    let s = self.site();
                    self.store_index_const.insert((s, base, off, from));
                } else {
                    let base = self.address(f, dest);
                    let s = self.site();
                    self.store_field
                        .insert((s, base, Field::from(field.as_str()), from));
                }
            }

            StatementKind::CallAssign { style, rets, args } => self.add_call(f, style, rets, args),

            // Only reachable with `Options::ssa`. A phi is a join, which for a
            // flow-insensitive analysis is exactly n moves.
            StatementKind::Phi { dest, operands } => {
                let to = self.var(f, dest);
                let srcs: Vec<_> = operands.iter().map(|(_, v)| self.var(f, v)).collect();
                let s = self.site();
                for v in srcs {
                    self.mov.insert((s.clone(), to.clone(), v));
                }
            }

            // An SSA anchor for parameters and the global heap. It defines no
            // data flow this schema does not already have from `formal`.
            StatementKind::ParamFlow { .. } | StatementKind::Nop => {}
        }
    }

    fn add_call(
        &mut self,
        f: &FunctionData,
        style: &CallStyle,
        rets: &[VariableRef],
        args: &[Exp],
    ) {
        // Everything that might emit a statement of its own happens before the
        // callsite's own label is taken.
        let argv: Vec<Var> = args.iter().map(|e| self.exp_var(f, e)).collect();

        // The operand dispatch reads, and whether the real arguments shift to
        // make room for it at slot 0.
        let (dispatch, shift) = match style {
            // A Java receiver is not in `args`; it *is* `par_0` of the callee.
            CallStyle::JavaCall { receiver, .. } => (Some(self.var(f, receiver)), 1),
            // A Lua receiver is already `args[0]`; re-emitting it at slot 0 is
            // a duplicate, which the set absorbs.
            CallStyle::LuaCall { receiver, .. } => (Some(self.var(f, receiver)), 0),
            // A function pointer is not a parameter at all. See the module
            // docs: it goes at slot 0 *beside* the real arguments.
            CallStyle::FuncPtrCall { callee, .. } => (Some(self.address(f, callee)), 0),
            _ => (None, 0),
        };

        let ret0 = rets.first().map(|r| self.var(f, r));
        let s = self.site();

        if let Some(d) = &dispatch {
            self.actual_arg.insert((s.clone(), 0, d.clone()));
        }
        for (i, a) in argv.into_iter().enumerate() {
            self.actual_arg.insert((s.clone(), i + shift, a));
        }
        // Decision 1 again: the 0th return value only.
        if let Some(r) = ret0 {
            self.bind_ret.insert((s.clone(), r));
        }

        match style {
            CallStyle::DirectCall {
                call_edges: CallEdges::Explicit(targets),
            } => {
                for t in targets {
                    self.direct_call.insert((s.clone(), Proc::from(t.as_str())));
                }
            }
            CallStyle::JavaCall {
                cls,
                simple_name,
                descriptor,
                ..
            } => {
                let key = Dispatch::Class(
                    cls.to_string(),
                    simple_name.to_string(),
                    descriptor.to_string(),
                );
                if let Some(d) = dispatch {
                    self.virtual_call.insert((s, d, key.sig()));
                    self.sites.insert(key);
                }
            }
            CallStyle::LuaCall { method, .. } => {
                let key = Dispatch::Lua(method.to_string());
                if let Some(d) = dispatch {
                    self.virtual_call.insert((s, d, key.sig()));
                    self.sites.insert(key);
                }
            }
            CallStyle::FuncPtrCall { signature, .. } => {
                let key = Dispatch::FnPtr(signature.clone().unwrap_or_default());
                if let Some(d) = dispatch {
                    self.virtual_call.insert((s, d, key.sig()));
                    self.sites.insert(key);
                }
            }
            // The front end could not say anything about this callee. Nothing
            // to emit: the arguments are already recorded, and with no callee
            // they flow nowhere, which is the right answer for an opaque call.
            CallStyle::Unknown => {}
        }
    }

    // ---------------------------------------------------------------------
    // Expressions and addresses
    // ---------------------------------------------------------------------

    /// What an expression contributes to an assignment, without forcing it
    /// through a temporary.
    fn rhs(&mut self, f: &FunctionData, e: &Exp) -> Rhs {
        match e {
            Exp::Variable(v) => Rhs::Var(self.var(f, v)),
            Exp::AccessPath(ap) => Rhs::Var(self.address(f, ap)),
            Exp::Str(_) | Exp::Bytes(_) => Rhs::Const(constant(e)),
            Exp::ObjectRef(o) => {
                if let CallObject::FunctionPtr(name) = o {
                    self.funcptrs.insert(Proc::from(name.as_ref()));
                }
                Rhs::Object(object_type(o))
            }
        }
    }

    /// An expression as a variable, introducing a temporary where the
    /// expression is not one already.
    fn exp_var(&mut self, f: &FunctionData, e: &Exp) -> Var {
        match self.rhs(f, e) {
            Rhs::Var(v) => v,
            Rhs::Const(c) => {
                let (s, t) = self.temp();
                self.const_assign.insert((s, t.clone(), c));
                t
            }
            Rhs::Object(ty) => {
                let (s, t) = self.temp();
                let site = Alloc::from(format!("l:{s}"));
                self.alloc.insert((s, t.clone(), site.clone()));
                self.alloc_type.insert((site, ty));
                t
            }
        }
    }

    /// The variable an address denotes, walking the offsets that lead to it.
    /// `x` is itself; `x.[8]` needs a load, and `x.[8].[4]` two.
    fn address(&mut self, f: &FunctionData, ap: &CirPath) -> Var {
        let mut cur = self.var(f, &ap.variable_ref);
        for fa in &ap.path.fields {
            let (s, t) = self.temp();
            let c = Const::from(fa.offset().0.to_string());
            self.load_index_const.insert((s, t.clone(), cur, c));
            cur = t;
        }
        cur
    }

    /// As [`Self::address`], but stopping one offset short and handing back
    /// that last offset — what a store through pointer arithmetic needs.
    /// A pathless address has no accessor and cannot be stored through.
    fn address_split(&mut self, f: &FunctionData, ap: &CirPath) -> Option<(Var, Const)> {
        let (last, rest) = ap.path.fields.split_last()?;
        let mut cur = self.var(f, &ap.variable_ref);
        for fa in rest {
            let (s, t) = self.temp();
            let c = Const::from(fa.offset().0.to_string());
            self.load_index_const.insert((s, t.clone(), cur, c));
            cur = t;
        }
        Some((cur, Const::from(last.offset().0.to_string())))
    }

    /// A CIR variable's name in this procedure's scope.
    ///
    /// Names are qualified even though the analysis keys every variable-bearing
    /// relation by procedure (through `in_proc`, `formal` or `ret`) and so does
    /// not need it: dex names every local `v0`, `v1`, ..., and an unqualified
    /// fact base is unreadable and one careless rule away from a silent
    /// cross-procedure join.
    fn var(&mut self, f: &FunctionData, v: &VariableRef) -> Var {
        let name = match &*v.variable {
            // The *unversioned* parameter is the incoming value, and is what
            // `formal` names. Without SSA every reference is unversioned and
            // this is the only case. With SSA every use is versioned and the
            // entry block anchors them with `par_i#0 = par_i`, so the versions
            // have to stay distinct from the formal — collapsing them here
            // would merge every write to a parameter back into its incoming
            // value and throw away exactly the precision SSA was run for.
            Variable::Param(i) => match v.version {
                None => return self.param_var(i.index()),
                Some(_) => format!("par{}", i.index()),
            },
            Variable::Local(i) => match f.locals.get(*i) {
                Some(d) => d.name.clone(),
                None => format!("local{}", i.index()),
            },
            // Only reachable where the heap is used as a plain value; a real
            // access goes through `load_static`/`store_static`, which is what
            // connects globals between procedures. This is deliberately an
            // opaque procedure-local, not a shared name.
            Variable::GlobalHeap => "$heap".to_string(),
        };
        match v.version {
            Some(n) => Var::from(format!("{name}#{n}@{}", self.scope)),
            None => Var::from(format!("{name}@{}", self.scope)),
        }
    }

    fn param_var(&self, i: ArgIdx) -> Var {
        Var::from(format!("par{i}@{}", self.scope))
    }

    // ---------------------------------------------------------------------
    // Statement labels
    // ---------------------------------------------------------------------

    /// Start a new CIR statement, whose EDB statements share `base`.
    fn begin(&mut self, base: String) {
        self.base = base;
        self.sub = 0;
    }

    /// The label of the statement being translated, recorded in `in_proc`.
    fn site(&mut self) -> Stmt {
        self.record(Stmt::from(self.base.as_str()))
    }

    /// A fresh label and variable for a temporary the translation needs.
    fn temp(&mut self) -> (Stmt, Var) {
        let n = self.sub;
        self.sub += 1;
        let s = self.record(Stmt::from(format!("{}~{n}", self.base)));
        // `base` already carries the scope, so this is unique on its own.
        let v = Var::from(format!("$t{n}@{}", self.base));
        (s, v)
    }

    fn record(&mut self, s: Stmt) -> Stmt {
        self.in_proc.push((s.clone(), self.proc.clone(), self.line));
        self.line += 1;
        s
    }

    // ---------------------------------------------------------------------
    // Dispatch and entries
    // ---------------------------------------------------------------------

    /// Turn every observed callsite key into `lookup` tuples, over the merged
    /// class hierarchy. This is ordinary CHA: for each type the receiver could
    /// have, the implementation that type inherits.
    fn resolve_dispatch(&mut self) {
        let sites = std::mem::take(&mut self.sites);
        for key in &sites {
            let sig = key.sig();
            match key {
                Dispatch::Class(cls, name, desc) => {
                    let cls = Type::from(cls.as_str());
                    let mut found = false;
                    for t in self.cha.subtypes(&cls) {
                        if let Some(p) = self.cha.resolve(&t, name, desc) {
                            self.cha.record(t, sig.clone(), p);
                            found = true;
                        }
                    }
                    // The declared class is not in the hierarchy: a library
                    // type the artifact does not ship. Every implementation of
                    // this signature is a candidate — imprecise, but the
                    // alternative is a call that resolves to nothing.
                    if !found && self.opts.cha_fallback {
                        for (t, p) in self.cha.declarers(name, desc) {
                            self.cha.record(t, sig.clone(), p);
                        }
                    }
                }
                // A Lua receiver has no declared class, so the candidates are
                // every class table that has this method, by name alone.
                Dispatch::Lua(name) => {
                    for (t, p) in self.cha.declarers(name, "") {
                        self.cha.record(t, sig.clone(), p);
                    }
                }
                // An indirect call reaches whatever function had its address
                // taken. The "type" of a function pointer is the function.
                Dispatch::FnPtr(_) => {
                    for p in &self.funcptrs {
                        self.cha.record(funcptr_type(p), sig.clone(), p.clone());
                    }
                }
            }
        }
        self.sites = sites;
    }

    /// Decision 3: an entry is a procedure with a body that nothing calls,
    /// directly or through dispatch.
    fn find_entries(&mut self) {
        let mut called: BTreeSet<&Proc> = BTreeSet::new();
        for (_, p) in &self.direct_call {
            called.insert(p);
        }
        for (_, _, p) in &self.cha.lookup {
            called.insert(p);
        }
        self.entry = self
            .procedure
            .iter()
            .filter(|p| !called.contains(p))
            .cloned()
            .collect();
    }
}

/// What the right-hand side of an assignment turned out to be.
enum Rhs {
    Var(Var),
    Const(Const),
    /// An allocation of this type; the site is named after the statement.
    Object(Type),
}

impl Dispatch {
    /// The signature a callsite dispatches on. It carries the declared class
    /// for Java: `sig_size` counts targets per signature, and keying on the
    /// bare name would make every `toString()` in the program one signature
    /// with hundreds of targets.
    fn sig(&self) -> Sig {
        match self {
            Dispatch::Class(cls, name, desc) => Sig::from(format!("{cls}->{name}{desc}")),
            Dispatch::Lua(name) => Sig::from(format!("lua->{name}")),
            Dispatch::FnPtr(sig) if sig.is_empty() => Sig::from("$fnptr"),
            Dispatch::FnPtr(sig) => Sig::from(format!("$fnptr({sig})")),
        }
    }
}

// =========================================================================
// Class hierarchy analysis
// =========================================================================

/// The method tables and hierarchy of every import, plus the `lookup` relation
/// built out of them.
#[derive(Default)]
struct Cha {
    /// `(class, name, descriptor)` → the implementation that class declares.
    decl: BTreeMap<(Type, String, String), Proc>,
    /// `(name, descriptor)` → every class declaring it, for the fallback and
    /// for Lua, which dispatches on the name alone.
    by_name: BTreeMap<(String, String), BTreeSet<(Type, Proc)>>,
    /// Subclass → its direct superclasses and interfaces.
    parents: BTreeMap<Type, BTreeSet<Type>>,
    /// The inverse, for enumerating a declared type's possible receivers.
    children: BTreeMap<Type, BTreeSet<Type>>,

    lookup: BTreeSet<(Type, Sig, Proc)>,
    proc_sigs: BTreeSet<(Proc, Sig)>,
}

impl Cha {
    fn add_vmt(&mut self, vmt: &VirtualMethodTable) {
        match vmt {
            VirtualMethodTable::Java {
                methods, hierarchy, ..
            } => {
                for (cls, name, desc, fq) in methods {
                    self.declare(
                        Type::from(cls.as_ref()),
                        name.to_string(),
                        desc.to_string(),
                        Proc::from(fq.as_ref()),
                    );
                }
                for (sub, supers) in hierarchy {
                    for sup in supers {
                        self.extend(Type::from(sub.as_ref()), Type::from(sup.as_ref()));
                    }
                }
            }
            // Lua has no descriptors: a method is unique within its class
            // table, and `__index` plays the role of a superclass.
            VirtualMethodTable::Lua {
                methods, hierarchy, ..
            } => {
                for (cls, name, fq) in methods {
                    self.declare(
                        Type::from(cls.as_ref()),
                        name.to_string(),
                        String::new(),
                        Proc::from(fq.as_ref()),
                    );
                }
                for (sub, supers) in hierarchy {
                    for sup in supers {
                        self.extend(Type::from(sub.as_ref()), Type::from(sup.as_ref()));
                    }
                }
            }
            // Binary front ends have no hierarchy at all; their indirect calls
            // resolve through the function pointers the IR takes addresses of,
            // which the translator collects as it goes.
            VirtualMethodTable::Native { .. } | VirtualMethodTable::Unknown => {}
        }
    }

    fn declare(&mut self, cls: Type, name: String, desc: String, imp: Proc) {
        self.decl
            .insert((cls.clone(), name.clone(), desc.clone()), imp.clone());
        self.by_name
            .entry((name, desc))
            .or_default()
            .insert((cls, imp));
    }

    fn extend(&mut self, sub: Type, sup: Type) {
        self.parents
            .entry(sub.clone())
            .or_default()
            .insert(sup.clone());
        self.children.entry(sup).or_default().insert(sub);
    }

    /// The implementation a receiver of type `t` inherits for `(name, desc)`,
    /// found by walking up. Breadth-first, so a superclass beats an interface
    /// at the same depth.
    fn resolve(&self, t: &Type, name: &str, desc: &str) -> Option<Proc> {
        let mut seen = BTreeSet::new();
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(t.clone());
        while let Some(cur) = queue.pop_front() {
            if !seen.insert(cur.clone()) {
                continue;
            }
            let key = (cur.clone(), name.to_string(), desc.to_string());
            if let Some(p) = self.decl.get(&key) {
                return Some(p.clone());
            }
            if let Some(parents) = self.parents.get(&cur) {
                queue.extend(parents.iter().cloned());
            }
        }
        None
    }

    /// `t` and everything below it — the runtime types a receiver declared `t`
    /// may hold, as CHA sees it.
    fn subtypes(&self, t: &Type) -> Vec<Type> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![t.clone()];
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur.clone()) {
                continue;
            }
            if let Some(kids) = self.children.get(&cur) {
                stack.extend(kids.iter().cloned());
            }
        }
        seen.into_iter().collect()
    }

    /// Every class declaring `(name, desc)`, wherever it sits.
    fn declarers(&self, name: &str, desc: &str) -> Vec<(Type, Proc)> {
        self.by_name
            .get(&(name.to_string(), desc.to_string()))
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default()
    }

    fn record(&mut self, t: Type, sig: Sig, p: Proc) {
        self.proc_sigs.insert((p.clone(), sig.clone()));
        self.lookup.insert((t, sig, p));
    }

    fn subtype_edges(&self) -> Vec<(Type, Type)> {
        self.parents
            .iter()
            .flat_map(|(sub, sups)| sups.iter().map(move |sup| (sub.clone(), sup.clone())))
            .collect()
    }
}

// =========================================================================
// Small helpers
// =========================================================================

/// Whether an address is rooted at the global heap rather than a variable.
fn is_global(ap: &CirPath) -> bool {
    matches!(&*ap.variable_ref.variable, Variable::GlobalHeap) && ap.path.fields.is_empty()
}

fn constant(e: &Exp) -> Const {
    match e {
        Exp::Str(s) => Const::from(s.as_ref()),
        Exp::Bytes(b) => Const::from(format!("$bytes:{}", b.len())),
        _ => Const::from("$const"),
    }
}

/// The type of the object an `ObjectRef` allocates. A function pointer's type
/// is the function it points at, which is what makes an indirect call resolve
/// through the points-to sets like any other dispatch.
fn object_type(o: &CallObject) -> Type {
    match o {
        CallObject::JavaObject(cls) => Type::from(cls.as_ref()),
        CallObject::LuaClass(cls) => Type::from(cls.as_ref()),
        CallObject::FunctionPtr(name) => funcptr_type(&Proc::from(name.as_ref())),
    }
}

fn funcptr_type(p: &Proc) -> Type {
    Type::from(format!("$fn:{p}"))
}

/// The class a JVM-style name declares: `Lcom/x/Y;->f(I)V` is declared in
/// `Lcom/x/Y;`. Front ends without qualified names contribute nothing here.
fn declaring_type(name: &str) -> Option<Type> {
    let (cls, _) = name.split_once("->")?;
    Some(Type::from(cls))
}

// =========================================================================
// Cutting an import down to size
// =========================================================================

/// Keep the `n` procedures with the most statements, and everything that
/// mentions only those. Type-level facts (`lookup`, `direct_subtype`,
/// `alloc_type`) are kept whole: they are small and dropping them would change
/// which calls count as critical, which is the thing being measured.
pub fn restrict(p: &Program, n: usize) -> Program {
    let mut by_size: Vec<(Proc, usize)> = {
        let mut counts: BTreeMap<Proc, usize> = Default::default();
        for (_, q, _) in &p.in_proc {
            *counts.entry(q.clone()).or_default() += 1;
        }
        counts.into_iter().collect()
    };
    by_size.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let keep: BTreeSet<Proc> = by_size.into_iter().take(n).map(|(q, _)| q).collect();
    let stmts: BTreeSet<Stmt> = p
        .in_proc
        .iter()
        .filter(|(_, q, _)| keep.contains(q))
        .map(|(s, _, _)| s.clone())
        .collect();

    let mut out = Program::default();
    let ks = |s: &Stmt| stmts.contains(s);
    let kp = |q: &Proc| keep.contains(q);

    out.procedure = p.procedure.iter().filter(|(q,)| kp(q)).cloned().collect();
    out.proc_type = p.proc_type.iter().filter(|(q, _)| kp(q)).cloned().collect();
    out.proc_sig = p.proc_sig.iter().filter(|(q, _)| kp(q)).cloned().collect();
    out.entry = p.entry.iter().filter(|(q,)| kp(q)).cloned().collect();
    out.in_proc = p.in_proc.iter().filter(|(s, _, _)| ks(s)).cloned().collect();
    out.alloc = p.alloc.iter().filter(|(s, _, _)| ks(s)).cloned().collect();
    out.const_assign = p.const_assign.iter().filter(|(s, _, _)| ks(s)).cloned().collect();
    out.mov = p.mov.iter().filter(|(s, _, _)| ks(s)).cloned().collect();
    out.load_field = p.load_field.iter().filter(|(s, _, _, _)| ks(s)).cloned().collect();
    out.store_field = p.store_field.iter().filter(|(s, _, _, _)| ks(s)).cloned().collect();
    out.load_static = p.load_static.iter().filter(|(s, _, _, _)| ks(s)).cloned().collect();
    out.store_static = p.store_static.iter().filter(|(s, _, _, _)| ks(s)).cloned().collect();
    out.load_index_const = p.load_index_const.iter().filter(|(s, _, _, _)| ks(s)).cloned().collect();
    out.store_index_const = p.store_index_const.iter().filter(|(s, _, _, _)| ks(s)).cloned().collect();
    out.load_index_var = p.load_index_var.iter().filter(|(s, _, _, _)| ks(s)).cloned().collect();
    out.store_index_var = p.store_index_var.iter().filter(|(s, _, _, _)| ks(s)).cloned().collect();
    out.direct_call = p.direct_call.iter().filter(|(s, _)| ks(s)).cloned().collect();
    out.virtual_call = p.virtual_call.iter().filter(|(s, _, _)| ks(s)).cloned().collect();
    out.actual_arg = p.actual_arg.iter().filter(|(s, _, _)| ks(s)).cloned().collect();
    out.bind_ret = p.bind_ret.iter().filter(|(s, _)| ks(s)).cloned().collect();
    out.formal = p.formal.iter().filter(|(q, _, _)| kp(q)).cloned().collect();
    out.ret = p.ret.iter().filter(|(q, _)| kp(q)).cloned().collect();
    out.alloc_type = p.alloc_type.clone();
    out.direct_subtype = p.direct_subtype.clone();
    out.lookup = p.lookup.clone();
    out
}
