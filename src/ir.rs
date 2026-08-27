//! The EDB schema: relations that encode a program.
//!
//! These are the *input* (extensional) relations only — the facts a front end
//! would emit for a program. No rules live here; the analysis (Hybrid Inlining,
//! §4 of the paper) is layered on top of this schema.
//!
//! The IR follows the language of §4.1.1:
//!
//! ```text
//! proc := stmt+
//! stmt := lv = expr | call proc(lv_0..n)
//! lv   := v | lv.f | lv[c] | lv[v]        f in F, v in V
//! expr := lv | c | l                      c in C, l in L
//! ```
//!
//! with the usual flattening assumptions of a Datalog-friendly IR: every
//! statement mentions at most one field/index access, temporaries have been
//! introduced where needed, and every statement has a unique [`Stmt`] id.
//!
//! Relation names are snake_case (they become field names on the generated
//! `Program` struct); the Datalog-conventional names are given in each comment,
//! e.g. `mov` is `Move`, `actual_arg` is `ActualArg`, `bind_ret` is `BindRet`.

use std::fmt;
use std::sync::Arc;

use ascent::ascent;

/// Interned-ish string newtypes. `Arc<str>` keeps clones cheap (Ascent clones
/// tuples freely) and keeps every column `Send + Sync`, so `ascent_par!` stays
/// available. Swapping in a real interner (`u32` ids) later only touches this
/// macro.
macro_rules! symbols {
    ($($(#[$m:meta])* $name:ident),* $(,)?) => {$(
        $(#[$m])*
        #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub Arc<str>);

        impl From<&str> for $name {
            fn from(s: &str) -> Self { Self(Arc::from(s)) }
        }

        impl From<String> for $name {
            fn from(s: String) -> Self { Self(Arc::from(s)) }
        }

        impl AsRef<str> for $name {
            fn as_ref(&self) -> &str { &self.0 }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&*self.0, f)
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!(stringify!($name), "({:?})"), &*self.0)
            }
        }
    )*};
}

symbols! {
    /// A procedure implementation (`proc`), e.g. `FacadeImpl.foo`.
    Proc,
    /// A unique statement label. Statement identity matters here: Hybrid
    /// Inlining classifies *statements* as critical or non-critical.
    Stmt,
    /// A local variable or formal (`v in V`).
    Var,
    /// A field name (`f in F`).
    Field,
    /// A constant used as a value or as an index (`c in C`).
    Const,
    /// An allocation site / abstract location (`l in L`).
    Alloc,
    /// A class or interface type.
    Type,
    /// A virtual callee's signature, resolved against a receiver's type by
    /// [`Program::lookup`], e.g. `poly(Obj)`.
    Sig,
}

/// Position of a formal parameter or actual argument. Index 0 is `par_0`, the
/// receiver (`this`) for instance methods, matching `call proc(lv_0..n)`.
pub type ArgIdx = usize;

/// Position of a statement within its enclosing procedure's body.
pub type Line = usize;

ascent! {
    /// The program under analysis, as a set of EDB relations. Populate the
    /// public fields directly; there are no rules yet, so `run()` is a no-op.
    pub struct Program;

    // ---------------------------------------------------------------------
    // Program structure
    // ---------------------------------------------------------------------

    /// `Procedure(p)`: `p` is a procedure with a body we can see.
    relation procedure(Proc);

    /// `ProcType(p, t)`: `p` is declared in class/interface `t`.
    relation proc_type(Proc, Type);

    /// `ProcSig(p, s)`: `p` implements signature `s` (used by dispatch).
    relation proc_sig(Proc, Sig);

    /// `Entry(p)`: `p` is a root/entry procedure, e.g. `service()`.
    relation entry(Proc);

    /// `InProc(s, p, n)`: statement `s` is the `n`-th statement of `p`'s body.
    /// This is `Lambda(p)` from §4.1.1, with source order retained so a
    /// flow-sensitive client can use it (the pointer analysis ignores `n`).
    relation in_proc(Stmt, Proc, Line);

    // ---------------------------------------------------------------------
    // Assignments: lv = expr
    // ---------------------------------------------------------------------

    /// `Alloc(s, v, l)`: `v = new ...` at allocation site `l`.
    relation alloc(Stmt, Var, Alloc);

    /// `AllocType(l, t)`: the site `l` allocates an object of type `t`.
    relation alloc_type(Alloc, Type);

    /// `ConstAssign(s, v, c)`: `v = c`.
    relation const_assign(Stmt, Var, Const);

    /// `Move(s, to, from)`: `to = from`. (Named `mov` because `move` is a
    /// Rust keyword and Ascent cannot use a raw identifier for a relation.)
    relation mov(Stmt, Var, Var);

    /// `LoadField(s, to, base, f)`: `to = base.f`.
    relation load_field(Stmt, Var, Var, Field);

    /// `StoreField(s, base, f, from)`: `base.f = from`.
    relation store_field(Stmt, Var, Field, Var);

    /// `LoadStatic(s, to, t, f)`: `to = t.f` for a static/global field.
    relation load_static(Stmt, Var, Type, Field);

    /// `StoreStatic(s, t, f, from)`: `t.f = from`.
    relation store_static(Stmt, Type, Field, Var);

    /// `LoadIndexConst(s, to, base, c)`: `to = base[c]`.
    relation load_index_const(Stmt, Var, Var, Const);

    /// `StoreIndexConst(s, base, c, from)`: `base[c] = from`.
    relation store_index_const(Stmt, Var, Const, Var);

    /// `LoadIndexVar(s, to, base, i)`: `to = base[i]` with a *variable* index.
    /// Critical: the index is unknown until the caller's context is known.
    relation load_index_var(Stmt, Var, Var, Var);

    /// `StoreIndexVar(s, base, i, from)`: `base[i] = from`. Also critical.
    relation store_index_var(Stmt, Var, Var, Var);

    // ---------------------------------------------------------------------
    // Calls: call proc(lv_0..n)
    // ---------------------------------------------------------------------

    /// `DirectCall(s, callee)`: the callee is statically known (static call,
    /// constructor, `super`, or a devirtualized site).
    relation direct_call(Stmt, Proc);

    /// `VirtualCall(s, recv, sig)`: `recv.sig(...)`, dispatched on the runtime
    /// type of `recv`. Critical: the implementation depends on the context.
    relation virtual_call(Stmt, Var, Sig);

    /// `ActualArg(s, i, v)`: `v` is the `i`-th argument at callsite `s`.
    /// For a virtual call, argument 0 is the receiver.
    relation actual_arg(Stmt, ArgIdx, Var);

    /// `BindRet(s, v)`: `v = <callsite s>`; absent when the result is dropped.
    relation bind_ret(Stmt, Var);

    /// `Formal(p, i, v)`: `v` is `par_i@p`. Index 0 is `this` for instance
    /// methods.
    relation formal(Proc, ArgIdx, Var);

    /// `Return(p, v)`: `v` flows to `ret@p`. A procedure may have several
    /// return statements, hence several facts.
    relation ret(Proc, Var);

    // ---------------------------------------------------------------------
    // Type hierarchy, for virtual dispatch
    // ---------------------------------------------------------------------

    /// `DirectSubtype(sub, super)`: immediate `extends` / `implements` edge.
    relation direct_subtype(Type, Type);

    /// `Lookup(t, sig, p)`: dispatching `sig` on a receiver of runtime type
    /// `t` selects implementation `p` — `dispatch(a, proc)` of §4.1.1,
    /// precomputed by the front end from the type hierarchy.
    relation lookup(Type, Sig, Proc);
}
