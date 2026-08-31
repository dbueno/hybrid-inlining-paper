//! Access paths and summary constraints (§4.1.1 of the paper).
//!
//! §4 represents an abstract state `a ∈ 𝔄` as a set of set constraints over
//! *access paths* `ω ∈ 𝕍 × (𝔽 ∪ ℂ)*`:
//!
//! ```text
//! ω ⊇ ω′        ω ⊇ {l}        ω ⊇ {c}
//! ```
//!
//! and an abstract summary `c` is `a ↦ a ∪ a_n`: a procedure's summary *is*
//! the set of new constraints `a_n` it adds to any precondition. In a
//! finished summary the paths are rooted at the *symbolic variables* the
//! analysis introduces per procedure (§2.1 "Summarization"): `par_i@p` for
//! the `i`-th formal and `ret@p` for the return value. While a procedure is
//! still being summarized, paths may also be rooted at its locals; those are
//! eliminated ("removing the inaccessible variables") before the summary is
//! published.
//!
//! The accessor alphabet is a field `.f` (`f ∈ 𝔽`), a constant index `[c]`
//! (`c ∈ ℂ`), or `[π]`, the paper's special symbol for an index that cannot
//! be decided yet (Definition (5) of Figure 4): a variable index whose
//! points-to set is not all constants.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::Arc;

use crate::ir::{Alloc, ArgIdx, Const, Field, Proc, Stmt, Var};

/// The identity of a *pending critical statement* — a critical statement
/// (§3.2.1) that has been kept as a placeholder in a hybrid summary
/// `𝔥 = (𝔠, S)` instead of being summarized under ⊤.
///
/// Propagating a hybrid summary into a caller (§3.2, "Propagation") renames
/// the placeholder, so an instance needs an identity *per holder*: the
/// original statement plus the chain of callsites it has been propagated
/// through. That chain is a call string, and bounding its length is the
/// k-limit of §3.2.2.
///
/// `chain` is ordered innermost-first: `⟨L25@L28·L31b⟩` is the `L25` instance
/// that reached `bar1` by being propagated out of `foo` through `L28` and then
/// out of `mid` through `L31b`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CritId {
    /// The critical statement itself.
    pub stmt: Stmt,
    /// Callsites the instance has been propagated through, innermost first.
    pub chain: Arc<[Stmt]>,
}

impl CritId {
    /// The instance as it originates, in the procedure that syntactically
    /// contains the critical statement.
    pub fn origin(stmt: impl Into<Stmt>) -> Self {
        Self {
            stmt: stmt.into(),
            chain: Vec::new().into(),
        }
    }

    /// Propagate one level out: the holder `p` is inlined at callsite `site`
    /// in some caller `q`, so the instance becomes a pending of `q`.
    pub fn push(&self, site: &Stmt) -> Self {
        let mut chain = self.chain.to_vec();
        chain.push(site.clone());
        Self {
            stmt: self.stmt.clone(),
            chain: chain.into(),
        }
    }

    /// Rename a callee's own pending `self` into the holder of the critical
    /// statement `outer` it is being inlined at (hybrid-in-hybrid, §5 of the
    /// plan): the callsite crossed is `outer.stmt`, and `outer`'s own chain
    /// follows.
    pub fn nest(&self, outer: &CritId) -> Self {
        let mut chain = self.chain.to_vec();
        chain.push(outer.stmt.clone());
        chain.extend(outer.chain.iter().cloned());
        Self {
            stmt: self.stmt.clone(),
            chain: chain.into(),
        }
    }

    /// How far this instance has been propagated: the value the k-limit bounds.
    pub fn depth(&self) -> usize {
        self.chain.len()
    }

    /// The depth [`CritId::nest`] would produce, without building it.
    pub fn nest_depth(&self, outer: &CritId) -> usize {
        self.chain.len() + 1 + outer.chain.len()
    }
}

impl fmt::Display for CritId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "⟨{}", self.stmt)?;
        for (n, site) in self.chain.iter().enumerate() {
            write!(f, "{}{site}", if n == 0 { "@" } else { "·" })?;
        }
        write!(f, "⟩")
    }
}

impl fmt::Debug for CritId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// The root of an access path: a program variable, one of the symbolic
/// variables the analysis invents to stand for values that flow into or out
/// of a procedure, or one of the placeholder nodes of a pending critical
/// statement.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Base {
    /// A local of the procedure being summarized. Transitively eliminated
    /// before the summary is published, so never seen by a caller.
    Var(Var),
    /// `par_i@p`: whatever the caller passes as `p`'s `i`-th argument.
    /// Index 0 is the receiver, matching [`crate::ir`]'s `formal`.
    Param(Proc, ArgIdx),
    /// `ret@p`: `p`'s return value.
    Ret(Proc),
    /// The `i`-th operand of a pending critical statement. This is the
    /// paper's "critical statements are connected with all the variables they
    /// access" made literal: the placeholder is an ordinary node of the
    /// constraint graph, so operands reach it by the usual `⊇` edges.
    CritSlot(CritId, ArgIdx),
    /// The result of a pending critical statement.
    CritRet(CritId),
}

impl Base {
    /// True for the symbolic roots — everything except a local. Only symbolic
    /// roots survive into a published summary, and only they can be `free(𝔞)`.
    pub fn is_symbolic(&self) -> bool {
        !matches!(self, Base::Var(_))
    }

    /// The pending instance this root belongs to, if any.
    pub fn crit_id(&self) -> Option<&CritId> {
        match self {
            Base::CritSlot(id, _) | Base::CritRet(id) => Some(id),
            _ => None,
        }
    }
}

impl From<Var> for Base {
    fn from(v: Var) -> Self {
        Base::Var(v)
    }
}

impl fmt::Display for Base {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Base::Var(v) => write!(f, "{v}"),
            Base::Param(p, i) => write!(f, "par_{i}@{p}"),
            Base::Ret(p) => write!(f, "ret@{p}"),
            Base::CritSlot(id, i) => write!(f, "{id}:arg{i}"),
            Base::CritRet(id) => write!(f, "{id}:res"),
        }
    }
}

impl fmt::Debug for Base {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// One step of an access path's suffix.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Accessor {
    /// `.f`
    Field(Field),
    /// `[c]`
    Index(Const),
    /// `[π]`: an index the analysis cannot decide under the current context.
    IndexUnknown,
}

impl fmt::Display for Accessor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Accessor::Field(fld) => write!(f, ".{fld}"),
            Accessor::Index(c) => write!(f, "[{c}]"),
            Accessor::IndexUnknown => write!(f, "[π]"),
        }
    }
}

impl fmt::Debug for Accessor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// An access path's *suffix*: the accessor sequence, with no root.
///
/// This is what the bound on access paths (`Paths` in [`crate::ir::edb`])
/// ranges over. A whole path cannot be enumerated ahead of the analysis — a
/// [`Base::CritSlot`] carries a call string the fixpoint invents — but a
/// suffix can, and the suffix is the only part of a path that ever grows:
/// [`AccessPath::rebase`] moves a root and leaves the suffix alone, so every
/// rule that lengthens a path lengthens this.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Suffix(pub Arc<[Accessor]>);

impl Suffix {
    /// The empty suffix, ε — the suffix of a bare root.
    ///
    /// One shared allocation for the whole program. `ε` is the prefix of
    /// every split a depth-1 path has, and depth 1 is where most of a real
    /// program's paths sit, so [`Suffix::splits`] asks for this often enough
    /// that handing back an `Arc` beats building an empty one.
    pub fn empty() -> Self {
        static EMPTY: std::sync::OnceLock<Arc<[Accessor]>> = std::sync::OnceLock::new();
        Self(Arc::clone(EMPTY.get_or_init(|| Vec::new().into())))
    }

    /// The accessors, in order.
    pub fn as_slice(&self) -> &[Accessor] {
        &self.0
    }

    /// How many accessors: the *depth* of any path carrying this suffix.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// True for ε.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// `self` followed by `rest`.
    pub fn extended(&self, rest: &[Accessor]) -> Self {
        let mut accessors = self.0.to_vec();
        accessors.extend_from_slice(rest);
        Self(accessors.into())
    }

    /// `a` followed by `self`. The direction the syntactic bound builds in:
    /// an outer accessor is discovered *after* the suffix beneath it.
    pub fn prepended(&self, a: &Accessor) -> Self {
        let mut accessors = Vec::with_capacity(self.0.len() + 1);
        accessors.push(a.clone());
        accessors.extend_from_slice(&self.0);
        Self(accessors.into())
    }

    /// Every way to cut this suffix into a prefix and a *non-empty* rest:
    /// `.f.g` yields `(ε, .f.g)` and `(.f, .g)`; `ε` yields nothing.
    ///
    /// This is the decomposition suffix congruence joins on. Doing it here,
    /// once per observed path, is what lets the join itself key on a whole
    /// path rather than on a base — see the `used_ext` relation of
    /// [`crate::analysis`].
    pub fn splits(&self) -> impl Iterator<Item = (Suffix, Suffix)> + '_ {
        (0..self.0.len()).map(|i| match i {
            // The whole-path split, which every path of depth 1 or more has
            // and a depth-1 path has only: both halves are already allocated.
            0 => (Suffix::empty(), self.clone()),
            _ => (Suffix(self.0[..i].into()), Suffix(self.0[i..].into())),
        })
    }
}

impl From<Vec<Accessor>> for Suffix {
    fn from(v: Vec<Accessor>) -> Self {
        Self(v.into())
    }
}

impl fmt::Display for Suffix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "ε");
        }
        for a in self.0.iter() {
            write!(f, "{a}")?;
        }
        Ok(())
    }
}

impl fmt::Debug for Suffix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// An access path `ω ∈ 𝕍 × (𝔽 ∪ ℂ)*`, e.g. `par_1@getP["cur"]` or
/// `ret@p.f[π]`. The suffix is shared (`Arc`) because Ascent clones tuple
/// values freely; extending a path allocates a fresh suffix.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AccessPath {
    pub base: Base,
    pub accessors: Arc<[Accessor]>,
}

impl AccessPath {
    /// The bare path `base`, with no accessors.
    pub fn new(base: Base) -> Self {
        Self {
            base,
            accessors: Vec::new().into(),
        }
    }

    /// The path `v` for a program variable, per Definition (1) of Figure 4:
    /// `eval(v)(a) := {v}`.
    pub fn var(v: impl Into<Var>) -> Self {
        Self::new(Base::Var(v.into()))
    }

    /// The path `par_i@p`.
    pub fn param(p: impl Into<Proc>, i: ArgIdx) -> Self {
        Self::new(Base::Param(p.into(), i))
    }

    /// The path `ret@p`.
    pub fn ret(p: impl Into<Proc>) -> Self {
        Self::new(Base::Ret(p.into()))
    }

    /// The placeholder node for the `i`-th operand of a pending critical
    /// statement. Operand 0 is the receiver of a virtual call.
    pub fn crit_slot(id: CritId, i: ArgIdx) -> Self {
        Self::new(Base::CritSlot(id, i))
    }

    /// The placeholder node for a pending critical statement's result.
    pub fn crit_ret(id: CritId) -> Self {
        Self::new(Base::CritRet(id))
    }

    fn extended(&self, a: Accessor) -> Self {
        let mut suffix = self.accessors.to_vec();
        suffix.push(a);
        Self {
            base: self.base.clone(),
            accessors: suffix.into(),
        }
    }

    /// `ω.f`
    pub fn field(&self, f: impl Into<Field>) -> Self {
        self.extended(Accessor::Field(f.into()))
    }

    /// `ω[c]`
    pub fn index(&self, c: impl Into<Const>) -> Self {
        self.extended(Accessor::Index(c.into()))
    }

    /// `ω[π]`
    pub fn index_unknown(&self) -> Self {
        self.extended(Accessor::IndexUnknown)
    }

    /// True for a bare root: a variable or symbolic variable itself.
    pub fn is_base(&self) -> bool {
        self.accessors.is_empty()
    }

    /// The same suffix hung off a different root. This is the whole of a
    /// substitution σ: inlining renames roots and keeps suffixes (§2.1).
    pub fn rebase(&self, base: Base) -> Self {
        Self {
            base,
            accessors: Arc::clone(&self.accessors),
        }
    }

    /// This path's accessor sequence, without its root — the thing the
    /// access-path bound is stated over.
    pub fn suffix(&self) -> Suffix {
        Suffix(Arc::clone(&self.accessors))
    }

    /// This path's root carrying `suffix` instead of its own. The dual of
    /// [`AccessPath::rebase`], and how a rule that has already built and
    /// checked a suffix turns it back into a path without rebuilding it.
    pub fn with_suffix(&self, suffix: &Suffix) -> Self {
        Self {
            base: self.base.clone(),
            accessors: Arc::clone(&suffix.0),
        }
    }

    /// This path with `rest` appended.
    pub fn extend(&self, rest: &[Accessor]) -> Self {
        let mut accessors = self.accessors.to_vec();
        accessors.extend_from_slice(rest);
        Self {
            base: self.base.clone(),
            accessors: accessors.into(),
        }
    }

    /// If `self` is `prefix` followed by more accessors, the extra accessors.
    ///
    /// Suffix congruence used to test this pair by pair; it now joins on
    /// [`Suffix::splits`] instead, which decides the same relation once per
    /// observed path. See the `used_ext` relation of [`crate::analysis`].
    /// `ω.f.g`.strip_prefix(`ω`) is `[.f, .g]`; unrelated paths give `None`.
    pub fn strip_prefix(&self, prefix: &AccessPath) -> Option<&[Accessor]> {
        if self.base != prefix.base || self.accessors.len() < prefix.accessors.len() {
            return None;
        }
        let (head, rest) = self.accessors.split_at(prefix.accessors.len());
        (head == &*prefix.accessors).then_some(rest)
    }
}

impl fmt::Display for AccessPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.base)?;
        for a in self.accessors.iter() {
            write!(f, "{a}")?;
        }
        Ok(())
    }
}

impl fmt::Debug for AccessPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// An element of a points-to set: what the right-hand side of a constraint
/// contributes to `pt(ω)`.
///
/// The `Path` case is what makes the whole scheme work. A compositional
/// summary is computed without a caller, so `pt(ω)` genuinely may contain
/// *symbolic* paths (§4.1.2) — "whatever the caller passes as `par_1@p`" — and
/// the analysis must never drop them. Adequacy (`Φ_a`, §4.1.3) is then exactly
/// the absence of such a tuple: `pt(recv) ∩ free(𝔞) = ∅` holds iff `pt(recv)`
/// contains no `Path` rooted at something still visible outside the holder.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PtVal {
    /// `ω ⊇ ω′`: an as-yet-unknown value, named by the path it will come from.
    Path(AccessPath),
    /// `ω ⊇ {l}`: the object allocated at site `l`.
    Alloc(Alloc),
    /// `ω ⊇ {c}`: the constant `c`.
    Const(Const),
}

impl PtVal {
    /// True for [`PtVal::Path`] — a value the caller may still change.
    pub fn is_path(&self) -> bool {
        matches!(self, PtVal::Path(_))
    }

    /// The constraint `sup ⊇ self`.
    pub fn constrain(&self, sup: AccessPath) -> Constraint {
        match self {
            PtVal::Path(sub) => Constraint::Path {
                sup,
                sub: sub.clone(),
            },
            PtVal::Alloc(sub) => Constraint::Alloc {
                sup,
                sub: sub.clone(),
            },
            PtVal::Const(sub) => Constraint::Const {
                sup,
                sub: sub.clone(),
            },
        }
    }
}

impl fmt::Display for PtVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PtVal::Path(w) => write!(f, "{w}"),
            PtVal::Alloc(l) => write!(f, "{{{l}}}"),
            PtVal::Const(c) => write!(f, "{{{c}}}"),
        }
    }
}

impl fmt::Debug for PtVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// One set constraint of an abstract state (§4.1.1).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constraint {
    /// `ω ⊇ ω′`: everything `ω′` may point to, `ω` may point to.
    Path { sup: AccessPath, sub: AccessPath },
    /// `ω ⊇ {l}`: `ω` may point to the object allocated at site `l`.
    Alloc { sup: AccessPath, sub: Alloc },
    /// `ω ⊇ {c}`: `ω` may hold the constant `c`.
    Const { sup: AccessPath, sub: Const },
}

impl Constraint {
    /// The access paths this constraint mentions, left-hand side first.
    pub fn paths(&self) -> impl Iterator<Item = &AccessPath> {
        let (lhs, rhs) = match self {
            Constraint::Path { sup, sub } => (sup, Some(sub)),
            Constraint::Alloc { sup, .. } | Constraint::Const { sup, .. } => (sup, None),
        };
        std::iter::once(lhs).chain(rhs)
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Path { sup, sub } => write!(f, "{sup} ⊇ {sub}"),
            Constraint::Alloc { sup, sub } => write!(f, "{sup} ⊇ {{{sub}}}"),
            Constraint::Const { sup, sub } => write!(f, "{sup} ⊇ {{{sub}}}"),
        }
    }
}

impl fmt::Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// An abstract summary `c : a ↦ a ∪ a_n`, represented by the new constraints
/// `a_n` the procedure contributes.
pub type Summary = BTreeSet<Constraint>;

#[cfg(test)]
mod tests {
    use super::*;

    // Figure 5's getP: `return map[key]` where map is par_1 and key is
    // par_2. Under the context that pins key to "cur" the result is
    // par_1@getP["cur"]; with no context the index is undecidable, π.
    #[test]
    fn display_matches_the_papers_notation() {
        let map = AccessPath::param("getP", 1);
        assert_eq!(map.index(r#""cur""#).to_string(), r#"par_1@getP["cur"]"#);
        assert_eq!(map.index_unknown().to_string(), "par_1@getP[π]");
        assert_eq!(AccessPath::ret("getP").field("g").to_string(), "ret@getP.g");
        assert_eq!(AccessPath::var("tv").to_string(), "tv");

        let c = Constraint::Path {
            sup: AccessPath::ret("FacadeImpl.id"),
            sub: AccessPath::param("FacadeImpl.id", 1),
        };
        assert_eq!(c.to_string(), "ret@FacadeImpl.id ⊇ par_1@FacadeImpl.id");
    }

    #[test]
    fn extending_a_path_leaves_the_original_untouched() {
        let map = AccessPath::param("getP", 1);
        let cur = map.index(r#""cur""#);
        assert!(map.is_base());
        assert!(!cur.is_base());
        assert_eq!(map.base, cur.base);
    }

    // Figure 1's L25 instance as it walks out of foo -> mid -> bar1.
    #[test]
    fn a_crit_id_prints_its_call_string() {
        let c0 = CritId::origin("L25");
        assert_eq!(c0.to_string(), "⟨L25⟩");
        assert_eq!(c0.depth(), 0);

        let c1 = c0.push(&"L28".into());
        let c2 = c1.push(&"L31b".into());
        assert_eq!(c1.to_string(), "⟨L25@L28⟩");
        assert_eq!(c2.to_string(), "⟨L25@L28·L31b⟩");
        assert_eq!(c2.depth(), 2);

        // The placeholder nodes are ordinary access-path roots.
        assert_eq!(
            AccessPath::crit_slot(c2.clone(), 0).to_string(),
            "⟨L25@L28·L31b⟩:arg0"
        );
        assert_eq!(AccessPath::crit_ret(c2).to_string(), "⟨L25@L28·L31b⟩:res");
    }

    // Inlining a callee that is itself hybrid renames the callee's pending
    // into the caller; the callsite crossed is the critical statement.
    #[test]
    fn nesting_splices_the_outer_call_string_on() {
        let inner = CritId::origin("L99").push(&"L50".into());
        let outer = CritId::origin("L25").push(&"L28".into());
        let nested = inner.nest(&outer);
        assert_eq!(nested.to_string(), "⟨L99@L50·L25·L28⟩");
        assert_eq!(nested.depth(), inner.nest_depth(&outer));
    }

    #[test]
    fn rebasing_keeps_the_suffix_and_stripping_recovers_it() {
        let callee = AccessPath::param("getP", 1).index(r#""cur""#);
        let sigma = callee.rebase(Base::Var("map@caller".into()));
        assert_eq!(sigma.to_string(), r#"map@caller["cur"]"#);

        let root = AccessPath::var("map@caller");
        assert_eq!(sigma.strip_prefix(&root).unwrap().len(), 1);
        assert_eq!(root.strip_prefix(&sigma), None);
        assert_eq!(sigma.strip_prefix(&callee), None); // different roots
        assert_eq!(root.extend(sigma.strip_prefix(&root).unwrap()), sigma);
    }

    #[test]
    fn only_locals_are_non_symbolic() {
        let id = CritId::origin("L25");
        assert!(!Base::Var("tv".into()).is_symbolic());
        assert!(Base::Param("foo".into(), 1).is_symbolic());
        assert!(Base::Ret("foo".into()).is_symbolic());
        assert!(Base::CritSlot(id.clone(), 0).is_symbolic());
        assert!(Base::CritRet(id.clone()).is_symbolic());
        assert_eq!(Base::CritRet(id.clone()).crit_id(), Some(&id));
        assert_eq!(Base::Ret("foo".into()).crit_id(), None);
    }

    #[test]
    fn a_pt_value_renders_as_the_constraint_it_stands_for() {
        let ret = AccessPath::ret("Z.poly");
        assert_eq!(
            PtVal::Alloc("l14".into())
                .constrain(ret.clone())
                .to_string(),
            "ret@Z.poly ⊇ {l14}"
        );
        assert_eq!(
            PtVal::Path(AccessPath::param("Y.poly", 1))
                .constrain(AccessPath::ret("Y.poly"))
                .to_string(),
            "ret@Y.poly ⊇ par_1@Y.poly"
        );
        assert!(PtVal::Path(ret).is_path());
        assert!(!PtVal::Const("0".into()).is_path());
    }

    #[test]
    fn a_constraint_yields_its_paths_lhs_first() {
        let l = AccessPath::ret("p");
        let r = AccessPath::param("p", 1);
        let subset = Constraint::Path {
            sup: l.clone(),
            sub: r.clone(),
        };
        assert_eq!(subset.paths().collect::<Vec<_>>(), vec![&l, &r]);
        let alloc = Constraint::Alloc {
            sup: l.clone(),
            sub: "l14".into(),
        };
        assert_eq!(alloc.paths().collect::<Vec<_>>(), vec![&l]);
    }
}
