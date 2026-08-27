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

use crate::ir::{Alloc, ArgIdx, Const, Field, Proc, Var};

/// The root of an access path: a program variable, or one of the symbolic
/// variables the analysis invents to stand for values that flow into or out
/// of a procedure.
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

    #[test]
    fn a_constraint_yields_its_paths_lhs_first() {
        let l = AccessPath::ret("p");
        let r = AccessPath::param("p", 1);
        let subset = Constraint::Path { sup: l.clone(), sub: r.clone() };
        assert_eq!(subset.paths().collect::<Vec<_>>(), vec![&l, &r]);
        let alloc = Constraint::Alloc { sup: l.clone(), sub: "l14".into() };
        assert_eq!(alloc.paths().collect::<Vec<_>>(), vec![&l]);
    }
}
