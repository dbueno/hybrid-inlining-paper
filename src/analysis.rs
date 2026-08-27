//! Hybrid Inlining (§3.2) for the compositional pointer analysis of §4.1.
//!
//! The analysis is a *round-based driver* around one stratified Ascent
//! program, [`Round`]. Each round is a complete re-derivation of every
//! procedure's summary from the EDB plus the resolutions discovered so far;
//! the driver ([`run_hybrid`]) accumulates resolutions until a round finds
//! nothing new.
//!
//! # Why a driver, and where the negations are
//!
//! The paper's `ready`/`Φ_a` machinery has one genuine cycle: resolving an
//! adequate critical statement adds constraints, which grow `pt`, which the
//! adequacy test negates over. No single stratified program can express that,
//! so it is broken across rounds. Everything *inside* a round is stratified,
//! and the macro checks it at compile time:
//!
//! | stratum | relations | negation |
//! |---------|-----------|----------|
//! | S1 | [`Round::sig_size`], [`Round::critical`], [`Round::eff_direct`] | `count` over the EDB (N1) |
//! | S2 | [`Round::edge`], [`Round::points`], [`Round::pending`], [`Round::pub_edge`] | `!resolved`, an input relation (N2) |
//! | S3 | [`Round::blocked`] | — (reads the `points` fixpoint) |
//! | S4 | [`Round::adequate`] | `!blocked` (N3) |
//! | S5 | [`Round::forced`], [`Round::dispatch`], [`Round::resolve_out`] | `!adequate` |
//!
//! S5 feeds nothing back into S2 — the feedback goes through the driver, as
//! the input relations [`Round::resolution`] and [`Round::resolved`] — which
//! is exactly what keeps the round stratified.
//!
//! # The constraint graph
//!
//! [`Round::edge`]`(p, sup, sub)` is `sup ⊇ sub` while `p` is being
//! summarized; [`Round::points`]`(p, ω, v)` is `v ∈ pt(ω)`. Critical
//! statements are *not* summarized: each pending instance contributes
//! placeholder nodes `CritSlot(id, i)` / `CritRet(id)` that are wired to the
//! statement's operands and result by ordinary `⊇` edges — the paper's
//! "critical statements are connected with all the variables they access",
//! made literal. Publishing a summary eliminates locals but keeps those
//! placeholders, and that is what makes the summary *hybrid*.

use std::collections::{BTreeMap, BTreeSet};

use ascent::aggregators::count;
use ascent::ascent;

use crate::access_path::{AccessPath, Accessor, Base, Constraint, CritId, PtVal, Summary};
use crate::ir::{Alloc, ArgIdx, Const, Field, Line, Proc, Program, Sig, Stmt, Type, Var};

ascent! {
    /// One round of Hybrid Inlining: a stratified derivation of every
    /// procedure's hybrid summary, given the EDB and the critical statements
    /// resolved by previous rounds.
    ///
    /// Build one with [`Round::for_program`]; the driver in [`run_hybrid`]
    /// owns the loop.
    pub struct Round;

    // =====================================================================
    // EDB — copied verbatim from `ir::Program` by `Round::for_program`.
    // =====================================================================

    relation procedure(Proc);
    relation entry(Proc);
    relation in_proc(Stmt, Proc, Line);
    relation alloc(Stmt, Var, Alloc);
    relation alloc_type(Alloc, Type);
    relation const_assign(Stmt, Var, Const);
    relation mov(Stmt, Var, Var);
    relation load_field(Stmt, Var, Var, Field);
    relation store_field(Stmt, Var, Field, Var);
    relation load_index_const(Stmt, Var, Var, Const);
    relation store_index_const(Stmt, Var, Const, Var);
    relation load_index_var(Stmt, Var, Var, Var);
    relation store_index_var(Stmt, Var, Var, Var);
    relation direct_call(Stmt, Proc);
    relation virtual_call(Stmt, Var, Sig);
    relation actual_arg(Stmt, ArgIdx, Var);
    relation bind_ret(Stmt, Var);
    relation formal(Proc, ArgIdx, Var);
    relation ret(Proc, Var);
    relation lookup(Type, Sig, Proc);

    // =====================================================================
    // Driver-fed inputs. These are what carries information between rounds,
    // and being inputs is what keeps every negation over them stratified.
    // =====================================================================

    /// The k-limit of §3.2.2, as a single tuple: a pending instance may be
    /// propagated while its call string is shorter than `k`.
    relation k_limit(usize);

    /// `resolution(p, id, callee)`: a previous round decided the pending
    /// critical statement `id`, held by `p`, may reach `callee`. The round
    /// re-inlines `callee`'s *current* summary at the placeholder, so a
    /// resolution keeps paying off as the callee's own summary improves.
    relation resolution(Proc, CritId, Proc);

    /// `index_resolution(p, id, acc)`: a previous round decided that the
    /// pending `lv[v]` access `id`, held by `p`, uses accessor `acc` — either
    /// a concrete `[c]` (one tuple per constant the index may hold) or `[π]`,
    /// the paper's undecidable index.
    relation index_resolution(Proc, CritId, Accessor);

    /// `resolved(p, id)`: the projection of `resolution` and
    /// `index_resolution` the negations use. Fed separately by the driver so
    /// it is unambiguously stratum 0.
    relation resolved(Proc, CritId);

    // =====================================================================
    // S1 — criticality and CHA devirtualization (N1)
    // =====================================================================

    /// The CHA target set of a signature, deduplicated over receiver types.
    relation sig_target(Sig, Proc);
    sig_target(sig.clone(), p.clone()) <-- lookup(_, sig, p);

    /// `|dispatch(⊤, proc)|` — the aggregation the criticality test negates.
    relation sig_size(Sig, usize);
    sig_size(sig.clone(), n) <-- virtual_call(_, _, sig), agg n = count() in sig_target(sig, _);

    /// A virtual call with a single CHA target is not critical: it is an
    /// ordinary direct call the front end simply did not resolve.
    relation mono_target(Stmt, Proc);
    mono_target(s.clone(), p.clone()) <--
        virtual_call(s, _, sig), sig_size(sig, n), if *n == 1, sig_target(sig, p);

    /// Callsites whose callee is statically known, and so may be summarized
    /// and inlined outright.
    relation eff_direct(Stmt, Proc);
    eff_direct(s.clone(), p.clone()) <-- direct_call(s, p);
    eff_direct(s.clone(), p.clone()) <-- mono_target(s, p);

    /// Critical statements (§4.1.3). Both kinds the paper identifies: a
    /// virtual call with more than one CHA target, and an assignment through
    /// `lv[v]`, whose index is not known until a caller pins it.
    relation critical(Stmt);
    critical(s.clone()) <-- virtual_call(s, _, sig), sig_size(sig, n), if *n > 1;
    critical(s.clone()) <-- load_index_var(s, _, _, _);
    critical(s.clone()) <-- store_index_var(s, _, _, _);

    // =====================================================================
    // S2 — the monotone core
    // =====================================================================

    /// `edge(p, sup, sub)`: the constraint `sup ⊇ sub` of `p`'s abstract
    /// state, over paths that may still be rooted at `p`'s locals.
    relation edge(Proc, AccessPath, AccessPath);

    /// `points(p, ω, v)`: `v ∈ pt(ω)` during `p`'s summarization.
    relation points(Proc, AccessPath, PtVal);

    // -- intraprocedural constraints, Figure 4 definitions 1-3 and 6-8 -----

    edge(p.clone(), AccessPath::var(to.clone()), AccessPath::var(from.clone())) <--
        mov(s, to, from), in_proc(s, p, _);

    points(p.clone(), AccessPath::var(v.clone()), PtVal::Alloc(l.clone())) <--
        alloc(s, v, l), in_proc(s, p, _);

    points(p.clone(), AccessPath::var(v.clone()), PtVal::Const(c.clone())) <--
        const_assign(s, v, c), in_proc(s, p, _);

    edge(p.clone(), AccessPath::var(to.clone()), AccessPath::var(base.clone()).field(f.clone())) <--
        load_field(s, to, base, f), in_proc(s, p, _);

    edge(p.clone(), AccessPath::var(base.clone()).field(f.clone()), AccessPath::var(from.clone())) <--
        store_field(s, base, f, from), in_proc(s, p, _);

    edge(p.clone(), AccessPath::var(to.clone()), AccessPath::var(base.clone()).index(c.clone())) <--
        load_index_const(s, to, base, c), in_proc(s, p, _);

    edge(p.clone(), AccessPath::var(base.clone()).index(c.clone()), AccessPath::var(from.clone())) <--
        store_index_const(s, base, c, from), in_proc(s, p, _);

    // -- the symbolic variables of §2.1 -----------------------------------

    edge(p.clone(), AccessPath::var(v.clone()), AccessPath::param(p.clone(), *i)) <--
        formal(p, i, v);

    edge(p.clone(), AccessPath::ret(p.clone()), AccessPath::var(v.clone())) <--
        ret(p, v);

    // -- closure ----------------------------------------------------------

    points(p.clone(), sup.clone(), v.clone()) <-- edge(p, sup, sub), points(p, sub, v);

    // The invariant adequacy depends on: `pt` never drops a symbolic path. A
    // compositional summary is computed without a caller, so "whatever the
    // caller passes as `par_1@p`" is a legitimate member of a points-to set
    // (§4.1.2) and must stay visible to `blocked`.
    points(p.clone(), sup.clone(), PtVal::Path(sub.clone())) <--
        edge(p, sup, sub), if sub.base.is_symbolic();

    /// Suffix congruence, `ω ⊇ ω′ ⟹ ω.a ⊇ ω′.a`, applied on demand: only for
    /// suffixes some path in `p` actually mentions, so the path set stays
    /// finite. Figure 1 has no field or index accesses, so this never fires
    /// there.
    relation path_used(Proc, Base, AccessPath);
    path_used(p.clone(), a.base.clone(), a.clone()) <-- edge(p, a, _);
    path_used(p.clone(), b.base.clone(), b.clone()) <-- edge(p, _, b);
    path_used(p.clone(), a.base.clone(), a.clone()) <-- points(p, a, _);

    edge(p.clone(), sup2.clone(), sub.extend(rest)) <--
        edge(p, sup, sub),
        let sup_base = sup.base.clone(),
        path_used(p, sup_base, sup2),
        if let Some(rest) = sup2.strip_prefix(sup),
        if !rest.is_empty();
    // The same congruence triggered from the other side: `ret@build ⊇ v` and
    // an observed `v["old"]` together justify `ret@build["old"] ⊇ v["old"]`,
    // which is how a store through a local reaches the published summary.
    edge(p.clone(), sup.extend(rest), sub2.clone()) <--
        edge(p, sup, sub),
        let sub_base = sub.base.clone(),
        path_used(p, sub_base, sub2),
        if let Some(rest) = sub2.strip_prefix(sub),
        if !rest.is_empty();

    // -- pending critical statements: origination and propagation ---------

    /// `crit_origin(p, s, id)`: the critical statement `s` sits in `p`, and
    /// `id` is its instance there, with an empty call string.
    relation crit_origin(Proc, Stmt, CritId);
    crit_origin(p.clone(), s.clone(), CritId::origin(s.clone())) <-- critical(s), in_proc(s, p, _);

    /// `pending(p, id)`: `p`'s summary carries `id` as a placeholder — the
    /// `S` of a hybrid summary `𝔥 = (𝔠, S)`.
    relation pending(Proc, CritId);
    pending(p.clone(), id.clone()) <-- crit_origin(p, _, id);

    // The placeholder is wired to the statement's operands and result. Every
    // later holder gets these edges for free, via the σ of inlining.
    edge(p.clone(), AccessPath::crit_slot(id.clone(), *i), AccessPath::var(a.clone())) <--
        crit_origin(p, s, id), actual_arg(s, i, a);
    edge(p.clone(), AccessPath::var(r.clone()), AccessPath::crit_ret(id.clone())) <--
        crit_origin(p, s, id), bind_ret(s, r);

    // `to = base[i]`: operand 0 is the base, operand 1 the index.
    edge(p.clone(), AccessPath::crit_slot(id.clone(), 0), AccessPath::var(base.clone())) <--
        crit_origin(p, s, id), load_index_var(s, _, base, _);
    edge(p.clone(), AccessPath::crit_slot(id.clone(), 1), AccessPath::var(i.clone())) <--
        crit_origin(p, s, id), load_index_var(s, _, _, i);
    edge(p.clone(), AccessPath::var(to.clone()), AccessPath::crit_ret(id.clone())) <--
        crit_origin(p, s, id), load_index_var(s, to, _, _);

    // `base[i] = from`: operand 2 is the stored value.
    edge(p.clone(), AccessPath::crit_slot(id.clone(), 0), AccessPath::var(base.clone())) <--
        crit_origin(p, s, id), store_index_var(s, base, _, _);
    edge(p.clone(), AccessPath::crit_slot(id.clone(), 1), AccessPath::var(i.clone())) <--
        crit_origin(p, s, id), store_index_var(s, _, i, _);
    edge(p.clone(), AccessPath::crit_slot(id.clone(), 2), AccessPath::var(from.clone())) <--
        crit_origin(p, s, id), store_index_var(s, _, _, from);

    // Propagation (§3.2): an unresolved placeholder moves into the caller,
    // where more context has accumulated. The k-limit bounds the call string
    // so recursion terminates.
    pending(q.clone(), id.push(s)) <--
        pending(p, id), !resolved(p, id),
        eff_direct(s, p), in_proc(s, q, _),
        k_limit(k), if id.depth() < *k;

    /// Whether propagation is still an option. Used (negated) in S5: a
    /// placeholder that can neither be resolved nor propagated must be
    /// ⊤-summarized here and now, or its constraints would be dropped.
    relation can_propagate(Proc, CritId);
    can_propagate(p.clone(), id.clone()) <--
        pending(p, id), eff_direct(s, p), in_proc(s, _, _),
        k_limit(k), if id.depth() < *k;

    /// The operand positions of a pending instance, and the signature it
    /// dispatches — both read off the original statement.
    relation crit_operand(CritId, ArgIdx);
    crit_operand(id.clone(), *i) <-- pending(_, id), let s = id.stmt.clone(), actual_arg(s, i, _);
    crit_operand(id.clone(), 0) <-- index_crit(id);
    crit_operand(id.clone(), 1) <-- index_crit(id);
    crit_operand(id.clone(), 2) <-- store_crit(id);

    /// Which kind of critical statement a pending instance stands for.
    relation call_crit(CritId);
    relation load_crit(CritId);
    relation store_crit(CritId);
    relation index_crit(CritId);
    call_crit(id.clone()) <--
        pending(_, id), let s = id.stmt.clone(), virtual_call(s, _, _);
    load_crit(id.clone()) <--
        pending(_, id), let s = id.stmt.clone(), load_index_var(s, _, _, _);
    store_crit(id.clone()) <--
        pending(_, id), let s = id.stmt.clone(), store_index_var(s, _, _, _);
    index_crit(id.clone()) <-- load_crit(id);
    index_crit(id.clone()) <-- store_crit(id);

    /// The operand whose points-to set decides the statement, and so the one
    /// `Φ_a` intersects against `free(𝔞)`: the receiver of a virtual call,
    /// the index of an `lv[v]` access.
    relation decisive_slot(CritId, ArgIdx);
    decisive_slot(id.clone(), 0) <-- call_crit(id);
    decisive_slot(id.clone(), 1) <-- index_crit(id);

    relation crit_sig(CritId, Sig);
    crit_sig(id.clone(), sig.clone()) <--
        pending(_, id), let s = id.stmt.clone(), virtual_call(s, _, sig);

    // -- publication: local elimination (§2.1), placeholders retained ------

    /// The published vocabulary of `p`: its symbolic variables, plus the
    /// placeholder nodes of its *unresolved* pendings (N2). Once resolved, a
    /// placeholder demotes to a local and is eliminated like any other.
    ///
    /// This is also `free(𝔞)` — the paths accessible outside `p`, which is
    /// what §4.1.3's adequacy predicate intersects `pt(recv)` against.
    relation pub_root(Proc, Base);
    pub_root(p.clone(), Base::Param(p.clone(), *i)) <-- formal(p, i, _);
    pub_root(p.clone(), Base::Ret(p.clone())) <-- procedure(p);
    pub_root(p.clone(), Base::CritRet(id.clone())) <-- pending(p, id), !resolved(p, id);
    pub_root(p.clone(), Base::CritSlot(id.clone(), *i)) <--
        pending(p, id), !resolved(p, id), crit_operand(id, i);

    /// `pub_edge(p, a, b)`: the constraint `a ⊇ b` of `p`'s published
    /// summary. Transitivity through locals has already happened inside
    /// `points`, so this is the local-eliminated closure.
    relation pub_edge(Proc, AccessPath, AccessPath);
    pub_edge(p.clone(), a.clone(), b.clone()) <--
        points(p, a, ?PtVal::Path(b)),
        let ab = a.base.clone(), pub_root(p, ab),
        let bb = b.base.clone(), pub_root(p, bb);

    /// `pub_points(p, a, v)`: the `a ⊇ {l}` / `a ⊇ {c}` half of the summary.
    relation pub_points(Proc, AccessPath, PtVal);
    pub_points(p.clone(), a.clone(), v.clone()) <--
        points(p, a, v), if !v.is_path(),
        let ab = a.base.clone(), pub_root(p, ab);

    // -- inlining a summary at a statically known callsite -----------------

    /// `root_map(s, from, to)`: the substitution σ_s a callsite induces on the
    /// callee's published roots. Suffixes are untouched; only roots move.
    relation root_map(Stmt, Base, Base);
    root_map(s.clone(), Base::Param(p.clone(), *i), Base::Var(a.clone())) <--
        eff_direct(s, p), actual_arg(s, i, a);
    root_map(s.clone(), Base::Ret(p.clone()), Base::Var(r.clone())) <--
        eff_direct(s, p), bind_ret(s, r);
    // A placeholder is renamed rather than resolved — this *is* propagation.
    root_map(s.clone(), Base::CritSlot(id.clone(), *i), Base::CritSlot(id.push(s), *i)) <--
        eff_direct(s, p), pending(p, id), !resolved(p, id), crit_operand(id, i),
        k_limit(k), if id.depth() < *k;
    root_map(s.clone(), Base::CritRet(id.clone()), Base::CritRet(id.push(s))) <--
        eff_direct(s, p), pending(p, id), !resolved(p, id),
        k_limit(k), if id.depth() < *k;

    edge(q.clone(), a.rebase(ta.clone()), b.rebase(tb.clone())) <--
        eff_direct(s, p), in_proc(s, q, _), pub_edge(p, a, b),
        let ab = a.base.clone(), root_map(s, ab, ta),
        let bb = b.base.clone(), root_map(s, bb, tb);

    points(q.clone(), a.rebase(ta.clone()), v.clone()) <--
        eff_direct(s, p), in_proc(s, q, _), pub_points(p, a, v),
        let ab = a.base.clone(), root_map(s, ab, ta);

    // -- inlining a summary at a *resolved* critical statement -------------

    /// `crit_map(p, id, from, to)`: the substitution σ_crit for a resolution.
    /// The callee's formals land on the placeholder's operand slots and its
    /// return on the placeholder's result, so the constraints the caller had
    /// already wired to the placeholder connect straight through.
    relation crit_map(Proc, CritId, Base, Base);
    crit_map(p.clone(), id.clone(), Base::Param(callee.clone(), *i), Base::CritSlot(id.clone(), *i)) <--
        resolution(p, id, callee), formal(callee, i, _);
    crit_map(p.clone(), id.clone(), Base::Ret(callee.clone()), Base::CritRet(id.clone())) <--
        resolution(p, id, callee);
    // Hybrid-in-hybrid: the callee's own placeholders are renamed into `p`.
    crit_map(p.clone(), id.clone(), Base::CritSlot(id2.clone(), *j), Base::CritSlot(id2.nest(id), *j)) <--
        resolution(p, id, callee), pending(callee, id2), !resolved(callee, id2),
        crit_operand(id2, j), k_limit(k), if id2.nest_depth(id) <= *k;
    crit_map(p.clone(), id.clone(), Base::CritRet(id2.clone()), Base::CritRet(id2.nest(id))) <--
        resolution(p, id, callee), pending(callee, id2), !resolved(callee, id2),
        k_limit(k), if id2.nest_depth(id) <= *k;

    pending(p.clone(), id2.nest(id)) <--
        resolution(p, id, callee), pending(callee, id2), !resolved(callee, id2),
        k_limit(k), if id2.nest_depth(id) <= *k;

    edge(p.clone(), a.rebase(ta.clone()), b.rebase(tb.clone())) <--
        resolution(p, id, callee), pub_edge(callee, a, b),
        let ab = a.base.clone(), crit_map(p, id, ab, ta),
        let bb = b.base.clone(), crit_map(p, id, bb, tb);

    points(p.clone(), a.rebase(ta.clone()), v.clone()) <--
        resolution(p, id, callee), pub_points(callee, a, v),
        let ab = a.base.clone(), crit_map(p, id, ab, ta);

    // -- resolving an lv[v] access ----------------------------------------

    // `eval(lv[v])(𝔞)` of Figure 4 definitions (4) and (5): the access path is
    // rooted at the base *operand itself*, extended by the decided accessor.
    // Suffix congruence then carries `ω[c]` down to whatever `ω` stands for,
    // which is what makes the result index-sensitive in the caller.
    edge(p.clone(), AccessPath::crit_ret(id.clone()), w.extend(std::slice::from_ref(acc))) <--
        index_resolution(p, id, acc), load_crit(id),
        let slot = AccessPath::crit_slot(id.clone(), 0),
        edge(p, slot, w);

    edge(p.clone(), w.extend(std::slice::from_ref(acc)), AccessPath::crit_slot(id.clone(), 2)) <--
        index_resolution(p, id, acc), store_crit(id),
        let slot = AccessPath::crit_slot(id.clone(), 0),
        edge(p, slot, w);

    // The base's *direct* operands above are not enough on their own: they
    // are the local the statement names, and locals are eliminated. A store
    // must also land on every symbolic path the base may denote, or
    // `setP`'s write to `map[key]` would never reach `par_1@setP[c]` and the
    // caller would not see it at all.
    edge(p.clone(), AccessPath::crit_ret(id.clone()), w.extend(std::slice::from_ref(acc))) <--
        index_resolution(p, id, acc), load_crit(id),
        let slot = AccessPath::crit_slot(id.clone(), 0),
        points(p, slot, ?PtVal::Path(w));

    edge(p.clone(), w.extend(std::slice::from_ref(acc)), AccessPath::crit_slot(id.clone(), 2)) <--
        index_resolution(p, id, acc), store_crit(id),
        let slot = AccessPath::crit_slot(id.clone(), 0),
        points(p, slot, ?PtVal::Path(w));

    // =====================================================================
    // S3 — where a context is *not* adequate (reads the `points` fixpoint)
    // =====================================================================

    /// `blocked(p, id)`: `pt(recv) ∩ free(𝔞) ≠ ∅`. The receiver slot may hold
    /// something rooted outside `p`, so a caller can still change which
    /// implementation this call dispatches to: keep propagating.
    relation blocked(Proc, CritId);
    blocked(p.clone(), id.clone()) <--
        pending(p, id), !resolved(p, id), decisive_slot(id, i),
        let decisive = AccessPath::crit_slot(id.clone(), *i),
        points(p, decisive, ?PtVal::Path(w)),
        let wb = w.base.clone(), pub_root(p, wb);

    /// N4, the `lv[v]` analogue of adequacy (Figure 4, definition (5)): the
    /// index is decidable only if its points-to set is *all* constants.
    /// Anything else — an allocation site, a path the caller still owns —
    /// means the index cannot be pinned, and `[π]` must be used.
    relation index_undecidable(Proc, CritId);
    index_undecidable(p.clone(), id.clone()) <--
        pending(p, id), !resolved(p, id), index_crit(id),
        let index = AccessPath::crit_slot(id.clone(), 1),
        points(p, index, v), if !matches!(v, PtVal::Const(_));

    /// Whether the index has any constant at all; an index with an empty
    /// points-to set is dead, and gets `[π]` rather than lingering forever.
    relation index_has_const(Proc, CritId);
    index_has_const(p.clone(), id.clone()) <--
        pending(p, id), index_crit(id),
        let index = AccessPath::crit_slot(id.clone(), 1),
        points(p, index, ?PtVal::Const(_));

    // =====================================================================
    // S4 — adequacy: the stratum that computes adequate contexts (N3)
    // =====================================================================

    /// `adequate(p, id)`: `Φ_a` holds here (§4.1.3). Note that an empty
    /// `pt(recv)` with no free roots is adequate and dispatches nothing —
    /// dead code, and sound.
    relation adequate(Proc, CritId);
    adequate(p.clone(), id.clone()) <-- pending(p, id), !resolved(p, id), !blocked(p, id);

    // =====================================================================
    // S5 — the subsequent stratum that *uses* adequacy. Output-only.
    // =====================================================================

    /// `forced(p, id)`: not adequate, and nowhere left to propagate to — an
    /// entry procedure, a procedure with no callers, or the k-limit. The
    /// instance must be ⊤-summarized here, which is precisely the
    /// context-insensitive treatment.
    relation forced(Proc, CritId);
    forced(p.clone(), id.clone()) <--
        pending(p, id), !resolved(p, id), !adequate(p, id), !can_propagate(p, id);
    // An entry procedure has a caller the analysis cannot see, so propagating
    // past it would never come back. Note this does *not* fire on Figure 1's
    // `service`: its instances are adequate, and get dispatched precisely.
    forced(p.clone(), id.clone()) <--
        pending(p, id), !resolved(p, id), !adequate(p, id), entry(p);

    /// `dispatch(p, id, callee)`: the implementations this instance may
    /// reach. Under an adequate context the receiver's points-to set pins the
    /// runtime types, so only those targets are taken; when forced, all CHA
    /// targets are.
    relation dispatch(Proc, CritId, Proc);
    dispatch(p.clone(), id.clone(), callee.clone()) <--
        adequate(p, id),
        let recv = AccessPath::crit_slot(id.clone(), 0),
        points(p, recv, ?PtVal::Alloc(l)),
        alloc_type(l, t), crit_sig(id, sig), lookup(t, sig, callee);
    dispatch(p.clone(), id.clone(), callee.clone()) <--
        forced(p, id), crit_sig(id, sig), sig_target(sig, callee);

    /// The accessor an `lv[v]` access resolves to: one tuple per constant the
    /// index may hold, or the single undecidable `[π]`.
    relation index_out(Proc, CritId, Accessor);
    index_out(p.clone(), id.clone(), Accessor::Index(c.clone())) <--
        adequate(p, id), index_crit(id), !index_undecidable(p, id),
        let index = AccessPath::crit_slot(id.clone(), 1),
        points(p, index, ?PtVal::Const(c));
    index_out(p.clone(), id.clone(), Accessor::IndexUnknown) <--
        adequate(p, id), index_crit(id), index_undecidable(p, id);
    index_out(p.clone(), id.clone(), Accessor::IndexUnknown) <--
        adequate(p, id), index_crit(id), !index_undecidable(p, id), !index_has_const(p, id);
    index_out(p.clone(), id.clone(), Accessor::IndexUnknown) <--
        forced(p, id), index_crit(id);

    /// The round's output to the driver. Consumed by nothing in-program —
    /// that is what keeps the whole struct stratified.
    relation resolve_out(Proc, CritId, Proc);
    resolve_out(p.clone(), id.clone(), callee.clone()) <-- dispatch(p, id, callee);
}

/// Everything earlier rounds have decided about critical statements — the
/// only state the driver carries between rounds.
///
/// It grows monotonically, and everything else about a round is re-derived
/// from scratch, so a decision made late still improves summaries computed
/// earlier and vice versa.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Decisions {
    /// `(holder, instance, callee)`: a virtual call that may reach `callee`.
    pub calls: BTreeSet<(Proc, CritId, Proc)>,
    /// `(holder, instance, accessor)`: an `lv[v]` access that uses `accessor`.
    pub indices: BTreeSet<(Proc, CritId, Accessor)>,
}

impl Decisions {
    fn len(&self) -> usize {
        self.calls.len() + self.indices.len()
    }

    /// The instances that have been decided, whichever kind they are. This is
    /// what `resolved` — and so every N2 negation — is fed from.
    fn resolved(&self) -> BTreeSet<(Proc, CritId)> {
        self.calls
            .iter()
            .map(|(p, id, _)| (p.clone(), id.clone()))
            .chain(
                self.indices
                    .iter()
                    .map(|(p, id, _)| (p.clone(), id.clone())),
            )
            .collect()
    }
}

impl Round {
    /// A fresh round over `prog` with k-limit `k` and the decisions earlier
    /// rounds have made; the round re-derives everything else.
    // Ascent generates private index fields alongside the public relation
    // fields, so a struct literal is not available here.
    #[allow(clippy::field_reassign_with_default)]
    pub fn for_program(prog: &Program, k: usize, decided: &Decisions) -> Round {
        let mut r = Round::default();

        r.procedure = prog.procedure.clone();
        r.entry = prog.entry.clone();
        r.in_proc = prog.in_proc.clone();
        r.alloc = prog.alloc.clone();
        r.alloc_type = prog.alloc_type.clone();
        r.const_assign = prog.const_assign.clone();
        r.mov = prog.mov.clone();
        r.load_field = prog.load_field.clone();
        r.store_field = prog.store_field.clone();
        r.load_index_const = prog.load_index_const.clone();
        r.store_index_const = prog.store_index_const.clone();
        r.load_index_var = prog.load_index_var.clone();
        r.store_index_var = prog.store_index_var.clone();
        r.direct_call = prog.direct_call.clone();
        r.virtual_call = prog.virtual_call.clone();
        r.actual_arg = prog.actual_arg.clone();
        r.bind_ret = prog.bind_ret.clone();
        r.formal = prog.formal.clone();
        r.ret = prog.ret.clone();
        r.lookup = prog.lookup.clone();

        r.k_limit = vec![(k,)];
        r.resolution = decided.calls.iter().cloned().collect();
        r.index_resolution = decided.indices.iter().cloned().collect();
        r.resolved = decided.resolved().into_iter().collect();
        r
    }

    /// The hybrid summary of every procedure that has one, as access-path
    /// constraints (Figure 3 of the paper). Procedures with an empty summary
    /// are omitted.
    pub fn summaries(&self) -> BTreeMap<Proc, Summary> {
        let mut out: BTreeMap<Proc, Summary> = BTreeMap::new();
        for (p, sup, sub) in &self.pub_edge {
            out.entry(p.clone()).or_default().insert(Constraint::Path {
                sup: sup.clone(),
                sub: sub.clone(),
            });
        }
        for (p, sup, v) in &self.pub_points {
            out.entry(p.clone())
                .or_default()
                .insert(v.constrain(sup.clone()));
        }
        out
    }

    /// The pending critical statements `p`'s summary still carries — the `S`
    /// of `𝔥 = (𝔠, S)`.
    pub fn placeholders(&self, p: &Proc) -> BTreeSet<CritId> {
        self.pending
            .iter()
            .filter(|(q, id)| q == p && !self.resolved.contains(&(q.clone(), id.clone())))
            .map(|(_, id)| id.clone())
            .collect()
    }

    /// `pt(ω)` as an outside observer should see it.
    ///
    /// Concrete values always count. A `PtVal::Path` counts only when its
    /// root is still published — "and whatever the caller supplies", or "and
    /// whatever this deferred critical statement returns". Paths rooted at a
    /// *resolved* placeholder are dropped for the same reason locals are:
    /// resolving it demoted the node to an internal one, and the values that
    /// actually flow through it are already in the set by transitivity.
    pub fn points_to_path(&self, p: &Proc, path: &AccessPath) -> BTreeSet<PtVal> {
        self.points
            .iter()
            .filter(|(q, w, _)| q == p && w == path)
            .map(|(_, _, val)| val.clone())
            .filter(|val| match val {
                PtVal::Path(w) => self.pub_root.contains(&(p.clone(), w.base.clone())),
                _ => true,
            })
            .collect()
    }

    /// [`Round::points_to_path`] for a bare local of `p`.
    pub fn points_to(&self, p: &Proc, v: impl Into<Var>) -> BTreeSet<PtVal> {
        self.points_to_path(p, &AccessPath::var(v.into()))
    }
}

/// The result of running Hybrid Inlining to a fixpoint.
pub struct Hybrid {
    /// The final round — every relation of the analysis, fully derived.
    pub round: Round,
    /// Everything the analysis decided about critical statements.
    pub decisions: Decisions,
    /// How many rounds it took, including the final round that found nothing.
    pub rounds: usize,
}

impl Hybrid {
    /// The call edges Hybrid Inlining admits for the critical statements —
    /// the precision claim of Figure 1 is a statement about this set.
    ///
    /// This is [`Hybrid::resolutions`], the union over all rounds, not the
    /// final round's `dispatch`: once an instance has been resolved it is no
    /// longer pending, so the round that reaches the fixpoint re-derives
    /// nothing.
    pub fn dispatches(&self) -> &BTreeSet<(Proc, CritId, Proc)> {
        &self.decisions.calls
    }

    /// The callees the instance `id` held by `p` may reach.
    pub fn callees_of(&self, p: &Proc, id: &CritId) -> BTreeSet<Proc> {
        self.decisions
            .calls
            .iter()
            .filter(|(q, i, _)| q == p && i == id)
            .map(|(_, _, callee)| callee.clone())
            .collect()
    }

    /// The accessors the `lv[v]` instance `id` held by `p` resolves to.
    pub fn accessors_of(&self, p: &Proc, id: &CritId) -> BTreeSet<Accessor> {
        self.decisions
            .indices
            .iter()
            .filter(|(q, i, _)| q == p && i == id)
            .map(|(_, _, acc)| acc.clone())
            .collect()
    }
}

/// A guard against a driver bug turning into a hang. Each round either adds a
/// decision or is the last, and decisions are bounded by
/// procedures × k-bounded call strings × (CHA targets ∪ constants), so real
/// programs stop far below this.
const MAX_ROUNDS: usize = 1_000;

/// Run Hybrid Inlining on `prog` with k-limit `k`.
///
/// The loop is the Datalog reading of the paper's repeated application of
/// `ready`: run the stratified round, feed every newly discovered resolution
/// back in as an input relation, and repeat until a round discovers nothing.
/// Because a round re-derives everything, a resolution discovered late still
/// benefits from summaries improved earlier, and vice versa.
///
/// `k = 0` forbids propagation entirely, so every critical statement is
/// ⊤-summarized where it occurs: that is exactly the compositional,
/// context-insensitive analysis (Figure 2).
pub fn run_hybrid(prog: &Program, k: usize) -> Hybrid {
    let mut decisions = Decisions::default();

    for round_no in 1..=MAX_ROUNDS {
        let mut round = Round::for_program(prog, k, &decisions);
        round.run();

        let before = decisions.len();
        decisions.calls.extend(round.resolve_out.iter().cloned());
        decisions.indices.extend(round.index_out.iter().cloned());
        if decisions.len() == before {
            return Hybrid {
                round,
                decisions,
                rounds: round_no,
            };
        }
    }
    panic!("hybrid inlining did not converge in {MAX_ROUNDS} rounds");
}

/// Render `id`'s dispatch decision for a human, e.g. `⟨L25@L28·L31b⟩ → Y.poly`.
pub fn render_dispatch(id: &CritId, callee: &Proc) -> String {
    format!("{id} → {callee}")
}

/// Present a summary the way Figure 3 does: the constraints, then the pending
/// critical statements the summary still defers.
pub fn render_summary(summary: &Summary, placeholders: &BTreeSet<CritId>) -> Vec<String> {
    let mut lines: Vec<String> = summary.iter().map(ToString::to_string).collect();
    for id in placeholders {
        lines.push(format!("critical {id} deferred"));
    }
    lines
}
