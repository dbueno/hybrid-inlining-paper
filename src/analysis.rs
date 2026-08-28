//! Hybrid Inlining (§3.2) for the compositional pointer analysis of §4.1.
//!
//! The analysis is a *single* Ascent program, [`HybridAnalysis`], evaluated to
//! one fixpoint. [`run_hybrid`] builds it, calls `run()`, and hands it back;
//! there is no driver and no round loop.
//!
//! # Why one fixpoint, and where the negations are
//!
//! The paper's `ready`/`Φ_a` machinery looks like it has a genuine cycle
//! through a negation: resolving an *adequate* critical statement adds
//! constraints, which grow `pt`, which the adequacy test negates over. The
//! way out is to notice that adequacy is a **scheduling** device, not a
//! **precision** device. What actually gets dispatched is per-allocation:
//! each `Alloc(l) ∈ pt(recv)` independently justifies the one callee
//! `lookup(type(l), sig)`. Firing that rule the moment each allocation
//! appears, at every holder, is monotone (it triggers on the *presence* of a
//! tuple), sound (a may-points-to member genuinely may be the receiver), and
//! no less precise (allocations only accumulate along a propagation chain,
//! and past the first adequate holder the set is frozen — Theorem 3.3's
//! early-vs-late confluence). So the whole cycle
//! `resolve → inline → edge → points → resolve` is ordinary positive
//! recursion in one strongly connected component.
//!
//! What is left of the negations, from the lowest stratum up — the macro
//! checks this stratification at compile time:
//!
//! | stratum | relations | negation |
//! |---------|-----------|----------|
//! | A | [`HybridAnalysis::sig_size`], [`HybridAnalysis::critical`], [`HybridAnalysis::eff_direct`], [`HybridAnalysis::is_called`] | `count` over the EDB (N1) |
//! | A′ | [`HybridAnalysis::uncalled`] | `!is_called`, over stratum A only |
//! | B | **the SCC**: [`HybridAnalysis::edge`], [`HybridAnalysis::points`], [`HybridAnalysis::pending`], [`HybridAnalysis::pub_edge`], [`HybridAnalysis::blocked`], [`HybridAnalysis::top`], [`HybridAnalysis::resolve`], [`HybridAnalysis::index_acc`] | none — all positive |
//! | C | [`HybridAnalysis::adequate`], [`HybridAnalysis::settled`] | `!blocked`, over the finished fixpoint |
//!
//! Stratum C is reporting only: it feeds nothing back, so negating over B is
//! legal there. Adequacy has been demoted from *control* to *classification*.
//!
//! The one place a genuine ⊤-fallback is still needed is a placeholder that
//! can neither be pinned nor propagated — at an entry, at a procedure with no
//! callers, or at the k-limit. That is [`HybridAnalysis::stuck`], whose only
//! negation (`uncalled`) is over stratum A, and it is combined with a
//! *presence* test — [`HybridAnalysis::blocked`], "the decisive slot sees a
//! path rooted in `free(𝔞)`" — rather than the absence test `!adequate` the
//! round-based version used.
//!
//! # The constraint graph
//!
//! [`HybridAnalysis::edge`]`(p, sup, sub)` is `sup ⊇ sub` while `p` is being
//! summarized; [`HybridAnalysis::points`]`(p, ω, v)` is `v ∈ pt(ω)`. Critical
//! statements are *not* summarized: each pending instance contributes
//! placeholder nodes `CritSlot(id, i)` / `CritRet(id)` that are wired to the
//! statement's operands and result by ordinary `⊇` edges — the paper's
//! "critical statements are connected with all the variables they access",
//! made literal. Publishing a summary eliminates locals but keeps those
//! placeholders, and that is what makes the summary *hybrid*.
//!
//! Nothing ever *retracts* a placeholder, so a resolved placeholder stays
//! published. What a caller does with it is a separate question, and the
//! answer is a *positive* test rather than a retraction: an instance crosses a
//! callsite only while [`HybridAnalysis::blocked`] holds of it — while the
//! caller still controls the operand that decides it. Adequacy is the
//! complement, and an adequate instance has already been decided here, so
//! spawning a child of it in every caller would duplicate a completed
//! decision. Propagation and the placeholder renaming in
//! [`HybridAnalysis::root_map`] carry the same guard, so `p` and its callers
//! agree on which instances cross the callsite.
//!
//! That the guard is monotone is what makes it legal inside the SCC:
//! `blocked` only ever grows, so "propagate iff blocked" is order-independent
//! and the fixpoint is unchanged. The duplication it removes was confluent
//! and harmless (Theorem 3.3) — it was simply never necessary, and calling it
//! the price of monotonicity was giving up too early.

use std::collections::{BTreeMap, BTreeSet};

use ascent::aggregators::count;
use ascent::{ascent, ascent_source};

use crate::access_path::{AccessPath, Accessor, Base, Constraint, CritId, PtVal, Summary};
use crate::ir::{Alloc, ArgIdx, Const, Field, Line, Proc, Program, Sig, Stmt, Type, Var};

// Every rule of the analysis, as a source that `HybridAnalysis` and the
// `parallel` compile-check both include, so the two cannot drift apart. The
// EDB these rules read comes from `crate::ir::edb`.
ascent_source! { hybrid_rules:
    /// The k-limit of §3.2.2, as a single tuple: a pending instance may be
    /// propagated while its call string is shorter than `k`.
    relation k_limit(usize);

    // =====================================================================
    // Stratum A — criticality and CHA devirtualization (N1)
    // =====================================================================

    /// The CHA target set of a signature, deduplicated over receiver types.
    relation sig_target(Sig, Proc);
    sig_target(sig.clone(), p.clone()) <-- lookup(_, sig, p);

    /// `|dispatch(⊤, proc)|` — the aggregation the criticality test negates.
    relation sig_size(Sig, usize);
    sig_size(sig.clone(), n) <-- virtual_call(_, _, sig), agg n = count() in sig_target(sig, _);

    /// A virtual call with a single CHA target is not critical: it is an
    /// ordinary direct call the front end simply did not resolve. This is
    /// also `Φ_a`'s second disjunct, `|dispatch(proc, 𝔞)| = 1`, handled once
    /// and for all at the CHA level.
    relation mono_target(Stmt, Proc);
    mono_target(s.clone(), p.clone()) <--
        virtual_call(s, _, sig), sig_size(sig, 1), sig_target(sig, p);

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

    /// Every procedure the EDB names, whether or not `procedure` lists it.
    relation known_proc(Proc);
    known_proc(p.clone()) <-- procedure(p);
    known_proc(p.clone()) <-- in_proc(_, p, _);

    /// `is_called(p)`: some statement in the program calls `p` outright.
    relation is_called(Proc);
    is_called(p.clone()) <-- eff_direct(s, p), in_proc(s, _, _);

    // =====================================================================
    // Stratum A′ — the only negation below the SCC
    // =====================================================================

    /// A procedure nothing calls. Propagating a placeholder out of it would
    /// never come back, so its pendings are [`HybridAnalysis::stuck`].
    relation uncalled(Proc);
    uncalled(p.clone()) <-- known_proc(p), !is_called(p);

    // =====================================================================
    // Stratum B — the SCC. Everything below here is positive, and all of it
    // is mutually recursive: constraints grow points-to sets, which resolve
    // critical statements, which inline summaries, which grow constraints.
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
    /// finite.
    relation path_used(Proc, Base, AccessPath);
    path_used(p.clone(), a.base.clone(), a.clone()) <-- edge(p, a, _);
    path_used(p.clone(), b.base.clone(), b.clone()) <-- edge(p, _, b);
    path_used(p.clone(), a.base.clone(), a.clone()) <-- points(p, a, _);

    edge(p.clone(), sup2.clone(), sub.extend(rest)) <--
        edge(p, sup, sub),
        path_used(p, sup.base, sup2),
        if let Some(rest) = sup2.strip_prefix(sup),
        if !rest.is_empty();
    // The same congruence triggered from the other side: `ret@build ⊇ v` and
    // an observed `v["old"]` together justify `ret@build["old"] ⊇ v["old"]`,
    // which is how a store through a local reaches the published summary.
    edge(p.clone(), sup.extend(rest), sub2.clone()) <--
        edge(p, sup, sub),
        path_used(p, sub.base, sub2),
        if let Some(rest) = sub2.strip_prefix(sub),
        if !rest.is_empty();

    // -- pending critical statements: origination and propagation ---------

    /// `crit_origin(p, s, id)`: the critical statement `s` sits in `p`, and
    /// `id` is its instance there, with an empty call string.
    relation crit_origin(Proc, Stmt, CritId);
    crit_origin(p.clone(), s.clone(), CritId::origin(s.clone())) <-- critical(s), in_proc(s, p, _);

    /// `pending(p, id)`: `p`'s summary carries `id` as a placeholder — the
    /// `S` of a hybrid summary `𝔥 = (𝔠, S)`.
    ///
    /// Nothing removes a tuple from `pending`: resolution *adds* constraints
    /// rather than retracting the placeholder. Use
    /// [`HybridAnalysis::settled`] to tell a still-deferred instance from one
    /// that has been decided.
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

    // Propagation (§3.2): a placeholder moves into the caller, where more
    // context has accumulated — but only while it is still `blocked`, i.e.
    // while the caller controls what decides it. An adequate instance has a
    // complete points-to set for its deciding operand (nothing outside `p` can
    // add to it, because any caller-reachable component would appear as a
    // symbolic path and block), so it is decided here and its callees are
    // exactly the ones a propagated copy would find. `blocked` is a presence
    // test and only grows, so the guard is monotone and lives in the SCC. The
    // k-limit bounds the call string so recursion terminates.
    pending(q.clone(), id.push(s)) <--
        pending(p, id),
        blocked(p, id),
        eff_direct(s, p), in_proc(s, q, _),
        k_limit(k), if id.depth() < *k;

    /// Whether propagation is still an option. Used *positively*: a
    /// placeholder whose values may still grow in a caller is part of
    /// `free(𝔞)`, and one that cannot propagate at all must be ⊤-summarized
    /// where it stands.
    relation can_propagate(Proc, CritId);
    can_propagate(p.clone(), id.clone()) <--
        pending(p, id), eff_direct(s, p), in_proc(s, _, _),
        k_limit(k), if id.depth() < *k;

    /// `stuck(p, id)`: nowhere left to propagate to. Its complement of
    /// `can_propagate`, decomposed so that the only negation involved
    /// (`uncalled`) is over stratum A rather than over the `points` fixpoint:
    /// a procedure with no callers, an entry procedure (whose caller the
    /// analysis cannot see), or the k-limit.
    relation stuck(Proc, CritId);
    stuck(p.clone(), id.clone()) <-- pending(p, id), uncalled(p);
    stuck(p.clone(), id.clone()) <-- pending(p, id), entry(p);
    stuck(p.clone(), id.clone()) <-- pending(p, id), k_limit(k), if id.depth() >= *k;

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
    /// `free(𝔞)` is intersected against: the receiver of a virtual call, the
    /// index of an `lv[v]` access.
    relation decisive_slot(CritId, ArgIdx);
    decisive_slot(id.clone(), 0) <-- call_crit(id);
    decisive_slot(id.clone(), 1) <-- index_crit(id);

    relation crit_sig(CritId, Sig);
    crit_sig(id.clone(), sig.clone()) <--
        pending(_, id), let s = id.stmt.clone(), virtual_call(s, _, sig);

    // -- free(𝔞) and the published vocabulary ------------------------------

    /// `free(𝔞)` of §4.1.3: the roots whose values a *caller* can still
    /// change. `par_i@p` and `ret@p` always qualify. A placeholder qualifies
    /// only while its own instance can still propagate — once it is stuck, it
    /// will be decided here, from values that are already in this procedure,
    /// so it is no longer something the outside can influence.
    relation free_root(Proc, Base);
    free_root(p.clone(), Base::Param(p.clone(), *i)) <-- formal(p, i, _);
    free_root(p.clone(), Base::Ret(p.clone())) <-- known_proc(p);
    free_root(p.clone(), Base::CritSlot(id.clone(), *i)) <--
        can_propagate(p, id), crit_operand(id, i);
    free_root(p.clone(), Base::CritRet(id.clone())) <-- can_propagate(p, id);

    /// The published vocabulary of `p`: its symbolic variables, plus the
    /// placeholder nodes of *every* pending it holds. Unlike `free_root`,
    /// this does not shrink when an instance is decided — the placeholder
    /// keeps carrying the constraints that were wired to it.
    relation pub_root(Proc, Base);
    pub_root(p.clone(), Base::Param(p.clone(), *i)) <-- formal(p, i, _);
    pub_root(p.clone(), Base::Ret(p.clone())) <-- known_proc(p);
    pub_root(p.clone(), Base::CritRet(id.clone())) <-- pending(p, id);
    pub_root(p.clone(), Base::CritSlot(id.clone(), *i)) <-- pending(p, id), crit_operand(id, i);

    /// `pub_edge(p, a, b)`: the constraint `a ⊇ b` of `p`'s published
    /// summary. Transitivity through locals has already happened inside
    /// `points`, so this is the local-eliminated closure.
    relation pub_edge(Proc, AccessPath, AccessPath);
    pub_edge(p.clone(), a.clone(), b.clone()) <--
        points(p, a, ?PtVal::Path(b)),
        pub_root(p, a.base),
        pub_root(p, b.base);

    /// `pub_points(p, a, v)`: the `a ⊇ {l}` / `a ⊇ {c}` half of the summary.
    relation pub_points(Proc, AccessPath, PtVal);
    pub_points(p.clone(), a.clone(), v.clone()) <--
        points(p, a, v), if !v.is_path(),
        pub_root(p, a.base);

    // -- inlining a summary at a statically known callsite -----------------

    /// `root_map(s, from, to)`: the substitution σ_s a callsite induces on the
    /// callee's published roots. Suffixes are untouched; only roots move.
    relation root_map(Stmt, Base, Base);
    root_map(s.clone(), Base::Param(p.clone(), *i), Base::Var(a.clone())) <--
        eff_direct(s, p), actual_arg(s, i, a);
    root_map(s.clone(), Base::Ret(p.clone()), Base::Var(r.clone())) <--
        eff_direct(s, p), bind_ret(s, r);
    // A placeholder is renamed rather than resolved — this *is* propagation, so
    // it carries the same `blocked` guard as the `pending` rule above. Without
    // that, an adequate instance would leave `q` holding placeholder-rooted
    // nodes for an obligation `q` never lists as pending.
    root_map(s.clone(), Base::CritSlot(id.clone(), *i), Base::CritSlot(id.push(s), *i)) <--
        eff_direct(s, p), pending(p, id), blocked(p, id), crit_operand(id, i),
        k_limit(k), if id.depth() < *k;
    root_map(s.clone(), Base::CritRet(id.clone()), Base::CritRet(id.push(s))) <--
        eff_direct(s, p), pending(p, id), blocked(p, id),
        k_limit(k), if id.depth() < *k;

    edge(q.clone(), a.rebase(ta.clone()), b.rebase(tb.clone())) <--
        eff_direct(s, p), in_proc(s, q, _), pub_edge(p, a, b),
        root_map(s, a.base, ta),
        root_map(s, b.base, tb);

    points(q.clone(), a.rebase(ta.clone()), v.clone()) <--
        eff_direct(s, p), in_proc(s, q, _), pub_points(p, a, v),
        root_map(s, a.base, ta);

    // -- resolution: monotone evidence, not adequacy -----------------------

    /// `blocked(p, id)`: `pt(decisive slot) ∩ free(𝔞) ≠ ∅`. Something the
    /// outside still controls may reach the operand that decides this
    /// statement.
    ///
    /// This is a *presence* test, so unlike the round-based version it lives
    /// in the SCC and can drive [`HybridAnalysis::top`] directly.
    relation blocked(Proc, CritId);
    blocked(p.clone(), id.clone()) <--
        pending(p, id), decisive_slot(id, i),
        let decisive = AccessPath::crit_slot(id.clone(), *i),
        points(p, decisive, ?PtVal::Path(w)),
        let wb = w.base.clone(), free_root(p, wb);

    /// `top(p, id)`: the instance must be ⊤-summarized here and now. It is
    /// blocked — the context never pins it — and there is nowhere left to
    /// propagate to, so deferring would silently drop constraints.
    ///
    /// This replaces the round-based `forced`, and with it the `!adequate`
    /// negation over the `points` fixpoint.
    relation top(Proc, CritId);
    top(p.clone(), id.clone()) <-- blocked(p, id), stuck(p, id);

    /// `resolve(p, id, callee)`: an implementation this instance may reach.
    ///
    /// The first rule is the whole re-think: one allocation in the receiver's
    /// points-to set is already enough evidence for the one callee it selects,
    /// so it fires as soon as the allocation appears, without waiting for the
    /// set to be provably complete. The second is the ⊤ fallback.
    relation resolve(Proc, CritId, Proc);
    resolve(p.clone(), id.clone(), callee.clone()) <--
        pending(p, id), call_crit(id),
        let recv = AccessPath::crit_slot(id.clone(), 0),
        points(p, recv, ?PtVal::Alloc(l)),
        alloc_type(l, t), crit_sig(id, sig), lookup(t, sig, callee);
    resolve(p.clone(), id.clone(), callee.clone()) <--
        top(p, id), call_crit(id), crit_sig(id, sig), sig_target(sig, callee);

    /// N4, the `lv[v]` analogue (Figure 4, definition (5)): the index holds a
    /// concrete value that is not a constant, so it cannot be pinned and
    /// `[π]` must be used. A *path* in the index does not count — that is the
    /// caller's business, and the instance simply propagates.
    relation index_undecidable(Proc, CritId);
    index_undecidable(p.clone(), id.clone()) <--
        pending(p, id), index_crit(id),
        let index = AccessPath::crit_slot(id.clone(), 1),
        points(p, index, ?PtVal::Alloc(_));

    /// The accessor an `lv[v]` access resolves to: one tuple per constant the
    /// index may hold — again on presence, as each constant appears — or the
    /// undecidable `[π]`. An index whose points-to set stays empty resolves
    /// to nothing at all: dead code, and more precise than defaulting to π.
    relation index_acc(Proc, CritId, Accessor);
    index_acc(p.clone(), id.clone(), Accessor::Index(c.clone())) <--
        pending(p, id), index_crit(id),
        let index = AccessPath::crit_slot(id.clone(), 1),
        points(p, index, ?PtVal::Const(c));
    index_acc(p.clone(), id.clone(), Accessor::IndexUnknown) <-- index_undecidable(p, id);
    index_acc(p.clone(), id.clone(), Accessor::IndexUnknown) <-- top(p, id), index_crit(id);

    // -- inlining a summary at a resolved critical statement ---------------

    /// `crit_map(p, id, from, to)`: the substitution σ_crit for a resolution.
    /// The callee's formals land on the placeholder's operand slots and its
    /// return on the placeholder's result, so the constraints the caller had
    /// already wired to the placeholder connect straight through.
    relation crit_map(Proc, CritId, Base, Base);
    crit_map(p.clone(), id.clone(), Base::Param(callee.clone(), *i), Base::CritSlot(id.clone(), *i)) <--
        resolve(p, id, callee), formal(callee, i, _);
    crit_map(p.clone(), id.clone(), Base::Ret(callee.clone()), Base::CritRet(id.clone())) <--
        resolve(p, id, callee);
    // Hybrid-in-hybrid: the callee's own placeholders are renamed into `p`.
    crit_map(p.clone(), id.clone(), Base::CritSlot(id2.clone(), *j), Base::CritSlot(id2.nest(id), *j)) <--
        resolve(p, id, callee), pending(callee, id2),
        crit_operand(id2, j), k_limit(k), if id2.nest_depth(id) <= *k;
    crit_map(p.clone(), id.clone(), Base::CritRet(id2.clone()), Base::CritRet(id2.nest(id))) <--
        resolve(p, id, callee), pending(callee, id2),
        k_limit(k), if id2.nest_depth(id) <= *k;

    pending(p.clone(), id2.nest(id)) <--
        resolve(p, id, callee), pending(callee, id2),
        k_limit(k), if id2.nest_depth(id) <= *k;

    edge(p.clone(), a.rebase(ta.clone()), b.rebase(tb.clone())) <--
        resolve(p, id, callee), pub_edge(callee, a, b),
        let ab = a.base.clone(), crit_map(p, id, ab, ta),
        let bb = b.base.clone(), crit_map(p, id, bb, tb);

    points(p.clone(), a.rebase(ta.clone()), v.clone()) <--
        resolve(p, id, callee), pub_points(callee, a, v),
        let ab = a.base.clone(), crit_map(p, id, ab, ta);

    // -- resolving an lv[v] access ----------------------------------------

    // `eval(lv[v])(𝔞)` of Figure 4 definitions (4) and (5): the access path is
    // rooted at the base *operand itself*, extended by the decided accessor.
    // Suffix congruence then carries `ω[c]` down to whatever `ω` stands for,
    // which is what makes the result index-sensitive in the caller.
    edge(p.clone(), AccessPath::crit_ret(id.clone()), w.extend(std::slice::from_ref(acc))) <--
        index_acc(p, id, acc), load_crit(id),
        let slot = AccessPath::crit_slot(id.clone(), 0),
        edge(p, slot, w);

    edge(p.clone(), w.extend(std::slice::from_ref(acc)), AccessPath::crit_slot(id.clone(), 2)) <--
        index_acc(p, id, acc), store_crit(id),
        let slot = AccessPath::crit_slot(id.clone(), 0),
        edge(p, slot, w);

    // The base's *direct* operands above are not enough on their own: they
    // are the local the statement names, and locals are eliminated. A store
    // must also land on every symbolic path the base may denote, or
    // `setP`'s write to `map[key]` would never reach `par_1@setP[c]` and the
    // caller would not see it at all.
    edge(p.clone(), AccessPath::crit_ret(id.clone()), w.extend(std::slice::from_ref(acc))) <--
        index_acc(p, id, acc), load_crit(id),
        let slot = AccessPath::crit_slot(id.clone(), 0),
        points(p, slot, ?PtVal::Path(w));

    edge(p.clone(), w.extend(std::slice::from_ref(acc)), AccessPath::crit_slot(id.clone(), 2)) <--
        index_acc(p, id, acc), store_crit(id),
        let slot = AccessPath::crit_slot(id.clone(), 0),
        points(p, slot, ?PtVal::Path(w));

    // =====================================================================
    // Stratum C — reporting. Negation over the finished fixpoint is ordinary
    // stratified negation here, because nothing below reads these.
    // =====================================================================

    /// `adequate(p, id)`: `Φ_a` holds here (§4.1.3) — nothing the caller still
    /// controls reaches the deciding operand. It no longer *drives* anything;
    /// it classifies, after the fact, the contexts in which resolution was
    /// complete.
    relation adequate(Proc, CritId);
    adequate(p.clone(), id.clone()) <-- pending(p, id), !blocked(p, id);

    /// `settled(p, id)`: this placeholder defers nothing any more. Either it
    /// was decided in an adequate context, or it was ⊤-summarized. `pending`
    /// never shrinks, so this is what the query layer uses to tell a genuine
    /// "critical ⟨…⟩ deferred" from a decided placeholder that is still
    /// carried along.
    relation settled(Proc, CritId);
    settled(p.clone(), id.clone()) <-- resolve(p, id, _), !blocked(p, id);
    settled(p.clone(), id.clone()) <-- index_acc(p, id, _), !blocked(p, id);
    settled(p.clone(), id.clone()) <-- top(p, id);
}

ascent! {
    /// Hybrid Inlining as one stratified derivation: every procedure's hybrid
    /// summary, every pending critical statement, and every resolution, in a
    /// single fixpoint.
    ///
    /// Build one with [`HybridAnalysis::for_program`] and `run()` it, or just
    /// call [`run_hybrid`].
    pub struct HybridAnalysis;

    // The EDB schema of `ir::Program`, included from the same source so the
    // two programs cannot drift apart. `for_program` copies the facts.
    include_source!(crate::ir::edb);
    include_source!(crate::analysis::hybrid_rules);
}

/// Copy the EDB of a [`Program`] into any Ascent program that includes the
/// [`crate::ir::edb`] source, and set its k-limit.
///
/// Every relation of the shared schema is named exactly once, here, so the
/// sequential and parallel programs cannot be seeded differently.
/// `every_edb_relation_is_copied_into_the_analysis` keeps the list from
/// falling behind the schema.
macro_rules! seed_edb {
    ($target:expr, $prog:expr, $k:expr) => {{
        let r = &mut $target;
        let prog = $prog;
        r.procedure = prog.procedure.clone().into_iter().collect();
        r.proc_type = prog.proc_type.clone().into_iter().collect();
        r.proc_sig = prog.proc_sig.clone().into_iter().collect();
        r.entry = prog.entry.clone().into_iter().collect();
        r.in_proc = prog.in_proc.clone().into_iter().collect();
        r.alloc = prog.alloc.clone().into_iter().collect();
        r.alloc_type = prog.alloc_type.clone().into_iter().collect();
        r.const_assign = prog.const_assign.clone().into_iter().collect();
        r.mov = prog.mov.clone().into_iter().collect();
        r.load_field = prog.load_field.clone().into_iter().collect();
        r.store_field = prog.store_field.clone().into_iter().collect();
        r.load_static = prog.load_static.clone().into_iter().collect();
        r.store_static = prog.store_static.clone().into_iter().collect();
        r.load_index_const = prog.load_index_const.clone().into_iter().collect();
        r.store_index_const = prog.store_index_const.clone().into_iter().collect();
        r.load_index_var = prog.load_index_var.clone().into_iter().collect();
        r.store_index_var = prog.store_index_var.clone().into_iter().collect();
        r.direct_call = prog.direct_call.clone().into_iter().collect();
        r.virtual_call = prog.virtual_call.clone().into_iter().collect();
        r.actual_arg = prog.actual_arg.clone().into_iter().collect();
        r.bind_ret = prog.bind_ret.clone().into_iter().collect();
        r.formal = prog.formal.clone().into_iter().collect();
        r.ret = prog.ret.clone().into_iter().collect();
        r.direct_subtype = prog.direct_subtype.clone().into_iter().collect();
        r.lookup = prog.lookup.clone().into_iter().collect();
        r.k_limit = ::std::iter::once(($k,)).collect();
    }};
}

impl HybridAnalysis {
    /// The analysis over `prog` with k-limit `k`, ready to `run()`.
    // Ascent generates private index fields alongside the public relation
    // fields, so a struct literal is not available here.
    #[allow(clippy::field_reassign_with_default)]
    pub fn for_program(prog: &Program, k: usize) -> HybridAnalysis {
        let mut r = HybridAnalysis::default();
        seed_edb!(r, prog, k);
        r
    }

    /// The instances that no longer defer anything, as a set for lookup.
    fn settled_set(&self) -> BTreeSet<(Proc, CritId)> {
        self.settled.iter().cloned().collect()
    }

    /// Whether `base` is a placeholder node of an instance `p` has settled —
    /// the internal plumbing of a decided critical statement, which the
    /// derivation keeps but no report should show.
    fn is_decided(settled: &BTreeSet<(Proc, CritId)>, p: &Proc, base: &Base) -> bool {
        match base.crit_id() {
            Some(id) => settled.contains(&(p.clone(), id.clone())),
            None => false,
        }
    }

    /// The hybrid summary of every procedure that has one, as access-path
    /// constraints (Figure 3 of the paper). Procedures with an empty summary
    /// are omitted.
    ///
    /// Constraints over a *settled* placeholder are dropped: the values that
    /// flow through it are already in the summary by transitivity, and the
    /// placeholder itself no longer stands for anything the caller must
    /// decide. That is §10.5's "stratum C hides the redundant derivation from
    /// reporting".
    pub fn summaries(&self) -> BTreeMap<Proc, Summary> {
        let settled = self.settled_set();
        let mut out: BTreeMap<Proc, Summary> = BTreeMap::new();
        for (p, sup, sub) in &self.pub_edge {
            if Self::is_decided(&settled, p, &sup.base) || Self::is_decided(&settled, p, &sub.base)
            {
                continue;
            }
            out.entry(p.clone()).or_default().insert(Constraint::Path {
                sup: sup.clone(),
                sub: sub.clone(),
            });
        }
        for (p, sup, v) in &self.pub_points {
            if Self::is_decided(&settled, p, &sup.base) {
                continue;
            }
            out.entry(p.clone())
                .or_default()
                .insert(v.constrain(sup.clone()));
        }
        out
    }

    /// The pending critical statements `p`'s summary still defers — the `S` of
    /// `𝔥 = (𝔠, S)`. A decided placeholder is still *carried*, but it is no
    /// longer deferred, so it is not reported here.
    pub fn placeholders(&self, p: &Proc) -> BTreeSet<CritId> {
        let settled = self.settled_set();
        self.pending
            .iter()
            .filter(|(q, id)| q == p && !settled.contains(&(q.clone(), id.clone())))
            .map(|(_, id)| id.clone())
            .collect()
    }

    /// `pt(ω)` as an outside observer should see it.
    ///
    /// Concrete values always count. A `PtVal::Path` counts only when its
    /// root is still published *and still stands for something undecided* —
    /// "and whatever the caller supplies", or "and whatever this deferred
    /// critical statement returns". A path rooted at a settled placeholder is
    /// dropped for the same reason locals are: the values that actually flow
    /// through it are already in the set by transitivity.
    pub fn points_to_path(&self, p: &Proc, path: &AccessPath) -> BTreeSet<PtVal> {
        let settled = self.settled_set();
        self.points
            .iter()
            .filter(|(q, w, _)| q == p && w == path)
            .map(|(_, _, val)| val.clone())
            .filter(|val| match val {
                PtVal::Path(w) => {
                    self.pub_root.contains(&(p.clone(), w.base.clone()))
                        && !Self::is_decided(&settled, p, &w.base)
                }
                _ => true,
            })
            .collect()
    }

    /// [`HybridAnalysis::points_to_path`] for a bare local of `p`.
    pub fn points_to(&self, p: &Proc, v: impl Into<Var>) -> BTreeSet<PtVal> {
        self.points_to_path(p, &AccessPath::var(v.into()))
    }

    /// The call edges Hybrid Inlining admits for the critical statements —
    /// the precision claim of Figure 1 is a statement about this set.
    pub fn dispatches(&self) -> BTreeSet<(Proc, CritId, Proc)> {
        self.resolve.iter().cloned().collect()
    }

    /// The callees the instance `id` held by `p` may reach.
    pub fn callees_of(&self, p: &Proc, id: &CritId) -> BTreeSet<Proc> {
        self.resolve
            .iter()
            .filter(|(q, i, _)| q == p && i == id)
            .map(|(_, _, callee)| callee.clone())
            .collect()
    }

    /// The accessors the `lv[v]` instance `id` held by `p` resolves to.
    pub fn accessors_of(&self, p: &Proc, id: &CritId) -> BTreeSet<Accessor> {
        self.index_acc
            .iter()
            .filter(|(q, i, _)| q == p && i == id)
            .map(|(_, _, acc)| acc.clone())
            .collect()
    }
}

/// Run Hybrid Inlining on `prog` with k-limit `k`.
///
/// One program, one fixpoint. Origination, propagation, publication,
/// inlining, resolution and re-inlining are all mutually recursive rules in
/// the same stratum, so a resolution discovered "late" still improves
/// summaries derived "early" — semi-naive evaluation handles that, instead of
/// a driver re-deriving everything.
///
/// `k = 0` forbids propagation entirely, so every critical statement whose
/// context never pins it is ⊤-summarized where it occurs: that is essentially
/// the compositional, context-insensitive analysis (Figure 2). An instance
/// whose receiver is a purely local allocation is still pinned even at
/// `k = 0`, which is strictly more precise than Figure 2.
pub fn run_hybrid(prog: &Program, k: usize) -> HybridAnalysis {
    let mut analysis = HybridAnalysis::for_program(prog, k);
    analysis.run();
    analysis
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

/// The same rules under Ascent's *parallel* backend.
///
/// The whole domain is `Arc`-backed and so `Send + Sync`, and a single
/// fixpoint has no driver serializing it between rounds, so `ascent_par!` is a
/// drop-in swap. Every program here includes the one [`hybrid_rules`] source,
/// so none of them can drift from the sequential [`HybridAnalysis`]: a build
/// fails if the rules ever stop being parallelizable.
///
/// Two flavours, because Ascent parallelizes along two independent axes:
///
/// - [`ParallelHybridAnalysis`] — *intra*-rule only, the `ascent_par!`
///   default: each rule's body is evaluated with a parallel iterator over the
///   driving relation's delta, one rule at a time.
/// - [`inter_rule::InterRuleHybridAnalysis`] — `#![inter_rule_parallelism]` on
///   top of that, so independent rules *within one SCC* also run
///   concurrently. This analysis has one very large SCC (stratum B), which is
///   exactly the shape that axis is meant for.
///
/// `examples/parallel.rs` runs all three over the scaled families and checks
/// that they agree tuple-for-tuple.
pub mod parallel {
    use ascent::ascent_par;

    use super::*;

    ascent_par! {
        /// Hybrid Inlining under `ascent_par!` with intra-rule parallelism.
        pub struct ParallelHybridAnalysis;

        include_source!(crate::ir::edb);
        include_source!(crate::analysis::hybrid_rules);
    }

    impl ParallelHybridAnalysis {
        /// As [`HybridAnalysis::for_program`], seeded from the same macro.
        #[allow(clippy::field_reassign_with_default)]
        pub fn for_program(prog: &Program, k: usize) -> Self {
            let mut r = Self::default();
            seed_edb!(r, prog, k);
            r
        }
    }

    /// The same again, with inter-rule parallelism enabled.
    pub mod inter_rule {
        use ascent::ascent_par;

        use super::super::*;

        ascent_par! {
            #![inter_rule_parallelism]
            /// Hybrid Inlining with both intra- and inter-rule parallelism.
            pub struct InterRuleHybridAnalysis;

            include_source!(crate::ir::edb);
            include_source!(crate::analysis::hybrid_rules);
        }

        impl InterRuleHybridAnalysis {
            /// As [`HybridAnalysis::for_program`], seeded from the same macro.
            #[allow(clippy::field_reassign_with_default)]
            pub fn for_program(prog: &Program, k: usize) -> Self {
                let mut r = Self::default();
                seed_edb!(r, prog, k);
                r
            }
        }
    }
}
