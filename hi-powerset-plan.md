# Hybrid Inlining with Powerset Lattice Contexts

> **Status: planning note.** This plan replaces the ordered call string inside
> `CritId` with a separate Ascent lattice value. The key idea is: keep
> `CritId` as the syntactic identity of the critical statement, and append a
> `CallCtx` lattice column to every relation whose old `CritId` value was really
> carrying a context. This intentionally joins contexts by union, doing less
> work at the cost of precision.

## 1. Core design

Today `CritId` is both the identity of a critical statement and the context in
which that instance was reached:

```rust
pub struct CritId {
    pub stmt: Stmt,
    pub chain: Arc<[Stmt]>,
}
```

That makes the call string part of ordinary relation keys. Ascent therefore
keeps `⟨L25@A⟩` and `⟨L25@B⟩` as different tuples throughout `pending`,
`edge`, `points`, `resolve`, and the reporting layer.

The powerset design splits those roles:

```rust
pub struct CritId {
    pub stmt: Stmt,
}

pub struct CallCtx(/* powerset lattice over callsites */);
```

`CritId` is now context-free and remains usable in `Base::CritSlot` /
`Base::CritRet`. `CallCtx` is the abstract context and appears as the **last
column** of Ascent `lattice` relations. Ascent uses all preceding columns as
the key and joins the last column when another value is derived for the same
key.

For example:

```text
lattice pending(Proc, CritId, CallCtx);
```

means there is one abstract pending context per `(Proc, CritId)`. If one rule
derives `(bar, L25, {A})` and another derives `(bar, L25, {B})`, Ascent stores
`(bar, L25, {A,B})`.

This is deliberately **not** equivalent to putting a canonical powerset inside
`CritId` and continuing to use ordinary relations. That would keep `{A}` and
`{B}` as different keys, so no lattice join would happen.

## 2. Call-string lattice

Use a powerset lattice over callsite statements:

```text
order:  A ≤ B iff A ⊆ B
bottom: ∅
meet:   A ∩ B
join:   A ∪ B
```

Ascent's `ascent::lattice::set::Set<T>` already has these semantics: `meet`
intersects and `join` unions. A thin wrapper is still useful so the analysis can
provide helper methods and deterministic display:

```rust
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CallCtx(ascent::lattice::set::Set<Stmt>);

impl CallCtx {
    pub fn bottom() -> Self;
    pub fn singleton(site: Stmt) -> Self;
    pub fn with_site(&self, site: &Stmt) -> Self;
    pub fn with_critical_crossing(&self, outer: &CritId, outer_ctx: &CallCtx) -> Self;
    pub fn can_add_site(&self, site: &Stmt, k: Option<usize>) -> bool;
    pub fn is_top(&self) -> bool; // only for the bounded variant
}

impl ascent::Lattice for CallCtx {
    fn meet(self, other: Self) -> Self { /* intersection */ }
    fn join(self, other: Self) -> Self { /* union */ }
    fn meet_mut(&mut self, other: Self) -> bool { /* intersection */ }
    fn join_mut(&mut self, other: Self) -> bool { /* union */ }
}
```

Start with an unbounded finite powerset. The finite callsite universe already
guarantees termination, including recursion. If we still want a `k` knob, add a
runtime-bounded wrapper later where union beyond `k` becomes `⊤`.

## 3. Relation schema changes

Convert context-carrying relations by appending `CallCtx` as the last column and
declaring them `lattice`. This increases arity by one but preserves the useful
key columns.

| Current relation | New relation | Key used by Ascent |
|---|---|---|
| `pending(Proc, CritId)` | `lattice pending(Proc, CritId, CallCtx)` | `(Proc, CritId)` |
| `can_propagate(Proc, CritId)` | `lattice can_propagate(Proc, CritId, CallCtx)` | `(Proc, CritId)` |
| `slot_from_formal(Proc, CritId, ArgIdx)` | `lattice slot_from_formal(Proc, CritId, ArgIdx, CallCtx)` | `(Proc, CritId, ArgIdx)` |
| `will_propagate(Proc, CritId)` | `lattice will_propagate(Proc, CritId, CallCtx)` | `(Proc, CritId)` |
| `blocked(Proc, CritId)` | `lattice blocked(Proc, CritId, CallCtx)` | `(Proc, CritId)` |
| `top(Proc, CritId)` | `lattice top(Proc, CritId, CallCtx)` | `(Proc, CritId)` |
| `resolve(Proc, CritId, Proc)` | `lattice resolve(Proc, CritId, Proc, CallCtx)` | `(Proc, CritId, Proc)` |
| `index_undecidable(Proc, CritId)` | `lattice index_undecidable(Proc, CritId, CallCtx)` | `(Proc, CritId)` |
| `index_acc(Proc, CritId, Accessor)` | `lattice index_acc(Proc, CritId, Accessor, CallCtx)` | `(Proc, CritId, Accessor)` |
| `adequate(Proc, CritId)` | `lattice adequate(Proc, CritId, CallCtx)` | `(Proc, CritId)` |
| `settled(Proc, CritId)` | `lattice settled(Proc, CritId, CallCtx)` | `(Proc, CritId)` |

Keep syntax-only relations ordinary and context-free:

- `crit_origin(Proc, Stmt, CritId)`
- `crit_operand(CritId, ArgIdx)`
- `call_crit(CritId)`, `load_crit(CritId)`, `store_crit(CritId)`, `index_crit(CritId)`
- `decisive_slot(CritId, ArgIdx)`
- `crit_sig(CritId, Sig)`

Keep graph relations context-free unless we decide to lift the whole pointer
domain into lattices too:

- `edge(Proc, AccessPath, AccessPath)`
- `points(Proc, AccessPath, PtVal)`
- `pub_points(Proc, AccessPath, PtVal)`
- `root_map(Stmt, Base, Base)`
- `free_root(Proc, Base)`, `pub_root(Proc, Base)`

Those relations will still become coarser because `Base::CritSlot(CritId, _)`
and `Base::CritRet(CritId)` no longer include a call string. The merged
placeholder graph is the intended abstraction.

Where a negation needs an existence check, add ordinary projection relations
over the lattice relation:

```text
relation will_propagate_key(Proc, CritId);
will_propagate_key(p.clone(), id.clone()) <-- will_propagate(p, id, ?_ctx);

relation blocked_key(Proc, CritId);
blocked_key(p.clone(), id.clone()) <-- blocked(p, id, ?_ctx);
```

Use these only at stratum boundaries where the old code already used negation.

## 4. Rule changes

### 4.1 Origination

Critical origins stay syntax-only, then seed `pending` with bottom context:

```text
crit_origin(p.clone(), s.clone(), CritId::origin(s.clone())) <--
    critical(s), in_proc(s, p, _);

pending(p.clone(), id.clone(), CallCtx::bottom()) <--
    crit_origin(p, _, id);
```

All operand/result wiring still uses context-free placeholder roots:

```text
edge(p, crit_slot(id, i), var(a)) <-- crit_origin(p, s, id), actual_arg(s, i, a)
edge(p, var(r), crit_ret(id))     <-- crit_origin(p, s, id), bind_ret(s, r)
```

### 4.2 Direct-call propagation

Current call-string rule:

```text
pending(q, id.push(site)) <-- pending(p, id), blocked(p, id),
                              eff_direct(site, p), in_proc(site, q, _),
                              id.depth() < k
```

New lattice rule:

```text
pending(q.clone(), id.clone(), ctx.with_site(site)) <--
    blocked(p, id, ?ctx),
    eff_direct(site, p), in_proc(site, q, _),
    if ctx.can_add_site(site, k);
```

The propagated context is a lattice value. If another path later derives a
different context for the same `(q, id)`, Ascent unions them.

`root_map` no longer builds a renamed `CritId`; it maps placeholder roots to the
same context-free id:

```text
root_map(site, CritSlot(id, i), CritSlot(id, i)) <-- ...
root_map(site, CritRet(id),    CritRet(id))    <-- ...
```

The context movement is represented by `pending(..., ctx.with_site(site))`, not
by changing the placeholder root.

### 4.3 `can_propagate`, `slot_from_formal`, and `will_propagate`

Every rule that previously preserved or extended an `id` call string now keeps
`id` fixed and derives a lattice context in the last column.

```text
can_propagate(p.clone(), id.clone(), ctx.clone()) <--
    pending(p, id, ?ctx),
    eff_direct(site, p), in_proc(site, _, _),
    if ctx.can_add_site(site, k);

slot_from_formal(p.clone(), id.clone(), *i, CallCtx::bottom()) <--
    crit_origin(p, s, id), decisive_var(s, v), carries(p, v, i);

slot_from_formal(q.clone(), id.clone(), ctx.with_site(site)) <--
    slot_from_formal(p, id, i, ?ctx),
    eff_direct(site, p), in_proc(site, q, _),
    actual_arg(site, i, a), carries(q, a, j),
    if ctx.can_add_site(site, k);

will_propagate(p.clone(), id.clone(), ctx.clone()) <--
    slot_from_formal(p, id, _, ?ctx),
    eff_direct(site, p), in_proc(site, _, _),
    if ctx.can_add_site(site, k);
```

The old `id.depth() < k` tests must disappear. With powersets, a recursive
site already in `ctx` does not increase the context and may still propagate
even when `ctx` is at the cardinality cap.

### 4.4 Blocking, top, and dispatch

`blocked` carries the pending context that is blocked by the current merged
points-to graph:

```text
blocked(p.clone(), id.clone(), ctx.clone()) <--
    pending(p, id, ?ctx), decisive_slot(id, i),
    points(p, crit_slot(id, i), Path(w)), free_root(p, w.base);
```

`top` carries the context being forced to the top/CHA summary:

```text
top(p.clone(), id.clone(), ctx.clone()) <--
    blocked(p, id, ?ctx), stuck_key(p, id);
```

`resolve` becomes a lattice relation keyed by `(holder, critical, callee)`:

```text
resolve(p.clone(), id.clone(), callee.clone(), ctx.clone()) <--
    pending(p, id, ?ctx), !will_propagate_key(p, id), call_crit(id),
    decisive_slot(id, i), points(p, crit_slot(id, i), Alloc(l)),
    alloc_type(l, ty), lookup(ty, sig, callee), crit_sig(id, sig);

resolve(p.clone(), id.clone(), callee.clone(), ctx.clone()) <--
    top(p, id, ?ctx), crit_sig(id, sig), sig_target(sig, callee);
```

If two merged contexts dispatch to the same callee, Ascent joins their
`CallCtx` values in the `resolve` row. If the merged points-to state creates
extra callees, that is the expected precision cost.

### 4.5 Index access resolution

`index_acc` mirrors `resolve`: the key is `(holder, critical, accessor)` and the
context is the lattice value.

```text
index_acc(p.clone(), id.clone(), Accessor::Index(c.clone()), ctx.clone()) <--
    pending(p, id, ?ctx), !will_propagate_key(p, id), index_crit(id),
    points(p, crit_slot(id, 1), Const(c));

index_acc(p.clone(), id.clone(), Accessor::IndexUnknown, ctx.clone()) <--
    index_undecidable(p, id, ?ctx);

index_acc(p.clone(), id.clone(), Accessor::IndexUnknown, ctx.clone()) <--
    top(p, id, ?ctx), index_crit(id);
```

`index_undecidable` should likewise become a context-carrying lattice relation
if it reports which abstract context made the index undecidable:

```text
lattice index_undecidable(Proc, CritId, CallCtx);
```

### 4.6 Hybrid-in-hybrid inlining

Current call-string rule:

```text
pending(p, id2.nest(id)) <-- resolve(p, id, callee), pending(callee, id2),
                             id2.nest_depth(id) <= k
```

New lattice rule:

```text
pending(p.clone(), id2.clone(), ctx2.with_critical_crossing(id, &outer_ctx)) <--
    resolve(p, id, callee, ?outer_ctx),
    pending(callee, id2, ?ctx2),
    if ctx2.can_cross_critical(id, &outer_ctx, k);
```

The derived context is:

```text
ctx2 ∪ {id.stmt} ∪ outer_ctx
```

The critical id itself does not change. Ascent joins the resulting context into
the one `(p, id2)` pending row.

### 4.7 `crit_subst`

`crit_subst` no longer creates nested `CritId`s or checks a call-string depth.
It only rebases roots through the resolved placeholder:

```rust
pub fn crit_subst(callee: &Proc, outer: &CritId, base: &Base) -> Option<Base> {
    match base {
        Base::Param(p, i) if p == callee => Some(Base::CritSlot(outer.clone(), *i)),
        Base::Ret(p) if p == callee => Some(Base::CritRet(outer.clone())),
        Base::CritSlot(inner, j) => Some(Base::CritSlot(inner.clone(), *j)),
        Base::CritRet(inner) => Some(Base::CritRet(inner.clone())),
        _ => None,
    }
}
```

The context/cardinality guard lives in the lattice `pending` rule above. The
path and points inlining rules read `resolve(p, id, callee, ?ctx)` but do not
need to put `ctx` into `AccessPath`; the whole point is that the placeholder
graph is merged for `(p, id)`.

## 5. `stuck` and the k policy

There are two reasonable policies.

### 5.1 Unbounded finite powerset

Drop `k_limit` from context propagation. The set of callsites in the program is
finite, and repeated recursion is idempotent, so termination still holds.

Then `stuck` can remain context-free for entry/uncalled boundaries:

```text
relation stuck_key(Proc, CritId);
stuck_key(p, id) <-- pending(p, id, ?_), uncalled(p);
stuck_key(p, id) <-- pending(p, id, ?_), entry(p);
```

This is the simplest first implementation and most directly targets reducing
work by joining contexts.

### 5.2 Bounded powerset with top

If we keep `k`, it means maximum context-set cardinality, not maximum sequence
length. A context at size `k` may still cross an already-present callsite.

Implement this with a custom `CallCtx` that can become `⊤` when a union would
exceed the runtime cap. Then add:

```text
top(p.clone(), id.clone(), ctx.clone()) <-- pending(p, id, ?ctx), if ctx.is_top();
```

Avoid rules like `if ctx.len() >= k` as a substitute for `stuck`; they are
wrong for recursive sites already in the set.

## 6. Stratification impact

The section 10–11 single-fixpoint architecture of `HI-DATALOG-PLAN.md` remains,
but context-bearing control relations are now lattice relations.

Expected strata:

```text
A   EDB + CHA criticality
A′  uncalled(p) from !is_called(p)
A″  syntactic helpers: carries, decisive_var, and any context-free projections
B   SCC: edge, points, pending, can_propagate, slot_from_formal,
    blocked, top, resolve, index_acc, pub_points
C   reporting: adequate, settled, rendered context views
```

Read lattice values with `?ctx` and derive new lattice values in the last
column. Do not negate over a lattice relation inside the SCC; use projection
relations such as `will_propagate_key` only at legal stratum boundaries.

## 7. Query and rendering changes

Because context is outside `CritId`, reporting should display `(CritId,
CallCtx)` pairs:

- `HybridAnalysis::placeholders(p)` should return or render pending rows from
  `pending(p, id, ctx)` filtered by `settled`.
- `dispatches()` can either return `(Proc, CritId, Proc)` for compatibility or
  `(Proc, CritId, Proc, CallCtx)` for diagnostics.
- `render_dispatch` should have a context-aware variant, e.g.
  `⟨L25@{L28,L31b}⟩ → Y.poly`.
- `points_to_path` and the settled-placeholder filter should key by the
  context-free `CritId`, because merged placeholders are intentionally hidden
  once settled.

## 8. Test plan

### 8.1 Lattice tests

Add unit tests for `CallCtx`:

- `join` is union.
- `meet` is intersection.
- partial order is subset.
- inserting an existing callsite is idempotent.
- crossing a critical computes `inner ∪ {outer.stmt} ∪ outer`.
- display is deterministic.

Add a tiny Ascent test proving duplicate keys join:

```text
lattice ctx(&'static str, CallCtx);
ctx("x", {A}) <-- seed_a();
ctx("x", {B}) <-- seed_b();
```

After `run()`, the only row for `"x"` should hold `{A,B}`.

### 8.2 Analysis behavior tests

Update or add:

- **Figure 1 precision:** verify `bar1` still avoids the spurious `Z.poly`
  edge if the joined context remains precise enough.
- **Permutation merge:** two paths with reversed callsite order produce one
  joined context row for the same `(Proc, CritId)`.
- **Recursive idempotence:** a recursive callsite appears once in the context
  and reaches a fixpoint without sequence growth.
- **Precision-loss fixture:** a program where ordered call strings distinguish
  flows but the powerset lattice merges them; assert the coarser result.
- **Scaling rewrite:** replace
  `tests/scaling.rs::call_strings_double_per_level_unless_k_caps_them` with a
  test that validates growth of `CallCtx` lattice values rather than growth of
  `CritId` keys.

## 9. Documentation and profiling updates

Update language that says `CritId` carries a call string:

- `src/access_path.rs` docs for `CritId` and `Base::CritSlot`.
- `src/analysis.rs` comments around propagation, `crit_subst`, `stuck`, and
  the memory-profile note about `crit_map`.
- `HI-DATALOG-PLAN.md` only if it should stop being a historical record;
  otherwise leave it and point to this file as the alternate design.
- `hi-complexity.md`, `backflash-profile.md`, `waste-profile.md`,
  `examples/memory.rs`, `examples/complexity.rs`, and `src/mem.rs` where they
  discuss call-string storage or growth.

Expected profiling changes:

- fewer distinct placeholder roots because `CritId` no longer includes context;
- fewer `edge` and `points` tuples where call strings were the multiplier;
- larger `CallCtx` lattice payloads in context-carrying relations;
- possible precision loss that increases downstream points-to values after
  contexts merge;
- much better recursive behavior because repeated callsites are idempotent.

## 10. Migration sequence

1. Add `CallCtx` with powerset `meet`/`join` semantics.
2. Remove `chain` from `CritId`; keep only the syntactic critical `stmt`.
3. Convert context-carrying relations to lattice relations by appending
   `CallCtx` as the last column.
4. Update rules to read lattice values with `?ctx` and derive extended contexts
   in the last column.
5. Remove `CritId::push`, `CritId::nest`, `depth`, and `nest_depth`; replace
   them with `CallCtx` extension helpers.
6. Rewrite `crit_subst` as pure root rebasing with no context construction.
7. Choose unbounded finite powerset first, or implement runtime-bounded `⊤` if
   preserving a `k` knob is mandatory.
8. Update query/rendering APIs to show `CallCtx` where diagnostics need it.
9. Refresh tests and profiling docs, then run targeted tests before full
   `cargo test`.
