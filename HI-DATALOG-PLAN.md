# Hybrid Inlining in Ascent Datalog

> **Status: implemented.** Sections 1–5 are the original plan, kept as the
> design record. Section 6 records what was built against each milestone,
> section 7 the places the implementation diverged from the sketch, and
> section 9 which risks turned out to be real. `cargo test` runs 39 tests;
> `cargo run --example figure1` and `--example figure5` print Figures 3 and 6.

Implement the paper's pointer analysis (§4.1) with Hybrid Inlining (§3.2) as an
Ascent program layered on the existing EDB schema (`src/ir.rs`) and access-path
domain (`src/access_path.rs`). The acceptance test is Figure 1: the analysis
must compute `pt(second) = {l37} = pt(first)` and `pt(third) = {l14}` in
`service()`, i.e. verify `first == second` is possible and `first != third`
always holds, and must *not* derive the spurious call edge `bar1 → … → Z.poly`.

## 1. Recap of what we're encoding

The compositional pointer analysis summarizes each procedure `p` once as a set
of constraints `ω ⊇ ω′ | ω ⊇ {l} | ω ⊇ {c}` over access paths rooted at the
symbolic variables `par_i@p` / `ret@p` (locals eliminated). Hybrid Inlining
(§3.2) refines this with *hybrid summaries* `𝔥 = (𝔠, S)`:

- **Critical statements** (for pointer analysis, §4.1.3): virtual calls with
  `|dispatch(⊤, proc)| > 1`, and `lv[v]` accesses with a variable index. These
  are kept as *placeholders* in the summary ("connected with all variables
  they access") instead of being summarized under ⊤.
- **Propagation**: inlining a hybrid summary at a callsite renames the
  placeholder into the caller, where more context has accumulated.
- **Adequate context predicate `Φ_a`** (§4.1.3): stop propagating and
  summarize a critical virtual call at holder `p` when
  `pt(recv) ∩ free(𝔞) = ∅` (the receiver's points-to set contains nothing the
  caller can still change) **or** `|dispatch(proc, 𝔞)| = 1`. For `lv[v]`:
  `pt(v) ∩ free(𝔞) = ∅`. `free(𝔞)` = paths accessible outside `p`, i.e. rooted
  at `par_i@p`/`ret@p` — and, in our encoding, at any still-unresolved
  critical placeholder.
- **k-limit** (§3.2.2): bound propagation depth so recursion terminates.

## 2. Where the negations are, and how they stratify

The user-facing requirement: adequacy is computed in one stratum and consumed
by a later one. The negations, from lowest stratum up:

| # | Negation | Over | Stratum boundary |
|---|----------|------|------------------|
| N1 | non-critical virtual call: `count(lookup(_, sig, _)) = 1` (devirtualize) vs `> 1` (critical) | EDB `lookup` | `agg count` over EDB — trivially stratified |
| N2 | `pending(p, id)` minus already-`resolved(p, id)` | `resolved`, an **input** relation fed by the driver from the previous round | stratified because `resolved` is EDB within a round |
| N3 | **adequate**: ¬∃ free-rooted value in `pt(receiver-slot)` | `points` (the pt fixpoint) | `agg () = not(...)` — `points` is a strictly lower stratum |
| N4 | (stretch, `lv[v]`) index decidable: ¬∃ non-constant in `pt(index-slot)` | `points` | same boundary as N3 |

There is one *genuine* cycle that no single stratified program can express:
resolving an adequate critical statement adds constraints, which grow `points`,
which N3 negates over. We break it with a **round-based driver** (the Datalog
reading: an iterated fixpoint of a locally-stratified program; the paper's
reading: repeated application of `ready`):

```
loop {
    run one Ascent program, internally stratified:
      S1  criticality + CHA devirtualization           (agg count over EDB)
      S2  monotone core: per-proc constraint graphs, pt fixpoint,
          summary publication, direct-call inlining,
          critical-placeholder propagation             (guarded by ¬resolved, N2)
      S3  blocked(p, id): receiver slot sees a free root    (reads points)
      S4  adequate(p, id) via not(blocked)             (N3)
      S5  dispatch + emit resolution facts             (reads adequate; output-only)
    driver: for each new resolution, inline the chosen callee's published
      summary at the placeholder (pure renaming, in Rust), append the results
      to input relations `resolved` and `inlined_edge`/`inlined_points`;
    if nothing new: break
}
```

Ascent 0.8 supports exactly this: `agg () = not() in rel(...)` and
`agg n = count() in rel(...)` (`ascent::aggregators::{not, count}` — confirmed
present in the vendored 0.8.0 source), and the macro rejects non-stratified
uses at compile time. S5's outputs feed nothing inside the program, so the
whole round compiles as one stratified `ascent!` struct.

Each round resolves at least one pending critical instance or terminates, and
the k-limit bounds the number of instances, so the driver terminates.

## 3. Domain extensions (`src/access_path.rs`)

A critical statement propagated along a call chain needs an identity per
holder — effectively a call string:

```rust
/// A pending critical-statement instance: the original statement plus the
/// chain of callsites it was propagated through (innermost first).
/// Arc'd cons-list or Arc<[Stmt]>; grows by one on each inlining.
pub struct CritId { pub stmt: Stmt, pub chain: Arc<[Stmt]> }
```

Extend `Base` so placeholders are ordinary nodes in the constraint graph —
this *is* the paper's "critical statements are connected with all variables
they access":

```rust
pub enum Base {
    Var(Var),
    Param(Proc, ArgIdx),
    Ret(Proc),
    CritSlot(CritId, ArgIdx),  // i-th operand of a pending critical stmt
    CritRet(CritId),           // its result
}
```

Add the points-to element type:

```rust
pub enum PtVal { Path(AccessPath), Alloc(Alloc), Const(Const) }
```

Key invariant (this makes N3 correct): the pt fixpoint **never drops symbolic
paths**. If `recv` may point to something the caller controls, `points`
contains a `PtVal::Path` rooted at `Param`/`Ret`/unresolved-`CritRet`, and N3
sees it. `pt(recv) ∩ free = ∅` is then literally "no such tuple exists".

## 4. The Ascent program (`src/analysis.rs`)

One `ascent!` struct `HybridAnalysis` containing (a) copies of the EDB
relations of `ir::Program` (driver copies the Vecs in), (b) the driver-fed
relations `resolved(Proc, CritId)`, `inlined_edge(Proc, AccessPath,
AccessPath)`, `inlined_points(Proc, AccessPath, PtVal)`, and (c) the IDB
below. Rule sketches (Ascent-ish pseudocode):

### S1 — criticality and devirtualization (N1)

```text
sig_size(sig, n)      <-- virtual_call(_, _, sig), agg n = count() in lookup(_, sig, _)
mono_target(s, p)     <-- virtual_call(s, _, sig), sig_size(sig, 1), lookup(_, sig, p)
eff_direct(s, p)      <-- direct_call(s, p) | mono_target(s, p)
critical(s)           <-- virtual_call(s, _, sig), sig_size(sig, n), if n > 1
critical(s)           <-- load_index_var(s, ..) | store_index_var(s, ..)   // stretch
```

### S2 — monotone core

Per-procedure constraint graphs. `edge(p, sup, sub)` means `sup ⊇ sub`;
`points(p, ω, v)` is `v ∈ pt(ω)` during `p`'s summarization.

Intraprocedural `cons` (Figure 4, defs 1–3 and 6–8):

```text
edge(p, var(to), var(from))      <-- mov(s, to, from), in_proc(s, p, _)
points(p, var(v), Alloc(l))      <-- alloc(s, v, l), in_proc(s, p, _)
points(p, var(v), Const(c))      <-- const_assign(s, v, c), in_proc(s, p, _)
edge(p, var(to), var(base).f)    <-- load_field(s, to, base, f), ...     // stretch
edge(p, var(base).f, var(from))  <-- store_field(s, base, f, from), ...  // stretch
edge(p, var(v), param(p, i))     <-- formal(p, i, v)
edge(p, ret(p), var(v))          <-- ret(p, v)
```

Closure:

```text
points(p, sup, v)  <-- edge(p, sup, sub), points(p, sub, v)
points(p, sup, Path(sub)) <-- edge(p, sup, sub), if sub is symbolically rooted
                              // keep the symbolic path itself: pt may contain
                              // non-local paths (§4.1.2), and N3 depends on it
flows(p, a, b)     <-- edge(p, a, b) | (edge(p, a, m), flows(p, m, b))
// stretch, for fields: suffix congruence ω ⊇ ω′ ⟹ ω.f ⊇ ω′.f, applied
// on demand for observed suffixes
```

Publication (local elimination, §2.1): the published vocabulary of `p` is
`Param(p,_) | Ret(p)` **plus the placeholder nodes of unresolved pendings**
(that's what makes the summary hybrid). Once resolved, placeholder nodes
demote to locals and are eliminated like any `Var`.

```text
pub_root(p, base)       <-- base is Param(p,_) or Ret(p)
pub_root(p, CritSlot(id,_)/CritRet(id)) <-- pending(p, id), !resolved(p, id)   // N2
pub_edge(p, a, b)       <-- flows(p, a, b), pub_root(a.base), pub_root(b.base)
pub_points(p, a, v)     <-- points(p, a, v), pub_root(a.base),
                            v is Alloc/Const or Path with pub_root
```

Direct-call inlining at site `s` in `q` calling `p` — substitution σ_s maps
roots and keeps suffixes: `Param(p,i) ↦ var(actual_arg(s,i))`,
`Ret(p) ↦ var(bind_ret(s))`, `CritSlot(id,i) ↦ CritSlot(push(s,id),i)`,
`CritRet(id) ↦ CritRet(push(s,id))`:

```text
edge(q, σ_s(a), σ_s(b))   <-- eff_direct(s, p), in_proc(s, q, _), pub_edge(p, a, b)
points(q, σ_s(a), σ_s(v)) <-- eff_direct(s, p), in_proc(s, q, _), pub_points(p, a, v)
```

Pending origination and propagation (guarded by N2; k-limit guard here too):

```text
pending(p, CritId{stmt: s, chain: []})  <-- critical(s), in_proc(s, p, _)
edge(p, critslot(id, i), var(a))        <-- pending-origin id at s, actual_arg(s, i, a)
edge(p, var(r), critret(id))            <-- pending-origin id at s, bind_ret(s, r)
pending(q, push(s, id))                 <-- pending(p, id), !resolved(p, id),
                                            eff_direct(s, p), in_proc(s, q, _),
                                            if id.chain.len() < K
// the slot/ret edges of a propagated instance arrive for free via pub_edge σ
```

### S3/S4 — adequacy (N3): *the stratum that computes adequate contexts*

```text
blocked(p, id)  <-- pending(p, id), points(p, critslot(id, 0), Path(w)),
                    if is_free_root(w.base)   // Param | Ret | CritRet of a
                                              // pending id2 with !resolved
adequate(p, id) <-- pending(p, id), !resolved(p, id),
                    agg () = not() in blocked(p, id)
forced(p, id)   <-- pending(p, id), entry(p)          // propagation ends at root
forced(p, id)   <-- pending(p, id), if id.chain.len() == K   // k-limit fallback
```

`blocked` is exactly `pt(lv₀) ∩ free(𝔞) ≠ ∅`; the single-dispatch disjunct of
`Φ_a` falls out below (if pt(recv) pins one type, one target is dispatched).
Empty `pt(recv)` with no free roots ⇒ adequate but dispatches nothing: dead
code, sound.

### S5 — dispatch, *the subsequent stratum that uses adequacy*

```text
dispatch(p, id, callee) <-- adequate(p, id), points(p, critslot(id, 0), Alloc(l)),
                            alloc_type(l, t), crit_sig(id, sig), lookup(t, sig, callee)
dispatch(p, id, callee) <-- forced(p, id), crit_sig(id, sig), lookup(_, sig, callee)
                            // ⊤-summarize at root / k-limit: all CHA targets
resolve_out(p, id, callee) <-- dispatch(p, id, callee)
```

`resolve_out` is consumed by nothing in-program — that keeps the struct
stratified. The driver turns each new `(p, id, callee)` into:

- `resolved(p, id)` (input for next round's N2), and
- σ_crit-renamed copies of `pub_edge(callee, ..)`/`pub_points(callee, ..)`
  appended to `inlined_edge`/`inlined_points`, where σ_crit maps
  `Param(callee, i) ↦ CritSlot(id, i)` and `Ret(callee) ↦ CritRet(id)`.
  If the callee's published summary itself carries pending placeholders
  (hybrid-in-hybrid), σ_crit renames them into `p` and the driver also seeds
  the corresponding `pending` facts — same semantics as any other inlining.

Design decision, noted for honesty: within one round an instance propagates
past a holder even if that holder turns out adequate in the same round (e.g.
Figure 1's `L25` instance reaches both `bar1` and `service` in round 1, and
both copies resolve to `Y.poly`). Suppressing that would need ¬adequate inside
S2 — a cycle. The duplication is confluent and harmless (Theorem 3.3 says
resolving early vs. late is equally precise); rounds still terminate.

## 5. Figure 1 walkthrough (expected derivations)

Round 1, S2 fixpoint:
- `L25` is critical (`poly(Obj)` has 2 CHA targets, N1). All other calls are
  `eff_direct`.
- `id`: `pub_edge(id, ret@id, par_1@id)` — matches Figure 2(b) and the
  existing `figure2_summaries()` oracle.
- `foo`: inlining `id` at L24 gives `tx ⊇ par_1@foo`; pending
  `c0 = (L25, [])` with `critslot(c0,0) ⊇ tx`, `critslot(c0,1) ⊇ par_2@foo`,
  `r25 ⊇ critret(c0)`, `ret@foo ⊇ r25`. Published: Figure 3(a).
- `mid` inlines `foo` at L28 → `c1 = (L25,[L28])`, Figure 3(b).
- `bar1` inlines `mid` at L31b → `c2 = (L25,[L28,L31b])` with
  `points(bar1, critslot(c2,0), Alloc(l31))` and
  `critslot(c2,1) ⊇ par_1@bar1`; `bar2` symmetrically gets `c3` with `l34`.
- `service` inlines both, extending to `c4`/`c5` with
  `critslot(c4,0) ∋ Alloc(l31)`, `critslot(c4,1) ⊇ first`,
  `second ⊇ critret(c4)` (and `l34`/`third` for `c5`).

Round 1, S3–S5: `c0` blocked at `foo` (receiver slot sees `par_1@foo`), `c1`
blocked at `mid` — propagation was correct. `c2`, `c4` adequate:
`pt = {l31}`, no free roots → `dispatch → Y.poly` only. `c3`, `c5` →
`Z.poly` only. **No `bar1 → Z.poly` edge exists** — the precision claim.

Round 2, after driver inlines resolutions (`Y.poly`: `ret ⊇ par_1`;
`Z.poly`: `ret ⊇ {l14}`):
- `critret(c4) ⊇ critslot(c4,1) ⊇ first` ⟹ `points(service, second, Alloc(l37))`
  and nothing else; `points(service, third, Alloc(l14))` and nothing else.
- `bar1` republishes as Figure 3(c) (`ret@bar1 ⊇ par_1@bar1`), `bar2` as 3(f)
  (`ret@bar2 ⊇ {l14}`).

Round 3: no new `resolve_out` → fixpoint. Assertions check out:
`pt(first) = pt(second) = {l37}`, `pt(third) = {l14}`, disjoint from
`pt(first)`.

Bonus checkpoint: running with `K = 0` forces every critical instance to
⊤-summarize at its origin — that *is* the context-insensitive analysis, and
its published summaries must equal `figure2_summaries()` (Figure 2). Free
regression oracle already in the repo.

## 6. Milestones — **all done**

Status as implemented. `cargo test` (39 tests) and both examples pass;
`cargo clippy --all-targets` is clean.

1. **Ascent spike** — ✅ done and discarded. Ascent 0.8 accepts everything the
   plan needed, and the driver-side fallback was *not* required:
   - `agg n = count() in rel(..)` over an EDB relation (N1);
   - first-class `!rel(args)` negation clauses (the macro desugars them to
     `agg () = not() in ..`), used for N2/N3 and the `forced` rules;
   - compound user types (`CritId`, `AccessPath`, `PtVal`, `Accessor`) as
     relation columns, with `let` / `if let` / `?pat` body clauses;
   - the S1→S2→S3→S4→S5 stratification, checked by the macro at compile time.
2. **Domain** — ✅ `CritId` (`origin`/`push`/`nest`/`depth`),
   `Base::{CritSlot, CritRet}`, `PtVal`, plus `AccessPath::{rebase, extend,
   strip_prefix, crit_slot, crit_ret}`. Display renders a placeholder as
   `⟨L25@L28·L31b⟩:arg0` / `:res`. Everything is `Arc`-backed and
   `Send + Sync`, so `ascent_par!` stays open. 8 unit tests.
3. **S1 + S2** — ✅ criticality, CHA devirtualization, the intra rules, the
   `points` closure, publication, and direct-call inlining. Checkpoint met:
   `id` publishes exactly `ret@FacadeImpl.id ⊇ par_1@FacadeImpl.id`.
4. **K = 0 baseline** — ✅ `k_zero_reproduces_figure_2_exactly` asserts the
   published summaries of *every* Figure 1 procedure equal
   `figure1::figure2_summaries()`, the pre-existing oracle, on the nose.
5. **Full pipeline** — ✅ pendings, S3–S5, the round driver, and the
   `resolution`/`index_resolution`/`resolved` feedback. Figure 1 runs exactly
   as §5 predicts, including the harmless `service` duplicates. Tests cover
   the two `service()` assertions, Figures 3(a)/3(b)/3(c)/3(f), the absence of
   any `bar1 → Z.poly` edge, and recursion.
6. **`examples/figure1.rs`** — ✅ runs the driver at `k = 0` and `k = 4`,
   prints per-procedure hybrid summaries Figure 3 style plus the resolved call
   edges, and reports the `service()` verdicts.
7. **Stretch** — ✅ both halves.
   - Field and constant-index rules (Figure 4 defs 6–8) with **on-demand
     suffix congruence**: `ω ⊇ ω′ ⟹ ω.a ⊇ ω′.a` fires only for suffixes some
     path in the procedure actually mentions, keeping the path set finite. It
     is triggered from *both* sides of an edge — the sub-side trigger is what
     lets a store through a local (`v["old"]`) reach the published summary via
     `ret@build ⊇ v`.
   - `lv[v]` criticals with N4 (`index_undecidable`): `src/figure5.rs` encodes
     Figure 5 and `examples/figure5.rs` reproduces Figure 6.

### What the analysis actually derives

Figure 1, `k = 4` (2 rounds):

```text
FacadeImpl.foo:   ret@foo ⊇ ⟨L25⟩:res             ⟨L25⟩ deferred
                  ⟨L25⟩:arg0 ⊇ par_1@foo
                  ⟨L25⟩:arg1 ⊇ par_2@foo          -- Figure 3(a)
FacadeImpl.mid:   ... ⟨L25@L28⟩ ...               -- Figure 3(b)
FacadeImpl.bar1:  ret@bar1 ⊇ par_1@bar1           -- Figure 3(c)
FacadeImpl.bar2:  ret@bar2 ⊇ {l14}                -- Figure 3(f)

⟨L25@L28·L31b⟩ → Y.poly     ⟨L25@L28·L34b⟩ → Z.poly
pt(first) = pt(second) = {l37}     pt(third) = {l14}
```

Figure 5, `k = 4` vs `k = 0` — the index-sensitivity Hybrid Inlining buys:

```text
k = 4   build:  ret@build["old"] ⊇ par_1@build["cur"]     -- Figure 6(d)
                getP/setP keep ⟨L2⟩ / ⟨L5⟩ deferred       -- Figure 6(a)
k = 0   build:  ret@build[π] ⊇ par_1@build[π]             -- every slot merged
```

## 7. Where the design moved

Six decisions differ from the sketch above; all are simplifications found
while building, not retreats.

- **No `flows` relation.** `points(p, a, PtVal::Path(b))` *is* the transitive
  closure restricted to symbolically-rooted targets, which is all publication
  and adequacy ever need. `pub_edge` reads it directly, so the separate
  transitive-closure relation was dropped.
- **No driver-side renaming.** The plan had the driver compute σ-renamed
  `inlined_edge`/`inlined_points` in Rust. Instead the driver feeds back only
  the *decisions* (`resolution`, `index_resolution`, `resolved`) as input
  relations, and the renaming happens inside S2 against the callee's
  **current** summary. Stratification is unaffected — the feedback relations
  are still inputs — and a decision made in round 1 keeps paying off as the
  callee's own summary improves in round 2.
- **`forced` is `!can_propagate`, not `entry`.** `can_propagate(p, id)` is
  false at an entry, at a procedure with no callers, *and* at the k-limit, so
  one rule covers all three. `entry(p)` gets its own rule as well, for a
  procedure that is both an entry and called from elsewhere. Both are guarded
  by `!adequate`, without which Figure 1's `service` would ⊤-summarize its
  own adequate instances and re-admit `Z.poly`.
- **`Φ_a`'s second disjunct is folded into N1.** `|dispatch(proc, 𝔞)| = 1` is
  handled at the CHA level by `sig_size(sig, 1) ⟹ mono_target`, which makes
  such a site non-critical from the start. Narrowing by a path's *declared*
  type is not modelled, so that case is CHA-only.
- **One schema, two Ascent programs.** `ir::Program` had become a pure data
  container — nothing called its `run()` — while `Round` re-declared all of
  its relations by hand. The EDB now lives in a single `ascent_source! { edb:
  … }` in `src/ir.rs` that both programs `include_source!`, so the schema
  cannot drift. `Round::for_program` still copies the facts relation by
  relation, which is the one thing sharing cannot fix; a test builds a program
  with every relation populated and compares `relation_sizes_summary()` across
  the copy, so a dropped line fails loudly instead of leaving a relation
  silently empty.
- **A decisive slot per kind of critical statement.** `blocked` intersects
  `free(𝔞)` with operand 0 for a virtual call (the receiver) and operand 1 for
  an `lv[v]` access (the index), via `decisive_slot`.
- **An `lv[v]` resolution lands on both the base's direct operands and its
  symbolic paths.** The operands catch a local base (`v["old"]` in `build`);
  the symbolic paths catch a parameter base (`par_1@setP[c]` in `setP`),
  without which a store would never become visible to the caller.

## 8. Files

- `src/ir.rs` — the EDB schema as an `ascent_source!`, plus the `Program`
  struct that includes it. Five relations (`proc_type`, `proc_sig`,
  `direct_subtype`, `load_static`, `store_static`) are declared and copied but
  read by no rule yet.
- `src/access_path.rs` — `Base::{CritSlot, CritRet}`, `CritId`, `PtVal`,
  path rebasing/extension. 8 unit tests.
- `src/analysis.rs` — the `ascent!` program `Round`, the `Decisions` the
  driver carries between rounds, and `run_hybrid(prog, k) -> Hybrid`.
- `src/figure1.rs`, `src/figure5.rs` — the two paper programs as EDB, with
  `figure2_summaries()` as the context-insensitive oracle. Moved out of
  `examples/` so `cargo test` actually runs their sanity tests, which it did
  not before.
- `tests/hybrid_inlining.rs` — 23 end-to-end tests.
- `examples/figure1.rs`, `examples/figure5.rs` — the runners.

## 9. Risks, resolved and remaining

- **Ascent negation ergonomics** — *resolved*. `!rel(args)` works directly on
  relations with compound value columns; no `agg`-based workaround and no
  driver-side fallback were needed.
- **Recursion** — *resolved*. A recursive *summary* is just the S2 fixpoint
  (`a_recursive_summary_is_just_a_fixpoint`). A recursive *pending chain* is
  bounded by the k-limit, and the deepest instance is `forced` to
  ⊤-summarize. When the receiver is the recursive procedure's own parameter,
  that ⊤ is unavoidable and shows up as imprecision — asserted, with the
  reasoning, in `a_receiver_the_recursion_never_pins_falls_back_to_top`.
- **Path explosion** — *still open, as expected*. Suffix congruence is
  on-demand but still quadratic in observed paths per procedure, and there is
  no depth cap on access paths. Fine at POC scale; a real program would need
  the paper's access-path bound.
- **Heap aliasing through fields** — *still open*. There are no alloc-rooted
  paths, so two variables pointing at the same allocation site do not share
  `l.f`. Figures 1 and 5 do not need it; a store through a base whose
  points-to set is a bare allocation site is where it would first bite.
- **Duplicated instances within a round** — *accepted, as the plan predicted*.
  `⟨L25@L28·L31b⟩` resolves at `bar1` while `⟨L25@L28·L31b·L38⟩` is created at
  `service` in the same round. Confluent and harmless (Theorem 3.3); at
  `k = 2` the duplicates never arise and the answer is identical, which
  `a_tight_k_limit_still_gets_the_right_answer` checks.
