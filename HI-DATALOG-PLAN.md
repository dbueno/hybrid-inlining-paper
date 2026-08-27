# Plan: Hybrid Inlining in Ascent Datalog

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

## 6. Milestones

1. **Ascent spike** — tiny throwaway `ascent!` verifying the exact syntax for
   `agg () = not() in ...` and `agg n = count() in ...` with a user value type
   as a column, and that the macro accepts the S2→S3→S4 stratification.
   Fallback if in-macro negation fights us: hoist N3 into the driver (compute
   `blocked`/`adequate` in Rust between two `ascent!` structs) — the strata
   stay, just materialized by the host.
2. **Domain** — `CritId`, `Base::{CritSlot, CritRet}`, `PtVal`; Display
   (`⟨L25@[L28,L31b]⟩.slot0` or similar) + unit tests alongside the existing
   ones. Keep everything `Send + Sync` (`Arc`) so `ascent_par!` stays open.
3. **S1 + S2 without pendings** — criticality, devirtualization, intra rules,
   direct-call inlining, publication. Checkpoint: `id`'s published summary is
   exactly `ret@id ⊇ par_1@id`.
4. **K=0 baseline** — forced ⊤-summarization at origin; assert published
   summaries for all Figure 1 procedures equal `figure2_summaries()`.
5. **Full pipeline** — pendings, S3–S5, driver loop, `resolved`/`inlined_*`
   feedback. Checkpoint: Figure 1 end-to-end as in §5; tests for the two
   assertions, for `bar1`/`bar2` summaries (Figure 3c/3f), and for the
   absence of any `dispatch(_, c2-or-c4, Z.poly)` fact.
6. **Wire up `examples/figure1.rs`** — build `HybridAnalysis` from
   `figure1()`'s `Program`, run the driver, print per-procedure hybrid
   summaries (Figure 3 style) and the `service()` verdicts. `cargo run
   --example figure1` and `cargo test` must pass.
7. **Stretch** — field rules (suffix congruence) and `lv[v]` criticals with
   N4 (`eval` defs 4–5: all-constants ⇒ per-constant indices, else `[π]`);
   encode Figure 5's `getP`/`setP` as a second example reproducing Figure 6.

## 7. Files

- `src/access_path.rs` — extend `Base`, add `CritId`, `PtVal`.
- `src/analysis.rs` (new) — the `ascent!` program(s) + `run_hybrid(prog:
  &Program, k: usize) -> HybridAnalysis` driver.
- `src/lib.rs` — `pub mod analysis;`.
- `examples/figure1.rs` — call the analysis, print summaries, assert results.

## 8. Risks / open questions

- **Ascent negation ergonomics**: `agg`-based `not` over a relation with
  compound value columns needs the right index pattern; the spike de-risks
  this first. Driver-side fallback preserves the stratified structure.
- **Path explosion**: `flows` is a full transitive closure over access paths;
  fine at POC scale, would need suffix-on-demand + depth capping for real
  programs (the paper caps access-path growth too).
- **Recursion**: the paper unrolls twice under DFS; here the monotone S2
  fixpoint handles recursive *summaries* natively, and the k-limit bounds
  recursive *pending chains*. Worth a small recursive test in milestone 5.
- **Heap aliasing through fields** (`x ⊇ {l}, y ⊇ {l}` sharing `l.f`) is out
  of scope for Figure 1/5; noted as future work (alloc-rooted paths).
