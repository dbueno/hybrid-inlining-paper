# Why the analysis does not finish on backflash.apk

> **Resolved.** Hypothesis 1 below was right, and the fix is the `paths`
> relation of `src/ir.rs` — a syntactic bound on the access-path vocabulary,
> computed by `src/path_bound.rs` and tested against by every rule that
> lengthens a path. Under it this same input converges in **3.6 s** with
> `edge` at 245,047 tuples, and the single-procedure case below in **21 ms**.
> The vocabulary of the whole program is 741 suffixes, four accessors deep at
> the most. Everything from here to "[After the bound](#after-the-bound)"
> describes the analysis *before* that bound, and is kept as the measurement
> that motivated it; that last section is where it stands now.

`backflash.apk` is a TaintBench Android app. CTADL imports it in a fraction of
a second and the translation into our EDB is instant. The analysis then runs
forever. This is what it is doing.

Everything below was measured with `examples/ctadl_profile.rs`, which runs
`analysis::profile::ProfiledHybridAnalysis` — the same rules as
`HybridAnalysis`, from the same `hybrid_rules` source, under Ascent's
`#![measure_rule_times]` and `#![generate_run_timeout]`. The timeout is what
makes any of this observable: the fixpoint never converges, and `run_timeout`
stops between iterations with every rule's timer already filled in.

```sh
cargo run --features ctadl,profile --release --example ctadl_profile -- \
    backflash.apk --k 1 --timeout 120
```

## The short version

The analysis has **no bound on how long an access path may get**. Suffix
congruence keeps extending paths, and a cycle among the constraints of a
single procedure lets it extend them without limit. On backflash it builds
paths like `x.wl.wl.wl.wl.length[]` — the same field repeated four times, which
no heap object can satisfy — and 85% of all the paths it invents are of that
kind. There is no fixpoint to reach. The clock is the only thing that stops it.

That is the cause. There is also a large constant factor on top of it — the
congruence join cannot use an index and rescans a multi-million-tuple relation
every iteration — but fixing the constant would only buy time, not termination.

## What the input looks like

The translation is not the problem. It takes 0.6s and produces a small,
ordinary fact base:

```
3898 CIR functions  ->  2375 procedure   29166 in_proc     5526 virtual_call
                        2477 direct_call  4330 lookup       754 entry
```

Note `virtual_call` (5526) is more than twice `direct_call` (2477), and no
CTADL front end populates `load_index_var`/`store_index_var`. So on this input
"critical statement" means "unresolved dispatch", and there are a lot of them.

## Where the time goes: one SCC, then two rules

The program has 50 SCCs. Forty-nine of them finish in about 60 milliseconds
between them. The fiftieth does not finish at all:

```
scc 41: iterations: 6, time: 7.914458ms
scc 42: iterations: 1, time: 146.666µs
scc 43: iterations: 2, time: 182.375µs
scc 44: iterations: 1, time: 29.541µs
scc 45: iterations: 8, sum of rule times: 455.283837205s     <-- 99.5% of wall
```

SCC 45 is stratum B, the big mutually-recursive block. Eight iterations, 455
seconds, still going. (Asking for a 120s timeout produced a 457s run: Ascent
only checks the deadline between iterations, and a single iteration here takes
about a minute. That is a symptom, not a measurement error.)

Inside SCC 45 there are 99 rules. Four of them account for 99.8% of it:

```
     secs      %  rule
   208.45  45.8%  edge <-- edge_indices_none_total, path_used_indices_0_1_delta, if let ⋯, if ⋯
   161.23  35.4%  edge <-- edge_indices_none_total, path_used_indices_0_1_delta, if let ⋯, if ⋯
    76.13  16.7%  edge <-- edge_indices_none_delta, path_used_indices_0_1_total+delta, if let ⋯, if ⋯
     8.79   1.9%  edge <-- edge_indices_none_delta, path_used_indices_0_1_total+delta, if let ⋯, if ⋯
     ----
     0.70   0.2%  the other 95 rules, combined
```

Those four are the two **suffix congruence** rules of `src/analysis.rs:238-251`,
each in the two semi-naive variants Ascent generates:

```rust
edge(p.clone(), sup2.clone(), sub.extend(rest)) <--
    edge(p, sup, sub),
    path_used(p, sup.base, sup2),
    if let Some(rest) = sup2.strip_prefix(sup),
    if !rest.is_empty();

edge(p.clone(), sup.extend(rest), sub2.clone()) <--
    edge(p, sup, sub),
    path_used(p, sub.base, sub2),
    if let Some(rest) = sub2.strip_prefix(sub),
    if !rest.is_empty();
```

The relation they feed grows to 9.7 million tuples from a 29-thousand-statement
input — a 334× blowup — before we stop it:

```
edge          9,747,467
path_used       616,299
points          172,632
in_proc          29,166   (the input)
```

## It is not a scaling problem

The obvious reading — "2375 procedures is just a lot" — is wrong. Shrinking the
input does not help:

| input | statements | result |
|---|---|---|
| all 2375 procedures | 29166 | no convergence, 10.2 GB, killed at 27 min |
| 25 largest procedures | 9670 | no convergence |
| **1 largest procedure** | **2039** | **no convergence**, `edge` = 1.47M |

One procedure. `Lcom/adobe/flashplayer_/AdobeUtil;->onCreate()V`, 2039
statements, and the fixpoint does not close. Nothing interprocedural is
involved.

Nor is it Hybrid Inlining's context sensitivity. Setting `--k 0`, which
forbids propagation entirely, changes nothing:

```
k=1, one procedure, 45s:  no convergence, edge = 1,465,954
k=0, one procedure, 60s:  no convergence, edge = 1,462,439
```

So the blowup is in the intraprocedural constraint closure — the part that is
just field-sensitive points-to — and the hybrid machinery on top of it is
innocent.

## Why it never terminates

Access paths have no length bound anywhere in the rules. The `k_limit` bounds
`CritId::depth()`, which is the *call string* of a pending critical statement.
It says nothing about `AccessPath::accessors`.

Measured on that one procedure (25s budget, so smaller than the table above),
at the moment we stop it:

```
=== access-path depth in `edge` ===
  depth   0:        422  ( 0.03%)
  depth   1:       2568  ( 0.17%)
  depth   2:      15408  ( 1.01%)
  depth   3:      91818  ( 6.03%)
  depth   4:     399312  (26.24%)
  depth   5:     713871  (46.91%)
  depth   6:     287463  (18.89%)
  depth   7:      11048  ( 0.73%)
```

The source IR writes **at most one accessor per statement**: a `load_field` is
`to = base.f`, depth 1. Everything past depth 1 was synthesized by congruence,
and that is 99.8% of the paths. The distribution is not converging on a
maximum — it has a frontier at depth 6-7 that is still advancing when we cut it
off.

The deepest path at that moment:

```
v51@...AdobeUtil;->onCreate()V . [] . <AdobeUtil.wl> . <AdobeUtil.wl>
                               . <AdobeUtil.wl> . <AdobeUtil.wl> . length . []
```

`AdobeUtil.wl` has type `PowerManager$WakeLock`. A `WakeLock` does not have a
field `AdobeUtil.wl`. So `.wl.wl` denotes no path through any heap that can
exist — and neither do most of the paths being built:

```
paths repeating an accessor: 426,679 of 503,560 distinct  (84.7%)
```

### The mechanism

`path_used` is fed from `edge`'s own two columns (`src/analysis.rs:234-236`):

```rust
path_used(p, a.base, a) <-- edge(p, a, _);
path_used(p, b.base, b) <-- edge(p, _, b);
```

So every longer path congruence invents is immediately a `path_used` fact, and
`path_used` is congruence's own second premise. The two rules pump each other.
One cycle in `edge` plus one strict extension is enough to run forever:

```
given   a ⊇ b   and   b ⊇ a.f
rule 1                       gives   a.f ⊇ b.f
rule 1 again, on b ⊇ a.f     gives   b.f ⊇ a.f.f
rule 1 again, on a ⊇ b       gives   a.f.f ⊇ b.f.f
...
```

Those cycles are there. In that single procedure:

```
503,560 distinct paths, 760,955 edges
paths on a cycle: 25,410   (largest SCC: 9 paths)
```

25 thousand paths sit on a cycle in the constraint graph. Each one is a
generator.

## Why it is also slow per iteration

Separate from termination, the constant factor is bad, for two compounding
reasons visible in Ascent's own plan.

**The join cannot use an index.** The plan says `edge_indices_none_total` —
`none` meaning no key, i.e. a full scan of `edge`. Ascent indexes on whole
columns, and this join keys on `sup.base`, which is a *projection of* column 1,
not a column. Compare a rule that does get an index:

```
points <-- edge_indices_0_2_total, points_indices_0_1_delta [SIMPLE JOIN]      0.07s
edge   <-- edge_indices_none_total, path_used_indices_0_1_delta, if let ⋯    208.45s
```

**And the scan is over `_total`, not `_delta`.** Every new `path_used` tuple
forces a rescan of the entire, by-then-enormous `edge` relation. Combined with
the fan-out of the join:

```
paths per base: n=134  mean=3758  p50=2504  p99=7022  max=12900
=> congruence scans ~760,955 edges x ~3758 paths/base per iteration
```

134 distinct bases, thousands of paths hanging off each. That is on the order
of 2.9 billion candidate pairs per iteration, each ending in a `strip_prefix`.
Which is exactly what a sample of the stuck 27-minute process shows — 32% of
samples sitting in `memcmp`, from prefix comparison and from hashing the
string-backed `Proc`/`Base` keys:

```
1104 _platform_memcmp  (in libsystem_platform.dylib)
 195 DYLD-STUB$$memcmp
     ... of 3550 total samples
```

## Hypothesis, stated plainly

1. **The cause is unbounded access-path depth.** Suffix congruence has no
   length cap, `path_used` feeds it from its own output, and cycles in `edge`
   make the closure infinite. The analysis has no fixpoint on this input, at
   any `k`, on a single procedure. This is the standard failure mode of a
   field-sensitive analysis that materializes access paths without widening.

2. **The constant factor is a missing index.** The congruence join keys on
   `sup.base`, which Ascent cannot index because it is not a column, so each
   iteration full-scans `edge` with a fan-out of ~3700. This makes the
   non-termination expensive rather than causing it.

3. **The precision being bought is fictional.** 85% of the paths are
   type-impossible (`.wl.wl`). Bounding depth is not only necessary for
   termination — at these depths it costs nothing real.

## What to try, in order

- **Cap access-path length** and widen past it (truncate to depth *d* and
  append an unknown-suffix accessor, the way `Accessor::IndexUnknown` already
  handles an unknown index). This is the fix for the cause; everything else is
  a speedup. Worth sweeping *d* = 2, 3, 4 to see where precision on the
  TaintBench queries stops improving — the depth histogram suggests well below
  where it currently runs.

- **Make the join indexable** by giving `edge` its bases as real columns
  (`edge(Proc, Base, AccessPath, Base, AccessPath)` or a companion relation), so
  Ascent can plan a `[SIMPLE JOIN]` on `(p, base)` instead of a full scan.

- **Filter congruence by type.** Reject an extension whose accessor is not a
  field of the static type reached so far. The EDB already has `alloc_type`,
  `proc_type` and the field names carry their declaring class, so `.wl.wl` is
  rejectable. This would remove 85% of the paths outright.

- **Restrict congruence to published roots.** It currently fires on every path
  in the procedure, including purely local ones that `pub_edge` will discard.
  Applying it only to `pub_root`-based paths would shrink both sides of the
  join.

## Reproducing

```sh
# the profile above
cargo run --features ctadl,profile --release --example ctadl_profile -- \
    backflash.apk --k 1 --timeout 120

# the single-procedure case, which is enough to show everything
cargo run --features ctadl,profile --release --example ctadl_profile -- \
    backflash.apk --k 1 --timeout 25 --max-procs 1

# the bytes, per relation, at four sizes
cargo run --features ctadl --release --example ctadl_memory -- \
    backflash.apk --k 1 --max-procs 100 --max-procs 400 --max-procs 1000
```

`--max-procs N` keeps the N procedures with the most statements and the facts
that mention only those; type-level facts (`lookup`, `direct_subtype`,
`alloc_type`) are kept whole so that what counts as critical does not change.

<a id="after-the-bound"></a>

# After the bound

Same input, same command, with `paths` in place. It converges.

```
procs=2375 stmts=29166 virtual_call=5526 direct_call=2477 k=1
converged=true wall=3.33s
```

Peak physical footprint is 1.67 GB, from a second run polled by `footprint`
(the polling costs it about a third of a second of wall). Against the run
above: no convergence, 10.2 GB, killed at 27 minutes. The
whole fixpoint is now shorter than the *translation* used to make it look
cheap by comparison.

## The vocabulary, and what it did to the paths

`paths` holds 741 suffixes. That is the entire access-path alphabet the
program's syntax asks for, and no rule may leave it:

```
                     before (25s, 1 proc)        after (3.3s, all 2375 procs)
depth 0                    0.03%                       13.76%
depth 1                    0.17%                       81.79%
depth 2                    1.01%                        4.40%
depth 3                    6.03%                        0.04%
depth 4                   26.24%                        0.00%  (17 tuples)
depth 5                   46.91%                          —
depth 6                   18.89%                          —
depth 7                    0.73%                          —
repeating an accessor      84.7%                        1.8%
```

The distribution now sits where the front end put it — 82% of paths are the
single accessor a `load_field` writes down — instead of on a frontier that was
still advancing when the clock stopped it. The deepest path left is four
accessors and is a real chain through real fields:

```
par0@…LoaderManagerImpl$LoaderInfo;->callOnLoadFinished(…)
  .<LoaderInfo.this$0> .<LoaderManagerImpl.mActivity>
  .<FragmentActivity.mFragments> .<FragmentManagerImpl.mNoTransactionsBecause>
```

Nothing like `x.wl.wl.wl.wl.length[]` survives. The cycles that generated
those are still there — 3,846 paths sit on one, largest SCC 205 — they simply
no longer produce anything new, which is the point: the bound does not remove
the cycles, it removes their range.

The join fan-out collapses with the vocabulary:

```
paths per base   before:  n=134    mean=3758  p50=2504  p99=7022  max=12900
                 after:   n=24145  mean=3     p50=1     p99=44    max=49
```

## Where the time goes now

One SCC still dominates — stratum B, as before — but it closes:

```
scc 45: iterations: 46, time: 3.259s   (sum of rule times 2.579s)
everything else: 62ms
```

Inside it, the ranking has changed hands. Suffix congruence is no longer the
whole cost; the alias closure is:

```
     ms      %  rule
  633.1  24.6%  points   <-- edge_total, points_delta                [SIMPLE JOIN]
  370.8  14.4%  pub_edge <-- points_delta, pub_root, pub_root
  300.2  11.6%  edge     <-- edge_total, path_used_delta, ⋯, paths   (congruence, sub side)
  285.6  11.1%  edge     <-- edge_total, path_used_delta, ⋯, paths   (congruence, sup side)
  194.1   7.5%  edge     <-- eff_direct, in_proc, pub_edge_delta, root_map, root_map
  114.9   4.5%  points   <-- edge_delta, points_total
   99.5   3.9%  path_used <-- points_delta
   87.1   3.4%  points   <-- edge_delta
   78.5   3.0%  edge     <-- edge_delta, path_used, ⋯, paths         (congruence, delta)
   58.3   2.3%  edge     <-- edge_delta, path_used, ⋯, paths         (congruence, delta)
```

The four congruence variants together are 722ms — 28% of the SCC, down from
99.5%, and down from 455 *seconds* in absolute terms. Note what did not
change: the plan still says `edge_indices_none_total`, a full scan. Hypothesis
2 is still true and still unfixed; the bound made it affordable rather than
fatal. A real index on `(proc, base)` is worth roughly half a second here.

Relation sizes at the fixpoint:

```
points     1,061,910      <-- the new leader
pub_edge     624,929
edge         245,047      (was 9,747,467 and still climbing)
path_used     76,332
pub_points    41,587
root_map      22,325
paths            741      (the bound itself)
in_proc       29,166      (the input)
```

`edge` is now 8.4× the input rather than 334× — and `points`, the alias
relation congruence used to feed, is the largest thing in the run.

## Where the bytes go now

`examples/ctadl_memory.rs` is the same allocator accounting
`examples/memory.rs` does over the families, pointed at an import.

```
## whole program — 2375 procedures, 29166 statements
  |P| = 90092 EDB facts;  retained 1.7 GiB, peak 1.8 GiB, 4,620,886 allocations

  relation      tuples   Vec bytes   B/tuple
  points     1,061,910    288.0 MiB    284.4
  pub_edge     624,929    144.0 MiB    241.6
  edge         245,047     36.0 MiB    154.0
  path_used     76,332     16.0 MiB    219.8
  pub_points    41,587      9.0 MiB    226.9
  -- total   2,141,341    501.4 MiB    245.5

  where `retained` went
    tuple Vecs      501.4 MiB   29%
    Arc payloads      4.8 MiB    0%   suffixes and call strings the fixpoint built
    Ascent indices    1.2 GiB   71%   by subtraction
```

Two things worth keeping:

- **The suffixes cost nothing.** 4.8 MiB of `Arc` payload against 1.7 GiB
  retained. Bounding the vocabulary to 741 suffixes means every access path in
  the run shares one of 741 allocations, so the part of memory that used to
  grow with path depth has stopped registering at all.

- **71% of the memory is Ascent's indices**, not tuples. That is now the thing
  to attack if 1.7 GiB is too much: it is decided by which columns the rules
  join on, and `relation_sizes_summary()` cannot see any of it.

## How it grows

```
  procs                100         400        1000       whole
  |P|                45457       64867       77084       90092
  tuples            458795      951931     1258400     2141341
  retained       287.4 MiB   645.0 MiB   974.8 MiB     1.7 GiB
  peak           344.1 MiB   740.6 MiB     1.0 GiB     1.8 GiB
  B/tuple            656.8       710.5       812.3       846.0
```

Doubling `|P|` costs about 4.7× the tuples and 6× the bytes — `tuples ~
|P|^2.3`, `retained ~ |P|^2.6` over this range. That is the intraprocedural
alias closure being quadratic (`tests/scaling.rs`:
`points_is_quadratic_in_a_single_procedure`), which is expected and bounded,
not the runaway this document was written about. The 29% rise in bytes per
tuple across the sweep is the indices growing faster than the relations they
index, which is the same finding as the split above.

## What is left to try

The list at the top of this document, minus the item that was done. In the
order the numbers now argue for:

1. **Index the congruence join** — `edge_indices_none_total` is still a full
   scan, and it is now the second-largest line item (~600ms of 2.6s). Give
   `edge` its bases as real columns, or add a companion relation, so Ascent
   can plan `[SIMPLE JOIN]` on `(p, base)`.
2. **Shrink the index footprint** — 71% of 1.7 GiB. Fewer binding patterns
   over `points` and `pub_edge` is the lever.
3. **Sweep precision against the bound.** The vocabulary is syntactic, so it
   is not a *depth* knob; but `path_bound.rs` decides how far it follows local
   data flow, and the TaintBench queries are what should decide how far is far
   enough.
4. **Type-filtering congruence** is no longer urgent: 1.8% of paths repeat an
   accessor now, against 84.7% before, so the fiction it would remove is
   mostly gone already.
