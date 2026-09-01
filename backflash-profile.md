# backflash.apk under the access-path bound

> **Configuration.** Every current-state number below was re-measured after the
> CTADL front end started running `ctadl index`'s four IR passes by default
> (dead temps, coalescing, SSA, copy propagation — `ctadl-comparison.md`
> measures why). That change is worth 3.7× in time and 3.9× in memory at
> `k = 1` and moves almost every figure in this document, so nothing here is
> comparable to a run of an older commit. Where a *historical* before/after
> table records a change already made — "`pub_edge` is no longer a relation",
> "The congruence join is indexed" — both of its columns predate the new
> default and are labelled as such; they are lineage, not current state.
> `--no-preprocess` reproduces the old configuration on today's binary.

## Running it, in one command

The input is a *name* in CTADL's import store, not a path in this repo:
`read_import` resolves `backflash.apk` to
`$XDG_STATE_HOME/ctadl/imports/backflash.apk` (`~/.local/state/ctadl/...`),
which holds `ir-program.bitcode` and `ir-vmt.bitcode`. If that directory is
not there, make it from the TaintBench APK — `ctadl import backflash.apk`
names an import after the file by default — and then, from this directory:

```sh
cargo run --features ctadl,profile --release --example ctadl_profile -- \
    backflash.apk --k 1 --timeout 120
```

1.0s, and it prints everything this document is drawn from: the EDB shape,
whether the fixpoint converged, per-SCC and per-rule times, **the size of every
relation in the program — all 65 of them, EDB and IDB alike** — and the
access-path depth histogram. The sizes are their own section of the output:

```sh
cargo run --features ctadl,profile --release --example ctadl_profile -- \
    backflash.apk --k 1 --timeout 120 |
  awk '/=== relation sizes ===/{s=1;next} /^$/{s=0} s' | sort -k3 -nr
```

```
edge size: 138217             <-- the largest thing in the run
used_ext size: 75012
points size: 69881
in_proc size: 41143           <-- the input
mov size: 38018
root_map size: 22066
actual_arg size: 14858
pub_root size: 10217
...
cat size: 922                 <-- the bound, as a lookup
paths size: 736               <-- the bound itself
```

`edge` overtaking `points` as the largest relation is itself a consequence of
the new default: SSA splits a variable into versions, which multiplies the
*nodes* of the access-path graph while removing the merged values that used to
sit on each one. `points` fell 15× and `edge` 1.8×; the order swapped.

`--features ctadl` is what compiles the front end (`src/ctadl.rs`), and
`profile` is what compiles the instrumented copy of the rules; the example
target requires both. `--timeout` is a wall-clock stop checked *between*
iterations, so a single long iteration overruns it and it is not a ceiling: the
`k = 6` row below asked for 240s and took 762s. At `k = 1` the run converges
long before either number matters. The memory and `k`-sweep commands are at the
end.

`backflash.apk` is a TaintBench Android app, and it is the input that motivated
the `paths` relation of `src/ir.rs` — the syntactic bound on the access-path
vocabulary computed by `src/path_bound.rs` and tested against by every rule
that lengthens a path. Without such a bound the fixpoint does not exist on this
program: suffix congruence feeds itself through `used_ext`, cycles in `edge`
make the closure infinite, and the clock is the only thing that stops it.
`src/path_bound.rs` sets out the argument. This document measures what the
analysis does on the app now that the bound is in place.

Everything below comes from four binaries:

- `examples/ctadl_profile.rs` — the same rules as `HybridAnalysis`, from the
  same `hybrid_rules` source, under Ascent's `#![measure_rule_times]`. Rule
  times, relation sizes, and the shape of the access paths.
- `examples/ctadl_memory.rs` — the allocator accounting of `src/mem.rs`,
  pointed at an import. Bytes, per relation, with the indices split out.
- `examples/ctadl_parallel.rs` — the same rules under all three of Ascent's
  evaluators, on one import, with the relation sizes diffed between them.
  Wall time, and what it takes to beat the sequential one.
- `examples/index_cost.rs` — every index Ascent generates for these rules,
  priced from the generated storage rather than by subtracting from the
  allocator, plus what one shared store would cost instead.

The commands for all three are at the end; the short one is at the top.

## What the input looks like

Decoding the import and translating it takes 0.4s, and produces a small,
ordinary fact base:

```
3898 CIR functions  ->  2375 procedure   41143 in_proc    5526 virtual_call
                         754 entry        4330 lookup     2477 direct_call
```

`in_proc` is 41,143 rather than the 29,166 this document used to report because
the four IR passes run first: SSA adds 25,510 statements and the three
shrinking passes give back 13,533. The call structure is untouched —
`virtual_call`, `direct_call`, `actual_arg`, `bind_ret`, `formal` and `lookup`
are identical to the fact.

`virtual_call` is more than twice `direct_call`, and no CTADL front end
populates `load_index_var`/`store_index_var`. So on this input "critical
statement" means "unresolved dispatch", and there are a lot of them: 473
critical statements, in 966 pending instances at `k = 1`.

## The run

```
procs=2375 stmts=41143 virtual_call=5526 direct_call=2477 k=1
converged=true wall=0.55s
```

Peak physical footprint is 455 MiB, from `/usr/bin/time -l`, and both figures
are the median of three back-to-back runs (551ms, 550ms, 543ms) that agree to
0.8%. The lineage, each step measured on the configuration of its day: 3.11s
and 1.55 GiB before `pub_edge` was de-tabulated, 2.53s and 1.43 GiB after,
1.98s and 1.37 GiB once the congruence join was indexed, and 0.55s and 455 MiB
now that the front end runs CTADL's IR passes. On today's binary the last step
alone is 2.09s / 1.42 GiB with `--no-preprocess` against 0.55s / 455 MiB
without it — 3.8× the wall and 3.2× the peak, from a front-end flag.
Everything from here to "How it grows with k" is at `k = 1`.

## `pub_edge` is no longer a relation

*Historical: both columns of every table in this section were measured before
the front end started preprocessing, and are left as they were recorded.*

The first item of "What is left to try" as it then stood, and the change the
next section's `before` column is measured against. `pub_edge` — `points`
filtered by `pub_root` on both endpoints — is gone; its two consumers drive on
`points` directly, and neither had to re-state the filter, because at a static
callsite `root_map`'s second column already holds only symbolic roots of the
callee, and at a resolved critical statement `crit_subst` is already undefined
on a local. The set itself is recomputed once after convergence, by
`HybridAnalysis::pub_edges()`, for the reporting layer. `src/analysis.rs`
states the argument where the rule used to be.

Two binaries, the previous commit's and this one's, same machine, same import,
`/usr/bin/time -l`, back to back:

```
                            before          after
  whole program, k=1     3.11s  1.55 GiB    2.52s  1.48 GiB
  whole program, k=2    19.41s  6.68 GiB   15.20s  5.97 GiB
  80 procedures, k=8    85.41s 21.92 GiB   61.19s 17.95 GiB
```

It is *not* a trade: the run is smaller and faster at every size measured. Two
things worth knowing before repeating the move somewhere else:

- **The derivation is unchanged, and that was checked rather than assumed.**
  The pre-change binary was built from the previous commit and its relation
  sizes diffed against the new one on this app at `k = 1`, `k = 2` and (at 80
  procedures) `k = 8`. All 64 surviving relations agree exactly, tuple count
  for tuple count; the only difference in the diff is the missing `pub_edge`
  row.
- **Keeping the `pub_root` guards on the consumers is the version that loses.**
  The first attempt spelled the filter out in both inlining rules rather than
  letting `root_map` and `crit_subst` discharge it. That is 27% *slower* than
  the original at `k = 2` and 6× slower at 80 procedures and `k = 8`: a
  recursive guard atom gives semi-naive one delta variant per body atom, and
  four of the five then re-scan `points` in full on every iteration. A
  de-tabulation only pays when the filter is discharged by something the rule
  already joins against.

## The congruence join is indexed

*Historical: both columns here also predate the preprocessing default. The
change they record is real and still in the code — the criterion benches
re-measured it independently, see the note at the end of this section — but the
absolute numbers are those of the old front end.*

The third item of "What is left to try" is done, and this section is what it
cost and bought. Everything outside the two historical sections has since been
re-measured under the new default.

Suffix congruence used to be written the way the rule reads:

```rust
edge(p, sup2, sub.with_suffix(&ext)) <--
    edge(p, sup, sub),
    path_used(p, sup.base, sup2),
    if let Some(rest) = sup2.strip_prefix(sup), …
```

and the profile said `edge_indices_none_total`: a full scan of `edge`, every
iteration, in both of the variants where `path_used` is the delta. Two separate
things in Ascent's planner cause that, and the obvious fix addresses only one
of them.

- **The join key was a projection.** `sup.base` is not a column, so no index on
  `edge` can be derived from it. Ascent indexes `path_used` on `(proc, base)`
  perfectly well — it is the *other* side that has nothing to look up by, and
  atoms are compiled in source order, so `edge` stays the outer loop.
- **The `if let` sat between the two atoms.** Ascent will swap the first two
  body clauses (and pick the smaller as the driver) only for a `[SIMPLE JOIN]`:
  two adjacent clauses of plain variables, with no condition on the second that
  mentions a variable of the first. `strip_prefix(sup)` mentions one. Giving
  `edge` a `Base` column would have fixed the first problem and left this one,
  and would still have been keyed on a root.

So the split moved out of the rule and into a relation. `used_ext(p, ω, ρ, σ)`
records that `p` mentions a path whose suffix is `σ = suffix(ω)·ρ` — the prefix
decomposition done once per observed path instead of once per candidate pair —
and `cat(α, ρ, α·ρ)` is `paths` restated as concatenation (922 tuples now,
933 when this was written), so the
admissibility test becomes a lookup that returns the vocabulary's own `Arc`.
Congruence is then three atoms, no conditions, and the join key is a whole
path:

```rust
edge(p, sup.with_suffix(&whole), sub.with_suffix(&ext)) <--
    used_ext(p, sup, rest, whole),
    edge(p, sup, sub),
    let sub_suffix = sub.suffix(),
    cat(sub_suffix, rest, ext);
```

The plan the profile now prints, for all four variants:

```
edge <-- used_ext_indices_0_1_delta, edge_indices_0_1_total+delta, ⋯, cat_indices_0_1_total [SIMPLE JOIN]
edge <-- used_ext_indices_0_1_total, edge_indices_0_1_delta,       ⋯, cat_indices_0_1_total [SIMPLE JOIN]
edge <-- used_ext_indices_0_1_delta, edge_indices_0_2_total+delta, ⋯, cat_indices_0_1_total [SIMPLE JOIN]
edge <-- used_ext_indices_0_1_total, edge_indices_0_2_delta,       ⋯, cat_indices_0_1_total [SIMPLE JOIN]
```

Same three sizes as the `pub_edge` table, same machine, same import,
`/usr/bin/time -l`, three runs each at the first two sizes and two at the
third. Wall clock repeats to within 0.5%, so one figure is quoted; the peak
does not, so its *lowest* observation is quoted on both sides, which is the
reading least flattering to the change:

```
                            before          after
  whole program, k=1     2.53s  1.42 GiB    1.98s  1.37 GiB
  whole program, k=2    15.26s  5.41 GiB   11.04s  5.10 GiB
  80 procedures, k=8    61.06s 18.01 GiB   42.89s 16.72 GiB
```

`/usr/bin/time -l` also counts instructions: 28.2G before, 20.7G after, on the
`k = 1` run. A quarter of the work is simply gone.

Three things worth knowing before repeating the move somewhere else.

- **The derivation is unchanged, and that was checked rather than assumed.**
  Pre-change and post-change binaries, relation sizes diffed on this app at
  `k = 1`, `k = 2` and (at 80 procedures) `k = 8`: all 63 relations the two
  versions share agree exactly, tuple count for tuple count, with only
  `path_used` missing and `used_ext`/`cat` new. The 80-procedure `k` sweep says
  it at eight points rather than one — `points`, `edge`, `pub_points` and
  `pub_root` are identical at every `k` from 1 to 8. The access-path depth
  histogram is identical too.

- **The observed-path table did not get more expensive, but only after one
  allocation was removed.** `used_ext` is a *replacement* for `path_used`, not
  an addition — 57,192 tuples against 76,332, because it drops the depth-0
  paths that can extend nothing. The first version of it nonetheless cost 213ms
  against `path_used`'s 165ms, all of it in `Suffix::splits` allocating both
  halves of every split. 82% of the paths here have depth 1, whose only split
  is `(ε, whole)` — two halves that already exist. Handing back a shared `ε`
  and an `Arc::clone` of the path's own suffix put it back to 165ms.

- **The criterion benches corroborate both changes independently.** `cargo
  bench` runs on the synthetic families of `src/families.rs` and never touches
  the CTADL front end — `pub mod ctadl` is behind `#[cfg(feature = "ctadl")]`
  and `cargo bench` does not enable that feature, so this front end is not
  compiled into the bench binaries at all. Re-running all three targets against
  a baseline predating these two commits gives −13% to −37% wall and, on the
  deterministic `memory` target, −14% to −25% bytes. Those deltas are the two
  changes in this section and the one above it; they cannot be the
  preprocessing default, which those binaries cannot see.

- **Allocation count fell by more than anything else.** `cat` returns a
  suffix out of the vocabulary instead of building one, and `splits` hands back
  `Arc`s it already has, so the run makes **869,983 allocations against
  4,635,107** — 5.3× fewer — and the `Arc` payload the fixpoint builds falls
  from 4.9 MiB to 1.3 MiB. Accounted bytes barely move, since the tuple `Vec`s
  are the same size. The process footprint does move, and it stops varying
  between runs: at 80 procedures and `k = 8` the two `before` runs read 18.01
  and 19.30 GiB, the two `after` runs 16.72 and 16.75. Allocator churn is the
  obvious explanation and is consistent with every reading here, but it was not
  isolated — nothing below rests on it.

## The vocabulary, and what it does to the paths

`paths` holds 736 suffixes. That is the entire access-path alphabet the
program's syntax asks for, and no rule may leave it. What ends up in `edge`:

```
=== access-path depth in `edge` ===
  depth 0     100645   36.41%
  depth 1     145326   52.57%
  depth 2      29256   10.58%
  depth 3       1090    0.39%
  depth 4        117    0.04%
```

The distribution sits where the front end put it: the source IR writes at most
one accessor per statement, and 53% of the paths in the finished relation are
exactly that one accessor. (It was 82% before the front end preprocessed. SSA
does not lengthen paths — the maximum is still four accessors — but it adds a
great many depth-0 versions, which is the whole of the shift from depth 1 to
depth 0.) The deepest path is four accessors and is a real chain through real
fields:

```
par0@…LoaderManagerImpl$LoaderInfo;->callOnLoadFinished(…)
  .<LoaderInfo.this$0> .<LoaderManagerImpl.mActivity>
  .<FragmentActivity.mFragments> .<FragmentManagerImpl.mNoTransactionsBecause>
```

Only 4,533 of the 120,236 distinct paths (3.8%) repeat an accessor — the
signature of a type-impossible path like `x.wl.wl`, which is what congruence
invents when nothing stops it.

The cycles that would generate those are still there, but they are dramatically
smaller. The largest strongly-connected component in the path graph falls from
**205 paths to 9**:

```
  120236 distinct paths, 138217 edges
  paths on a cycle: 2886  (largest SCC: 9 paths)
```

That is the clearest single picture of what version-merging was doing. A cycle
in this graph is a path that reaches itself through congruence; a 205-path SCC
is one variable's merged versions tying 205 access paths into a mutual
dependency. Splitting the versions cuts the largest such knot to nine.

They simply no longer produce anything new. The bound does not remove the
cycles, it removes their range.

The congruence join's fan-out is correspondingly small. It is now measured
the way the indexed join actually works — one lookup per `used_ext` tuple,
retrieving the edges hanging off that exact path:

```
  edges per (proc, path) retrieved: n=150024 mean=1.4 p50=1 p99=7 max=234
  => congruence considers ~206089 (edge, extension) pairs per full pass,
     from 150024 indexed lookups; before the join was indexed it rescanned
     all 138217 edges every iteration instead
```

The median lookup returns one edge, and now so does the mean, near enough: 1.4
against 11.8, with p99 at 7 against 173. The fan-out that made the mean 11.8
was the merged roots carrying hundreds of values each, and it is gone — the
whole rule now considers 206K candidate pairs per pass against 1.35M.

## Where the time goes

One SCC dominates: stratum B, the big mutually-recursive block.

```
scc 46: iterations: 67, time: 424ms   (sum of rule times 311ms)
the other 9 SCCs: 94ms between them
```

More iterations than before (67 against 42) over a far smaller fixpoint. Inside
it there are the same 86 rules, of which ten are 83% of the time:

```
     ms      %  rule
   50.2  16.1%  edge      <-- used_ext_delta, edge_0_1, ⋯, cat  (congruence, sup side)
   42.5  13.7%  edge      <-- used_ext_delta, edge_0_2, ⋯, cat  (congruence, sub side)
   40.2  12.9%  points    <-- edge_0_2_total, points_0_1_delta          [SIMPLE JOIN]
   29.8   9.6%  edge      <-- eff_direct, in_proc, points_delta, root_map
   22.8   7.3%  used_ext  <-- edge_delta, for_
   20.9   6.7%  used_ext  <-- edge_delta, for_
   15.2   4.9%  pub_points<-- points_total, ⋯, pub_root_delta
   14.4   4.6%  points    <-- edge_0_2_delta, points_0_1_total          [SIMPLE JOIN]
   12.7   4.1%  points    <-- eff_direct, in_proc, pub_points_delta, root_map
    7.8   2.5%  points    <-- edge_delta, ⋯
```

By group, out of 311ms of rule time, against the same table before the front
end preprocessed (1.502s):

```
                                                   now          before
  suffix congruence (four variants)              101ms  32%   161ms  11%
  points, the alias closure                       63ms  20%   828ms  55%
  inlining at a static callsite (eight variants)  62ms  20%   242ms  16%
  used_ext, the observed-path table               49ms  16%   166ms  11%
  publication (pub_points)                        19ms   6%        —
  inlining at a resolved critical statement         2ms   1%    10ms   1%
```

**The conclusion this section used to draw is now inverted.** It read
"congruence is no longer where to look; `points` is now 55% of rule time on its
own". Under the new front end `points` is 20% and congruence is 32% — not
because congruence got slower (101ms against 161ms; it got faster) but because
`points` fell 13×, from 828ms to 63ms, while congruence fell only 1.6×.

That asymmetry is the whole story of the preprocessing change, stated in time
rather than in bytes. The alias closure is quadratic in the values that pile up
on one variable, so splitting a variable's versions attacks it directly.
Congruence is driven by the number of distinct *paths*, which SSA raises
(120,236 against 75,284) even as it lowers the values per path — so congruence
is the one group that partly pays for the change rather than being paid by it.
`points` is no longer the thing to attack; congruence is, again.

Relation sizes at the fixpoint:

```
edge         138,217      <-- the largest thing in the run (3.4x the input)
used_ext      75,012
points        69,881
root_map      22,066
pub_root      10,217
pub_points     4,350
cat              922      (the bound, as a lookup)
paths            736      (the bound itself)
in_proc       41,143      (the input)
```

## Where the bytes go

```
## whole program — 2375 procedures, 41143 statements
  |P| = 129668 EDB facts;  retained 366.8 MiB, peak 381.0 MiB, 801,836 allocations

  relation      tuples   Vec bytes   B/tuple
  edge         138,217     36.0 MiB    273.1
  points        69,881     18.0 MiB    270.1
  used_ext      75,012     14.0 MiB    195.7
  root_map      22,066      3.5 MiB    166.3
  pub_points     4,350      1.1 MiB    271.2
  pub_root      10,217      1.0 MiB    102.6
  carries       10,774    640.0 KiB     60.8
  cat              922     48.0 KiB     53.3
  -- total     378,560     76.5 MiB    212.0

  where `retained` went
    tuple Vecs       76.5 MiB   21%
    Arc payloads      2.7 MiB    1%   suffixes and call strings the fixpoint built
    Ascent indices  287.5 MiB   78%   by subtraction
```

3.9× less retained than the 1.4 GiB this table used to show, from 3.9× fewer
tuples; bytes per tuple are essentially unchanged (212 against 244), which is
the sign that the saving is in what gets derived and not in how it is stored.

Three things worth keeping:

- **The suffixes cost nothing.** 2.7 MiB of `Arc` payload against 366.8 MiB
  retained — it was 4.9 MiB before `cat` started handing extensions back out
  of the vocabulary instead of building them. A vocabulary of 736 suffixes
  means every access path in the run shares one of 736 allocations, so the
  part of memory that grows with path depth does not register at all.

- **78% of the memory is Ascent's indices**, not tuples, and the share went
  *up* as the run got smaller — 76% → 78% here, and 80–83% at the smaller
  sizes below. That is the thing to attack now that the tuples have gone: it is
  decided by which columns the rules join on, and `relation_sizes_summary()`
  cannot see any of it. `ctadl-comparison.md` prices the same problem against
  CTADL's BYODS store at 1.7–2.3×.

- **Dropping a relation moves less memory than dropping its tuples suggests.**
  `pub_edge` was 625K tuples and 144 MiB of `Vec` here, 29% of the tuple count;
  removing it took 500.3 → 356.3 MiB of `Vec` but only 1.7 → 1.5 GiB of
  retained, because its index set was smaller than average and the two
  consumers now need an index on `points` they did not need before. The share
  of retained that is indices went *up*, from 71% to 76%. At `k = 1` this is
  the whole story; at `k = 8` the tuples are numerous enough that the index
  arithmetic stops mattering, which is the next section.

### The indices, priced index by index

"78% by subtraction" was as far as `ctadl_memory` could see: Ascent's index
fields are private, so the allocator's retained total less the tuple `Vec`s and
the `Arc` payloads was the only handle on them. `examples/index_cost.rs`
computes the same quantity from the other end, by modelling what Ascent 0.8
generates:

- `ascent_hir.rs:249` gives **every** relation a full index,
  `RelFullIndexType<Tuple, ()> = HashMap<Tuple, ()>`, for insert-time dedup.
  Its key is the whole tuple, so it is a complete second copy of the relation.
- every binding pattern the rules join on gets a
  `ToRelIndexType<K, V> = HashMap<K, Vec<V>>` where `V` is the **non-key columns
  stored inline** (`IndexValType::Direct`, `ascent_hir.rs:191-198`). Key plus
  value is the whole tuple again, so each of those is another full copy, split
  in two.
- the `indices_none` pattern is that with an empty key: one `Vec` holding every
  tuple of the relation, verbatim.
- every per-key `Vec<V>` is born `Vec::with_capacity(4)`
  (`internal.rs`, `index_insert`), so a pattern whose keys are nearly unique
  pays four value slots to store one value.

That is 133 indices over 65 relations, and the binary checks its inventory
against `HybridAnalysis::summary()` — the generated plan — before pricing
anything, so a rule edit that adds a binding pattern cannot go unpriced. At
`k = 1`:

```sh
cargo run --features ctadl --release --example index_cost -- backflash.apk --k 1
```

```
  relation        tuples        Vec  indices now  copies       ids     ideal
  edge            138,217   36.0 MiB    140.0 MiB     3.9  31.1 MiB   6.1 MiB
  points           69,881   18.0 MiB     68.2 MiB     3.8   9.1 MiB   2.3 MiB
  used_ext         75,012   14.0 MiB     21.3 MiB     1.5   4.4 MiB   1.3 MiB
  in_proc          41,143    2.5 MiB     11.4 MiB     4.6   3.8 MiB   1.4 MiB
  root_map         22,066    3.5 MiB     10.4 MiB     3.0   3.3 MiB 662.2 KiB
  mov              38,018    3.0 MiB      6.9 MiB     2.3   1.9 MiB 884.5 KiB
  actual_arg       14,858  640.0 KiB      5.1 MiB     8.2   2.7 MiB 900.1 KiB
  -- total        523,540   85.4 MiB    287.5 MiB     3.4  64.1 MiB  16.6 MiB
```

**The model lands on 287.5 MiB of indices, which is the by-subtraction figure
to the decimal**, and the two accountings reconcile term by term rather than
merely landing near each other:

```
  model, whole store                                373.0 MiB
    less the EDB tuple Vecs (85.4 - 76.5)            -8.9      seeded before run()
    plus the Arc payloads the model does not price   +2.7      suffixes, call strings
  = mem::report retained                            366.8 MiB
```

`mem::report`'s own split of that 366.8 is 76.5 MiB of IDB `Vec`s, 2.7 MiB of
`Arc` payloads and 287.5 MiB of "indices, by subtraction". Neither number is
the other's ground truth — the model does not see the delta/new copies
semi-naive keeps, and the allocator cannot see inside a private field — so the
agreement is a result, not a definition. What follows can be read off the
model.

The individual indices say it more sharply than the totals:

```
  index         pattern   tuples      keys      bytes     ideal  values/key
  edge            0_1_2   138,217   138,217   36.2 MiB   1.2 MiB        1.0
  edge             none   138,217         1   36.0 MiB 540.0 KiB  138,217.0
  edge              0_2   138,217    88,690   35.8 MiB   2.2 MiB        1.6
  edge              0_1   138,217    72,422   32.0 MiB   2.2 MiB        1.9
  points            0_1    69,881    53,327   19.8 MiB   1.1 MiB        1.3
  points          0_1_2    69,881    69,881   18.1 MiB 640.0 KiB        1.0
  points           none    69,881         1   18.0 MiB 273.0 KiB   69,881.0
  used_ext      0_1_2_3    75,012    75,012   14.1 MiB 640.0 KiB        1.0
  points              0    69,881     2,375   12.2 MiB 325.0 KiB       29.4
```

`edge` is 36.0 MiB of tuples and 140.0 MiB of index — **the relation is stored
five times over**, once as itself and four times as a key/value split of
itself. `edge_indices_none` is the plainest case: a single-key map whose one
`Vec` holds all 138,217 tuples, an exact duplicate of `edge` itself, and it is
there because some rule scans `edge` with nothing bound.

Two structural readings, both of which generalise past this app:

- **A relation with nearly-unique keys pays the most.** `edge_indices_0_1_2`,
  `points_indices_0_1_2` and `used_ext_indices_0_1_2_3` are full indices with
  exactly one value per key, and they are the largest single item for their
  relation. `points_indices_0` has 29.4 values per key and costs 12.2 MiB for
  the same 69,881 tuples that `points_indices_0_1` spends 19.8 MiB on. Ascent's
  `with_capacity(4)` is why: at 1.3 values per key, three quarters of the value
  slots in `points_indices_0_1` are empty.
- **The multiplier is a property of the schema, not of the run.** It is 3.4× at
  `k = 1`, 3.7× at `k = 2` and `k = 3`, 3.6× at `k = 4` and 3.3× at `k = 5`.
  Nothing about raising `k` changes how many times a tuple is copied.

### If each rule stored one copy of the relation data

The counterfactual the table's last two columns price. `ids` is the realistic
one: an index stores a 4-byte **row id** into the relation's own `Vec` instead
of a copy of the non-key columns, and the full index becomes a table of row ids
hashed by the tuple they point at — the shape CTADL's `#[ds(locals_trie)]`
BYODS store has, and item 4 of `ctadl-comparison.md`. `ideal` is the lower
bound: one copy of the data and every index a pure row-id structure, keys
reached through the store rather than materialised in it.

```
  k = 1     now        373.0 MiB  =   85.4 MiB Vec + 287.5 MiB indices
            row ids    149.5 MiB  =   85.4 MiB Vec +  64.1 MiB indices   2.5x
            ideal      102.1 MiB  =   85.4 MiB Vec +  16.6 MiB indices   3.7x

  k = 5     now          3.0 GiB  =  717.3 MiB Vec +   2.3 GiB indices
            row ids    992.1 MiB  =  717.3 MiB Vec + 274.8 MiB indices   3.1x
            ideal      812.8 MiB  =  717.3 MiB Vec +  95.6 MiB indices   3.8x

  k = 6     now         11.1 GiB  =    2.7 GiB Vec +   8.5 GiB indices
            row ids      3.6 GiB  =    2.7 GiB Vec + 931.2 MiB indices   3.1x
            ideal        3.0 GiB  =    2.7 GiB Vec + 352.8 MiB indices   3.7x
```

At `k = 6` the same list is five separate 1.1 GiB items, four of them copies
of the same two relations:

```
  index         pattern     tuples       keys      bytes     ideal  values/key
  edge            0_1_2  5,439,654  5,439,654    1.1 GiB  40.0 MiB         1.0
  points          0_1_2  6,578,767  6,578,767    1.1 GiB  40.0 MiB         1.0
  edge             none  5,439,654          1    1.1 GiB  20.8 MiB   5,439,654
  points           none  6,578,767          1    1.1 GiB  25.1 MiB   6,578,767
  points              0  6,578,767      2,375    1.1 GiB  25.1 MiB     2,770.0
  points            0_1  6,578,767  1,303,770  757.8 MiB  51.1 MiB         5.0
  edge              0_1  5,439,654  1,185,611  696.6 MiB  46.8 MiB         4.6
  edge              0_2  5,439,654    371,025  551.4 MiB  27.3 MiB        14.7
```

`points` and `edge` between them are 7.6 GiB of the 11.1: 2.2 GiB of tuples and
5.4 GiB of copies of those tuples. `points_indices_0` is the extreme case —
2,375 keys, one per procedure, 2,770 values each, and 1.1 GiB spent on it
because the value stored is the other two columns of `points` rather than a
row number.

The `k = 6` row is the model's own out-of-sample check: 11.1 GiB modelled
against the sequential run's measured 10.38 GiB peak, on a run 31× larger than
the `k = 1` one the model was reconciled against. It is the row that matters
practically, too — **row-id indices would put the `k = 6` fixpoint in 3.6 GiB
instead of 10.4**, which is the difference between a run that needs a big
machine and one that does not.

**2.5× to 3.7×, at every `k` measured, and the ceiling is 4.4×** — that is what the tuple `Vec`s
alone would cost, so no amount of index sharing can do better than take the
run to 23% of what it is now. `ideal` gets to 27%, which means an index scheme
that stores nothing but row ids has essentially reached the floor and the
remaining question is the width of a tuple, not the number of copies of it.

Three things worth knowing before reaching for it:

- **`ids` is most of the win and is much the smaller change.** Keeping keys
  materialised in the tables costs 47.5 MiB of the 64.1 MiB that the `ids`
  column spends at `k = 1`, and buys back 2.5× of 3.7×. What it does *not*
  need is a new hash-lookup path: `HashMap<K, Vec<u32>>` is the same map with
  a narrower value.
- **It composes with interning rather than competing with it.** Item 1 of
  `ctadl-comparison.md` — `u32` symbol ids, a 144-byte `points`/`edge` tuple
  down to something like 40 — shrinks the `Vec` that `ideal` is a floor on.
  The two together would put this run on the order of 40 MiB against today's
  373; either alone is about 3×.
- **CTADL measured its own version of this at 1.7×, not 3.7×**
  (`assign_like store estimate: trie 13.9 MB … default equiv ~23.9 MB`). The
  difference is tuple width: at 24 bytes a copy is cheap and the key half of
  each index dominates; at 144 it is not. The lever is worth roughly twice as
  much here as it was there, for the same reason everything else in
  `ctadl-comparison.md` is worth more here.

## How it grows with the program

`--max-procs N` keeps the N procedures with the most statements:

```
  procs                100         400        1000       whole
  |P|                57008       89470      109226      129668
  tuples            212894      281050      330472      378560
  retained       172.3 MiB   252.6 MiB   289.9 MiB   366.8 MiB
  peak           186.3 MiB   277.9 MiB   308.8 MiB   381.0 MiB
  B/tuple            848.6       942.6       920.3      1015.9
  index share          80%         81%         83%         78%
```

**The quadratic is gone from this range.** `|P|` grows 2.27× across the sweep
and tuples grow 1.78× — `tuples ~ |P|^0.70`, `retained ~ |P|^0.92`, against
`|P|^2.1` and `|P|^2.5` before. That is not a claim that the intraprocedural
alias closure stopped being quadratic; `tests/scaling.rs` still pins it
(`points_is_quadratic_in_a_single_procedure`), and it is quadratic in the
values that accumulate *on one variable*. Splitting a variable into versions is
exactly the operation that empties that accumulator, so on this app the
quadratic term no longer dominates over this range. It will still be there at
some larger size; it is no longer where the bytes are at this one.

Bytes per tuple are flat-to-slightly-rising (849 → 1016) and the index share
sits at 78–83%, so the per-tuple index bill is now the whole scaling story
here.

## How it grows with k

Two questions live here, and they need two different experiments. *What happens
if I raise `k` on this app?* is asked of the whole program. *How does the
fixpoint grow with `k`?* can only be asked of runs that reach one.

Until the front end started preprocessing, those were two different
experiments, because nothing past `k = 2` converged at full size. They are now
nearly the same experiment: **`k = 1` through `k = 5` all converge on the whole
program inside a 240s budget**, where before the ceiling was `k = 2` — and
`k = 6` converges too, in 647s under `par+ir`, which is what the converged
sweep two subsections down is measured on.

### On the whole program, the ceiling moved from `k = 2` to `k = 6`

`--timeout 240` under a 64 GiB cap, peaks from `/usr/bin/time -l`:

```
  k                    1           2           3           4           5            6            7      8
  outcome      converged   converged   converged   converged   converged      timeout      timeout killed
  wall             0.56s       0.79s       1.53s       6.42s       96.8s         490s         322s     —
  peak GiB          0.45        0.51        0.75        1.21        3.34        10.36        44.29    >64
  iterations          67          67          82          82          82           18           17     —
  pending            966       2,040       4,680      12,576      41,605      155,128      703,304     —
  points          69,881     100,151     178,644     440,600   1,513,424    5,243,311   25,431,012     —
  edge           138,217     174,115     240,067     450,570   1,299,387    4,471,602   22,894,273     —
  pub_points       4,350      10,557      24,738      54,217     128,738      248,535    1,023,783     —
  max depth            4           4           4           4           4            4            4     —
```

Against the old table, at the two `k` that converged on both sides:

```
                   k = 1                      k = 2
              before      now            before      now
  wall          2.0s     0.56s            11.0s     0.79s     14x
  peak GiB      1.37      0.45             5.22      0.51     10x
  points   1,061,910    69,881        3,550,302   100,151     35x
```

`k = 4` converges in 6.4 seconds and 1.2 GiB where it used to exhaust a 240s
budget at 44 GiB. That is the largest single consequence of the preprocessing
default anywhere in this document.

**`pending` is the row that did not move.** 41,605 instances at `k = 5` against
the old run's 41,273 at the same `k`; 12,576 at `k = 4` against 14,042. The
instance space — the thing hybrid inlining actually mints, and the thing `k`
bounds — is within a few percent of what it always was. What collapsed is the
closure carried *per instance*. That is worth stating plainly because it is the
opposite of what the old table suggested: raising `k` was never mostly buying
instances, it was multiplying a merged points-to set by them.

The `k = 6` and `k = 7` columns remain snapshots at the cutoff and are **not
comparable to each other or to the converged columns** — `--timeout` is checked
between iterations, so `k = 6` overran its 240s budget to 490s inside a single
iteration and is a snapshot of a *longer* run than `k = 7`'s. Read them as
"where the budget got to". `k = 8` has no column at all: `memguard.sh` killed
it at the 64 GiB cap, and the kill takes the process before it prints.

`k = 6` has since been run to convergence, and "timeout" turns out to have
meant "needs 2553s, not 240" — see "`k = 6` converges; nobody had waited for
it" below, which also compares that snapshot against the fixpoint it was 19%
of the way to. The ceiling in this heading is a ceiling on *patience*, not on
the analysis. `k = 7` and `k = 8` are still open.

### The converged sweep, `k = 1` through `k = 6`

The table above is what `ctadl_profile` reaches inside a 240s budget. Run the
same `k` under `par+ir` with no budget and every one of them converges, which
is what the rest of this section is measured on — one run each, `--repeat 1`,
under a 100 GiB cap, peaks from `/usr/bin/time -l`:

```sh
for k in 1 2 3 4 5 6; do
    ./scripts/memguard.sh 100 /usr/bin/time -l \
        ./target/release/examples/ctadl_parallel backflash.apk \
        --k $k --repeat 1 --backend par+ir
done
```

```
  k                        1         2         3         4         5          6
  wall (par+ir)        0.91s     1.01s     1.50s     3.19s    29.34s     647.0s
  peak GiB              0.43      0.49      0.71      1.23      3.51      12.74
  instructions (G)        15        19        34       224     4,823    130,108
  tuples, all rels      524K      639K      875K     1.58M     4.25M     16.5M
  pending                966     2,040     4,680    12,576    41,605    164,693
  points              69,881   100,151   178,644   440,600 1,513,424  6,578,767
  edge               138,217   174,115   240,067   450,570 1,299,387  5,439,654
  used_ext            75,012   100,697   135,906   209,704   393,139  1,026,181
  resolve              1,527     3,914    11,262    40,126   169,339    777,279
  pub_root            10,217    13,318    20,770    42,439   121,167    455,695
  pub_points           4,350    10,557    24,738    54,217   128,738    371,848
  crit_operand         2,025     4,052     8,864    22,637    72,336    283,776
  top                    556     1,280     3,084     9,126    34,240    148,518
```

`k = 1..5` agree with the converged columns of the `ctadl_profile` table above
relation for relation, which is the check that changing the evaluator changed
nothing; `k = 6` is the run "`k = 6` converges" below reports, re-measured here
at 647.0s against that section's 647.6s.

**Everything grows, and everything grows at the rate of the instance space.**
Fitting `k = 3..6`:

```
  pending        k^5.07      settled     k^5.52      points     k^5.12
  top            k^5.53      blocked     k^5.33      edge       k^4.40
  stuck          k^5.24      resolve     k^6.05      used_ext   k^2.83
  crit_operand   k^4.93      pub_root    k^4.37      all tuples k^4.13
```

That is a completely different regime from the 80-procedure sweep below, where
tuples fit `k^0.65`. The two are consistent — `k` doubles call strings only
where there are call sites to double them, and 2,375 procedures have far more
of them than 80 do — but on the size that matters the growth in `k` is `k^4`,
not `k^0.65`, and the 80-procedure fit should not be read as this app's.

### What grows is `pending`; everything else is a constant times it

Divide each row by `pending` and the table stops moving:

```
  k                          1         2         3         4         5         6
  pending (instances)      966     2,040     4,680    12,576    41,605   164,693
  points   / pending      72.3      49.1      38.2      35.0      36.4      39.9
  edge     / pending     143.1      85.4      51.3      35.8      31.2      33.0
  pub_root / pending      10.6       6.5       4.4       3.4       2.9       2.8
  resolve  / pending      1.58      1.92      2.41      3.19      4.07      4.72
  top      / pending      0.58      0.63      0.66      0.73      0.82      0.90
  all tuples / pending   542.0     313.3     187.1     125.6     102.1      99.9
```

**From `k = 3` up, the closure carried per instance is flat.** `points` is 35–40
tuples per pending instance, `edge` 31–36, the whole fixpoint about 100–125.
The 31× growth in tuples from `k = 1` to `k = 6` is 170× more instances against
a per-instance cost that *fell* by 5.4×, and past `k = 3` the fall has stopped.
So the answer to "what grows so much" is not a relation. It is `pending`, and
`points`, `edge` and the rest are riding it at a fixed rate.

Two rows do climb per instance, and they are the two that say why the run gets
harder rather than just bigger: `resolve/pending` triples over the range and
`top/pending` rises 0.58 → 0.90. Deeper call strings mint instances that are
*less* decided — nine in ten instances at `k = 6` end ⊤-summarised, against
six in ten at `k = 1` — while each one dispatches to more callees. Raising `k`
past 3 on this app is buying instances that mostly fall back to the CHA answer.

### Bytes track tuples exactly; instructions do not

```
  k                       1         2         3         4         5         6
  B/tuple (peak)        879       829       874       838       887       831
  instructions/tuple    29K       29K       39K      142K    1,136K    7,906K
  µs/tuple (wall)       1.7       1.6       1.7       2.0       6.9      39.3
```

**Bytes per tuple is flat to within 7% across a 31× range in tuples and a 30×
range in peak.** Memory on this app is *pure relation growth*: nothing about
raising `k` makes a tuple more expensive to store, and the index multiplier
priced in "The indices, priced index by index" above is flat too (3.2–3.7×
at every `k` measured). If the memory footprint is the problem, the tuple count
is the whole of it.

**Instructions per derived tuple rise 268×** over the same range, and 7× in the
single step from `k = 5` to `k = 6`. That is not relation growth by any
reading: the run is doing vastly more work per tuple it keeps. Two candidates,
neither of them isolated yet, and this is the open question of the section:

- **Redundant derivation.** Semi-naive hands each of stratum B's 86 rules a
  delta every round, and a candidate tuple that already exists costs a full
  index probe before the full index rejects it. If the number of *derivations*
  grows faster than the number of distinct tuples — which is what a fan-out
  growing with `pending` would do — the ratio above is exactly what it looks
  like.
- **Probes that get more expensive with `k`.** A `CritId` is a `Stmt` plus an
  `Arc<[Stmt]>` call string of length up to `k`, every column is
  `#[derive(Hash)]` over `Arc<str>`, and there is no interner
  (`ctadl-comparison.md`, "the same story in time"). So an index probe on a
  `CritId`-keyed relation hashes the *contents* of up to `k + 1` dex statement
  labels. That is linear in `k`, though — a 6× factor over this range, not a
  268× one.

The first is much the larger candidate and it is measurable: build under
`--features profile`, take the per-rule times at `k = 5` and `k = 6`, and
compare a rule's time against the tuples it added. Nothing here does that yet.

### At 80 procedures, every `k` converges — and now barely grows

80 procedures is where the earlier sweep found the ceiling — the largest
`--max-procs` at which `k = 8` still reached a fixpoint, 100 blowing 20 GiB —
and the size is kept here so the tables can be read against each other:

```
  k                  1         2         3         4         5         6         7         8
  tuples          200K      208K      217K      227K      243K      271K      325K      437K
  retained     168 MiB   170 MiB   177 MiB   188 MiB   192 MiB   207 MiB   269 MiB   359 MiB
  peak         182 MiB   183 MiB   190 MiB   196 MiB   205 MiB   217 MiB   286 MiB   396 MiB
  index share      80%       80%       81%       79%       79%       77%       78%       77%
  Arc          1.4 MiB   1.4 MiB   1.5 MiB   1.6 MiB   1.9 MiB   2.6 MiB   4.5 MiB   7.5 MiB

  points        25,297    26,888    29,255    32,850    38,943    50,412    73,973   123,940
  edge          88,876    91,521    93,750    96,537   101,376   110,789   130,600   173,519
  pub_points       489       950     1,651     2,508     3,465     4,610     6,143     8,440
  used_ext      57,702    59,983    61,767    63,240    65,105    67,718    71,887    79,108
  pub_root         645       832     1,074     1,369     1,735     2,222     2,972     4,227
```

At `k = 8` that is **44× fewer tuples and 51× less retained** than the same
sweep before the front end preprocessed (437K against 19.2M, 359 MiB against
18.0 GiB). The whole `k = 1..8` sweep now fits in less memory than the old
`k = 1` column.

**The growth in `k` is close to flat.** Fitting `k = 3..8`, against the same
fit before:

```
                 now       before
  tuples      k^0.65      k^2.45
  retained    k^0.64      k^2.53
  points      k^1.38      k^2.36
  edge        k^0.56      k^2.66
  used_ext    k^0.23      k^0.97
  Arc         k^1.59      k^5.61
  pub_points  k^1.63      k^1.62   <-- unchanged
  pub_root    k^1.35      k^1.36   <-- unchanged
```

**The last two rows are the finding.** `pub_points` and `pub_root` grow with
exactly the exponent they always did, to two decimal places, while every other
exponent falls by a factor of three or more. Those two relations are the
publication surface — one row per published root per instance — and they track
the instance space, which the whole-program table above already showed is
unchanged. Everything that *did* fall is closure carried on top of it.

So the old fit's headline, "the growth is polynomial in `k`, not exponential",
survives and gets stronger: at *this size* the polynomial in `k` is now roughly
`k^0.65` in tuples. The exponent that hybrid inlining itself is responsible for
— `pub_root ~ k^1.35` — was never the one doing the damage.

**Do not read `k^0.65` as this app's exponent.** It is 80 procedures'. The
converged whole-program sweep two subsections up fits `k^4.13` in tuples and
`k^5.07` in `pending`, on the same rules and the same `k` range, because a
2,375-procedure call graph has call sites to double where an 80-procedure cut
has run out of them. Both fits are right about their own size; the whole
program is the one a run is going to be asked for.

The call-string space *is* exponential in `k` in principle — that is what
`tests/scaling.rs::call_strings_double_per_level_unless_k_caps_them` pins down —
but it doubles only where there are call sites to double it, and this app's call
graph runs out of them. What explodes on the whole program is `|P|` interacting
with `k`, not `k` alone.

Read `retained` in steps, not ratios: `Vec` byte counts are allocated capacity,
which doubles, so `edge` and `points` both report exactly 1.1 GiB at `k = 7`
and the k=6→7 byte ratio is 1.10 against a tuple ratio of 1.46. The tuple row
is the smooth signal; over the whole range tuples grow 58× and retained 70×, so
bytes do track tuples, at a roughly constant ~850–1000 B/tuple.

### The two relations are converging on being one relation

`points` and `edge` are 57% of all tuples at `k = 1` and 68% at `k = 8`, and
the ratio between them has turned over: `edge` is now the larger of the two at
every `k`, by 3.5× at `k = 1`.

```
  k                  1     2     3     4     5     6     7     8
  edge/points      3.51  3.40  3.20  2.94  2.60  2.20  1.77  1.40
  (points+edge)/all 0.57  0.57  0.57  0.57  0.58  0.59  0.63  0.68
```

The old table ran the other way — `edge/points` from .26 up to .91, with the
two relations converging on being one relation as `k` rose. They still
converge, from the other side: SSA hands the run many more paths carrying much
less each, so `edge` starts large and `points` catches up. The section title
is still right; the direction of travel is reversed.

The relation this table used to have a third row for was `pub_edge`, whose
ratio to `points` ran .51 → .96 over the same range. That row is what
de-tabulating it removed, and the reason it *could* be removed is still visible
in `pub_root` — but the arithmetic behind it has changed and is worth
restating. `pub_root` grows as `k^1.35` while `points` now grows as `k^1.38`,
so the two are growing *together* where they used to diverge (`k^1.36` against
`k^2.36`). **The publication filter no longer stops filtering**: 18% of
`points` survives publication at `k = 1` here, against the 96% at `k = 8` that
made storing a filtered copy equivalent to storing `points` twice. Item 4 below
was written against the diverging version of this and is correspondingly less
urgent.

`Arc` payloads no longer outpace the closure: `k^1.59` against `k^5.61`, and
7.5 MiB of 359 MiB at `k = 8`. The call strings are the same call strings — the
instance space did not change — so what fell is the number of distinct suffixes
they are attached to. Not worth watching either.

The access-path bound is untouched by any of this: `paths` stays 736 by
construction and the depth histogram tops out at 4 accessors at every `k`, on
both the whole program and the 80-procedure cut. Nothing about raising `k`
lengthens a path, and neither does SSA — it adds versions, not accessors.

## Running it in parallel

`src/analysis.rs` builds these rules three ways — one `hybrid_rules` source,
three Ascent macros, so nothing but the evaluator differs:

| backend | macro | axis |
|---|---|---|
| `HybridAnalysis` | `ascent!` | sequential |
| `parallel::ParallelHybridAnalysis` | `ascent_par!` | intra-rule: a parallel iterator over each rule's delta |
| `parallel::inter_rule::InterRuleHybridAnalysis` | `ascent_par!` + `#![inter_rule_parallelism]` | the above, plus independent rules within one SCC run concurrently |

`hi-complexity.md` measures all three on the synthetic families of
`src/families.rs` and finds parallelism losing by 6× to 1700× on everything at
the scale of the paper's examples, breaking even only at `wide(2048, 8)` and
winning only at `wide(8192, 8)` — thousands of independent procedures
advancing in the same round. It closes with a caveat: `wide` has no critical
statements in it at all, so whether the
*hybrid inlining* rules parallelize — the ones keyed on `CritId`, fed by a
serial chain of propagation steps — was untested, "and there is reason to
think they would do worse."

`backflash.apk` is that test. It has 473 critical statements, and between 966
pending instances at `k = 1` and 164,693 at `k = 6`. **They parallelize.**

```sh
cargo run --features ctadl --release --example ctadl_parallel -- \
    backflash.apk --k 4 --repeat 3
```

`examples/ctadl_parallel.rs` runs the backends over one import and diffs their
relation sizes against the sequential run's before it reports any speedup, the
way `benches/backends.rs` does for the families. **All 65 relations agree with
`seq` at every `k` below**; that is the first result here and the timings are
the second, because a backend that is fast because it derived less is a bug.

### The crossover is at `k = 3`

Whole program, 20 threads on a 20-core M1 Ultra, medians of three runs (two at
`k = 5`, one at `k = 6`), which repeat to within 2%:

```
  k                       1         2         3         4         5         6*
  tuples               523K      639K      875K     1.58M     4.25M     16.5M
  seq                0.644s    0.894s    1.693s    6.796s   101.58s    2552.9s
  par                1.247s    1.535s    2.222s    4.615s    32.64s         —
  par+ir             0.834s    0.964s    1.369s    3.168s    29.36s     647.6s
  par                 0.52x     0.58x     0.76x     1.47x     3.11x         —
  par+ir              0.77x     0.93x     1.24x     2.15x     3.46x     3.94x
```

\* One run each at `k = 6` rather than three — the sequential fixpoint there
takes 43 minutes, and `par` was not run at all — and its own subsection below,
because until now no run at `k = 6` had ever finished.

Wall clock here includes seeding the EDB into the Ascent program, which
`ctadl_profile` does *outside* its timer; that is the whole of the ~0.1s by
which this `seq` row sits above the `wall` row of the whole-program `k` table.
The convention is the same on all three backends, so the ratios are unaffected.

Two readings.

**The break-even is a size, and it is the size `hi-complexity.md` predicted.**
`par+ir` goes 0.77× → 0.93× → 1.24× across `k = 1, 2, 3`, crossing 1.0 at
roughly 700K tuples and one second of sequential work. The `wide` family
crossed at ~450K tuples on the same machine. Two completely different programs
— 8192 synthetic procedures with no dispatch, and one Android app whose
parallelism comes from context — break even within a factor of 1.5 of each
other, which says the threshold is a property of this rule set and Ascent's
parallel runtime rather than of either program.

**On this app the width comes from `k`, not from the procedure count.** The
program is fixed at 2375 procedures throughout that table; what grows is the
number of pending instances, from 966 to 41,605, and with it the number of
tuples a rule's delta carries in one round. That is a second way to get the
delta width `wide` gets from having 8192 procedures at once, and it is the
answer to the caveat: the `CritId`-keyed rules are not the ones that fail to
parallelize, they are the ones supplying the width.

### The tax is instructions, and it is paid in cycles that were idle anyway

`/usr/bin/time -l`, one backend per process (a peak footprint is per process,
so three fixpoints in one process report one peak):

```
                        seq        par     par+ir
  k = 1, wall         0.649s     1.273s     0.856s
         peak        442 MiB    437 MiB    439 MiB
         instr         5.89G     17.45G     13.41G
         cycles        2.42G     61.22G     40.11G

  k = 4, wall         6.787s     4.636s     3.189s
         peak       1.19 GiB   1.25 GiB   1.23 GiB
         instr        88.11G    230.21G    221.51G
         cycles       21.63G    231.95G    159.48G

  k = 5, wall        100.83s     32.98s     29.44s
         peak       3.30 GiB   3.62 GiB   3.54 GiB
         instr        1757G      4836G      4821G
         cycles      315.5G      1765G      1582G

  k = 6, wall        2552.9s          —     647.6s
         peak      10.38 GiB          —  12.73 GiB
         instr       47,537G          —   130,102G
         cycles       7,978G          —    35,594G
```

**Memory is a few percent, not a factor — but the few percent grows.**
`par+ir` peaks 1% *below* sequential at `k = 1`, 3–7% above at `k = 4` and
`k = 5`, and 20–23% above at `k = 6` (12.4 GiB and 12.7 GiB on two runs,
against 10.38 GiB). Ascent's parallel relations are `boxcar` vectors and
`DashMap` indices rather than `Vec` and `HashMap`, and that swap costs a
constant fraction of a growing thing; on the largest run here it is a fifth.
Nothing in "Where the bytes go" needs re-reading for the parallel backends,
but a run near a memory cap should not be moved onto them without headroom.

**Instructions are the price.** `par+ir` retires 2.3–2.7× the instructions the
sequential run does, at every `k`, on identical output. That ratio barely
moves with size, so it is the fixed cost of the concurrent data structures —
the sharded lookup, the atomics, the re-checks — and not something that
amortizes away.

Which leaves the question of what the speedup is made of, and the two counters
answer it between them. Apple's cycle counter is summed over threads, so
cycles ÷ wall in units of the sequential run's own rate is how many cores were
busy; instructions ÷ cycles is what each of them was doing:

```
                                     k = 1   k = 4   k = 5   k = 6
  cores' worth of cycles in flight    12.6    15.7    17.2    17.6   (par+ir, of 20)
  instructions per cycle, seq          2.43    4.07    5.57    5.96
  instructions per cycle, par+ir       0.33    1.39    3.05    3.66
  instruction tax                      2.28x   2.51x   2.74x   2.74x
```

Speedup is the product of the three rows: occupancy × IPC ratio ÷ tax. At
`k = 1` that is 12.6 × 0.14 ÷ 2.28 = 0.77×, and at `k = 6` 17.6 × 0.61 ÷ 2.74
= 3.95×, against the 0.77× and 3.94× measured. Occupancy hardly moves across
that range, and past `k = 5` neither does the tax. **The entire difference
between losing by a quarter and winning by 3.9× is the parallel IPC**, which
rises 11× while the sequential one rises 2.5×.

That is what makes `k = 1` legible. Twenty cores are already two-thirds busy
there and retiring a third of an instruction per cycle each: not work,
contention — twelve cores' worth of cycles spent spinning on deltas of a
handful of tuples, which is `hi-complexity.md`'s diagnosis on the small
families read directly off the counters. Parallelism does not start winning
here by finding more cores. It wins by giving the cores it already had
something to do.

### How many threads is a function of `k`

`RAYON_NUM_THREADS` swept, against the same sequential runs as above (6.796s
at `k = 4`, 101.58s at `k = 5`):

```
  threads                 1         2         4         8        20
  k = 4, par         7.506s    4.977s    3.650s    3.555s    4.699s
  k = 4, par+ir      7.554s    4.615s    2.988s    2.747s    3.218s
    vs seq            0.90x     1.47x     2.27x     2.47x     2.11x
  k = 5, par+ir     94.466s   64.022s   40.592s   31.552s   29.540s
    vs seq            1.08x     1.59x     2.50x     3.22x     3.44x
```

**The concurrent data structures are no longer a tax.** At one thread `par+ir`
is 7.554s against sequential's 6.796s at `k = 4` — 11% — and at `k = 5` it is
94.5s against 101.6s, which is 7% *faster* than sequential with no parallelism
at all. On the synthetic families that same one-thread overhead ran from 1.3×
to 32×, amortizing toward break-even only at the largest sizes. Here it has
amortized past break-even. `boxcar` and `DashMap` are not the reason anything
below `k = 3` loses.

**The useful thread count moves right with `k`, and 20 is not always it.** At
`k = 4` the curve peaks at eight threads and then *reverses* — 2.47× at eight
against 2.11× at twenty, a 17% loss for 12 more cores. At `k = 5` it does not
reverse: eight gives 3.22× and twenty gives 3.44×, still climbing. Under
`#![inter_rule_parallelism]` the pool has two things to spread — the rules of
one SCC, and each rule's delta — and stratum B has 86 rules of which ten are
83% of the time, so what decides the peak is whether those ten rules have
deltas big enough to keep 20 workers apart. At `k = 4` they do not. So:
`RAYON_NUM_THREADS=8` at `k = 4`, and the whole machine from `k = 5` up.

Scaling is poor in either case, and that is the honest summary of this
section: `k = 5` goes 94.5s → 29.5s from 1 thread to 20, which is 3.2× out of
20 cores. It is worth having and it is not close to linear.

**Inter-rule parallelism is again the better axis.** `par+ir` beats plain `par`
in every row of both tables — 1.1× to 1.6× — and the two are indistinguishable
at one thread (7.554s against 7.506s), which is what it should look like: with
one worker there is nothing to run concurrently and the difference is
scheduling overhead alone. Both parts of `hi-complexity.md`'s reading survive
contact with a real program.

### `k = 6` converges; nobody had waited for it

The whole-program `k` table stops calling runs converged at `k = 5` because
`k = 6` "timed out" — `--timeout 240` is checked between iterations, that run
overran to 490s and 18 iterations, and the column records where the budget got
to. It was never evidence that the fixpoint does not exist. It does, and both
backends reach it:

```
                              seq        par+ir     the old k = 6 column
                                                    (snapshot at 490s)
  outcome                converged     converged    timeout
  wall                     2552.9s        647.6s    490s
  peak                   10.38 GiB     12.73 GiB    10.36 GiB
  tuples, all relations  16,456,234    16,456,234   --
  pending                   164,693       164,693   155,128
  points                  6,578,767     6,578,767   5,243,311
  edge                    5,439,654     5,439,654   4,471,602
  pub_points                371,848       371,848   248,535
  pub_root                  455,695       455,695   --
```

The two backend columns are the same 65-line list, diffed — not two lists that
agree wherever someone happened to look.

Three things fall out of it.

**The old snapshot was much closer to done than "timeout" suggests.** At the
cutoff it had 94% of the final `pending`, 80% of `points`, 82% of `edge` — and
100% of the memory: 10.36 GiB against the completed run's 10.38. The footprint
is essentially final at 19% of the run time. Whatever the last four fifths of
a long fixpoint here are doing, they are not allocating; they are closing over
a structure that is already allocated. Read that back into the standing
warning that a truncated run's relation sizes are a function of the budget:
its *peak* may nonetheless be the real one.

**`pending` again did not move.** 164,693 against the snapshot's 155,128: the
instance space was 94% minted at 19% of the time. That is the same finding the
preprocessing change produced from the other direction — the instances are not
what the long tail of a run is spent on.

**`k = 6` is where parallelism is worth the most and costs the most.** 3.94× is
the best speedup measured here and 20-23% is the worst memory premium. 43
minutes down to 11 is the difference between a run you wait for and a run you
schedule; 10.4 GiB up to 12.7 GiB is nothing on a 128 GiB machine and would be
the whole story on a 16 GiB one.

`k = 7` is still open. Its column in the whole-program table is a 322s
snapshot at 44.29 GiB, and nothing here says whether it converges — only that
"timeout" was the wrong reading one column to its left. `par+ir` under
`memguard.sh` is how to find out, and 44 GiB of snapshot against a 64 GiB cap
says to expect the guard rather than an answer.

## What is left to try

In the order the numbers argue for:

0. ~~**Run CTADL's IR passes in the front end.**~~ Done, and it is now the
   default — dead temps, coalescing, SSA, copy propagation, the same four
   `ctadl index` runs. −73% wall and −68% peak at `k = 1`; the convergence
   ceiling on the whole program moved from `k = 2` to `k = 5`; the 80-procedure
   `k = 8` run went from 19.2M tuples and 18.0 GiB to 437K and 359 MiB. No
   dispatch edge was lost that was not spurious (`examples/dispatch_diff.rs`
   checks that directly; `ctadl-comparison.md` reports it). Everything above is
   measured after it.

1. ~~**De-tabulate `pub_edge`.**~~ Done — see "`pub_edge` is no longer a
   relation" above. −33% tuples, −20% retained and −28% wall at 80 procedures
   and `k = 8`, with the derivation unchanged. Everything below is measured
   after it.

2. **Shrink the index footprint** — now 77-83% of retained at every `k` and
   every program size, and it *rose* as item 0 removed tuples. This is a flat
   4-6× multiplier on everything above rather than something that gets worse,
   and with the tuple counts down by 40× it is now the largest thing left by a
   wide margin. It is the largest absolute lever left, and it is unrelated
   to `k`. *No longer a subtraction*: "The indices, priced index by index"
   above prices all 133 of them and lands on the by-subtraction number to the
   decimal, so the lever now has a size. **Row-id indices over one shared
   store are worth 2.5×, a pure row-id scheme 3.7×, and the floor — indices
   free — is 4.4×.** `edge` alone is stored five times over, once as itself and
   four times as a key/value split of itself, and `edge_indices_none` is a
   verbatim duplicate of the whole relation under a single key. Fewer binding
   patterns over `points` is still a lever and a cheaper one; note that item 1
   *raised* this share, because it removed tuples and their comparatively
   cheap index set while adding an index on `points` that the two inlining
   rules now need.

3. ~~**Index the congruence join.**~~ Done — see "The congruence join is
   indexed" above. Congruence went 664ms → 161ms at `k = 1` and the whole run
   −22% wall, −28% at `k = 2`, −30% at 80 procedures and `k = 8`, with the
   derivation unchanged at all three. Not by giving `edge` `Base` columns,
   which would have keyed on a root and left the `if let` in the way, but by
   splitting the observed path in a relation so the key is the whole path.
   Everything above is measured after it.

4. **Make the publication filter filter again.** *Largely overtaken by item 0.*
   `pub_root` grows as `k^1.35` against `points` at `k^1.38` — together, not
   diverging, where the pre-preprocessing fit had `k^1.36` against `k^2.36`. At
   `k = 1` on the whole program 18% of `points` survives publication, against
   the 96% at `k = 8` that motivated this item. That no longer
   costs a copy of `points` — item 1 took that away — but it still decides how
   much of a callee's closure every caller inlines, and so how fast `points`
   itself grows. A placeholder is published for every pending instance and
   never withdrawn (`src/analysis.rs` says so out loud where `pub_root` is
   defined). Withdrawing the ones that are settled, or publishing only bases
   some caller can actually reach, is the precision-side attack on the same
   growth.

5. **Bound the instance space.** *The item the converged `k = 1..6` sweep
   promotes to first place.* `k` is the only thing limiting it, and item 0 did
   not touch it: `pending` is within a few percent of what it always was at
   every `k`, and `pub_root` and `pub_points` grow with unchanged exponents.
   Everything else got 40× smaller around it. On the whole program `pending`
   fits `k^5.07` over `k = 3..6` — 966 instances to 164,693 — and **every other
   relation is a constant times it**: from `k = 3` up, `points` is 35–40 tuples
   per instance, `edge` 31–36 and the whole fixpoint 100–125, all flat. Bytes
   per tuple are flat too, so the memory footprint of a run at this size is
   `pending` times two constants and nothing else. (The `k^0.65` fit below is
   the 80-procedure cut, where the call graph runs out of sites to double; it
   is not the whole-program regime.) Worse, the instances bought at the top of
   the range are the least useful ones: `top/pending` climbs 0.58 → 0.90, so
   nine in ten instances at `k = 6` end ⊤-summarised — falling back to exactly
   the CHA answer — while `resolve/pending` triples. The whole program does
   reach a fixpoint out to `k = 6` (2553s sequentially, 647s under `par+ir`),
   `k = 7` has never been run to convergence, and `k = 8` is still killed at a
   64 GiB cap before it reports anything. If `k > 3` is wanted at full size the
   instances need a second bound: merging instances whose decisive slot has the
   same points-to set — which is what CTADL's lattice-valued `resolvent` column
   does, see `ctadl-comparison.md` — or a tighter `blocked`, since `blocked` is
   what decides whether an instance is copied into its callers at all.

6. **Sweep precision against the bound.** The vocabulary is syntactic, so there
   is no depth knob to turn; but `path_bound.rs` decides how far it follows
   local data flow, and the TaintBench queries are what should decide how far
   is far enough.

7. **Turn on `#![inter_rule_parallelism]` above `k = 2`.** Measured rather
   than speculated — "Running it in parallel" above. It is worth 2.5× at
   `k = 4`, 3.5× at `k = 5` and 3.9× at `k = 6`, for no change to the rules and
   no change to what is derived; and it *costs* 23% at `k = 1`. So it is a
   switch to throw on the expensive runs rather than a default —
   `RAYON_NUM_THREADS=8` at `k = 4`, the whole machine above it. Two things it
   is not: free of memory (3-7% at `k <= 5`, 20-23% at `k = 6`) and free of
   work (2.5-2.7× the instructions, so not the lever to reach for on a shared
   machine). And it buys throughput only — the instance space is untouched, so
   item 5 is unaffected by it.

8. **Find out where the instructions go above `k = 4`.** *The open question
   this document now has no answer to.* Bytes per tuple are flat across the
   whole converged sweep and the index multiplier is flat with them, so the
   memory story is entirely "how many tuples"; instructions per derived tuple
   rise 268× over the same range, and 7× in the step from `k = 5` to `k = 6`
   alone. Something is doing far more work per tuple it keeps, and nothing here
   separates redundant derivation (each of 86 rules probing an index for a
   tuple that already exists) from probes that get more expensive with `k` (a
   `CritId` hashes `k + 1` un-interned dex statement labels). The first is the
   larger candidate and the measurement is cheap: per-rule times under
   `--features profile` at `k = 5` and `k = 6`, against the tuples each rule
   added. See "Bytes track tuples exactly; instructions do not".

9. **Type-filtering congruence** — rejecting an extension whose accessor is not
   a field of the static type reached so far. 3.8% of paths repeat an accessor,
   against 1.8% before, so there is slightly more fiction to remove than there
   was; but congruence is now the largest group of rule time (32%, against
   `points`' 20% — the two have swapped places), so this is worth more than its
   old ranking suggests. It is a time argument now, not a space one.

## Measuring this, on macOS

Every memory figure above is a **physical footprint**, never RSS. `ps -o rss=`
counts only resident *uncompressed* pages, and macOS compresses cold ones, so
a run holding 20 GB can show 5 GB of RSS. Reading RSS is how a job that is
thrashing the machine gets called healthy. Activity Monitor's "Memory" column
is the footprint; so is `footprint -p <pid>` and `/usr/bin/time -l`'s
`peak memory footprint`.

Take the number two different ways, for two different jobs:

- **To report a finished run**, use `/usr/bin/time -l` and read
  `peak memory footprint`. It is a true high-water mark kept by the kernel, not
  a sample, so nothing can slip between polls. It has to wrap the binary
  *directly* — see trap 2.

- **To cap a run in flight**, poll `footprint`. `scripts/memguard.sh` does it:
  `scripts/memguard.sh <limit-GiB> <command> [args...]` runs the command, polls
  the whole process tree every 2s, kills the tree if the total passes the cap,
  and exits 137 if it did.

The two compose, in this order and not the other — the guard outside, `time -l`
inside, wrapping the binary:

```sh
./scripts/memguard.sh 64 /usr/bin/time -l \
    ./target/release/examples/ctadl_profile backflash.apk --k 16 --timeout 300
```

The polled peak is *not* a substitute for `time -l`'s: at a 2s interval the
`k = 1` run here gets two samples and reports 0.98 GiB against the 1.65 GiB
`time -l` sees, because the fixpoint is over in 3.1s. Poll to enforce a cap and
to watch the trajectory (climbing vs plateaued); quote `time -l` for a peak.

Three ways to get a guard that silently never fires, all of which have happened
here:

1. **Finding the PID with `pgrep -f`.** A pattern matching the binary also
   matches any shell whose command line mentions it — a `for k in ...; do
   ./target/release/examples/ctadl_profile ...` loop, for instance. The guard
   then polls a shell, reads a small, perfectly valid integer, and never fires,
   while the real process runs uncapped. This is what once let a `k = 16` run
   reach 144 GB on a 128 GB machine. Take the PID from `$!` of the command the
   guard itself launched, and from nowhere else.

2. **Measuring a wrapper instead of the work.** `phys_footprint` is per
   process and is *not* aggregated over children the way `maximum resident set
   size` is. Run `/usr/bin/time -l` on a shell script that runs the analysis
   and it reports `peak memory footprint: 2130304` — 2 MB, the shell's own —
   next to a `maximum resident set size` of 1.79 GB from the child. A poller
   aimed at the wrapper's PID is blind the same way, which is why
   `memguard.sh` sums the tree, walking it by parent (`pgrep -P`) and never by
   name. So: `time -l` goes *inside* the guard, wrapping the binary itself.

3. **Parsing the wrong field.** `footprint -p <pid> -f bytes` prints
   `phys_footprint: 1868136 B`; the trailing `B` is its own field, so
   `awk '{print $NF}'` yields `"B"` and every numeric comparison against it is
   false. Take `$2`. Without `-f bytes` the units switch with magnitude
   (`1856 KB`, then `19.50 GB`), so a parser that assumes KB reads 19.5 GB as
   19 KB. Always `-f bytes`, always `$2`.

A sanity check on the *shape* of the reading (is it a positive integer?) cannot
catch any of these on its own — a wrong process and a wrong scale both yield
plausible integers. Check the first sample against a number you already
believe: `/usr/bin/time -l` on a short run, or Activity Monitor.

## Reproducing

```sh
# rule times, relation sizes, access-path shape
cargo run --features ctadl,profile --release --example ctadl_profile -- \
    backflash.apk --k 1 --timeout 120

# the bytes, per relation, at four sizes
cargo run --features ctadl --release --example ctadl_memory -- \
    backflash.apk --k 1 --max-procs 100 --max-procs 400 --max-procs 1000

# whole-program k sweep, under a 64 GiB cap.  k=1..5 converge; k=6 and k=7 are
# snapshots at the cutoff and are not comparable across k; k=8 is killed by the
# guard before it prints at all.
cargo build --features ctadl,profile --release --example ctadl_profile
for k in 1 2 3 4 5 6 7 8; do
    ./scripts/memguard.sh 64 /usr/bin/time -l \
        ./target/release/examples/ctadl_profile backflash.apk --k $k --timeout 240
done

# sequential vs. the two parallel evaluators, with the relation sizes diffed
# between them first.  `--backend X` runs one alone, which is what to do under
# `/usr/bin/time -l`: a peak footprint is per process.  `--timeout SECS` caps
# each backend the way `ctadl_profile`'s does — between iterations, so it is
# not a ceiling — and defaults to none, because the comparison this program
# exists to make needs converged runs: a backend stopped at the budget has
# derived less than one that finished, so the tool withholds the speedup and
# labels the size diff rather than reporting a truncated run as a
# disagreement.
cargo run --features ctadl --release --example ctadl_parallel -- \
    backflash.apk --k 4 --repeat 3
for t in 1 2 4 8 20; do
    RAYON_NUM_THREADS=$t ./target/release/examples/ctadl_parallel \
        backflash.apk --k 4 --repeat 2 --backend par --backend par+ir
done

# k = 6 to convergence: 648s under par+ir, 2553s sequentially, and the same 65
# relation sizes from both.  This is the run the whole-program k table above
# only ever had a 490s snapshot of.
cargo build --features ctadl --release --example ctadl_parallel
for b in par+ir seq; do
    ./scripts/memguard.sh 64 /usr/bin/time -l \
        ./target/release/examples/ctadl_parallel backflash.apk --k 6 --repeat 1 --backend $b
done

# every index Ascent generates, priced, and the two counterfactuals.  The
# inventory is checked against the generated plan before anything is priced.
cargo run --features ctadl --release --example index_cost -- backflash.apk --k 1

# the converged whole-program sweep this document's k tables are drawn from.
# par+ir with no --timeout: every k from 1 to 6 reaches a fixpoint, k = 6 in
# 647s.  Sequentially k = 6 is 2553s and k = 7 has never been run at all.
cargo build --features ctadl --release --example ctadl_parallel
for k in 1 2 3 4 5 6; do
    ./scripts/memguard.sh 100 /usr/bin/time -l \
        ./target/release/examples/ctadl_parallel backflash.apk \
            --k $k --repeat 1 --backend par+ir
done

# the same run with the front end's IR passes off, which is the configuration
# every number in this document was taken under before them
./scripts/memguard.sh 64 /usr/bin/time -l \
    ./target/release/examples/ctadl_profile backflash.apk --k 1 --timeout 240 --no-preprocess

# the converged k sweep: 80 procedures, where every k reaches a fixpoint, so
# the sizes mean something.  `--no-whole` skips the whole-program pass that
# `ctadl_memory` otherwise always appends — at these k it would run to the cap.
cargo build --features ctadl --release --example ctadl_memory
for k in 1 2 3 4 5 6 7 8; do
    ./scripts/memguard.sh 56 ./target/release/examples/ctadl_memory \
        backflash.apk --k $k --max-procs 80 --no-whole
done
```

Raw logs for the converged `k = 1..6` sweep are in
`/Volumes/Shampoo/hi-parir-ksweep/` and for the index model in
`/Volumes/Shampoo/hi-index-cost/`.

`--max-procs N` keeps the N procedures with the most statements and the facts
that mention only those; type-level facts (`lookup`, `direct_subtype`,
`alloc_type`) are kept whole so that what counts as critical does not change.

Four things to know before re-running the sweeps. **Every number here depends
on whether the front end preprocesses**, and by up to 51× — a sweep taken with
`--no-preprocess` is measuring the old configuration and cannot be compared
with one taken without it. A guard kill yields **no data** — the process dies before it prints its relation sizes — so a `k` that
hits the cap is a wasted run, not a short one; if the sizes are what you want,
lower `--timeout` (or `--max-procs`) until the run survives to its own report.
A truncated run's relation sizes are a function of the budget, not of `k`:
comparing them across `k` is how you conclude that `points` shrinks between
`k = 4` and `k = 6`, which is false. Scaling claims need converged runs, which
is what the 80-procedure sweep is for. And `--timeout` cannot cut an iteration
short, only decline to start another, so a truncated run can take several times
the budget — `k = 6` above took 762s of an asked-for 240s.

Finally, if what you are measuring is a *rule* edit rather than the app, build
the binary *before* editing, keep it, and diff the two relation-size lists
before believing any timing. That is what established that removing `pub_edge`
left the other 64 relations tuple-for-tuple identical, and that indexing the
congruence join left the 63 it shares with its predecessor identical at `k = 1`,
`k = 2` and — relation by relation, at every `k` from 1 to 8 — on the
80-procedure cut. A sweep that only gets faster and smaller looks exactly the
same as one that quietly derives less.

Two practical notes on doing that. The comparison binary does not need a second
worktree: build it from the clean tree first and copy it aside
(`cp target/release/examples/ctadl_profile …/ctadl_profile_before`), which
avoids a second 30 GiB `target` on a machine that may not have room for one.
And read the diff by relation *name* as well as by size — a change that renames
or replaces a relation, as this one did, produces a list of a different length,
and a comparison that only checks shared rows will silently skip whatever went
missing.
