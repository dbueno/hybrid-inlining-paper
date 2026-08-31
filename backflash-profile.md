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

Everything below comes from two binaries:

- `examples/ctadl_profile.rs` — the same rules as `HybridAnalysis`, from the
  same `hybrid_rules` source, under Ascent's `#![measure_rule_times]`. Rule
  times, relation sizes, and the shape of the access paths.
- `examples/ctadl_memory.rs` — the allocator accounting of `src/mem.rs`,
  pointed at an import. Bytes, per relation, with the indices split out.

The commands for both are at the end; the short one is at the top.

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
program**, where before the ceiling was `k = 2`.

### On the whole program, the ceiling moved from `k = 2` to `k = 5`

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
survives and gets stronger: on this app the polynomial in `k` is now roughly
`k^0.65` in tuples. The exponent that hybrid inlining itself is responsible for
— `pub_root ~ k^1.35` — was never the one doing the damage.

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
   to `k`. Fewer binding patterns over `points` is the lever; note that item 1
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

5. **Bound the instance space.** *Now the most interesting item on the list.*
   `k` is the only thing limiting it, and item 0 did not touch it: `pending` is
   within a few percent of what it always was at every `k`, and `pub_root` and
   `pub_points` grow with unchanged exponents. Everything else got 40× smaller
   around it. On a program that converges `k` limits the fixpoint
   *polynomially* — now `k^0.65` in tuples, not the `k^2.5` measured before —
   and the whole program reaches a fixpoint out to `k = 5`. But `k >= 6` still
   never converges, and `k = 8` is still killed at a 64 GiB cap before
   it reports anything. If `k > 2` is wanted at full size, the instances need a
   second bound: merging instances whose decisive slot has the same points-to
   set, or a tighter `blocked`, since `blocked` is what decides whether an
   instance is copied into its callers at all.

6. **Sweep precision against the bound.** The vocabulary is syntactic, so there
   is no depth knob to turn; but `path_bound.rs` decides how far it follows
   local data flow, and the TaintBench queries are what should decide how far
   is far enough.

7. **Type-filtering congruence** — rejecting an extension whose accessor is not
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
