# backflash.apk under the access-path bound

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

2.5s, and it prints everything this document is drawn from: the EDB shape,
whether the fixpoint converged, per-SCC and per-rule times, **the size of every
relation in the program — all 65 of them, EDB and IDB alike** — and the
access-path depth histogram. The sizes are their own section of the output:

```sh
cargo run --features ctadl,profile --release --example ctadl_profile -- \
    backflash.apk --k 1 --timeout 120 |
  awk '/=== relation sizes ===/{s=1;next} /^$/{s=0} s' | sort -k3 -nr
```

```
points size: 1061910          <-- the largest thing in the run
edge size: 245047
used_ext size: 57192
pub_points size: 41587
in_proc size: 29166           <-- the input
root_map size: 22325
actual_arg size: 14858
pub_root size: 10476
...
cat size: 933                 <-- the bound, as a lookup
paths size: 741               <-- the bound itself
```

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
3898 CIR functions  ->  2375 procedure   29166 in_proc    5526 virtual_call
                         754 entry        4330 lookup     2477 direct_call
```

`virtual_call` is more than twice `direct_call`, and no CTADL front end
populates `load_index_var`/`store_index_var`. So on this input "critical
statement" means "unresolved dispatch", and there are a lot of them: 473
critical statements, in 1034 pending instances at `k = 1`.

## The run

```
procs=2375 stmts=29166 virtual_call=5526 direct_call=2477 k=1
converged=true wall=1.98s
```

Peak physical footprint is 1.37 GiB, from `/usr/bin/time -l`, and both figures
are the median of three back-to-back runs that agree to 0.5%. The lineage: 3.11s
and 1.55 GiB before `pub_edge` was de-tabulated, 2.53s and 1.43 GiB after, 1.98s
and 1.37 GiB now that the congruence join is indexed.
Everything from here to "How it grows with k" is at `k = 1`.

## `pub_edge` is no longer a relation

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

The third item of "What is left to try" is done, and this section is what it
cost and bought. Everything above and below was re-measured after it.

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
and `cat(α, ρ, α·ρ)` is `paths` restated as concatenation, 933 tuples, so the
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

`paths` holds 741 suffixes. That is the entire access-path alphabet the
program's syntax asks for, and no rule may leave it. What ends up in `edge`:

```
=== access-path depth in `edge` ===
  depth 0      67442   13.76%
  depth 1     400865   81.79%
  depth 2      21557    4.40%
  depth 3        213    0.04%
  depth 4         17    0.00%
```

The distribution sits where the front end put it: the source IR writes at most
one accessor per statement, and 82% of the paths in the finished relation are
exactly that one accessor. The deepest path is four accessors and is a real
chain through real fields:

```
par0@…LoaderManagerImpl$LoaderInfo;->callOnLoadFinished(…)
  .<LoaderInfo.this$0> .<LoaderManagerImpl.mActivity>
  .<FragmentActivity.mFragments> .<FragmentManagerImpl.mNoTransactionsBecause>
```

Only 1,324 of the 75,284 distinct paths (1.8%) repeat an accessor — the
signature of a type-impossible path like `x.wl.wl`, which is what congruence
invents when nothing stops it.

The cycles that would generate those are still there:

```
  75284 distinct paths, 245047 edges
  paths on a cycle: 3846  (largest SCC: 205 paths)
```

They simply no longer produce anything new. The bound does not remove the
cycles, it removes their range.

The congruence join's fan-out is correspondingly small. It is now measured
the way the indexed join actually works — one lookup per `used_ext` tuple,
retrieving the edges hanging off that exact path:

```
  edges per (proc, path) retrieved: n=114384 mean=11.8 p50=1 p99=173 max=231
  => congruence considers ~1347479 (edge, extension) pairs per full pass,
     from 114384 indexed lookups; before the join was indexed it rescanned
     all 245047 edges every iteration instead
```

The median lookup returns one edge. The mean is 11.8 because a few symbolic
roots carry hundreds — but those are retrievals of tuples the rule will use,
not candidates it will reject, which is the difference the key made.

## Where the time goes

One SCC dominates: stratum B, the big mutually-recursive block.

```
scc 46: iterations: 42, time: 1.921s   (sum of rule times 1.502s)
the other 50 SCCs: 47ms between them
```

Inside it there are 86 rules, of which ten are 90% of the time:

```
     ms      %  rule
  641.8  42.7%  points    <-- edge_0_2_total, points_0_1_delta          [SIMPLE JOIN]
  192.6  12.8%  edge      <-- eff_direct, in_proc, points_delta, root_map, root_map
  106.4   7.1%  points    <-- edge_0_2_delta, points_0_1_total          [SIMPLE JOIN]
   97.9   6.5%  used_ext  <-- points_delta, for_
   79.7   5.3%  points    <-- edge_delta
   77.2   5.1%  edge      <-- used_ext_delta, edge_0_2, ⋯, cat  (congruence, sub side)
   68.4   4.6%  edge      <-- used_ext_delta, edge_0_1, ⋯, cat  (congruence, sup side)
   37.5   2.5%  used_ext  <-- edge_delta, for_
   31.0   2.1%  used_ext  <-- edge_delta, for_
   26.6   1.8%  points    <-- eff_direct, in_proc, pub_points_delta, root_map
```

By group, out of 1.502s of rule time:

```
  points, the alias closure                        828ms   55%
  inlining at a static callsite (three variants)   242ms   16%
  used_ext, the observed-path table                166ms   11%
  suffix congruence (four variants)                161ms   11%
  inlining at a resolved critical statement         10ms    1%
  cat, built once from `paths`                     0.3ms    0%
```

Against the same table before the join was indexed — `points` 816ms/41%,
congruence **664ms/33%**, callsite 250ms/13%, `path_used` 165ms/8%. Congruence
fell 4.1×, from the second-largest group to the fourth, and nothing else moved:
`points`, the callsite rules and the observed-path table are all within 2% of
what they cost before, so the 497ms the run lost is the scan and nothing else.

Two rules are missing from the table that earlier versions of this document
had near the top: the publication rule, at 350ms, which went with `pub_edge`,
and the callsite rule that consumed it, which now drives on `points` for
242ms.

Congruence is no longer where to look. `points` is now 55% of rule time on its
own, and its two big variants are already `[SIMPLE JOIN]`s on whole columns —
there is no plan left to fix there, only the quadratic itself.

Relation sizes at the fixpoint:

```
points     1,061,910      <-- the largest thing in the run
edge         245,047      (8.4x the input)
used_ext      57,192
pub_points    41,587
root_map      22,325
pub_root      10,476
cat              933      (the bound, as a lookup)
paths            741      (the bound itself)
in_proc       29,166      (the input)
```

## Where the bytes go

```
## whole program — 2375 procedures, 29166 statements
  |P| = 90092 EDB facts;  retained 1.4 GiB, peak 1.5 GiB, 869,983 allocations

  relation      tuples   Vec bytes   B/tuple
  points     1,061,910    288.0 MiB    284.4
  edge         245,047     36.0 MiB    154.0
  pub_points    41,587      9.0 MiB    226.9
  used_ext      57,192      7.0 MiB    128.3
  root_map      22,325      3.5 MiB    164.4
  pub_root      10,476      1.0 MiB    100.1
  cat              933     48.0 KiB     52.7
  -- total   1,493,644    347.3 MiB    243.8

  where `retained` went
    tuple Vecs      347.3 MiB   24%
    Arc payloads      1.3 MiB    0%   suffixes and call strings the fixpoint built
    Ascent indices    1.1 GiB   76%   by subtraction
```

Three things worth keeping:

- **The suffixes cost nothing.** 1.3 MiB of `Arc` payload against 1.4 GiB
  retained — it was 4.9 MiB before `cat` started handing extensions back out
  of the vocabulary instead of building them. A vocabulary of 741 suffixes
  means every access path in the run shares one of 741 allocations, so the
  part of memory that grows with path depth does not register at all.

- **76% of the memory is Ascent's indices**, not tuples. That is the thing to
  attack if 1.5 GiB is too much: it is decided by which columns the rules join
  on, and `relation_sizes_summary()` cannot see any of it.

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
  |P|                45457       64867       77084       90092
  tuples            344610      695631      896040     1493644
  retained       264.5 MiB   562.6 MiB   838.7 MiB     1.4 GiB
  peak           302.0 MiB   615.6 MiB   901.5 MiB     1.5 GiB
  B/tuple            804.9       848.1       981.5      1028.3
```

Doubling `|P|` costs about 4.3× the tuples and 5.6× the bytes — `tuples ~
|P|^2.1`, `retained ~ |P|^2.5` over this range. That is the intraprocedural
alias closure being quadratic, which `tests/scaling.rs` already pins down
(`points_is_quadratic_in_a_single_procedure`): expected, and bounded. Bytes per
tuple are 27% higher than they were with `pub_edge` in the table and still rise
27% across the sweep: the same tuples now carry the whole index bill between
fewer of them, and the indices still grow faster than the relations they
index.

## How it grows with k

Two questions live here, and they need two different experiments. *What happens
if I raise `k` on this app?* is asked of the whole program, and the answer is
that past `k = 2` nothing converges — so those runs measure the budget, not the
fixpoint. *How does the fixpoint grow with `k`?* can only be asked of runs that
reach one, which means shrinking the program until they exist.

### On the whole program, `k > 2` does not converge

`--timeout 240` under a 64 GiB cap, peaks from `/usr/bin/time -l`. `k = 1` and
`k = 2` converge in seconds, so their budget is immaterial:

```
  k                    1           2            4            5            6            7      8
  outcome      converged   converged      timeout      timeout      timeout      timeout killed
  wall              2.0s       11.0s         246s         259s         762s         391s     —
  peak GiB          1.37        5.22        43.97        40.37        42.73        59.39    >64
  iterations          42          42           50           19           17           15     —
  pending          1,034       2,183       14,042       41,273      159,491      710,364     —
  points       1,061,910   3,550,302   32,021,999   26,381,136   21,652,385   43,490,363     —
  edge           245,047   1,817,143   20,009,328   21,927,124   25,123,527   37,833,805     —
  pub_points      41,587     187,658    1,615,912    1,334,542      963,666    1,685,023     —
  max depth            4           4            4            4            4            4     —
```

The `k >= 4` columns are snapshots at the cutoff, and — this is the trap — they
are **not comparable to each other**. `points` *falls* from 32.0M at k=4 to
21.7M at k=6 and then rises to 43.5M at k=7, not because the fixpoint moves
that way but because the higher-k runs spend more of their budget minting
instances (`pending` 14K → 710K) and get a different distance into the closure:
the k=4 run managed 50 iterations of the big SCC, the k=7 run 15. The `wall`
row makes the same point from the other side — `--timeout` is checked between
iterations, so k=6 overran 240s by a factor of three inside a single iteration
and its column is a snapshot of a *longer* run than its neighbours. Read each
column as "where the budget got to" and nothing more. `k = 8` has no column at
all: `memguard.sh` killed it at 64.4 GiB, and the kill takes the process before
it prints, so a capped run yields no relation sizes.

Only the `k = 1` and `k = 2` columns are current. Their sizes are unchanged by
the congruence index — that was checked — and their `wall` and `peak` rows are
re-measured. The `k >= 4` columns predate it and were not re-run: they measure
where a 240s budget got to, so re-running them would produce different numbers
whether or not anything had changed, which is the whole point of the paragraph
above.

### At 80 procedures, every `k` converges

80 procedures is where the earlier sweep found the ceiling — the largest
`--max-procs` at which `k = 8` still reached a fixpoint, 100 blowing 20 GiB —
and the size is kept here so the two tables can be read against each other.
Removing `pub_edge` has moved that ceiling up; where to has not been measured.
At 80 procedures all of `k = 1..8` converge — 61s at `k = 8` for
`ctadl_profile`, wall clock for the whole binary, import included, against 85s
before — and the numbers are comparable:

```
  k                  1         2         3         4         5         6         7         8
  tuples          333K      774K     1.76M     3.49M     6.09M     9.55M     13.9M     19.2M
  retained     262 MiB   644 MiB   1.4 GiB   2.8 GiB   4.8 GiB   9.0 GiB   9.9 GiB  18.0 GiB
  peak         296 MiB   788 MiB   1.8 GiB   3.5 GiB   5.5 GiB  10.1 GiB  11.2 GiB  19.3 GiB
  index share      79%       82%       79%       79%       75%       74%       76%       74%
  Arc          0.4 MiB   0.4 MiB   0.8 MiB   2.8 MiB  16.2 MiB  43.2 MiB  90.6 MiB 156.3 MiB

  points       218,292   460,702   974,566 1,863,132 3,190,922 4,942,324 7,151,120 9,804,384
  edge          57,499   231,299   660,520 1,450,878 2,670,490 4,316,730 6,414,674 8,957,736
  pub_points     8,986    26,465    57,444    99,313   145,050   190,839   236,858   283,031
  used_ext      20,615    26,711    34,366    43,143    52,492    62,557    74,594    90,035
  pub_root         635       812     1,050     1,341     1,703     2,186     2,932     4,183
```

`points`, `edge`, `pub_points` and `pub_root` are identical column for column
at every `k`, both to the pre-de-tabulation sweep and to the pre-index one —
that is the check that neither change altered the derivation, run at the size
where the alternatives differ most. `pub_edge` took `tuples` down 33% when it
went; indexing the congruence join left `tuples` and `retained` essentially
untouched, which is the honest summary of it: **it is a time change, not a
space one.** `Arc` payloads are the exception, down 4-8× at every `k` because
`cat` returns interned suffixes; and the *process* footprint at `k = 8` is
16.7 GiB against 18.0-19.3 GiB, which this accounting cannot see and which the
5× drop in allocation count is the likely but unisolated cause of.

**The growth is polynomial in `k`, not exponential.** Fitting `k = 3..8`:

```
  tuples ~ k^2.45    points ~ k^2.36    edge ~ k^2.66    pub_points ~ k^1.62
  retained ~ k^2.53  pub_root ~ k^1.36  used_ext ~ k^0.97  Arc ~ k^5.61
```

Every exponent but `Arc`'s is what it was before the congruence index, which
follows from the relations being identical. `Arc`'s got steeper only because
its base got smaller: 0.8 MiB at `k = 3` instead of 3.3, against 156 MiB at
`k = 8` instead of 163.

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

`points` and `edge` are 83% of all tuples at `k = 1` and **97.8% at `k = 8`**.
Everything else — `root_map` flat at ~11K, `eff_direct`, `mono_target`,
`sig_target` exactly constant — is noise beside them:

```
  k                  1     2     3     4     5     6     7     8
  edge/points      .26   .50   .68   .78   .84   .87   .90   .91
  (points+edge)/all .83  .89   .93   .95   .96   .97   .97   .98
```

The relation this table used to have a third row for was `pub_edge`, whose
ratio to `points` ran .51 → .96 over the same range. That row is what
de-tabulating it removed, and the reason it *could* be removed is still
visible in `pub_root`: it grows as `k^1.36` while `points` grows as `k^2.36`,
so **the publication filter stops filtering** — 96% of `points` was publishable
at `k = 8`. Storing the filtered copy was therefore storing `points` twice. It
still means that raising `k` makes every published summary bigger, in the
caller as much as the callee; it just no longer costs a second table to find
that out.

`Arc` payloads are the one component outpacing the closure (`k^5.61` — the call
strings themselves getting longer and more numerous; the suffixes are interned
and contribute nothing), but at 156 MiB of 18.0 GiB they are still 0.8% of the
bill. Worth watching, not worth fixing.

The access-path bound is untouched by any of this: `paths` stays 741 by
construction and the depth histogram tops out at 4 accessors at every `k`, on
both the whole program and the 80-procedure cut. Nothing about raising `k`
lengthens a path.

## What is left to try

In the order the numbers argue for:

1. ~~**De-tabulate `pub_edge`.**~~ Done — see "`pub_edge` is no longer a
   relation" above. −33% tuples, −20% retained and −28% wall at 80 procedures
   and `k = 8`, with the derivation unchanged. Everything below is measured
   after it.

2. **Shrink the index footprint** — still 74-82% of retained at *every* `k`, so
   this is a flat 4-5× multiplier on everything above rather than something
   that gets worse. It is the largest absolute lever left, and it is unrelated
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

4. **Make the publication filter filter again.** `pub_root` is what decides how
   much of `points` becomes summary, and it grows as `k^1.36` against `points`
   at `k^2.36`, so by `k = 8` almost nothing is filtered out. That no longer
   costs a copy of `points` — item 1 took that away — but it still decides how
   much of a callee's closure every caller inlines, and so how fast `points`
   itself grows. A placeholder is published for every pending instance and
   never withdrawn (`src/analysis.rs` says so out loud where `pub_root` is
   defined). Withdrawing the ones that are settled, or publishing only bases
   some caller can actually reach, is the precision-side attack on the same
   growth.

5. **Bound the instance space.** `k` is the only thing limiting it. On a
   program that converges it limits it *polynomially* — `k^2.5`, not the
   doubling the synthetic test shows — but on the whole app `k >= 4` still
   never reaches a fixpoint, and `k = 8` is still killed at a 64 GiB cap before
   it reports anything. If `k > 2` is wanted at full size, the instances need a
   second bound: merging instances whose decisive slot has the same points-to
   set, or a tighter `blocked`, since `blocked` is what decides whether an
   instance is copied into its callers at all.

6. **Sweep precision against the bound.** The vocabulary is syntactic, so there
   is no depth knob to turn; but `path_bound.rs` decides how far it follows
   local data flow, and the TaintBench queries are what should decide how far
   is far enough.

7. **Type-filtering congruence** — rejecting an extension whose accessor is not
   a field of the static type reached so far — is no longer urgent: 1.8% of the
   paths repeat an accessor, so there is little fiction left for it to remove.

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

# whole-program k sweep, under a 64 GiB cap.  Nothing past k=2 converges, so
# these are snapshots at the cutoff and are not comparable across k; k=8 is
# killed by the guard before it prints at all.
cargo build --features ctadl,profile --release --example ctadl_profile
for k in 1 2 4 5 6 7 8; do
    ./scripts/memguard.sh 64 /usr/bin/time -l \
        ./target/release/examples/ctadl_profile backflash.apk --k $k --timeout 240
done

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

Three things to know before re-running the sweeps. A guard kill yields **no
data** — the process dies before it prints its relation sizes — so a `k` that
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
