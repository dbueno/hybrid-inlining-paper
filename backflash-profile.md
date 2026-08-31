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

3.1s, and it prints everything this document is drawn from: the EDB shape,
whether the fixpoint converged, per-SCC and per-rule times, **the size of every
relation in the program — all 66 of them, EDB and IDB alike** — and the
access-path depth histogram. The sizes are their own section of the output:

```sh
cargo run --features ctadl,profile --release --example ctadl_profile -- \
    backflash.apk --k 1 --timeout 120 |
  awk '/=== relation sizes ===/{s=1;next} /^$/{s=0} s' | sort -k3 -nr
```

```
points size: 1061910          <-- the largest thing in the run
pub_edge size: 624929
edge size: 245047
path_used size: 76332
pub_points size: 41587
in_proc size: 29166           <-- the input
root_map size: 22325
actual_arg size: 14858
...
paths size: 741               <-- the bound itself
```

`--features ctadl` is what compiles the front end (`src/ctadl.rs`), and
`profile` is what compiles the instrumented copy of the rules; the example
target requires both. `--timeout` is a wall-clock stop checked between
iterations, so it is a ceiling, not a schedule — at `k = 1` this run converges
long before it. The memory and `k`-sweep commands are at the end.

`backflash.apk` is a TaintBench Android app, and it is the input that motivated
the `paths` relation of `src/ir.rs` — the syntactic bound on the access-path
vocabulary computed by `src/path_bound.rs` and tested against by every rule
that lengthens a path. Without such a bound the fixpoint does not exist on this
program: suffix congruence feeds itself through `path_used`, cycles in `edge`
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
converged=true wall=3.05s
```

Peak physical footprint is 1.67 GB, from `/usr/bin/time -l` on a second run.
Everything from here to "How it grows with k" is at `k = 1`.

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

The congruence join's fan-out — the number of paths sharing a base, which is
the multiplier on every scan of `edge` — is correspondingly small:

```
  paths per base: n=24145  mean=3  p50=1  p99=44  max=49
```

## Where the time goes

One SCC dominates: stratum B, the big mutually-recursive block.

```
scc 45: iterations: 45, time: 2.989s   (sum of rule times 2.342s)
the other 49 SCCs: 50ms between them
```

Inside it there are 89 rules, of which ten are 90% of the time:

```
     ms      %  rule
  603.5  25.8%  points   <-- edge_total, points_delta                [SIMPLE JOIN]
  350.5  15.0%  pub_edge <-- points_delta, pub_root, pub_root
  288.9  12.3%  edge     <-- edge_total, path_used_delta, ⋯, paths   (congruence, sub side)
  274.4  11.7%  edge     <-- edge_total, path_used_delta, ⋯, paths   (congruence, sup side)
  184.6   7.9%  edge     <-- eff_direct, in_proc, pub_edge_delta, root_map, root_map
  107.2   4.6%  points   <-- edge_delta, points_total                [SIMPLE JOIN]
   94.8   4.1%  path_used <-- points_delta
   80.9   3.5%  points   <-- edge_delta
   76.8   3.3%  edge     <-- edge_delta, path_used, ⋯, paths         (congruence, delta)
   57.0   2.4%  edge     <-- edge_delta, path_used, ⋯, paths         (congruence, delta)
```

The cost is the alias closure — `points`, and the `pub_edge` publication built
on it — with the four suffix-congruence variants together at 697ms, 30% of the
SCC.

One thing the profile still says out loud: congruence's plan is
`edge_indices_none_total`, a full scan. Ascent indexes on whole columns and
this join keys on `sup.base`, a *projection of* column 1, so it cannot be
planned as a `[SIMPLE JOIN]`. With the fan-out down to 3 that costs about
560ms rather than being fatal, but it is still the second-largest line item
and the most obvious speedup available.

Relation sizes at the fixpoint:

```
points     1,061,910      <-- the largest thing in the run
pub_edge     624,929
edge         245,047      (8.4x the input)
path_used     76,332
pub_points    41,587
root_map      22,325
paths            741      (the bound itself)
in_proc       29,166      (the input)
```

## Where the bytes go

```
## whole program — 2375 procedures, 29166 statements
  |P| = 90092 EDB facts;  retained 1.7 GiB, peak 1.8 GiB, 4,627,188 allocations

  relation      tuples   Vec bytes   B/tuple
  points     1,061,910    288.0 MiB    284.4
  pub_edge     624,929    144.0 MiB    241.6
  edge         245,047     36.0 MiB    154.0
  path_used     76,332     16.0 MiB    219.8
  pub_points    41,587      9.0 MiB    226.9
  root_map      22,325      3.5 MiB    164.4
  -- total   2,136,780    500.3 MiB    245.5

  where `retained` went
    tuple Vecs      500.3 MiB   29%
    Arc payloads      4.9 MiB    0%   suffixes and call strings the fixpoint built
    Ascent indices    1.2 GiB   71%   by subtraction
```

Two things worth keeping:

- **The suffixes cost nothing.** 4.9 MiB of `Arc` payload against 1.7 GiB
  retained. A vocabulary of 741 suffixes means every access path in the run
  shares one of 741 allocations, so the part of memory that grows with path
  depth does not register at all.

- **71% of the memory is Ascent's indices**, not tuples. That is the thing to
  attack if 1.7 GiB is too much: it is decided by which columns the rules join
  on, and `relation_sizes_summary()` cannot see any of it.

## How it grows with the program

`--max-procs N` keeps the N procedures with the most statements:

```
  procs                100         400        1000       whole
  |P|                45457       64867       77084       90092
  tuples            458409      950222     1254971     2136780
  retained       287.1 MiB   643.8 MiB   972.5 MiB     1.7 GiB
  peak           343.9 MiB   740.8 MiB     1.0 GiB     1.8 GiB
  B/tuple            656.7       710.5       812.5       845.7
```

Doubling `|P|` costs about 4.7× the tuples and 6× the bytes — `tuples ~
|P|^2.3`, `retained ~ |P|^2.6` over this range. That is the intraprocedural
alias closure being quadratic, which `tests/scaling.rs` already pins down
(`points_is_quadratic_in_a_single_procedure`): expected, and bounded. The 29%
rise in bytes per tuple across the sweep is the indices growing faster than the
relations they index, the same finding as the split above.

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
  wall              3.1s       19.3s         246s         270s         273s         292s     —
  peak GiB          1.55        6.69         47.4         41.7         46.9         57.3    >64
  iterations          45          44           28           20           18           17     —
  pending          1,034       2,183       14,034       42,617      161,840      713,316     —
  points       1,061,910   3,550,302   28,813,057   27,602,204   24,342,636   33,813,698     —
  pub_edge       624,929   2,923,630   25,625,431   18,230,537   14,986,135   12,100,149     —
  edge           245,047   1,817,143   18,916,799   20,394,507   23,264,646   34,777,649     —
  max depth            4           4            4            4            4            4     —
```

The `k >= 4` columns are snapshots at the cutoff, and — this is the trap — they
are **not comparable to each other**. `pub_edge` *falls* from 25.6M at k=4 to
12.1M at k=7 not because the fixpoint is smaller but because the higher-k run
spends more of its 240s minting instances (`pending` 14K → 713K) and gets less
far into the closure. Read each column as "where 240s got to" and nothing more.
`k = 8` has no column at all: `memguard.sh` killed it at 64.7 GiB, and the kill
takes the process before it prints, so a capped run yields no relation sizes.

### At 80 procedures, every `k` converges

80 is the largest `--max-procs` at which `k = 8` still reaches a fixpoint (100
blows 20 GiB). At that size all of `k = 1..8` converge — 91s at `k = 8`, wall
clock for the whole binary, import included — and the numbers are comparable:

```
  k                  1         2         3         4         5         6         7         8
  tuples          446K     1.11M     2.58M     5.15M     9.04M     14.2M     20.7M     28.6M
  retained     285 MiB   778 MiB   1.7 GiB   3.4 GiB   5.9 GiB  11.2 GiB  12.2 GiB  22.5 GiB
  peak         335 MiB   910 MiB   2.1 GiB   4.1 GiB   6.9 GiB  12.9 GiB  13.6 GiB  25.1 GiB
  index share      74%       75%       74%       74%       70%       69%       71%       69%
  Arc          1.5 MiB   2.9 MiB   4.6 MiB   7.2 MiB  20.4 MiB  47.5 MiB  95.0 MiB 165.9 MiB

  points       218,292   460,702   974,566 1,863,132 3,190,922 4,942,324 7,151,120 9,804,384
  pub_edge     112,277   336,943   819,501 1,665,949 2,947,753 4,653,117 6,815,645 9,422,487
  edge          57,499   231,299   660,520 1,450,878 2,670,490 4,316,730 6,414,674 8,957,736
  pub_root         635       812     1,050     1,341     1,703     2,186     2,932     4,183
```

**The growth is polynomial in `k`, not exponential.** Fitting `k = 3..8`:

```
  tuples ~ k^2.46    points ~ k^2.36    pub_edge ~ k^2.50    edge ~ k^2.66
  retained ~ k^2.56  pub_root ~ k^1.36  Arc ~ k^3.85
```

The call-string space *is* exponential in `k` in principle — that is what
`tests/scaling.rs::call_strings_double_per_level_unless_k_caps_them` pins down —
but it doubles only where there are call sites to double it, and this app's call
graph runs out of them. What explodes on the whole program is `|P|` interacting
with `k`, not `k` alone.

Read `retained` in steps, not ratios: `Vec` byte counts are allocated capacity,
which doubles, so at `k = 7` `edge`, `points` and `pub_edge` all report exactly
1.1 GiB and the k=6→7 byte ratio is 1.09 against a tuple ratio of 1.46. The
tuple row is the smooth signal; over the whole range tuples grow 64× and
retained 81×, so bytes do track tuples at a roughly constant ~700 B/tuple.

### The three relations are converging on being one relation

`points`, `pub_edge` and `edge` are 87% of all tuples at `k = 1` and **98.5% at
`k = 8`**. Everything else — `root_map` flat at ~11K, `eff_direct`,
`mono_target`, `sig_target` exactly constant — is noise beside them. But the
useful part is what happens to the ratios between them:

```
  k                  1     2     3     4     5     6     7     8
  pub_edge/points  .51   .73   .84   .89   .92   .94   .95   .96
  edge/points      .26   .50   .68   .78   .84   .87   .90   .91
```

`pub_edge` is by construction a filtered projection of `points` — the filter is
`pub_root` on both endpoints. `pub_root` grows as `k^1.36` while `points` grows
as `k^2.36`, so **the publication filter stops filtering**: half of `points` is
published at `k = 1`, 96% of it at `k = 8`. At high `k` the run is storing
three near-copies of the same closure, each with its own index set.

`Arc` payloads are the one component outpacing the closure (`k^3.85` — the call
strings themselves getting longer and more numerous), but at 166 MiB of 22.5 GiB
they are still 0.7% of the bill. Worth watching, not worth fixing.

The access-path bound is untouched by any of this: `paths` stays 741 by
construction and the depth histogram tops out at 4 accessors at every `k`, on
both the whole program and the 80-procedure cut. Nothing about raising `k`
lengthens a path.

## What is left to try

In the order the numbers argue for:

1. **De-tabulate `pub_edge`** — the same move that `crit_map` → `crit_subst`
   already made, on the relation that is now the obvious candidate. `pub_edge`
   is a materialized view: `points` filtered by `pub_root` on both endpoints
   (`src/analysis.rs:474`). By `k = 8` it holds 96% of `points`, 9.4M tuples,
   plus its own indices — call it a third of the run's memory to store a copy
   of something already stored. Its only two consumers use it as a join driver
   (`src/analysis.rs:507` for a static callsite, `:591` for a resolved
   critical one), so both could drive on `points` with `pub_root` guards
   instead. This is the largest single lever in the k direction.

2. **Make the publication filter filter again.** `pub_root` is what decides how
   much of `points` becomes summary, and it grows as `k^1.36` against `points`
   at `k^2.36` — which is *why* `pub_edge` degenerates into a copy. A
   placeholder is published for every pending instance and never withdrawn
   (`src/analysis.rs:464-468` says so out loud). Withdrawing the ones that are
   settled, or publishing only bases some caller can actually reach, attacks
   the cause where item 1 attacks the symptom.

3. **Shrink the index footprint** — 69-75% of retained at *every* `k`, so this
   is a flat 3-4× multiplier on everything above rather than something that
   gets worse. Largest absolute lever, unrelated to `k`. Fewer binding patterns
   over `points` and `pub_edge` is the lever, and item 1 removes a whole index
   set on its own.

4. **Index the congruence join.** `edge_indices_none_total` is a full scan and
   the second-largest line item at `k = 1` (~560ms of 2.3s). Give `edge` its
   bases as real columns (`edge(Proc, Base, AccessPath, Base, AccessPath)`, or
   a companion relation) so Ascent can plan `[SIMPLE JOIN]` on `(p, base)`.

5. **Bound the instance space.** `k` is the only thing limiting it. On a
   program that converges it limits it *polynomially* — `k^2.5`, not the
   doubling the synthetic test shows — but on the whole app `k >= 4` never
   reaches a fixpoint at all, and `k = 8` is killed at a 64 GiB cap before it
   reports anything. If `k > 2` is wanted at full size, the instances need a
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

Two things to know before re-running the sweeps. A guard kill yields **no
data** — the process dies before it prints its relation sizes — so a `k` that
hits the cap is a wasted run, not a short one; if the sizes are what you want,
lower `--timeout` (or `--max-procs`) until the run survives to its own report.
And a truncated run's relation sizes are a function of the budget, not of `k`:
comparing them across `k` is how you conclude that `pub_edge` shrinks as `k`
rises, which is false. Scaling claims need converged runs, which is what the
80-procedure sweep is for.
