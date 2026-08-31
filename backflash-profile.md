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

3.2s, and it prints everything this document is drawn from: the EDB shape,
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
converged=true wall=3.33s
```

Peak physical footprint is 1.8 GB, from `/usr/bin/time -l` on a second run.
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
scc 45: iterations: 46, time: 3.259s   (sum of rule times 2.579s)
the other 49 SCCs: 62ms between them
```

Inside it there are 99 rules, of which ten are 86% of the time:

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

The cost is the alias closure — `points`, and the `pub_edge` publication built
on it — with the four suffix-congruence variants together at 722ms, 28% of the
SCC.

One thing the profile still says out loud: congruence's plan is
`edge_indices_none_total`, a full scan. Ascent indexes on whole columns and
this join keys on `sup.base`, a *projection of* column 1, so it cannot be
planned as a `[SIMPLE JOIN]`. With the fan-out down to 3 that costs about
600ms rather than being fatal, but it is still the second-largest line item
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
  tuples            458795      951931     1258400     2141341
  retained       287.4 MiB   645.0 MiB   974.8 MiB     1.7 GiB
  peak           344.1 MiB   740.6 MiB     1.0 GiB     1.8 GiB
  B/tuple            656.8       710.5       812.3       846.0
```

Doubling `|P|` costs about 4.7× the tuples and 6× the bytes — `tuples ~
|P|^2.3`, `retained ~ |P|^2.6` over this range. That is the intraprocedural
alias closure being quadratic, which `tests/scaling.rs` already pins down
(`points_is_quadratic_in_a_single_procedure`): expected, and bounded. The 29%
rise in bytes per tuple across the sweep is the indices growing faster than the
relations they index, the same finding as the split above.

## How it grows with k

Same input, whole program, `--timeout 300` each. The runs overshoot the
deadline because Ascent checks the clock only between iterations, and at
`k >= 4` a single iteration takes minutes:

```
  k                     1           2            4            8           16
  outcome       converged   converged      timeout      timeout      timeout
  wall               3.4s       23.2s         362s         364s         508s
  peak footprint   1.8 GB      6.8 GB      35.8 GB      57.6 GB     144.2 GB
  iterations           46          45           20           16           13
  pending           1,034       2,183       13,451    3,370,221   78,915,729
  crit_map          4,561      13,990      174,246   27,404,613  101,941,225
  edge            245,047   1,817,143   15,221,101   15,113,082    2,345,930
  points        1,061,910   3,550,302   18,386,632    8,205,158    1,599,446
  max depth             4           4            4            4            4
```

The `k >= 4` columns are snapshots at the cutoff, not fixpoints. Read them as
"where it had got to", which is why `edge` and `points` are *smaller* at k=16
than at k=8: the k=16 run spent its whole budget minting instances and never
got far into the alias closure.

Two things the table says.

**The access-path bound is orthogonal to the k-limit, and it holds.** `paths`
stays 741 by construction, and the depth histogram tops out at 4 accessors at
every k — the same LoaderManagerImpl chain is the deepest path in all five
runs. Nothing about raising k lengthens a path.

**What explodes with k is the instances.** `pending` is one row per
`(procedure, CritId)`, and a `CritId` is a call string of up to k sites; each
level multiplies by the call sites that reach it, which is the doubling
`tests/scaling.rs::call_strings_double_per_level_unless_k_caps_them` pins down
on a synthetic input. Here `pending` goes 1,034 → 2,183 → 13,451 → 3.4M →
78.9M, and `crit_map` — the renaming that carries a caller's paths into an
instance — runs an order of magnitude above it (13× at k=4, 8× at k=8). From
k=8 on, `crit_map` is the largest relation in the run and everything else is
noise beside it.

So on this app the analysis is memory-bound in k, not time-bound: k=16 peaked
at 144 GB of physical footprint on a 128 GB machine, which is past the point
where the numbers mean anything but "it thrashed". Practically, `k = 1` is the
setting this app runs at, `k = 2` is affordable at 7× the time and 4× the
memory, and `k = 4` needs the instance space bounded by something other than
the call-string length before it is worth measuring.

## What is left to try

In the order the numbers argue for:

1. **Index the congruence join.** `edge_indices_none_total` is a full scan and
   the second-largest line item (~600ms of 2.6s). Give `edge` its bases as real
   columns (`edge(Proc, Base, AccessPath, Base, AccessPath)`, or a companion
   relation) so Ascent can plan `[SIMPLE JOIN]` on `(p, base)`.

2. **Shrink the index footprint** — 71% of 1.7 GiB. Fewer binding patterns over
   `points` and `pub_edge` is the lever.

3. **Bound the instance space.** `k` is the only thing limiting it, and it
   limits it exponentially: at `k = 8` the run is 27M `crit_map` tuples and
   nothing else matters. If `k > 2` is wanted on an app this size, the
   instances need a second bound — merging instances whose decisive slot has
   the same points-to set, or a tighter `blocked`, since `blocked` is what
   decides whether an instance is copied into its callers at all.

4. **Sweep precision against the bound.** The vocabulary is syntactic, so there
   is no depth knob to turn; but `path_bound.rs` decides how far it follows
   local data flow, and the TaintBench queries are what should decide how far
   is far enough.

5. **Type-filtering congruence** — rejecting an extension whose accessor is not
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
`time -l` sees, because the fixpoint is over in 3.3s. Poll to enforce a cap and
to watch the trajectory (climbing vs plateaued); quote `time -l` for a peak.

Three ways to get a guard that silently never fires, all of which have happened
here:

1. **Finding the PID with `pgrep -f`.** A pattern matching the binary also
   matches any shell whose command line mentions it — a `for k in ...; do
   ./target/release/examples/ctadl_profile ...` loop, for instance. The guard
   then polls a shell, reads a small, perfectly valid integer, and never fires,
   while the real process runs uncapped. This is what let the `k = 16` run
   above reach 144 GB on a 128 GB machine. Take the PID from `$!` of the
   command the guard itself launched, and from nowhere else.

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

# the k sweep: 1, 2, 4, 8, 16, each under a 64 GiB cap.  `time -l` gives the
# peak; memguard kills the run if it climbs past what the machine can hold.
cargo build --features ctadl,profile --release --example ctadl_profile
for k in 1 2 4 8 16; do
    ./scripts/memguard.sh 64 /usr/bin/time -l \
        ./target/release/examples/ctadl_profile backflash.apk --k $k --timeout 300
done
```

`--max-procs N` keeps the N procedures with the most statements and the facts
that mention only those; type-level facts (`lookup`, `direct_subtype`,
`alloc_type`) are kept whole so that what counts as critical does not change.
