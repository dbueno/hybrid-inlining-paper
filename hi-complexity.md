# Complexity of the Hybrid Inlining relations

What each relation of `HybridAnalysis` costs, measured rather than argued.

Everything below is reproducible:

```sh
cargo run --release --example complexity   # relation sizes, fitted exponents
cargo run --release --example parallel     # seq vs. ascent_par vs. inter-rule
cargo test  --test scaling                 # the regression guards
```

The programs being measured are the parametric families in `src/families.rs`.
Each turns one integer knob into a program of a fixed shape, so a fit against
the program's EDB fact count `|P|` says something about the relation rather
than about one hand-written example. `examples/complexity.rs` reports, per
relation, the least-squares slope `d` in `|R| ~ |P|^d`, plus a `last/prev`
column — a power law cannot express an exponential, and the families where the
parameter steps by 1 need the ratio to be readable.

## Figure 1

`figure1::program()` at `k = 4` is 82 EDB facts: 8 procedures, 12 statements,
one critical statement (`L25`, the `tx.poly(obj)` whose callee the context
decides).

| relation | size | | relation | size |
|---|---|---|---|---|
| `path_used` | 71 | | `pending` | 6 |
| `points` | 63 | | `call_crit` / `crit_sig` / `decisive_slot` | 6 |
| `edge` | 47 | | `eff_direct` | 6 |
| `pub_root` | 43 | | `is_called` | 5 |
| `free_root` | 37 | | `adequate` / `can_propagate` / `resolve` / `settled` | 4 |
| `root_map` | 36 | | `uncalled` | 3 |
| `pub_edge` | 17 | | `blocked` / `sig_target` / `stuck` | 2 |
| `crit_map` / `crit_operand` | 12 | | `crit_origin` / `critical` / `sig_size` | 1 |
| `pub_points` | 11 | | | |

520 derived tuples for 82 input facts — a factor of 6, and nothing here is
large enough for asymptotics to show. That is what the families are for.

## The short answer

Three distinct growth regimes, and the analysis touches all three.

| regime | relations | driven by |
|---|---|---|
| linear in program size | `edge`, `points`, `pending`, `pub_edge`, `root_map`, … | call depth and fan-in, on their own |
| **quadratic in program size** | `points`, `edge`, `path_used` | points-to sets, and suffix congruence, *within one procedure* |
| **exponential in call depth** | `pending` and everything keyed on a `CritId` | the number of call strings; bounded only by `k` |

So yes — there are n² relations, and there is something worse than n².

## Yes, there are n² relations

Two independent mechanisms, both intraprocedural, both visible with the
critical-statement machinery switched entirely off.

### `points` — the |paths| × |values| product

`alias(n)` is `n` allocations merged into a chain of `n` variables, so that
`pt(c_i) = {l_0..l_i}`. No calls, no critical statements, nothing of Hybrid
Inlining involved:

```
  relation                |P|^d  last/prev   sizes (n = 4 8 16 32 64)
  points                   1.74       3.73   19 53 169 593 2209   <== superlinear
  pub_points               1.01       2.00   4 8 16 32 64
  edge                     0.97       1.98   9 17 33 65 129
  path_used                0.91       1.96   11 19 35 67 131
```

`points` quadruples as `n` doubles: `Θ(n²)`, and `2209 ≈ n²/2 + …` at `n = 64`.
This is the textbook points-to bound — `points(p, ω, v)` is one tuple per
(access path, value) pair, and the closure rule
`points(p, sup, v) <-- edge(p, sup, sub), points(p, sub, v)` fills the product.
Nothing in this design makes it worse, and nothing makes it better; it is the
floor for any points-to analysis.

Note that only `points` blows up. `pub_points` stays linear, because
publication is restricted to `pub_root` — the summary of `alias(n)` is `n`
constraints, not `n²`. **The quadratic does not escape the procedure.**

### `edge` / `path_used` — suffix congruence

`fields(n)` is a chain of `n` distinct field loads off a parameter, inside one
procedure:

```
  relation                |P|^d  last/prev   sizes (n = 2 4 8 16 32 64)
  edge                     2.04       3.71   11 22 56 172 596 2212   <== superlinear
  points                   2.04       3.71   11 22 56 172 596 2212   <== superlinear
  path_used                1.94       3.62   15 28 66 190 630 2278   <== superlinear
  pub_edge                 0.00       1.00   1 1 1 1 1 1
```

Also `Θ(n²)`, from the two congruence rules

```
edge(p, sup2, sub.extend(rest)) <-- edge(p, sup, sub), path_used(p, sup.base, sup2), …
edge(p, sup.extend(rest), sub2) <-- edge(p, sup, sub), path_used(p, sub.base, sub2), …
```

which pair every path with every *observed* suffix on the same base. The
`path_used` gate is what keeps this finite at all — congruence over all
suffixes would not terminate — but within a procedure it still pairs prefixes
with suffixes, and that is a product.

Again `pub_edge` stays at **1**: the published summary of `fields(n)` is the
single constraint `ret@F ⊇ par_1@F.f1.….fn`. The quadratic is local, and a
caller inlining this procedure pays one edge, not `n²`.

That containment is the design working. The published vocabulary
(`pub_root`) is what stops an intraprocedural quadratic from being multiplied
by the number of callsites, which is what would turn `n²` into `n³`.

## The real blowup is exponential, and it is `pending`

`branching(d)`: every level calls the level below from *two* statements. The
program grows linearly in `d` — 52 EDB facts at `d = 1`, 178 at `d = 8` — but
the number of call strings of length `d` doubles per level, and `pending`
counts call strings.

```
  relation                |P|^d  last/prev   sizes (d = 1..8)
  pending                  4.07       2.00   5 11 23 47 95 191 383 767   <== superlinear
  crit_operand             4.07       2.00   10 22 46 94 190 382 766 1534
  pub_edge                 4.05       2.00   12 26 54 110 222 446 894 1790
  crit_map                 3.94       2.00   6 12 24 48 96 192 384 768
  resolve / settled        3.94       2.00   2 4 8 16 32 64 128 256
  points                   3.63       1.98   41 72 131 246 473 924 1823 3618
  edge                     3.53       1.97   33 58 103 188 353 678 1323 2608
  path_used                3.14       1.94   48 75 120 201 354 651 1236 2397
```

`pending` is exactly `3·2^d − 1`; the `|P|^4` fits are an artefact of fitting a
power law to a doubling. The right reading is `2^Θ(|P|)`. Concretely,
`branching(12)` is **250 EDB facts and 393,995 derived tuples**, and
`branching(14)` — 286 facts — is 1,573,755.

Every relation keyed on a `CritId` inherits this: `crit_operand`, `crit_sig`,
`call_crit`, `decisive_slot`, `blocked`, `can_propagate`, `stuck`, `crit_map`,
`resolve`, `settled`. And because placeholder nodes are part of the published
vocabulary, `pub_edge`, `pub_root` and `free_root` inherit it too — a summary
carrying `2^d` placeholders is a summary of size `2^d`.

This is the k-CFA call-string explosion, unchanged: `CritId::push` is a
call-string extension, and `k` is the depth limit. It is not a defect of this
implementation, it is what the paper's §3.2.2 k-limit exists to contain — and
it does contain it. The same programs with `k` held at 3:

```
  relation                                    sizes (d = 1..8)
  pending                                     5 11 15 15 15 15 15 15
  points                                      41 72 130 139 148 157 166 175
  edge                                        33 58 80 87 94 101 108 115
```

Flat past `d = k`, and everything else with it. **The k-limit is the only
thing standing between this analysis and an exponential**; there is no other
brake in the rules.

Two other things worth knowing about that. First, the cost of capping is paid
in ⊤-summarization: at `k = 3`, `top` goes from 0 to 8 at `d = 3` and
`adequate` drops to 0, exactly as designed. Second, the explosion needs
*both* depth and branching. `chain(n)` — depth `n` with `k = n+2` — is linear
in every relation, and so is `fanin(m)`, one critical procedure called from
`m` distinct callers. Depth alone is free, fan-in alone is free; it is the
number of distinct call *paths* that multiplies.

## What tuple counts hide: access-path depth

`fields_chain(n)` is `n` procedures, each appending one accessor to its
callee's summary path. Every relation stays linear in tuples — `edge` goes
23, 39, 71, 135, 263 for `n` = 2…32. But:

```
     n       chain max  chain accessors      fields max fields accessors
     2               3               34               2               17
     4               5               88               4               70
     8               9              268               8              348
    16              17              916              16             2040
    32              33             3364              32            13552
```

The deepest access path is `n+1`, growing linearly with call depth, and the
total accessor count is quadratic. **Access-path depth has no limit of its
own.** `k` bounds call strings; `path_used` bounds which suffixes congruence
may use; neither bounds how long a path grows through `rebase` during
inlining. A relation whose tuple count is linear can still cost `Θ(n²)` in
memory and in comparison time, and that is invisible in
`relation_sizes_summary()`. Most published access-path analyses impose a
depth-k limit on paths as well; this one does not, and if a real front end is
ever pointed at it, that is the first thing to add.

The termination question is separate, and the answer is better than expected.
`recursive_field()` — `P(x) { y = x.f; return P(y) }` — reaches a fixpoint
with `edge = 6` and a deepest path of 1. It does *not* append `.f` forever.
It gets there by deriving nothing at all for the recursive call, though: `P`
has no summary, because `pub_edge` needs `points(P, ret@P, Path(b))` and the
only thing that could produce it is `P`'s own summary. That is a precision
(indeed soundness) gap for recursion rather than a complexity one, but it is
the reason the fixpoint is small, and it should not be mistaken for the
access-path domain being safe under recursion.

## Summary table

Per relation, the mechanism and the worst family measured.

| relation | worst observed | mechanism |
|---|---|---|
| `points` | `Θ(n²)` intraproc; `2^Θ(d)` with branching | access paths × points-to values |
| `edge` | `Θ(n²)` intraproc; `2^Θ(d)` with branching | suffix congruence; inlined summaries |
| `path_used` | `Θ(n²)` intraproc | one tuple per (base, path) observed |
| `pending` | `2^Θ(d)`, capped by `k` | call strings — the k-CFA explosion |
| `crit_operand`, `crit_sig`, `call_crit`, `decisive_slot`, `blocked`, `can_propagate`, `stuck` | as `pending` | keyed on `CritId` |
| `crit_map`, `resolve`, `settled`, `adequate`, `top` | as `pending` × callees | one tuple per (instance, callee) |
| `pub_edge`, `pub_root`, `free_root` | as `pending`; linear otherwise | placeholders are part of the vocabulary |
| `pub_points` | linear | published summary of concrete values |
| `root_map` | linear in callsites × callee roots | the σ of inlining |
| `eff_direct`, `is_called`, `known_proc`, `uncalled`, `critical`, `sig_target`, `sig_size`, `mono_target` | linear | stratum A, over the EDB |

Nothing is cubic. The two quadratics are both intraprocedural and both stay
inside the procedure that produced them, which is the compositional design
paying off. The exponential is real, is inherent to context-sensitivity, and
is bounded by `k` alone.

## Parallel evaluation

`src/analysis.rs` now builds the same rules three ways. All three
`include_source!` the one `hybrid_rules` block, so no rule was touched to make
this comparison — only the evaluator changes:

| backend | macro | axis |
|---|---|---|
| `HybridAnalysis` | `ascent!` | sequential |
| `parallel::ParallelHybridAnalysis` | `ascent_par!` | intra-rule: a parallel iterator over each rule's delta |
| `parallel::inter_rule::InterRuleHybridAnalysis` | `ascent_par!` + `#![inter_rule_parallelism]` | the above, plus independent rules within one SCC run concurrently |

`ParallelHybridAnalysis` used to exist as a `#[cfg(test)]` compile-check only.
It is now a real, runnable program, seeded by the same `seed_edb!` macro as the
sequential one so the three cannot be given different inputs.
`examples/parallel.rs` checks every backend's relation sizes against the
sequential ones on every case — the `agree` column below — so this is a
correctness test as much as a timing one. **All three agree everywhere.**

### The result: parallelism loses, badly — and more threads make it worse

20 rayon threads, `--release`, best-of within a 750 ms budget per case.

```
  case                           |P|    tuples         seq         par      par+ir    par×     ir×
  figure1, k = 4                  82       520      0.56ms    237.61ms    146.83ms   0.00x   0.00x
  chain(8), k = n+2              122       779      0.39ms    384.08ms    225.93ms   0.00x   0.00x
  chain(32), k = n+2             386      2507      2.54ms   1248.90ms    733.94ms   0.00x   0.00x
  chain(128), k = n+2           1442      9419     42.52ms   5067.20ms   3263.11ms   0.01x   0.01x
  chain(512), k = n+2           5666     37067   1454.96ms  25518.22ms  15546.54ms   0.06x   0.09x
  fanin(8), k = 3                162      1177      0.37ms    194.16ms    114.22ms   0.00x   0.00x
  fanin(32), k = 3               570      4261      1.28ms    199.27ms    127.32ms   0.01x   0.01x
  fanin(128), k = 3             2202     16597      4.94ms    223.34ms    137.80ms   0.02x   0.04x
  fanin(512), k = 3             8730     65941     21.40ms    288.10ms    202.79ms   0.07x   0.11x
  branching(6), k = d+2          142      6587      3.08ms    383.85ms    247.06ms   0.01x   0.01x
  branching(8), k = d+2          178     25131     13.05ms    541.11ms    343.30ms   0.02x   0.04x
  branching(10), k = d+2         214     98971     63.69ms    897.79ms    614.74ms   0.07x   0.10x
  branching(12), k = d+2         250    393995    329.65ms   1890.53ms   1497.50ms   0.17x   0.22x
  alias(64)                      385      2991      1.05ms    689.50ms    463.37ms   0.00x   0.00x
  alias(256)                    1537     36495     15.41ms   2652.30ms   1711.23ms   0.01x   0.01x
  alias(512)                    3073    138511     64.17ms   4285.40ms   2905.10ms   0.01x   0.02x
  fields(16)                      38       584      1.23ms    460.08ms    320.01ms   0.00x   0.00x
  fields(32)                      70      1904      8.73ms    893.47ms    590.01ms   0.01x   0.01x
  fields(64)                     134      6848     92.12ms   2092.09ms   1598.67ms   0.04x   0.06x
  fields_chain(32)               367      1762      2.47ms   2748.42ms   1954.83ms   0.00x   0.00x
  fields_chain(128)             1423      6850     20.56ms  11689.65ms   7597.57ms   0.00x   0.00x
  fields_chain(256)             2831     13634     75.18ms  22890.16ms  15131.47ms   0.00x   0.00x
```

Both parallel backends are **10× to 1000× slower than sequential**, on every
single case. On Figure 1 itself: 0.56 ms sequential against 238 ms parallel.

The obvious question is how much of that is the concurrent data structures
(`DashMap`-backed indices, `boxcar` relations) and how much is threads getting
in each other's way. `RAYON_NUM_THREADS=1` separates them — same parallel
programs, same concurrent data structures, but no actual parallelism:

```
  case                           |P|    tuples         seq         par      par+ir    par×     ir×
  figure1, k = 4                  82       520      0.21ms      5.22ms      3.95ms   0.04x   0.05x
  chain(32), k = n+2             386      2507      2.45ms     30.12ms     22.57ms   0.08x   0.11x
  chain(128), k = n+2           1442      9419     40.90ms    170.61ms    138.28ms   0.24x   0.30x
  chain(512), k = n+2           5666     37067   1466.08ms   2805.25ms   2651.40ms   0.52x   0.55x
  fanin(128), k = 3             2202     16597      4.94ms     10.73ms      9.50ms   0.46x   0.52x
  fanin(512), k = 3             8730     65941     21.41ms     32.34ms     31.08ms   0.66x   0.69x
  branching(8), k = d+2          178     25131     13.05ms     27.61ms     24.84ms   0.47x   0.53x
  branching(10), k = d+2         214     98971     63.56ms     99.94ms     96.15ms   0.64x   0.66x
  branching(12), k = d+2         250    393995    324.99ms    430.26ms    427.44ms   0.76x   0.76x
  alias(512)                    3073    138511     60.73ms    172.48ms    153.59ms   0.35x   0.40x
  fields(64)                     134      6848     88.89ms    178.23ms    168.83ms   0.50x   0.53x
  fields_chain(256)             2831     13634     75.68ms    502.03ms    420.27ms   0.15x   0.18x
```

This is the interesting result. **Going from 1 rayon thread to 20 makes the
parallel backend 4× to 45× slower**, not faster:

| case | par @ 1 thread | par @ 20 threads | penalty |
|---|---|---|---|
| `figure1` | 5.2 ms | 237.6 ms | 45× |
| `chain(32)` | 30.1 ms | 1248.9 ms | 41× |
| `fields_chain(256)` | 502.0 ms | 22890.2 ms | 46× |
| `chain(512)` | 2805.3 ms | 25518.2 ms | 9.1× |
| `branching(12)` | 430.3 ms | 1890.5 ms | 4.4× |

So the diagnosis is not "concurrent data structures are expensive" — at one
thread the overhead is a modest 1.3×–25×, and it *amortizes away* as the work
grows: `branching(12)` reaches 0.76× of sequential, `fanin(512)` 0.66×, and
the trend across each family is monotone toward break-even. The diagnosis is
**contention and dispatch across threads on deltas that are far too small**.
This program has roughly 90 rules; each round hands most of them a delta of a
handful of tuples, and paying rayon's fork/join plus cross-shard `DashMap`
traffic on those is pure loss. The penalty shrinks (45× → 4.4×) exactly as the
per-round work grows, which is the same story from the other direction.

Two further readings:

**Inter-rule parallelism is the better of the two axes.** `par+ir` beats plain
`par` on every case at both thread counts, by 1.3–1.6× at 20 threads. That is
the axis this program's shape actually offers: stratum B is one very large
SCC, so there are many mutually independent rules available to run at once,
whereas most individual rules have nothing to spread across 20 threads.
Enabling `#![inter_rule_parallelism]` was the right call — it is just not
enough to overcome the per-rule overhead.

**Nothing here is big enough for parallelism to pay.** Extrapolating the
1-thread trend, the concurrent data structures stop costing anything around
`branching(12)`-scale work (~400k tuples). Multi-threading would then need
deltas large enough to amortize fork/join, which on this rule set means
something one or two orders of magnitude larger again. If parallel evaluation
is ever wanted seriously, the lever is not the thread count — it is reducing
the number of rules that fire per round, or batching rounds so each rule sees
a bigger delta.

The practical conclusion is that the parallel backends should stay what they
were meant to be: a guarantee that the rules remain parallelizable, plus a
differential test of the sequential evaluator. `RAYON_NUM_THREADS=1` is the
configuration to use if one of them must be run.

### Time is not the same shape as tuple count

The sequential column also makes visible what the relation sizes hide.
`fields(n)` goes 584 → 1,904 → 6,848 tuples (the `Θ(n²)` from suffix
congruence) while sequential time goes 1.2 ms → 8.7 ms → 92 ms. Tuples grow
~3.3× per step; time grows 7× then 11×. The extra factor is access-path
length: paths here reach depth `n`, and every hash and comparison on an
`AccessPath` is `O(depth)`. Cost per tuple makes it plainest —
`fields_chain(256)` spends 5.5 µs per tuple (13,634 tuples, 75 ms) against
`alias(512)`'s 0.46 µs (138,511 tuples, 64 ms), a 12× difference for the same
evaluator on the same machine.

So the honest summary of the access-path domain is: quadratic in tuples,
super-quadratic in time, and unbounded in depth. A depth limit on access paths
is the one piece of the standard toolkit this implementation is missing.

## Regression guards

`tests/scaling.rs` pins the results above so a rule edit cannot quietly change
them. Each test names the property it defends:

- `figure1_relation_sizes_are_stable` — the 10 headline sizes on Figure 1.
- `a_linear_call_chain_costs_a_constant_per_level` — every relation fits below
  `|P|^1.35` on `chain(n)`; `pending` is exactly one per level; exactly one
  `resolve`.
- `call_strings_double_per_level_unless_k_caps_them` — `pending = 3·2^d − 1`
  with `k = d+2`, and flat once `k` is fixed.
- `points_is_quadratic_in_a_single_procedure` — fit above `|P|^1.5`, and at
  least `n(n+1)/2` tuples.
- `suffix_congruence_is_quadratic_within_a_procedure` — `edge`, `points`,
  `path_used` all above `|P|^1.5` on `fields(n)`.
- `access_path_depth_grows_with_call_depth` — deepest path is exactly `n+1`.
- `recursion_through_a_field_load_terminates` — bounded `edge`, depth ≤ 1.
- `parallel_backends_derive_the_same_relations` — all three backends agree on
  five programs.

The two examples are the full picture and are meant to be re-run by hand after
any rule change; the tests are the part that fails automatically.
