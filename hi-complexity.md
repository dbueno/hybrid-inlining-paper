# Complexity of the Hybrid Inlining relations

What each relation of `HybridAnalysis` costs, measured rather than argued.

Everything below is reproducible:

```sh
cargo run --release --example complexity   # relation sizes, fitted exponents
cargo bench --bench backends               # seq vs. ascent_par vs. inter-rule
cargo bench --bench families               # wall time per family, sequential
cargo test  --test scaling                 # the regression guards
```

**These tables predate two de-tabulations and have not been regenerated.**
`crit_map` and `pub_edge` are no longer relations: the first became the
function `analysis::crit_subst`, the second is discharged by `root_map` and
`crit_subst` where it used to be joined against, and is recomputed after the
fixpoint by `HybridAnalysis::pub_edges()` for reporting. Every other relation
below is unaffected — the derivation is unchanged, and `backflash-profile.md`
records the check — so read a `crit_map` or `pub_edge` row as the shape of a
quantity that is now computed instead of stored, and everything else as
current. Re-running `cargo run --release --example complexity` regenerates the
tables without them.

**`path_used` is also gone, and that one does change the numbers.** `421a6be`
replaced it with `cat` and `used_ext`. Wherever a table below has a
`path_used` row, the relation no longer exists, and on `fields(n)` its
replacements are near-cubic where it was quadratic — see *Time is not the
same shape as tuple count*. The two parallel-evaluation sections and that one
were re-measured on 2026-08-31 at `978ed29` and are current; everything above
them is not.

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
| `path_used` | 65 | | `crit_operand` / `known_proc` | 8 |
| `points` | 53 | | `crit_map` / `eff_direct` | 6 |
| `edge` | 40 | | `is_called` / `pub_points` | 5 |
| `free_root` / `pub_root` | 37 | | `call_crit` / `can_propagate` / `crit_sig` / `decisive_slot` / `pending` | 4 |
| `root_map` | 30 | | `uncalled` | 3 |
| `pub_edge` | 16 | | `adequate` / `blocked` / `resolve` / `settled` / `sig_target` | 2 |
| | | | `crit_origin` / `critical` / `sig_size` | 1 |

352 tuples in the derived relations above — 452 across every relation the
program declares, which is the basis the `tuples` column of the parallel table
below uses. Either way nothing here is large enough for asymptotics to show.
That is what the families are for.

`resolve = 2` is the entire dispatch answer: `bar1 → Y.poly` and
`bar2 → Z.poly`, one tuple each, with the spurious `bar1 → Z.poly` absent. It
used to be 4, and the two that went away were not call edges — they were child
instances in `service` re-deciding what `bar1` and `bar2` had already decided.
The section on the `blocked` guard below is why they are gone.

## The short answer

Three distinct growth regimes, and the analysis touches all three.

| regime | relations | driven by |
|---|---|---|
| linear in program size | `edge`, `points`, `pending`, `pub_edge`, `root_map`, … | call depth, fan-in, and procedure count, on their own |
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
thing standing between this analysis and an exponential.** The one other brake
in the rules — the `blocked` guard on propagation, below — prunes placeholders
that are already *decided*, and `branching(d)`'s are not: its receiver comes
from the top, so every intermediate holder is genuinely blocked and every one
of those `2^d` call strings is a distinct undecided obligation. Nothing but `k`
touches those.

Two other things worth knowing about that. First, the cost of capping is paid
in ⊤-summarization: at `k = 3`, `top` goes from 0 to 8 at `d = 3` and
`adequate` drops to 0, exactly as designed. Second, the explosion needs
*both* depth and branching. `chain(n)` — depth `n` with `k = n+2` — is linear
in every relation, and so is `fanin(m)`, one critical procedure called from
`m` distinct callers. Depth alone is free, fan-in alone is free; it is the
number of distinct call *paths* that multiplies.

## What `pending` counts, and what the `blocked` guard removes

A placeholder crosses a callsite only while it is `blocked` — while the caller
still controls the operand that decides it:

```
pending(q, id.push(s)) <-- pending(p, id), blocked(p, id), eff_direct(s, p), … ;
```

`root_map`'s two placeholder-renaming rules carry the same guard, so a
procedure and its callers agree on which instances cross. The justification is
the paper's adequacy condition read as a *presence* test: an adequate instance
has a points-to set for its deciding operand that no caller can add to, because
any caller-reachable component would appear as a symbolic path — that is what
`points(p, sup, Path(sub)) <-- edge(p, sup, sub)`, for symbolic `sub`, is for —
and would therefore block. So an adequate instance is decided where it stands,
and a propagated copy re-derives the same callees. `blocked` only ever grows,
so the guard is monotone and needs no new stratum.

What it removes is duplication, and it is a constant factor:

| | before | after |
|---|---|---|
| `figure1`, all relations | 520 | **452** |
| `figure1`, `resolve` | 4 | **2** |
| `fanin(32)`, all relations | 4261 | **3173** |
| `fanin(32)`, `pending` | 65 | **33** |

(All-relation totals on the same basis as the `tuples` column of the parallel
table below, so the two sections can be read against each other.)

`fanin` is where it bites: each caller allocates and pins its own receiver, so
the instance is adequate at the caller and has no business climbing to `Entry`.

What it does **not** remove is a single call string. `chain(n)` and
`branching(d)` are unchanged tuple for tuple, because their receiver is supplied
from the top and every intermediate holder is genuinely blocked; `pending` on
`branching(d)` is still exactly `3·2^d − 1`. **The guard prunes *decided*
placeholders. The exponential is made of undecided ones, and only `k` bounds
those.**

One corner is worth naming, because `blocked` is a presence test: a deciding
operand whose points-to set is **empty** is vacuously unblocked, so the guard
keeps the instance where it is. That is the right answer — by the seeding rule
an operand fed by a parameter, or by a field of one, carries a symbolic member
and blocks, so an empty set means no reaching definition of any kind, i.e. dead
code — and propagating it would only manufacture equally empty placeholders in
every caller. `families::dead_receiver()` is the program, and
`a_receiver_with_no_values_stays_put_and_dispatches_nothing` pins the behaviour.

## The ordinary case: many procedures, real flow, nothing critical

The families above each isolate one axis, and between them they left a gap.
The shapes with many procedures — `chain`, `fanin`, `fields_chain` — give each
procedure a body of one or two statements; the shapes with a real
intraprocedural closure — `alias`, `fields` — are a single procedure with no
calls at all. Nothing measured the ordinary large program: many procedures,
each doing a nontrivial amount of pointer flow, with dispatch essentially
free.

`wide(m, w)` is that program. `m` leaf procedures, each an `alias`-style merge
of `w` allocations into `w` variables with the parameter seeded into the chain;
the leaves grouped four at a time under mid-level callers that merge their
results; `Entry` merging the mids. Depth is fixed at 3 while `m` grows. There
is no `virtual_call` and no variable index anywhere in it, so `critical`,
`pending`, `resolve`, `top` and `adequate` are all **empty** and `k` is
irrelevant — this is the rest of the analysis, measured with the
critical-statement machinery switched off.

The two costs stay separate, which is the property worth having:

```
  wide(m, 8) — m procedures with a nontrivial local closure each
  relation                |P|^d  last/prev   sizes (m = 4 8 16 32 64)
  points                   1.00       2.00   368 733 1463 2923 5843
  edge                     1.00       2.00   86 171 341 681 1361
  path_used                0.99       1.99   99 194 384 764 1524
  pub_edge                 1.01       2.00   5 10 20 40 80
  root_map                 1.01       2.00   15 30 60 120 240

  wide(64, w) — 64 procedures, local closure of width w in each
  relation                |P|^d  last/prev   sizes (w = 2 4 8 16)
  points                   1.79       2.71   1043 2387 5843 15827   <== superlinear
  edge                     0.92       1.75   593 849 1361 2385
  pub_edge                 0.00       1.00   80 80 80 80
  root_map                 0.00       1.00   240 240 240 240
```

Every relation is **linear in `m`**: adding a procedure costs a constant, not
a constant times the rest of the program. Widening the local closure is the
`Θ(w²)` of `alias` again, and `pub_edge` is flat at one per procedure while it
happens — the same containment `alias(n)` and `fields(n)` showed, now
confirmed across a call graph rather than inside one body. **The
intraprocedural quadratic is not multiplied by the number of callsites.** That
is the compositional claim, and this is the family that tests it.

`wide` also differs from every other large family in a way tuple counts do not
show: it is *wide* rather than *deep* in fixpoint iterations. `alias(n)` needs
roughly `n` semi-naive rounds to push `l_0` along the chain to `c_n`, and each
round carries a small delta. `wide(m, w)` has `m` mutually independent
procedures whose closures all advance in the same round, so the delta per
round grows with `m`. That distinction is what the parallel section below
turns on.

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
ever pointed at it, that is the first thing to add. The bytes are measured
directly in the next section.

The termination question is separate, and the answer is better than expected.
`recursive_field()` — `P(x) { y = x.f; return P(y) }` — reaches a fixpoint
with `edge = 6` and a deepest path of 1. It does *not* append `.f` forever.
It gets there by deriving nothing at all for the recursive call, though: `P`
has no summary, because `pub_edge` needs `points(P, ret@P, Path(b))` and the
only thing that could produce it is `P`'s own summary. That is a precision
(indeed soundness) gap for recursion rather than a complexity one, but it is
the reason the fixpoint is small, and it should not be mistaken for the
access-path domain being safe under recursion.

## What tuple counts hide: bytes

`examples/memory.rs` counts at the allocator (`src/mem.rs` installs a counting
global allocator), so it sees what a tuple count cannot. Two numbers per
family: `retained`, the live heap the finished relations hold, and `peak`, the
high-water mark over the fixpoint.

The headline is that **the tuples are a fifth of the memory and the indices
are the rest**:

```
                        tuple Vecs   Arc payloads   Ascent indices     retained
  Figure 1 (k = 4)     54.4 KiB 21%   1.5 KiB  1%   209.4 KiB  79%    265.3 KiB
  wide(512, 8)         15.4 MiB 22%   384 KiB  1%    55.5 MiB  78%     71.3 MiB
  fields_chain(32)    256.1 KiB 19%  45.1 KiB  3%   1020.7 KiB 77%      1.3 MiB
```

- **Tuple `Vec`s** are `capacity × size_of::<Tuple>()` summed over the IDB —
  the relations Ascent exposes and the only thing `relation_sizes_summary()`
  can see. Capacity, not length: Ascent grows relations by doubling.
- **`Arc` payloads** are the access-path suffixes and call strings the
  fixpoint itself built (`Arc<[Accessor]>`, `Arc<[Stmt]>`). Symbols cloned out
  of the EDB are not charged here — cloning an `Arc<str>` handle allocates
  nothing — and each shared allocation is counted once, which is precisely
  what a per-tuple estimate would get wrong.
- **Ascent indices** are the remainder, and there is no way to measure them
  directly: the codegen emits `pub <rel>: Vec<Tuple>` beside one *private*
  `<rel>_index_...` field per binding pattern the rules join on. They are
  three-quarters of the memory.

That last point is the one that matters for optimizing rules: *the cost of a
relation is set as much by how it is joined as by how many tuples it has.* Add
a body literal that needs a new binding pattern and a whole index appears;
drop one and it goes away. Neither shows up in a tuple count.

Density runs 560–1350 bytes per derived tuple across the families. It is
roughly flat within a family whose tuples keep their shape, which is what
makes the exceptions legible:

```
                       B/tuple, smallest n → largest n
  wide(m, 8)              816 → 824    flat: tuples are a fixed shape
  chain(n), k = n+2       677 → 685    flat
  fields_chain(n)         798 → 950    +19%: suffixes lengthen with call depth
  fields(n)               934 → 1354   +45%: suffixes lengthen within a procedure
```

`fields(n)` is the clearest case in the repo of memory outrunning tuples:
tuples fit `|P|^1.91` and retained bytes fit `|P|^2.06`. The gap is the
access-path suffix growing with `n` — the same phenomenon as the accessor
table above, now in bytes.

Two caveats on the numbers. They are what the program asked the allocator for:
no size-class rounding, no per-allocation header, no fragmentation. Real RSS
runs above them — the largest single run in the example sweep peaks at
76.8 MiB by this count, and the process it runs in tops out at 104 MiB of
`maximum resident set size`. And the counters are process-wide, so
`retained` is only meaningful when nothing else is allocating; under
`ascent_par!` treat `peak` as the trustworthy one.

`cargo bench --bench memory` measures the same `retained` figure under
criterion, which is the form to use when the question is comparative:

```text
cargo bench --bench memory -- --save-baseline before
# edit the rules
cargo bench --bench memory -- --baseline before
```

The fixpoint is deterministic, so the samples of a point are bit-identical and
the reported change is exact rather than statistical.

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
`benches/backends.rs` checks every backend's relation sizes against the
sequential ones before it times a case, so this is a correctness test as much
as a timing one; a disagreement aborts the benchmark rather than being
reported as a speedup. **All three agree everywhere**, which
is also the differential check that the `blocked` guard on propagation derives
the same relations under all three evaluators.

### The result on small programs: parallelism loses, badly

20 rayon threads, `--release`, from `cargo bench --bench backends`. Each
number is criterion's median over 10 samples; the confidence intervals are in
`target/criterion/`. Tuple counts are omitted here — criterion measures time,
and the sizes are `examples/complexity.rs`'s job.

```
  case                             |P|         seq         par      par+ir    par×     ir×
  figure1, k = 4                    82      0.15ms    253.91ms    168.73ms   0.00x   0.00x
  chain(8), k = n+2                122      0.31ms    483.99ms    302.96ms   0.00x   0.00x
  chain(32), k = n+2               386      1.80ms   1494.96ms    909.60ms   0.00x   0.00x
  chain(128), k = n+2             1442     28.06ms   5614.15ms   3391.68ms   0.00x   0.01x
  chain(256), k = n+2             2850    151.22ms  11250.72ms   6806.59ms   0.01x   0.02x
  fanin(8), k = 3                  162      0.22ms    184.71ms    126.54ms   0.00x   0.00x
  fanin(32), k = 3                 570      0.68ms    187.69ms    130.21ms   0.00x   0.01x
  fanin(128), k = 3               2202      2.60ms    202.39ms    138.83ms   0.01x   0.02x
  fanin(512), k = 3               8730     10.72ms    233.34ms    163.64ms   0.05x   0.07x
  branching(6), k = d+2            142      2.16ms    418.73ms    268.05ms   0.01x   0.01x
  branching(8), k = d+2            178      8.96ms    547.97ms    346.66ms   0.02x   0.03x
  branching(10), k = d+2           214     41.57ms    768.96ms    513.33ms   0.05x   0.08x
  branching(12), k = d+2           250    215.14ms   1335.91ms   1001.43ms   0.16x   0.21x
  alias(64)                        385      1.01ms    645.39ms    447.29ms   0.00x   0.00x
  alias(128)                       769      3.54ms   1244.42ms    833.38ms   0.00x   0.00x
  alias(256)                      1537     15.53ms   2449.91ms   1628.99ms   0.01x   0.01x
  fields(16)                        38      2.45ms    533.73ms    362.46ms   0.00x   0.01x
  fields(32)                        70     22.86ms   1018.52ms    675.35ms   0.02x   0.03x
  fields(64)                       134    311.60ms   2109.59ms   1438.43ms   0.15x   0.22x
  fields_chain(32)                 367      0.21ms    144.17ms    107.29ms   0.00x   0.00x
  fields_chain(128)               1423      0.70ms    145.01ms    108.41ms   0.00x   0.01x
```

Two rows moved since the tables earlier in this document were taken, and the
cause is the rule set rather than the evaluator: `path_used` is gone, replaced
by `used_ext` and `cat`. That makes `fields_chain(n)` dramatically cheaper
(0.21 ms sequential at `n = 32`, against 2.22 ms before) and `fields(n)`
markedly more expensive (311.6 ms at `n = 64`, against 78.2 ms), because
`used_ext` and `cat` are themselves superlinear on `fields` — 49,920 and
45,760 tuples at `n = 64`, where `path_used` had 2,278. The backend
comparison is unaffected, since all three run the same rules, but the `seq`
column should not be read against the older tables above.

Both parallel backends are **6× to 1700× slower than sequential**, on every
single case. On Figure 1 itself: 0.15 ms sequential against 254 ms parallel.
(The `wide` family is measured separately below; it is the case where this
stops being true.)

The obvious question is how much of that is the concurrent data structures
(`DashMap`-backed indices, `boxcar` relations) and how much is threads getting
in each other's way. `RAYON_NUM_THREADS=1` separates them — same parallel
programs, same concurrent data structures, but no actual parallelism:

```
  case                             |P|         seq         par      par+ir    par×     ir×
  figure1, k = 4                    82      0.15ms      4.74ms      3.80ms   0.03x   0.04x
  chain(8), k = n+2                122      0.31ms      8.73ms      6.80ms   0.04x   0.05x
  chain(32), k = n+2               386      1.79ms     28.15ms     21.56ms   0.06x   0.08x
  chain(128), k = n+2             1442     28.15ms    140.72ms    114.54ms   0.20x   0.25x
  chain(256), k = n+2             2850    151.10ms    435.73ms    379.85ms   0.35x   0.40x
  fanin(8), k = 3                  162      0.21ms      3.60ms      2.95ms   0.06x   0.07x
  fanin(32), k = 3                 570      0.68ms      4.31ms      3.67ms   0.16x   0.18x
  fanin(128), k = 3               2202      2.59ms      7.16ms      6.42ms   0.36x   0.40x
  fanin(512), k = 3               8730     10.72ms     18.28ms     17.52ms   0.59x   0.61x
  branching(6), k = d+2            142      2.15ms     10.61ms      8.72ms   0.20x   0.25x
  branching(8), k = d+2            178      8.98ms     22.24ms     19.98ms   0.40x   0.45x
  branching(10), k = d+2           214     41.60ms     68.44ms     66.33ms   0.61x   0.63x
  branching(12), k = d+2           250    215.07ms    282.95ms    283.47ms   0.76x   0.76x
  alias(64)                        385      1.00ms     12.49ms     10.47ms   0.08x   0.10x
  alias(128)                       769      3.55ms     26.13ms     22.05ms   0.14x   0.16x
  alias(256)                      1537     15.54ms     61.16ms     53.78ms   0.25x   0.29x
  fields(16)                        38      2.45ms     13.30ms     11.33ms   0.18x   0.22x
  fields(32)                        70     22.87ms     54.33ms     49.97ms   0.42x   0.46x
  fields(64)                       134    312.29ms    519.72ms    509.84ms   0.60x   0.61x
  fields_chain(32)                 367      0.21ms      2.75ms      2.48ms   0.07x   0.08x
  fields_chain(128)               1423      0.69ms      3.48ms      3.20ms   0.20x   0.22x
```

This is the interesting result. **Going from 1 rayon thread to 20 makes the
parallel backend 4× to 55× slower**, not faster:

| case | par @ 1 thread | par @ 20 threads | penalty |
|---|---|---|---|
| `figure1` | 4.7 ms | 253.9 ms | 53.5× |
| `chain(32)` | 28.2 ms | 1495.0 ms | 53.1× |
| `fields_chain(128)` | 3.5 ms | 145.0 ms | 41.7× |
| `alias(256)` | 61.2 ms | 2449.9 ms | 40.1× |
| `chain(256)` | 435.7 ms | 11250.7 ms | 25.8× |
| `fanin(512)` | 18.3 ms | 233.3 ms | 12.8× |
| `branching(12)` | 283.0 ms | 1335.9 ms | 4.7× |

So the diagnosis is not "concurrent data structures are expensive" — at one
thread the overhead is a modest 1.3×–32×, and it *amortizes away* as the work
grows: `branching(12)` reaches 0.76× of sequential, `fanin(512)` 0.59×, and
the trend across each family is monotone toward break-even. The diagnosis is
**contention and dispatch across threads on deltas that are far too small**.
This program has roughly 90 rules; each round hands most of them a delta of a
handful of tuples, and paying rayon's fork/join plus cross-shard `DashMap`
traffic on those is pure loss. The penalty shrinks (54× → 4.7×) exactly as the
per-round work grows, which is the same story from the other direction.

Two further readings:

**Inter-rule parallelism is the better of the two axes.** `par+ir` beats plain
`par` on every case at both thread counts, by 1.2–1.7× at 20 threads. That is
the axis this program's shape actually offers: stratum B is one very large
SCC, so there are many mutually independent rules available to run at once,
whereas most individual rules have nothing to spread across 20 threads.
Enabling `#![inter_rule_parallelism]` was the right call — it is just not
enough to overcome the per-rule overhead.

**Nothing above is big enough for parallelism to pay.** Extrapolating the
1-thread trend, the concurrent data structures stop costing anything around
`branching(12)`-scale work (~330k tuples). Multi-threading would then need
deltas large enough to amortize fork/join, which on this rule set means
something one or two orders of magnitude larger again. That prediction turned
out to be right, and the next section is the family that reaches it.

### Where parallelism does pay: wide programs

None of the families above tests the shape a parallel evaluator actually
wants. Every large case is either iteration-*deep* — `alias(n)` needs `n`
semi-naive rounds, each with a small delta — or exponential in a single
relation. `wide(m, 8)` is the first that is iteration-*wide*: `m` independent
procedures whose local closures all advance in the same round, so the delta a
rule sees grows with `m` instead of staying at a handful of tuples.

20 threads:

```
  case                             |P|         seq         par      par+ir    par×     ir×
  wide(32, 8)                     1916      1.88ms    218.84ms    156.68ms   0.01x   0.01x
  wide(128, 8)                    7652      7.91ms    231.36ms    165.47ms   0.03x   0.05x
  wide(512, 8)                   30596     44.31ms    259.38ms    185.85ms   0.17x   0.24x
  wide(2048, 8)                 122372    267.64ms    349.26ms    270.23ms   0.77x   0.99x
  wide(8192, 8)                 489476   1486.46ms    714.19ms    600.24ms   2.08x   2.48x
  wide(128, 4)                    4580      3.66ms    185.99ms    135.55ms   0.02x   0.03x
  wide(128, 8)                    7652      8.00ms    233.66ms    168.70ms   0.03x   0.05x
  wide(128, 16)                  13796     23.86ms    331.21ms    233.39ms   0.07x   0.10x
```

`RAYON_NUM_THREADS=1`, the same programs:

```
  case                             |P|         seq         par      par+ir    par×     ir×
  wide(32, 8)                     1916      1.86ms      6.63ms      5.96ms   0.28x   0.31x
  wide(128, 8)                    7652      7.89ms     15.31ms     14.53ms   0.52x   0.54x
  wide(512, 8)                   30596     44.02ms     58.86ms     58.34ms   0.75x   0.75x
  wide(2048, 8)                 122372    262.20ms    295.53ms    294.35ms   0.89x   0.89x
  wide(8192, 8)                 489476   1465.40ms   1654.12ms   1655.75ms   0.89x   0.89x
  wide(128, 4)                    4580      3.64ms      8.63ms      8.01ms   0.42x   0.45x
  wide(128, 8)                    7652      7.94ms     15.18ms     14.58ms   0.52x   0.54x
  wide(128, 16)                  13796     23.78ms     36.08ms     35.32ms   0.66x   0.67x
```

**`wide(8192, 8)` is the first case in the suite where a parallel backend
beats sequential**: `par+ir` at 2.48×, `par` at 2.08×. Three things make this
readable rather than lucky.

*It is threads, not the data structures.* At one thread the same program is
0.89× — the concurrent-structure overhead has flattened to a stable ~11% tax
that no longer grows with size, exactly as the 1-thread trend above predicted.
Everything beyond that is real parallel speedup: 1656 ms at one thread against
600 ms at twenty, which is 2.8× out of 20 cores.

*The crossover is a size, and it is knowable.* `par+ir` goes 0.01× → 0.05× →
0.24× → 0.99× → 2.48× across a 256× range in `m`, breaking even almost exactly
at `wide(2048, 8)` — call it ~120k EDB facts and ~450k tuples on this machine
(20-core M1 Ultra). Below that the per-round fork/join toll dominates; the
parallel column is nearly flat from `wide(32)` to `wide(512)` (219 → 259 ms
while sequential grows 24×), which is what a fixed toll looks like.

Holding `m` fixed and widening the local closure instead — `wide(128, w)` —
moves nothing: `par+ir` is 0.03× at `w = 4` and 0.10× at `w = 16`. More work
per procedure is not more width, and only width pays.

*Width is what matters, not tuple count.* `branching(12)` has 332k tuples and
still runs at 0.21×; `wide(2048, 8)` has 453k — comparable — and reaches
0.99×. The difference is that `branching`'s tuples are produced by a long
serial chain of rounds over one exploding relation, while `wide`'s are
produced by thousands of independent procedures at once. **The predictor of
parallel payoff on this rule set is delta width per round, and delta width
comes from the number of procedures in flight — not from how many tuples the
analysis ends up with.**

The practical conclusion changes accordingly. The parallel backends are still
the wrong choice for anything at the scale of the paper's example, and
`RAYON_NUM_THREADS=1` is still the setting for those. But for the workload a
real front end would actually produce — tens of thousands of procedures with
ordinary pointer flow and dispatch that is mostly monomorphic — parallel
evaluation with `#![inter_rule_parallelism]` is worth turning on, and the
speedup grows with the program.

One caveat on generality: `wide` has nothing critical in it. Whether the
critical-statement rules parallelize as well is untested, and there is reason
to think they would do worse — the `pending`/`CritId` relations are the ones
whose deltas come from a serial chain of propagation steps. A family that
crosses `wide`'s width with a modest number of critical statements is the
obvious next measurement.

### Time is not the same shape as tuple count

The sequential column also makes visible what the relation sizes hide.
`fields(n)` goes 2,437 → 14,829 → 102,333 tuples at `n` = 16, 32, 64 while
sequential time goes 2.51 ms → 23.46 ms → 316.95 ms. Tuples grow ~6.5× per
step; time grows 9.3× then 13.5×.

Two things are stacked in that. The tuple count itself is no longer the
`Θ(n²)` of suffix congruence: `edge` and `points` are still quadratic
(172 → 596 → 2,212), but `cat` and `used_ext` — which `421a6be` introduced in
place of `path_used` — grow like `n³` (816 → 5,984 → 45,760 and
1,088 → 7,040 → 49,920 over the same three points). `path_used` was 190 → 630
→ 2,278 there. On top of that sits access-path length: paths here reach depth
`n`, and every hash and comparison on an `AccessPath` is `O(depth)`. Cost per
tuple makes the second factor plainest — `fields(64)` spends 3.1 µs per tuple
(102,333 tuples, 316.9 ms) against `alias(512)`'s 0.48 µs (137,486 tuples,
65.3 ms), a 6.5× difference for the same evaluator on the same machine, on
top of the extra tuples.

The trade `421a6be` made is legible in the other direction too: `fields_chain`,
which is the same field chain spread over `n` procedures rather than one,
went from 73.6 ms at `n` = 256 to 1.61 ms, and from 5.4 µs per tuple to
0.18 µs (9,025 tuples). Factoring the join out is a large win where the
suffixes are shared across procedures and a large loss where one procedure
accumulates them all. `fields(n)` is the family to watch if that is worth
revisiting.

`cargo bench --bench families` is the target that makes this axis its own
measurement: a least-squares fit of its medians against the family parameter
gives `fields(n)` an exponent of **3.2 in time**, `alias(n)` **2.0**,
`fields_chain(n)` **0.94**, and `wide(m, 8)` **1.2** where every relation is
linear in `m`.

So the honest summary of the access-path domain is: quadratic in tuples for
the points-to relations, near-cubic for the suffix bookkeeping `cat`/`used_ext`
on a single deep procedure, super-quadratic in time, and unbounded in depth. A
depth limit on access paths is the one piece of the standard toolkit this
implementation is missing.

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
- `many_procedures_cost_a_constant_each_when_nothing_is_critical` — `wide(m, 8)`
  is linear in `m` in every relation; `critical`, `pending`, `resolve`, `top`
  and `adequate` are empty; the `Θ(w²)` local closure leaves `pub_edge` flat.
- `parallel_backends_derive_the_same_relations` — all three backends agree on
  five programs.
- `a_receiver_with_no_values_stays_put_and_dispatches_nothing` — the vacuous
  corner of adequacy: an empty deciding operand does not propagate, admits no
  call edge, and is not ⊤-summarized.
- `every_renamed_placeholder_is_pending_in_the_procedure_it_lands_in` — the
  structural invariant behind the `blocked` guard: if a callsite renames a
  placeholder into `q`, then `q` holds it as pending. Guarding `pending`
  without guarding `root_map` breaks this and leaves `q` holding an obligation
  with no owner.

The examples and the three `cargo bench` targets are the full picture and are
meant to be re-run by hand after any rule change; the tests are the part that
fails automatically. Nothing pins memory: `cargo bench --bench memory
--baseline` is the comparison, and it is a report, not an assertion.
