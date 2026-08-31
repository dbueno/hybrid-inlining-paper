# What the fixpoint derives and then throws away

`adequate` and `settled` live in stratum C: they are decided *after* the main
fixpoint, by negating over the finished `blocked`. The design question that
raises is whether the analysis should be restructured so that it never derives
a tuple the end of the run discards.

Three answers, in decreasing order of confidence:

1. **Adequacy is not the place to look.** Deciding it late costs exactly
   nothing, measured against a perfect oracle at four program sizes. *Re-run
   under the new front end at all four: still nothing.*
2. **The placeholder hop is a small, safe, provable saving** — but *much*
   smaller than this document first reported: 2.9% of `points` at `k = 0`, not
   24%. Every tuple of it is still demonstrably a duplicate.
3. **The large mass is speculative propagation**, and the pre-pass that was
   going to gate it — `pin_distance` — turns out to have been reading an
   artifact. *This is the section the re-measurement changes most; §2b is
   rewritten.*

> **Configuration.** Every number below was re-measured after the CTADL front
> end started running `ctadl index`'s four IR passes by default (dead temps,
> coalescing, SSA, copy propagation; `ctadl-comparison.md` measures why). The
> ablation is `--no-preprocess`, and it reproduces this document's previous
> figures exactly — including `pin_distance`'s table to the row — so the two
> configurations can be compared on today's binary.

All measurements on `backflash.apk` unless stated. Raw output in
`/Volumes/Shampoo/hi-vs-ctadl/rebase/`; commands at the end.

## 1. The adequacy oracle changes nothing

`resolve` fires unless `will_propagate`, the *syntactic* under-approximation of
`blocked` that `src/analysis.rs` settles below the fixpoint. The exact test is
`blocked`, and it is only known at the end. So give the analysis the answer:
run once, take `blocked`, seed it into `will_propagate`, run again. The second
run resolves only where the finished fixpoint says the instance is adequate —
a redesign with a perfect, free adequacy oracle, and therefore an **upper bound
on what any such redesign can save**.

```
                            baseline        oracle      delta
  whole program, k=1         334,256       334,853       0.2%   554ms -> 546ms
  whole program, k=2         445,581       446,979       0.3%
  whole program, k=3         671,554       674,912       0.5%
  80 procedures, k=8         416,137       417,468       0.3%
```

Every one of the seventeen compared relations is **identical at all four
sizes**; the only row that moves is `will_propagate` itself, which is the seed,
and it is the whole of the 0.2–0.5%. (The percentage is larger than the 0.0%
this table used to show only because the denominator shrank 4× — the seed is
the same 655 tuples it always was.) `summaries()`, the settled dispatch and
every `resolve` tuple are identical on both sides at every size: 1,527 →
1,527 at `k = 1`, 11,262 → 11,262 at `k = 3`, lost 0 and gained 0. `summaries()`, the
settled dispatch and every `resolve` tuple are identical too, so this is not a
saving that quietly costs an answer. There is nothing to save.

The reason is in the rules, not in the app. Adequacy already does not drive
anything: propagation is gated *positively* by `blocked`, monotone and inside
the SCC, and resolution is gated by `!will_propagate`, settled before the
fixpoint starts. Stratum C only classifies. The one thing an exact test could
add is suppressing a resolution at an instance that is blocked **and** has a
caller to redo it, and that count is **zero** at every size measured (k = 0, 1,
2, 3 whole-program, and 80 procedures at k = 8). Every blocked-instance
resolution on this app is the ⊤-fallback, which is the only answer available.

### The residual class is real, and small, and closing it has a price

`carries` follows moves only, so a receiver blocked through a *field load* —
`y = x.f` with `x` a formal — is invisible to `will_propagate`: blocked, does
propagate, resolved here anyway. `examples/redundant_shape.rs` is that shape:

```
  receiver blocked through a move chain (will_propagate sees it)
     n  resolve  redundant  points  points under the oracle
    32        2          0     289     289

  receiver blocked through a FIELD LOAD (will_propagate is blind)
     n  resolve  redundant  points  points under the oracle
     2        4          3      58      49
     8       10          9     130     103
    32       34         33     418     319   (-24%)
```

(`examples/redundant_shape.rs` builds its own EDB and never reads an import, so
this is the one table in this document the front-end change cannot touch. It is
reproduced here unchanged.)

The class exists and costs ~24% of `points` on a program built entirely out of
it; it never occurs on `backflash.apk`. And suppressing it is not free: the
settled dispatch and `Entry`'s summary are unchanged, but every intermediate
`P_i` loses 2 of its 6 published constraints — resolving early is what makes a
callee's summary *say* what the call does instead of deferring it.

## 2. Where the discarded tuples are

Three filters run after convergence: publication (a local-rooted path is
eliminated), `is_decided` (a constraint over a *settled* placeholder is
dropped), and adequacy. What `points` comes to:

```
                                     k=0        k=1        k=2         k=3
  points                          60,099     69,881    100,151     178,644
  key rooted at a local            92.4%      82.1%      61.3%       35.2%
  survives publication              7.6%      17.9%      38.7%       64.8%
  reaches the reported summary      4.6%       5.6%       8.9%       12.9%
  dropped as settled-placeholder    3.0%      12.3%      29.8%       51.9%
```

The shape is the same and the slopes are the same; what moved is where it
starts. The local-rooted share is now 92% at `k = 0` rather than 73%, because
SSA turns one merged local into several versions and every version is
local-rooted. The settled-placeholder class — the one this section is about —
is 3.0% at `k = 0` where it was 24.6%.

The local-rooted half is the intraprocedural closure: intermediate by
construction, not waste. The **settled-placeholder half** — 46% of `points` at
`k = 1`, 78% at `k = 3` — is material published onto a node standing for a
critical statement that turned out to be decided, which the report then drops
because transitivity has already carried its content elsewhere. It splits in
two, and the halves have different answers.

### 2a. The hop at a settle-in-place instance: 2.9% of `points` at k=0, provably duplicate

`CritSlot(id,i)` is wired `CritSlot(id,i) ⊇ a_i`, and `r ⊇ CritRet(id)`. When
the instance is settled *at its origin* — decided here, never propagated —
that node is one hop between the resolved callee's summary and the local the
statement writes, and a design that inlined the callee onto `a_i` and `r`
directly, as `eff_direct` already does for a static callee, would not build it.
`examples/waste.rs` checks every such tuple against its twin at the local:

```
                                                 k=0     k=1     k=2     k=3
  points at a settled placeholder, depth 0      2.9%    1.5%    1.2%    0.8%
    whose twin at the local already exists      2.9%    1.5%    1.2%    0.8%
  points at a settled placeholder, deeper       0.0%   10.6%   28.0%   50.3%
```

100.0% of the depth-0 class is still duplicate — the proof was never
quantitative — but it is now **1,725 of 60,099 tuples at `k = 0`**, not 54,047
of 224,542. The saving fell 31× in absolute terms and 8× as a share.

That is the honest correction to answer 2 above, and the reason is worth
stating: the duplicate hop is a tuple derived once at a placeholder node and
once at the local it stands for. Merging a variable's versions inflates *both*
copies, so a measurement of the class taken on a merged IR overstates what
collapsing it would save. At 2.9% of a run that now takes 0.46s, this is no
longer obviously worth the rule change — it remains correct, provable, and
knowable before the fixpoint (`stuck` is decided in stratum A), but it has
stopped being a lever.

### 2b. Propagation: how far away is the resolvent?

The deeper half of that table is placeholders of instances that were
propagated into a caller and then ⊤-summarized anyway. Whether that is waste
cannot be read off a `k = 1` or `k = 2` run: if the allocation that would pin
the receiver lives further up than `k` reaches, those runs measure the budget,
not the design. (Neither does the 80-procedure `k = 8` run answer it —
`--max-procs` keeps the biggest procedures and *deletes most of the callers*,
which is exactly the material propagation needs.)

`examples/pin_distance.rs` measures the distance directly, without a deep run.
It walks propagation with the instances taken out: start at a critical
receiver, ask whether it holds a concrete allocation, and if not follow the
symbolic paths it does hold outward through every callsite of the holder, one
level at a time. The points-to sets it reads are the `k = 0` ones — merged
over all contexts — and the call graph is CHA's, which contains every `k`'s,
so a receiver it cannot pin at depth `d` cannot be pinned by a real run at
`k = d`.

With the front end's IR passes **off**, reproducing this document's original
table exactly:

```
  473 critical virtual calls                      of those, at the pinning site
  depth   count   cumulative                      purely concrete   still merged
      0      32        6.8%                                     2             30
      1      16       10.1%                                     2             14
      2      15       13.3%                                     0             15
      3      23       18.2%                                     0             23
  never    387       81.8%   (searched to depth 24; the cap was never reached)
```

And **on**, which is the default:

```
  depth   count   cumulative                      purely concrete   still merged
      0       1        0.2%                                     1              0
  never    472       99.8%   (searched to depth 24; the cap was never reached)
    the search stopped because:
      the holder has no caller                             97
      the value is a deferred call's result                 9
      the receiver's points-to set holds nothing to follow 366
```

**The 86 pinnable receivers were 85 parts artifact.** The walk follows a
receiver outward only while its points-to set holds a path rooted at the
holder's own formal. On a merged IR a receiver carries the union of every
version of its register, so it inherits a formal-rooted path from some *other*
use of the same register and the walk follows it. Split the versions and the
receiver carries only what was actually assigned to it: 366 of 473 then hold
nothing the walk can follow at all.

This retracts the previous version of this section. "The resolvent really is
further away than `k = 2`; 23 statements need exactly `k = 3`" was measuring
register reuse, not data flow. The traced example that illustrated it — the
receiver of `DialogFragment.onActivityCreated` pinned three callsites up in
`FragmentManagerImpl.attachFragment` — does not survive the split.

Two things stop this from being a simple retraction, and both matter.

**The analysis's own answer did not move at all.** Below-CHA resolutions are 1
at `k ≤ 2` and 3 at `k = 3`, identical on both sides, and at `k = 0` the number
of receivers the *fixpoint* finds empty rises only from 219 to 230 of 473. So
the dispatch machinery is not losing receiver flow; it is `pin_distance`'s
outward walk, and only that walk, whose input was inflated.

**Which means the walk's soundness claim is now visibly too strong.** It says
"what it cannot pin at depth `d`, no run can pin at `k = d`" — yet it now puts
472 of 473 statements in `never`, while a real `k = 3` run answers 3 instances
below CHA. That contradiction was already latent (the previous version noted
the walk is blind to *purification*, so the instances `k = 3` narrows were
always invisible to it); the split has simply made the blind spot the entire
picture. **As a gating pre-pass, `pin_distance` should not be built on until
that gap is understood** — it would now gate away 99.8% of statements including
the ones that pay.

### 2c. What k = 3 actually costs and buys

`k = 3` converges, and now so does `k = 5` on the whole program:

```
  k                      0          1          2           3
  wall                0.46s      0.55s      0.79s       1.53s
  peak                0.45 GiB   0.50 GiB   0.58 GiB    0.87 GiB
  points             60,099     69,881    100,151     178,644
  edge              125,867    138,217    174,115     240,067
  instances             473        966      2,040       4,680

  instances answered below CHA
                          1          1          1           3
  (stmt, callee) edges  614        589        586         582   (CHA alone: 1,106)
  statements answered with nothing
                        230        241        241         241
```

`k = 3` costs 1.53s and 0.87 GiB where it used to cost 50.84s and 18.93 GiB —
33× the wall and 22× the memory, gone. But **the yield is exactly what it
was**: 3 instances below CHA at `k = 3`, 1 at `k ≤ 2`, and a statement-level
call graph that moves by a handful of edges out of ~600.

That is the cleanest statement of what the front-end change did and did not do.
It made propagation to `k = 3` nearly free. It did not make propagation buy
anything more than it bought before, because what propagation buys was never
limited by cost — it is limited by the ⊤ fallback, which is the next heading
but one.

An instance that *is* narrowed still sits beside sibling instances of the same
statement that are ⊤, and the union over instances is CHA again. That is why 3
narrowed instances move the statement-level call graph by 4 edges and no more.

### 2d. Dead procedures: 27.6%, and now a lever

950 of 2,375 known procedures (40.0%) are unreachable from any of the 754
entries and are summarized in full. They hold **27.6% of `points` and 32.6% of
`edge`** at `k = 0`, rising to 39.5% of `points` at `k = 3`.

This is the one item in this document that got *more* interesting. The absolute
number barely moved — ~16.6K `points` tuples in unreachable procedures now
against ~24.4K before — but everything around it shrank by 15×, so the share
went from 2.3% to 27.6%. "The unreachable ones are the small ones" is no longer
true in relative terms, and "not a lever" was a judgement about a share that no
longer holds: skipping procedures no entry reaches is now the largest single
block of derivable-but-unwanted work measured anywhere in this document.

The caveat that made it unattractive still applies — a library procedure with no
entry is exactly what a *different* set of entry points would reach, so this is
a configuration question, not a soundness one.

## 3. What this argues for

**Not a redesign around adequacy.** The oracle bound is 0.0% at four sizes,
the residual class is empty on this input, and closing it would make
intermediate summaries defer what they currently answer.

**Not the `pin_distance` pre-pass either, until its blind spot is understood.**
The argument for it still holds in form: gating propagation on "can a caller
pin this?" is circular if the test is the analysis's own fixpoint, but not if
the test lives in a strictly cheaper, over-approximating domain — the same move
`will_propagate` makes one stratum down. What has changed is the evidence. On a
merged IR the walk found 86 pinnable receivers and put 81.8% in `never`; on the
split IR it finds 1 and puts 99.8% in `never`, while the real analysis keeps
answering the same 3 instances below CHA at `k = 3`. A gate built on that would
suppress the propagation that pays along with the propagation that does not.
The walk's blindness to *purification* was noted as a limit before; it is now
the dominant term, and it has to be fixed before the pre-pass is worth
building.

**The real ceiling is the ⊤ fallback, not the depth — and that is now the
whole story.** Raising `k` used to multiply the fixpoint by ~3.5 per level, so
"the wall moves out one level and costs 3.5×" was a cost argument as much as a
precision one. It is no longer a cost argument: `k = 3` is 1.53s and 0.87 GiB,
`k = 5` converges on the whole program, and the yield is still 3 instances.
Propagation is cheap now and still buys almost nothing, which isolates the
fallback as the only thing left in the way. Whatever splits a merged receiver
is the lever; nothing about `k` is.

**Skipping unreachable procedures is the largest measured block of unwanted
work.** 27.6% of `points` at `k = 0` and 39.5% at `k = 3`, in procedures no
entry reaches. It is a configuration question rather than a soundness one
(§2d), and it is now worth more than everything else in this document combined.

**The hop collapse no longer stands on its own.** 2.9% of `points` at `k = 0`
rather than 24%, all of it still demonstrably duplicate, on a run that takes
0.46 seconds. Correct, provable, and no longer worth a rule change.

## Reproducing

```sh
cargo build --features ctadl --release --example waste
cargo build --features ctadl --release --example pin_distance

# accounting, dispatch precision by depth, the hop, dead procedures, the oracle
./target/release/examples/waste backflash.apk --k 1

# the k sweep the propagation argument rests on; k=3 converges in 1.5s / 0.9 GiB
for k in 0 1 2 3; do
    ./scripts/memguard.sh 110 /usr/bin/time -l \
        ./target/release/examples/waste backflash.apk --k $k --no-oracle
done

# how far away the resolvent is, and whether it arrives merged.  The second
# form is the ablation: it reproduces this document's original table, and the
# gap between the two is §2b.
./target/release/examples/pin_distance backflash.apk --max-depth 24 --cha
./target/release/examples/pin_distance backflash.apk --max-depth 24 --cha --no-preprocess

# the shape will_propagate cannot see
cargo run --release --example redundant_shape
```

`--no-preprocess` is available on `waste`, `pin_distance` and `points_anatomy`
as well, and translates the IR exactly as `ctadl import` cached it — the
configuration this document reported before. `--no-oracle` skips the second
fixpoint. The baseline is dropped before the
oracle run is built, so the two never coexist. `--max-procs` is available on
both binaries but should not be used for anything about propagation: it keeps
the largest procedures and deletes the callers propagation depends on.
