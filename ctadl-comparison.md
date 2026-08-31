# This engine against CTADL's index, on backflash.apk

CTADL implements hybrid inlining too — `ctadl index --strategy hi` — over the
same IR this repo's front end reads. So the two can be pointed at one import
and the difference read off rather than argued. Everything below is one
machine (20-core M1 Ultra), one import
(`~/.local/state/ctadl/imports/backflash.apk`), back to back, with
`/usr/bin/time -l` for the footprint. Raw logs are in
`/Volumes/Shampoo/hi-vs-ctadl/`.

## The headline

```
                            wall     peak footprint   instructions   derived tuples
  ctadl index (mixed)       0.29s          91 MiB          3.08 G          ~289 K
  ctadl index (hi)          0.29s          95 MiB          3.13 G          ~287 K
  this engine, k = 0        0.61s         373 MiB              —            386 K
  this engine, k = 1        2.93s        1.49 GiB         20.40 G          1,494 K
```

("derived tuples" is every IDB relation, on both sides: for this engine the
basis `examples/ctadl_memory.rs` totals; for CTADL `locals + assign_like +
call_target_assign_like + summary + paths + critical_summary + the four
context relations, plus the `alias_of_formal`/`copy_edge` pre-passes.)

`ctadl index` is **10× faster and 16× smaller** at `k = 1`. The gap is not one
thing. It factors, cleanly and multiplicatively, into three — and only the
third has anything to do with hybrid inlining.

## Is the comparison fair? Mostly, and where it is not it favours CTADL

Same import, same IR, so the front ends reconcile exactly. The call structure
is *identical* — CTADL's `DirectCall: 2477` / `JavaCall: 5526` against this
engine's `direct_call 2477` / `virtual_call 5526`, fact for fact. What differs:

```
  ctadl   3898 functions   1523 external_function   55,319 assign (post-SSA)
  this    2375 procedures                           29,166 in_proc  (no SSA)
          3898 - 1523 = 2375, exactly
```

**Procedures.** `src/ctadl.rs:334-336` skips any function with an empty body
(`if f.blocks.is_empty() { continue; }`), and that is exactly CTADL's 1,523
`external_function` rows. CTADL keeps them and gives them behaviour: 166
propagation models matched from its default `java-index.jsonl`, so taint
crosses `StringBuilder.append`, `ArrayList.size`, and the rest of the
platform. This engine has no equivalent — those calls are `uncalled` (1,418).

**Statements.** Three causes, in order of size:

1. **Exceptions cost CTADL two facts where this engine records at most one**
   (next section).
2. **`ret` here has no site identity and is deduplicated.**
   `ret: BTreeSet<(Proc, Var)>` (`src/ctadl.rs:258`) carries no `Stmt`, and an
   ordinary `return x;` adds **no `in_proc` row at all** — `exp_var` only calls
   `temp()` for constant/object returns. CTADL's `assign` is a plain
   non-deduplicated `Vec`, and every `Return` terminator gets a fresh site
   (`codegen/mod.rs:808-825`). A function with several exits is several facts
   there and one deduplicated tuple here.
3. **SSA.** `ctadl index` runs SSA before codegen — the trace says
   `preprocessing 3898 function(s) (SSA) and generating facts`, and the
   `[mem cp]` checkpoints put `after SSA transform` before
   `after codegen_program`. Phi nodes and versioned copies are extra `assign`
   facts. `Options::ssa` here defaults to `false`, the analysis being
   flow-insensitive.

Two things cut the other way, and are worth naming so this is not read as
one-sided: this engine keeps constant/string assignments (5,193 `const_assign`)
that CTADL's `trans_exp` drops (`codegen/mod.rs:846-854` returns `None` for
`ObjectRef`/`Str`/`Bytes`), and it expands nested access paths into extra
`in_proc` rows where CTADL counts one statement.

Net: **CTADL is doing strictly more of the program in less memory.** The gap
below is a floor, not a ceiling.

## Exceptions: CTADL models them, this engine does not

CTADL has no exception construct in its IR — `StatementKind` is 7 variants,
`TerminatorKind` is `Return`/`Goto` (`ctadl-ir/src/mir/mod.rs:261-320`,
`terminator.rs:20-28`). Exceptions are a *front-end convention* on top:

- every function is `ReturnType { arity: 2 }` — slot 0 the normal return,
  slot 1 the exception return (`languages/dex/mod.rs:306`: "All Java functions
  return 2 values: (normal_return, exception_return)");
- every `CallAssign` carries `rets: [retval, throwval]`;
- `throw`/`athrow` becomes an `Assign` into a shared per-function `throwval`
  local plus `Return { args: [empty, throw_exp] }`;
- `move-exception` / a JVM handler entry is an ordinary `Assign` reading that
  same local;
- try ranges become real CFG `Goto` edges to the handler block
  (`dex-reader/src/basic_blocks.rs:120-147`; `jvm-reader/src/flow.rs:427-454`).

It is coarse — one `throwval` per function, so every throw site in a function
merges with every handler in it — but the *value* genuinely flows: a callee's
thrown object reaches the caller's catch variable through ordinary `assign`
facts, and every relation above (`locals`, `assign_like`, `summary`) carries
it with no extra machinery. That is the cheap part of the design: exceptions
cost CTADL two return slots, not a new relation.

This engine drops all of it, by a decision documented at `src/ctadl.rs:50-53`:

> **Multiple returns.** A CIR call returns a tuple (`rets`), and dex gives
> every call arity 2 — a value and an exception slot. We keep `rets[0]` and
> the first operand of each `Return`, and drop the rest. **Exception flow is
> therefore invisible.**

`add_call` takes `rets.first()` (`:545`) and `add_function` takes
`args.first()` (`:404-414`); `rets[1]` is read nowhere in the file. The
statements that write and read `throwval` still translate as ordinary `mov`s,
so catch blocks exist as vertices — with no edge connecting any throw site to
any handler. On a TaintBench app, where exception-carried data is a routine
exfiltration path, this is a real coverage hole, and it is on the side of the
engine using 16× the memory.

## First: the two programs are not computing the same relation

This is the part that has to be settled before any byte is compared, because
it accounts for more of the gap than the data structures do.

CTADL's index is not a points-to closure. Its core relation is

```rust
// ctadl-ascent/src/index_engine/mod.rs:1078
#[ds(crate::index_engine::locals_trie)]
relation locals(FunctionId, FlowVariable, Path, FormalIndex, Path);
```

— "local reachability", *which formal parameter* reaches this variable at this
path. The fifth column is a **formal index**, bounded by the arity of the
procedure. `locals` on backflash is 54,880–69,731 rows: **1.23 rows per
variable**, essentially linear in the program.

This engine's core relation is

```rust
relation points(Proc, AccessPath, PtVal);   // src/analysis.rs:226
```

where `PtVal` ranges over *values* — allocation sites, constants, and symbolic
paths. That is 1,061,910 rows. But look at what is in them:

```
points = 1061910
  PtVal::Path  (symbolic)     990832   93.3%
  PtVal::Alloc (concrete)      31555    3.0%
  PtVal::Const                 39523    3.7%
  mentions a placeholder      947384   89.2%
edge = 245047
  mentions a placeholder      196467   80.2%
```

**93.3% of `points` is symbolic** — the same "reachable from a symbolic
source" information CTADL keeps in `locals`. This engine spends 990,832 tuples
on it; CTADL spends 68,611. The concrete half — the 3% that is `Alloc` —
is the only part CTADL does not compute at index time at all: it defers it to
`ctadl query`, where `taint(FunctionId, TaintState, FlowVariable, Path,
QueryEndpoint)` is seeded from the query's actual sources (9 of them, on the
model I used) instead of from every allocation in the app. That query costs
0.44s and 73 MiB.

So the architectures differ on two axes at once, and both favour CTADL on
memory: an abstract domain keyed on formal index rather than on value, and a
value closure that is demand-driven rather than eager.

## Second: bytes per tuple — this is the data-structure half, and it is ~8×

Run this engine at `k = 0`, where every instance is immediately `stuck` and
falls back to ⊤. The critical-statement machinery is then neutralised and the
two programs derive comparable amounts:

```
                        core tuples   relation bytes   B/tuple
  ctadl (strategy hi)       192,195          18.6 MB        97
  this engine, k = 0        386,017         295.3 MiB      803
```

**2.0× the tuples, but 8.3× the bytes per tuple.** That factor is real, it is
present with hybrid inlining switched off, and it decomposes further:

### Tuple width: 144 B against 24 B

| this engine | | CTADL | |
|---|---|---|---|
| `Proc`, `Stmt`, `Var`, … | 16 B (`Arc<str>`, **no interner**) | `FunctionId`, `FlowVariable` | 4–8 B (ids) |
| `Suffix` | 16 B (`Arc<[Accessor]>`) | `Path` | **8 B** (`tailshare::Seq`, interned) |
| `Base` | **48 B** | | |
| `AccessPath` | 64 B | | |
| `PtVal` | 64 B | | |
| **`points` / `edge` tuple** | **144 B** | **`locals` leaf** | **24 B** |

Two things drive this. `Path` in CTADL is `tailshare::Seq<PathSegment>` — a
globally interned, suffix-shared cons list whose handle is a single 8-byte
`&'static` pointer with pointer-identity `Hash`/`Eq`. Here an `AccessPath` is
a `Base` plus an `Arc<[Accessor]>` — 64 bytes, and the symbols inside it are
`Arc<str>` allocated fresh at every construction site in `src/ctadl.rs`, with
no interner at all (`src/ir.rs:31-34` says so out loud).

And `Base` is 48 bytes **because of the placeholder variant**:
`CritSlot(CritId, ArgIdx)` where `CritId` is `Stmt` + `Arc<[Stmt]>` = 32 B.
Every access path in the program pays 48 bytes for a base so that 1,034
pending instances can carry a call string. That cost lands in all 1.06 M
`points` tuples and all 245 K `edge` tuples, whether or not they are contextual.

### Index redundancy: 76–81% of retained, and half the `points` Vec is empty

```
  this engine, k = 1        tuple Vecs 347.3 MiB (24%)   indices 1.1 GiB (76%)
  this engine, k = 0        tuple Vecs  56.4 MiB (19%)   indices 237.9 MiB (81%)
```

Ascent 0.8.0's sequential index is `HashMap<K, Vec<V>>` where `V` is the
**projected non-key columns stored inline** — so `points_indices_0_1` is
`HashMap<(Proc, AccessPath), Vec<PtVal>>`: an 80-byte key and 64-byte values,
with `Vec::with_capacity(4)` on first insert regardless of how many values the
key ends up with. One such map per binding pattern per relation.

CTADL hit exactly this and fixed it. `locals_trie.rs:1-11` opens:

> `locals(...)` uses more memory than anything else in the index phase. As a
> normal Ascent relation it is stored about 6 times over: once in the physical
> `Vec`, and again in each of the indices `none`, `0_1`, `0_1_2`, the full
> existence index `0_1_2_3_4`, and the inverse `0_3_4`. Every index stores its
> value columns *inline*, so the full 5-column tuple is copied many times.

The fix is Ascent's BYODS hook (`#[ds(...)]`): one shared store, every logical
index a view over it. **But it is worth being honest about what that bought
CTADL**, because its own instrumentation prints it:

```
assign_like store estimate: trie 13.9 MB over 139387 rows
  | default equiv ~23.9 MB (Vec 5.3 + full 10.3 + 0_3 8.3) | saving ~9.9 MB
```

**1.7×.** Not 8×. The module doc says the same thing about `locals` — "1.1–2.3×
smaller, not about 10×". So the custom data structures are the *smaller* part
of the 8.3×; the larger part is the 144 B versus 24 B tuple, which is interning.

One free win visible in the same numbers: `points` holds 1,061,910 tuples of
144 B = 145.8 MiB of data in a 288.0 MiB `Vec`. Ascent grows by doubling, so
**49% of the largest allocation in the run is unused capacity** — about
142 MiB at `k = 1`, for a `shrink_to_fit` after the fixpoint.

### And the same story in time

`/usr/bin/time -l` counts instructions, and the fixpoints can be separated
from the front ends by their own wall clocks (CTADL's `ascent_run` is 88 ms of
its 290 ms; this engine's `run()` is 423 ms of 610 ms at `k = 0`):

```
                        fixpoint instructions   derived tuples   instr/tuple
  ctadl (strategy hi)              ~0.95 G            ~287 K          3,300
  this engine, k = 0               ~3.3 G              386 K          8,500
```

**~2.6× per tuple.** Some of that is the wider tuple; a good deal of it is
that every column here is `#[derive(Hash)]` over an `Arc<str>`, so an index
probe on `(Proc, AccessPath)` hashes the *contents* of a dex procedure name
plus every field name on the path — often 150+ bytes of string per probe —
where CTADL's `Path` hashes as a pointer (`std::ptr::hash` on the interned
`Seq`) and `FunctionId` is a `u32`. Interning fixes the memory and this at
the same time, which is why it is first on the list at the end.

## Third: the context machinery, ~4.7×

`k = 0` → `k = 1` — one level of call string — on the same program:

```
                    k = 0      k = 1     ratio
  points          224,542  1,061,910      4.7×
  edge             48,354    245,047      5.1×
  pub_points        6,878     41,587      6.0×
  retained       295.3 MiB    1.4 GiB      4.9×
  wall              0.42s      2.07s       4.9×
  resolve             649      1,665       2.6×
```

This is the factor that *is* hybrid inlining, and it is the one the `k`-bound
exists to hold. It is also where the comparison gets interesting, because
CTADL has no `k` and does not pay it.

## Does the extra memory buy better coverage?

Partly, and less than the cost suggests. Two measurements.

**On dispatch, this engine resolves far more than CTADL's HI does.**

```
  this engine, k = 1     critical 473   pending 1,034   resolve 1,665   top 600
  ctadl --strategy hi    critical_summary 2,018   resolvent 17
                         context_assign 57  context_locals 142  context_summary 1
  ctadl --strategy cha   callee_resolvents 11,168 (class hierarchy)   resolvent 0
  ctadl --strategy mixed (default)                                    resolvent 0
```

CTADL's entire context-sensitive layer on this app is **217 tuples**, and with
the default `mixed` strategy it is **empty** — every call is resolved by class
hierarchy analysis and hybrid inlining contributes nothing. This engine mints
1,034 instances and derives 1,665 call edges from them. That is genuinely more
work done on the dispatch problem.

**But 600 of the 1,034 instances end in `top`** — ⊤-summarised, i.e. falling
back to exactly the CHA answer CTADL got for free. So the precise part of the
answer covers ~434 instances, at a cost of 3.9× the memory of the `k = 0` run.

**And end to end, CTADL's cheap path finds more.** Running the same
source/sink model against each index:

```
  ctadl --strategy mixed   40 findings   0.44s   73 MiB
  ctadl --strategy cha     40 findings   0.47s   77 MiB
  ctadl --strategy hi       8 findings   0.24s   61 MiB
```

CTADL's own hybrid inlining, run alone, is *worse* than its CHA on this app —
consistent with `resolvent: 17`. Which is the honest reading of `mixed` being
the default: on Android, CHA is nearly free and nearly right, and hybrid
inlining is worth invoking only where CHA is ambiguous.

**The verdict.** More coverage on one axis, less on three:

| axis | this engine, k = 1 | CTADL |
|---|---|---|
| context-sensitive dispatch | **1,665 edges from 1,034 instances** (600 ⊤) | 17 resolvents; 0 by default |
| exception value flow | none — `rets[1]` dropped | modelled, at 2 return slots per call |
| library / bodyless functions | 1,523 skipped | modelled, 166 propagation models |
| flow sensitivity | none (`ssa: false`) | SSA before codegen |

So the extra memory is not buying coverage in general. It is buying
context-sensitive dispatch specifically, and paying for it with a 48-byte
`Base` and a placeholder in 89% of `points`.

## Why CTADL has no `k` and does not need one

Two mechanisms, neither of which is a depth limit.

**The call string is bounded by acyclicity, not by depth.** `CallString::push`
(`ctadl-ascent/src/facts.rs:331-344`) refuses to push a site whose function is
already on the string. So a string can be as long as the longest *acyclic*
call chain and no longer — finite by construction, with no `k`.

**The instance space is collapsed by a lattice, not truncated.**

```rust
lattice resolvent(FunctionId, FormalIndex, Path, CallTargetObject, SmallestCallString);
```

The call string is a *lattice column*, so the other four columns functionally
determine at most **one** call string per key — the shortest, lexicographically
smallest one. There is no `2^d` of distinct call strings to bound, because
distinct strings reaching the same key join instead of multiplying.

That is the structural difference from `pending(Proc, CritId)` here, which is
one tuple *per call string* and is exactly the `2^d` that `k` exists to cut
off. `hi-complexity.md` already names `k` as "the only thing standing between
this analysis and an exponential"; CTADL's answer is that if the context is a
lattice value rather than a key, there is no exponential to stand in front of.

This is item 5 of `backflash-profile.md`'s "what is left to try" — "merging
instances whose decisive slot has the same points-to set" — and CTADL is a
worked example of it.

## Summary: where the 75× goes

On the core derived relations, `k = 1` against `ctadl --strategy hi`:

| factor | ratio | what it is | is it fixable here? |
|---|---|---|---|
| context machinery | **4.7×** | `k = 0` → `k = 1`; placeholders in 89% of `points` | a lattice-valued context, not a keyed one |
| tuples at equal context | **2.0×** | eager value closure vs. deferred to query | architectural |
| tuple width | **~4×** | 144 B vs 24 B — no symbol interner, 48-byte `Base` | yes, and it is the cheapest win |
| index redundancy | **~2×** | Ascent `HashMap<K,Vec<V>>` per pattern vs. one BYODS store | yes — CTADL measures this at 1.7× |

4.7 x 2.0 x 4 x 2 = 75, against ~75x observed (1.39 GiB of `points`/`edge`/
`pub_points`/`used_ext`/`root_map`/`pub_root` against CTADL's 18.6 MB of
`locals` + `assign_like`). The two right-hand rows are
the "data structures" half and are worth **~8×** together; the two left-hand
rows are the "tuples" half and are worth **~9×**.

## What to do about it, in order

1. **Intern the symbols.** `src/ir.rs:31-34` already anticipates this
   ("swapping in a real interner (`u32` ids) later only touches this macro").
   `Proc`/`Var`/`Field` go 16 B → 4 B, and `AccessPath` follows. CTADL's
   `immortal`/`tailshare` pair is the reference implementation, and `Suffix`
   is already half-interned through the `paths` vocabulary.
2. **Get `CritId` out of `Base`.** A 48-byte base so that 1,034 instances can
   carry a call string is the single worst byte-per-tuple decision in the
   schema. Boxing the `CritSlot`/`CritRet` payload takes `Base` to 16 B and
   `AccessPath` to 32 B — a 2× cut on the two largest relations, for a
   pointer-chase on 0.1% of bases.
3. **`shrink_to_fit` the relations after the fixpoint.** ~142 MiB at `k = 1`,
   free.
4. **Then** consider BYODS. It is worth 1.7–2.3× by CTADL's own measurement,
   and it is much more work than 1–3.

And one that is not about memory at all: **keep `rets[1]`**. Exception flow is
two extra `bind_ret`/`ret` facts per call in a schema that already has both
relations — CTADL gets it for the price of a second return slot and no new
relation. It is the cheapest coverage available here, and on TaintBench apps
it is coverage that matters.

## Reproducing

```sh
OUT=/Volumes/Shampoo/hi-vs-ctadl; mkdir -p $OUT/store/imports
cp -R ~/.local/state/ctadl/imports/backflash.apk $OUT/store/imports/

# CTADL, all three strategies, with the engine's own relation stats
cd ../ctadl-rs
for s in mixed hi cha; do
  RUST_LOG=warn,ctadl_ascent::index_engine=debug /usr/bin/time -l \
    ./target/release/ctadl --store $OUT/store index bf-$s backflash.apk --strategy $s \
    > $OUT/ctadl-$s.log 2>&1
done
grep -E "store estimate|relation increase|hybrid inlining" $OUT/ctadl-*.log

# this engine, context off and context on
cd ../hybrid-inlining-scratchpad
for k in 0 1; do
  /usr/bin/time -l ./target/release/examples/ctadl_profile backflash.apk --k $k --timeout 300 \
    > $OUT/hi-k$k.log 2> $OUT/hi-k$k.time
  ./target/release/examples/ctadl_memory backflash.apk --k $k > $OUT/hi-memory-k$k.log 2>&1
done

# what the million points tuples actually contain
cargo run --features ctadl --release --example ptval_split -- backflash.apk --k 1
```

`examples/ptval_split.rs` is new and is the only file this comparison added:
it runs the ordinary `HybridAnalysis` and splits `points` by `PtVal` variant
and by whether the tuple mentions a `CritSlot`/`CritRet` base.
