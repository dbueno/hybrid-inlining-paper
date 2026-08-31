# Hybrid Inlining in Datalog

AI-assisted reproduction of the Hybrid Inlining paper[^1], implemented in Datalog.

[^1]: Jiangchao Liu, Jierui Liu, Peng Di, Diyu Wu, Hengjie Zheng, Alex X. Liu, Jingling Xue: Hybrid Inlining: A Framework for Compositional and Context-Sensitive Static Analysis. ISSTA 2023: 114-126

## The access-path bound

The paper's abstract domain is access paths of unbounded length, and closing a
field-sensitive analysis over it has no fixpoint on real code: suffix
congruence feeds its own premise, so one cycle in the constraint graph
generates paths forever. `backflash-profile.md` is that failure measured.

So the analysis takes its access-path vocabulary as an input. `paths` is an EDB
relation — a set of admissible accessor sequences, fixed before the fixpoint
starts — and every path a rule constructs is tested against it before entering
`edge` or `points`. The EDB knows nothing about where the set comes from; a
front end may supply one, and `src/path_bound.rs` computes the default from the
program's own syntax: the suffixes its statements spell out, concatenated along
local data flow, which is finite because a concatenation step always moves
backward through the statement order.

The bound is a precision knob and the module documents which precision it
gives up. On `backflash.apk` the whole 41,143-statement program has a
vocabulary of 736 suffixes and the analysis converges in 0.55 seconds.

## Analyzing real code

The `ctadl` feature adds a front end (`src/ctadl.rs`) that reads the IR
[CTADL](../ctadl-rs) caches when it imports an artifact — dex/APK, JVM, Ghidra
pcode, Lua, C — and translates it into this crate's EDB. It depends on
`ctadl-ir` alone, and on the IR that `ctadl import` already wrote to disk; none
of CTADL's own Datalog codegen is involved.

```sh
ctadl import --name app app.apk                       # once, in ../ctadl-rs
cargo run --features ctadl --release --example ctadl_import -- app
cargo run --features ctadl --release --example ctadl_import -- app --run --k 2
```

Before translating, the front end runs the same four IR passes `ctadl index`
runs — dead-temporary elimination, copy coalescing, SSA, copy propagation. That
is the default because it is worth 3.7× in time and 3.9× in memory at `k = 1`
on `backflash.apk`, for no lost dispatch precision; `ctadl-comparison.md`
measures it. `--no-preprocess` turns them off and translates the IR exactly as
`ctadl import` cached it.

The feature is off by default because `ctadl-ir` pulls in arrow and parquet;
without it the crate still builds in seconds.

See the module docs for the mapping, and for the four places the two IRs
disagree — multiple returns, by-reference parameters, statement identity, and
what counts as an entry.
