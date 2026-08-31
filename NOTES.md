# Summary


**Pending**: Critical statements start off in `crit_origin`. That's how they enter `pending`. They
have a `CritId` that holds the critical statement and a stack (initially empty). Calls to `pending`
procs are also put into pending (if they obey the k-limit), pushing into the Id's stack. Resolving
calls enables `pending` entries: if a callee is pending and we resolve a call to it, then add a new
pending entry with the nested stack.

**Publishing**:
`Base` are variables
`pub_edge` used to contain the data flow summary edges; it is de-tabulated now, and
`HybridAnalysis::pub_edges()` recomputes it from `points` + `pub_root` for reporting
- `pub_root` has formals/ret plus "p


- `uncalled(p)` is only the statically uncalled things; how is this used?
- `edge` is intraprocedural constraints `sub ⊇ sub`. It is interesting because it gets edges
  depending on the critical statements as well; edges to actuals, for example. edge gets
  instantiated based on calls and published edges after substitution into the calling context.
- `can_propagate` is $k$-limited

## Questions

- What are "placeholder nodes", like used in `pub_root`. `CritSlot` and `CritRet`
- Change comments for `resolve`



Critical statement at the call site gets put into `pending`. It is associated with the procedure,
like a summary. It's just the `S` of the hybrid summary.
