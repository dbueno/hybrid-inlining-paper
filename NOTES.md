# Summary


Critical statements start off in `crit_origin`. That's how they enter `pending`.
Calls to `pending` procs are also put into pending (if they obey the k-limit).
If a call from `p` to `callee` is resolved, and `callee` was pending, then `p` is marked pending with the nested id.

- `uncalled(p)` is only the statically uncalled things; how is this used?
- `edge` is intraprocedural constraints `sub ⊇ sub`. It is interesting because it gets edges
  depending on the critical statements as well; edges to actuals, for example. edge gets
  instantiated based on calls and published edges after substitution into the calling context.
- `can_propagate` is $k$-limited
- `pub_edge` contains data flow summary edges
- `pub_root` has formals/ret plus "p

## Questions

- What are "placeholder nodes", like used in `pub_root`. `CritSlot` and `CritRet`
- Change comments for `resolve`



Critical statement at the call site gets put into `pending`. It is associated with the procedure,
like a summary. It's just the `S` of the hybrid summary.
