# Summary

- `uncalled(p)` is only the statically uncalled things; how is this used?
- `edge` is intraprocedural constraints `sub ⊇ sub`. It is interesting because it gets edges
  depending on the critical statements as well; edges to actuals, for example. edge gets
  instantiated based on calls and published edges after substitution into the calling context.
- `can_propagate` is $k$-limited
- `pub_edge` contains data flow summary edges
- `pub_root` has formals/ret plus "p

## Questions

- What are "placeholder nodes", like used in `pub_root`.



Critical statement at the call site gets put into `pending`. It is associated with the procedure,
like a summary. It's just the `S` of the hybrid summary.
