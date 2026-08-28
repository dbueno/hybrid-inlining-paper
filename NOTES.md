- `uncalled(p)` is only the statically uncalled things; how is this used?
- `pub_edge` contains data flow summary edges
- `edge` is intraprocedural constraints `sub ⊇ sub`. It is interesting because it gets edges
  depending on the critical statements as well; edges to actuals, for example.
- `can_propagate` is $k$-limited


Critical statement at the call site gets put into `pending`. It is associated with the procedure,
like a summary. It's just the `S` of the hybrid summary.
