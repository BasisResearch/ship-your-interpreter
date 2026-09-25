# IrisHoles ledger

Every assumption left in the Iris route is a field of `structure IrisHoles` and has a row here. `scripts/check_iris_holes.py` checks the two agree. A hole is discharged by proving the field and deleting both the field and its row in the same commit.

| field | what it assumes | owner | satisfiability evidence | discharge plan |
|---|---|---|---|---|
| `newlib.snprintf` | `snprintf(dst, n, fmt, a3…a7)` with `0 < n < 2^31` and a `%s`/`%d` format (`FmtArgsOK`) writes a NUL-terminated string into `dst[0,n)`, keeps `stdioOwn`, prints nothing, returns with the ABI frame, in 1024 bytes of stack (`Newlib.snprintfSpec`) | H5; scheduled after E1–E6 (user, Q4) | proved for an aligned return address, stack/destination above newlib's data and readable bytes in RAM (`Sym.snprintf_gen`, `Vsa/SnpGen.lean`); consumers lack the RAM bound on shared strings and `rtErr_spec` lacks the stack/`Sro` bounds (PROOF_CLOSURE_PLAN.md, lane N2) | narrow the statement to `snprintf_gen`'s premises; supply them at `rtErr_spec`, `cloArityTail`, `wp_topAbrupt` (shared-view RAM bound at the boundary) |
