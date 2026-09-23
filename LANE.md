# Lane H5: runtime_error, longjmp/setjmp, exit, the abort landing

Branch `lane-h5` (from `hub/iris-main`), pushed to `hub`. Design: `VsaIris/INTERP_DESIGN.md`
§4.2, §4.4, §9 H5; statement changes in §10 "STATEMENT CHANGES (H5)", open questions Q6/Q7.

## Done (all in `lake build VsaIris`, axioms ⊆ {propext, Classical.choice, Quot.sound})

- **`IrisHoles.newlib` is exact** (`VsaIris/Vsa/Newlib.lean`): `NewlibHoles := ∃ Ierr,
  NewlibHolesAt Ierr` with fields `snprintf`, `fprintf` (`%s`/`%d` formats, `FmtArgsOK`),
  `fwrite` (the out-of-memory message) and `exitHandlers` (`exit`'s newlib interior). Every field
  is an Iris statement for both WPs. `HOLES.md` rows match; `scripts/check_iris_holes.py` now
  reads the skeleton's `IrisHoles`, follows `∃`-defs, and reports `alloc : True` as a placeholder.
- **newlib's runtime data is owned** (`Vsa/Stdio.lean`, `Vsa/StdioRead.lean`): `stdioFoot` (every
  `.data`/`.bss` byte outside the allocator's globals, `Newlib.stdioFoot_off_alloc`), `StdioOK`
  (VSA's `ConsoleStream` + `ExitRuntimeData` + the `stderr` pointer), `stdioOwn`; `world` carries
  it. `StdioOK.impure`/`.stderr` read words off the image; `stdioAt_open`/`_close`.
- **`struct Interp` repaired** (`Interp/Repr.lean`): the `jmp_buf` is 208 bytes, `err_msg` is at
  `in+224`; `err_msg` is a parameter (`interpCoreE`/`interpCtxE`/`worldE`, `errAny`/`errStr`).
- **`exit(e)` halts with code `e`** (`Vsa/Exit.lean`, `wp_exitCall`), for either WP: prologue and
  `_exit` segments, the `exitHandlers` hole, `jal _exit`, F2's `wp_exitW`.
- **`main`'s error line then `exit(70)`** (`Vsa/MainErr.lean`, `wp_mainErrTail`): `bnez`, the
  stdio loads, `fprintf(stderr, "%s\n", in->err_msg)` through the hole, `main`'s epilogue, `crt0`'s
  `j exit`, `wp_exitCall` at `main`'s stack top.
- **Reusable layer**: `JalSite` (one descriptor + decided `Cert` → `JalExec`), `binImg` +
  `instrAt_of_binImg` (code from the persistent image, one `decide`), `SegImg` (owned images as
  segment footprints, `ldFact`, `bytesVal_imgWord`), `scripts/gen_h5_sites.py` +
  `scripts/h5_sites.tsv` (code lists, `Loaded` predicates and `_at_` pins for `chain_facts`, jal
  sites).

## In flight

- The landing: `interp_run`'s `setjmp` return (`0x80004428`, `a0 = 1`) → epilogue → `main`
  (`wp_mainErrTail`), and `abortCore` (landing registers from the `jmp_buf`, or `exit(1)`'s entry).
- `runtime_error` + `longjmp` as a `fnSpecAbort` with abort resource `abortRes`.
- The out-of-memory block (`fwrite` → `exit(1)`), one descriptor per inlined `xmalloc` site.

## Findings

- `jmp_buf`/`err_msg` offsets were wrong in `Interp/Repr.lean` (fixed, INTERP_DESIGN §10).
- `stderr` output is console output (`_write` ignores the descriptor): VSA's
  `FprintfStderrNeutral` is false.
- The out-of-memory path is `fwrite` + `exit(1)`.
- **Q6**: the boundary does not pin `_impure_data._stderr`, which `main`'s error line loads.
- **Q7**: `runtime_error` + `snprintf` need 1152+ bytes of stack; the budget's leaf headroom at the
  deepest call is 1088.
- `exit`'s newlib interior may use only `err_msg` below `main`'s frame (the rest of
  `struct Interp` is read-only): `exitHandlersNeed = 256` (measured 240).

## Holes

`newlib.snprintf`, `newlib.fprintf`, `newlib.fwrite`, `newlib.exitHandlers` (see `VsaIris/HOLES.md`).
