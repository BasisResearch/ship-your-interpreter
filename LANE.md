# Lane H5: runtime_error, longjmp/setjmp, exit, the abort landing

Branch `lane-h5` (from `hub/iris-main`), pushed to `hub`. Design: `VsaIris/INTERP_DESIGN.md`
§4.2, §4.4, §9 H5; statement changes in §10 "STATEMENT CHANGES (H5)", open questions Q6/Q7.
All in `lake build VsaIris`; axioms ⊆ {propext, Classical.choice, Quot.sound} (`VsaIris/Audit.lean`).

## Interface for other lanes

- **The abort resource** (`VsaIris/Interp/Abort.lean`): `abortRes N L Room inp s n =
  abortAt (abortCore … s n) s n`, `abortCore s n = landingCore ∨ oomCore s n`.
  - A child's abort widens to its caller's core: `abortRes_widen` (then F3's `wp_callArmAbort` at
    `Core := abortCore … s n`, through `fnSpecAbort_mono`).
  - **The continuation**: `wp_abort` — at `interp_run`'s `jal exec_stmt` (`sp = sM - 176`),
    `abortRes` plus `interp_run`'s own frame, the `jmp_buf` it wrote and `main`'s saved pair
    (`TopLanding`) end the run with exit code 70 (landing) or 1 (out of memory), for either WP.
    With `Φ := fun v => ⌜v.1 ≠ 0⌝` and `Inst.vsa_adequacyP_nonzero`: `Halts c out e ∧ e ≠ 0`.
- **Error arms** (E1–E6): `RtErr.rtErr_spec` — `runtime_error(in, line, fmt, a1, a2)` as a
  `fnSpecAbort` with an empty return branch and abort resource `abortRes s rtErrNeed`
  (`rtErrNeed = 1248`). Needs `FmtArgsOK` for `fmt`/`a1`/`a2`, the `jmp_buf` read-only
  (`jmpRO`), the world, every callee-saved register.
- **Out-of-memory arms** (H1 `env_new`/`env_define`, H2 `stringify`): `Oom.wp_oomBlock` with the
  generated `OomSites.oom80002a38_ok` (env_new), `oom80002bd0_ok` (env_define),
  `oom80003140_ok` (stringify). From the block head with the site's whole region `[s - n, s)`
  (`OomBlockSp`: 768 bytes below `sp`), it hands the caller's continuation `abortRes s n`.
- **Exits**: `Exit.wp_exitCall` (`exit(e)` halts with `e`, any WP — `term_sim`'s `exit(0)` too),
  `MainErr.wp_mainErrTail` (`main`'s error line → `exit(70)`), `Landing.wp_landing`
  (`setjmp` return → `interp_run` returns 1 → `main`).
- **newlib's runtime data**: `Stdio.stdioOwn` is in `world`; `StdioOK` = VSA's `ConsoleStream` +
  `ExitRuntimeData` + the `stderr` pointer (Q6). `StdioRead`: `StdioOK.impure`/`.stderr`,
  `stdioAt_open`/`_close`.
- **Reusable layer**: `JalSite` (+ `Cert` → `JalExec`), `binImg`/`instrAt_of_binImg`/`TextAt`,
  `SegImg` (`ldFact`, `bytesVal_imgWord`, `ownImg_range`, `blockOwn_of_W`), `SegRO`
  (`wp_segRW`: segments reading `gp` read-only), `AluStep` (`wp_aluA0W`: an observed ALU step,
  e.g. `sltiu`), `scripts/gen_h5_sites.py` + `scripts/h5_sites.tsv` (code lists with `Loaded`
  predicates and `_at_` pins for `chain_facts`, jal sites, `oom` instances).

## Holes (`VsaIris/HOLES.md`, `IrisHoles.newlib`)

`newlib.snprintf`, `newlib.fprintf`, `newlib.fwrite`, `newlib.exitHandlers`: exact Iris statements
(`VsaIris/Vsa/Newlib.lean`), `NewlibHoles := ∃ Ierr, NewlibHolesAt Ierr`.

## Findings

- `jmp_buf`/`err_msg` offsets in `Interp/Repr.lean` were wrong (208-byte `jmp_buf`, `err_msg` at
  `in+224`); fixed.
- `stderr` output is console output (`_write` ignores the descriptor): VSA's
  `FprintfStderrNeutral` is false.
- The out-of-memory path is `fwrite` + `exit(1)`, not `fprintf`.
- **Q6** (needs the user): the boundary does not pin `_impure_data._stderr`.
- **Q7** (needs the user): `runtime_error` + `snprintf` need 1152+ bytes of stack; the budget's
  leaf headroom at the deepest call is 1088.
- `exit`'s newlib interior may use only `err_msg` below `main`'s frame: `exitHandlersNeed = 256`.
- `abortCore` depends on the site's region (the out-of-memory `exit` must fit inside it).

## Next

- `setjmp` (`0x80006ffc`) spec for `interp_run`'s prologue (the `jmp_buf` image `TopLanding`
  names).
- `eval_expr`'s `fn`-arm out-of-memory block (`0x80003e28`, two spills interleaved).
- Discharge `newlib.exitHandlers`' `__call_exitprocs` half (20 straight-line instructions with
  `__atexit = 0`).
