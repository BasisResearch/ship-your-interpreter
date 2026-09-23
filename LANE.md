# Lane H5: runtime_error, longjmp/setjmp, exit, the abort landing

Branch `lane-h5` (from `hub/iris-main`), pushed to `hub`. Design: `VsaIris/INTERP_DESIGN.md`
§4.2, §4.4, §9 H5.

## Plan

1. Repair `interpCore` (the `jmp_buf` is 208 bytes, `err_msg` is at `in+224`); give the
   `world` the newlib stdio state `stdioOwn` (VSA's `ConsoleStream` + `ExitRuntimeData`).
2. `IrisHoles.newlib`: exact Iris statements of `snprintf`, `fprintf`, `fwrite` and the
   newlib interior of `exit` (`__call_exitprocs`, `stdio_exit_handler`), with `HOLES.md` rows.
3. `abortCore`: the `longjmp` landing (registers from the `jmp_buf`) or an out-of-memory
   block head; `abortRes = abortAt abortCore`.
4. The exit chain: `exit(e)` → `_exit` → `wp_exitW`, for either WP and any `e`.
5. The landing: `interp_run`'s `setjmp` return → `main`'s `fprintf` → `exit(70)`; the
   out-of-memory block → `fwrite` → `exit(1)`.
6. `runtime_error` + `longjmp` as a `fnSpecAbort` whose abort branch is `abortRes`.

## Findings

- `interpErrOff`/`interpJmpLen` in `Interp/Repr.lean` were wrong: newlib's riscv `jmp_buf`
  is 26 words (`[in+16, in+224)`), `err_msg` is at `in+224` (`runtime_error`:
  `addi a0,s0,224`; `main`: `addi a2,sp,496` with `in = sp+272`).
- `fprintf(stderr, …)` prints to the console: `_write` ignores the descriptor and stores to
  `tohost`. VSA's `FprintfStderrNeutral` (output unchanged) is false; the Iris holes let the
  error path print.
- The out-of-memory path is `fwrite(msg, 1, 14, stderr)` then `exit(1)`, not `fprintf`.

## Holes

None yet.
