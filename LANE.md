# Lane N3: newlib stderr holes (`newlib.fprintf`, `newlib.fwrite`)

Branch `lane-n3`. `newlib.exitHandlers` moved to lane N4 (parent, 2026-09-25). Merged `hub/lane-n4` at `52b1e9d` (exitHandlers proved; exit takes errno) and `hub/lane-n5` at `88e8da1`.
Merged
`hub/iris-main` at `286c2ad` and `hub/lane-n1` at `34fe574` (errno lending, `outSpec`, `sfvwrite_run`).

## Status

- **`newlib.fwrite`: proved** (`Newlib.fwrite_proved`, `VsaIris/Vsa/Stderr/FwriteSpec.lean`;
  axioms `propext, Classical.choice, Quot.sound`). HOLES row and `NewlibHolesAt.fwrite`
  removed; `Oom.wp_oomBlock` consumes the theorem. Statement changes: INTERP_DESIGN.md §10
  "STATEMENT CHANGES (N3)".
- **`newlib.fprintf`**: statement narrowed to `main`'s only call (INTERP_DESIGN N3), consumers
  rewired (errno lent from the dropped world). Run pieces proved: `vfpEntry_run` (shared with N5),
  `vfpErr_run` (stderr setup via `swsetupErr_run`), `sprintErr_run` (the unbuffered
  one-piece flush; `_vfprintf_r` flushes after each conversion and at the end), `sprintErr_hook` +
  `SprintPost.printRet` (N5's `vfp_printH` hook for stderr, empty piece included), `LRO.promote` (owned string through the data view). Waiting on N5's
  format-loop pieces (`vfp_head` landed; `%s` with a strlen hook and the end next), then the
  fprintf prologue/epilogue glue and the Iris wrapper.

## Findings (checked against `experiments/disasm.txt`)

1. `fprintf(stderr, …)` does not reach `__sbprintf`: `stderr` is `__SRW|__SNBF` (`0x12`), so
   after `__swsetup_r` the test `(flags & 0x1a) == 0x0a` (`0x8000abe8`) fails. The path is
   `_vfprintf_r` → `__sprint_r` → `__sfvwrite_r` → `__swrite` → `_write_r` → `_write`.
2. `errno` (`0x8001ba08`) is written by `_write_r`/`_fstat_r`/`_close_r`: the stderr/exit specs
   own it (`Stdio.errnoOwn`, N1's definition).
3. `StdioOK` pins `stderr`'s `_bf._base`/`_write` (`StderrStream`, N3) and the locale
   (`LocaleData`, N2).
4. `%s` calls word-at-a-time `strlen` (`0x8000cfc8`): up to 7 bytes past the NUL, outside
   `FmtArgsOK`'s coverage (to be handled by havoc loads or a statement change).
5. The state after one `stderr` write is `StdioErrOK` (flags `0x201a`, `_p = _bf._base =
   stderr + 119`; `StdioErr.lean`, `stdioErrOK_of_write`).

## For N1

- Merging your layer: `StdioOK.written` now also transports `LocaleData`/`StderrStream`
  (five conjuncts). Your hand-edited `Case/CallArmP`, `CallPrintT`, `CallPrintlnT` (`hEL`)
  were not in the templates; I added `hEL` to `callArm_P.lean`/`callOut_T.lean` so
  `gen_iris_cases.py` reproduces them (stage a3 was stale).
- Merged your `34fe574` (scoped stdout `sx_side` rules): my stderr rule is scoped the same way
  (`Stderr/Swrite.lean`). `Tac.lean` keeps your version plus `nx_runB` (`nxRunCore … budgetPct`,
  budgeted `#ix_piece` runs); `ITac.ixPre` holds the candidate prefixes (with your `itS…`).
  The stdio table adds `__swsetup_r`, `__smakebuf_r`, `__swhatbuf_r`, `_fstat_r`, `_fstat`,
  `memset`, `__hidden___udivdi3` (stderr's first write).
- `errS` is gone: stderr runs use your `outS` and the `impDt`-style data view
  (`_impure_ptr` from `Dt`).

## For N4 (`exitHandlers`)

- `Abort.oomCore` now carries `errnoOwn` (the OOM `fwrite` borrowed it); `wp_abortOom` drops
  it until `exitHandlersSpec` takes it (the close path writes `errno`).
- `StdioErrOK`, `CloseReady`, `CloseCommon` in `StdioErr.lean`; the old exit run is at
  commit `0e15f23` (`ExitRun.lean`, `gen_exit_run.py`).

## Next

- `newlib.fprintf`: `_vfprintf_r` format loop (`%s`, `%d`) on the stderr path; `errnoOwn` in
  `fprintfSpec`; the `strlen` over-read; memset's `jr` (no step lemma at `0x80006b38`).
