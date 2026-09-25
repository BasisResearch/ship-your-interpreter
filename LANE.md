# Lane N3: newlib stderr holes (`newlib.fprintf`, `newlib.fwrite`)

Branch `lane-n3`. `newlib.exitHandlers` moved to lane N4 (parent, 2026-09-25). Merged `hub/lane-n4` at `52b1e9d` (exitHandlers proved; exit takes errno) and `hub/lane-n5` at `4423d4b`.
Merged
`hub/iris-main` at `286c2ad` and `hub/lane-n1` at `34fe574` (errno lending, `outSpec`, `sfvwrite_run`).

## Status

- **`newlib.fwrite`: proved** (`Newlib.fwrite_proved`, `VsaIris/Vsa/Stderr/FwriteSpec.lean`;
  axioms `propext, Classical.choice, Quot.sound`). HOLES row and `NewlibHolesAt.fwrite`
  removed; `Oom.wp_oomBlock` consumes the theorem. Statement changes: INTERP_DESIGN.md §10
  "STATEMENT CHANGES (N3)".
- **`newlib.fprintf`: proved** (`Newlib.fprintf_proved`, `fprintf_ok`,
  `VsaIris/Vsa/Stderr/FprintfSpec.lean`; axioms `propext, Classical.choice, Quot.sound`).
  The run: `fprintfHead_run` (prologue, `vfpEntry_run`, `vfpErr_run`, `vfp_head` → `FprLoop`),
  `FprintfBody` (`fpr_s`: `%s` staged and flushed or empty; `fpr_nl`: `"\n"`; `fpr_end`: the
  last flush, `vfp_end`, the epilogue; `FprMid` carries `stderr`, the spills and the frame).
  The owned string enters the data view through `LRO.promote`. HOLES row removed; the field
  moved from the assumed `NewlibCoreAt` to `NewlibHolesAt.fprintf : FprintfProved`, which
  `NewlibCore.full` takes from `Supply`/`EndToEnd` (the proof imports N5's loop, above
  `MainErr`). Statement changes: INTERP_DESIGN.md §10 "STATEMENT CHANGES (N3)".
- Both N3 holes are discharged.
- Tooling note: core `omega` hits "maximum recursion depth" on goals with a Nat
  subtraction such as `a < P - 256` (even pure Nat, no imports). Use
  `Nat.lt_sub_of_add_lt` / `Nat.add_lt_of_lt_sub`, or split the disjunction first.

## Findings (checked against `experiments/disasm.txt`)

1. `fprintf(stderr, …)` does not reach `__sbprintf`: `stderr` is `__SRW|__SNBF` (`0x12`), so
   after `__swsetup_r` the test `(flags & 0x1a) == 0x0a` (`0x8000abe8`) fails. The path is
   `_vfprintf_r` → `__sprint_r` → `__sfvwrite_r` → `__swrite` → `_write_r` → `_write`.
2. `errno` (`0x8001ba08`) is written by `_write_r`/`_fstat_r`/`_close_r`: the stderr/exit specs
   own it (`Stdio.errnoOwn`, N1's definition).
3. `StdioOK` pins `stderr`'s `_bf._base`/`_write` (`StderrStream`, N3) and the locale
   (`LocaleData`, N2).
4. `%s` calls word-at-a-time `strlen` (`0x8000cfc8`): up to 7 bytes past the NUL, outside
   `FmtArgsOK`'s coverage: `fprintfSpec` owns the buffer, its over-read in RAM off tohost.
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

- Nothing left in N3's scope.
