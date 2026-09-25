# Lane N1: newlib stdout holes (`out.fputs`, `out.fputc`, `out.fwrite`)

Branch `lane-n1` (from `hub/iris-main`). Brief: `~/lane-n1-aws.md`. `out.fprintf` moved to N5.

## Done
- Printing local runs: `LocalRunO.lean` (`SegFromO`, `LRO`, `wp_lroW`), `Vsa/SymRunO.lean`
  (`SWPO`, `swp_putc`), `Vsa/SymJalr.lean` (`swp_jalr`).
- Stdio step table (`scripts/gen_interp_steps.py --table stdio` → `Vsa/Stdout/Steps`), driver
  `nx_run`/`#nx_chain` (`Vsa/Stdout/Tac.lean`; its `sx_side` rules are scoped:
  `open scoped VsaIris.Sym.Stdout`), abstract memory posts (`MemKeep`, `nx_mem_keep`).
- Shared chain summaries: `write_run'` (`_write`), `swrite_run` (`__swrite`/`_write_r`),
  `sflush_run`, `fflush_run`, `swbuf_run'`, `fputc_run`.
- Statement changes (INTERP_DESIGN N1): stdout calls borrow `errno` (`stdioW`), aligned
  return address, stack above `.bss` for proved out-holes.
- **`out.fputc` proved**: `Sym.fputc_out` (`Vsa/Stdout/OutSpec.lean`); generic Iris wrapper
  `outSpec_of_run` + end-state lemma `outEnd_of` for the remaining stdout calls.

## Holes
- Remaining (mine): `out.fputs`, `out.fwrite`.

## Next
- Extend the stdio table with `fputs`/`_fputs_r`/`__sfvwrite_r`/`fwrite`/`_fwrite_r`; prove
  `__sfvwrite_r`'s unbuffered path (loop of `__swrite` chunks); wrappers via `outSpec_of_run`.
