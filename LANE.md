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
  `outSpec_of_run` (data view indexed by an opened image) + `outEnd_of`.
- `__sfvwrite_r` unbuffered path: `sfvwrite_run` (`Vsa/Stdout/Sfvwrite.lean`), shared with N3/N5.
- **`out.fwrite` proved**: `Sym.fwrite_out` (`Vsa/Stdout/StrOut.lean`, over `fwrite_run`).
- Leaf calls inside symbolic runs: `LocalRun.frame`/`swpo_leaf` (`Vsa/SymLeaf.lean`);
  `swpo_strlen` (`Vsa/Stdout/Strlen.lean`) splices `StrLeaf.strlenRunL`.
- **`out.fputs` proved**: `Sym.fputs_out` (`Vsa/Stdout/StrOut.lean`, over `fputs_run`); string
  arguments opened once by `strView_open` (`StrView`).

## Holes
- All of lane N1's holes are proved (`out.fputs`, `out.fputc`, `out.fwrite`); `out.fprintf` is N5's.
