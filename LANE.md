# Lane N1: newlib stdout holes (`out.fputs`, `out.fputc`, `out.fwrite`, `out.fprintf`)

Branch `lane-n1` (from `hub/iris-main`). Brief: `~/lane-n1-aws.md`.

## Done
- `VsaIris/LocalRunO.lean`: printing local runs. `SegFromO` (a segment that may print), `LRO`
  (least fixed point, impredicative: no uniform fuel), `wp_lroW` (either WP, console cell in the
  footprint), `lro_of_localRun` (silent `LocalRun`s embed), `segFromO_of_runFactO`.
- `VsaIris/Vsa/SymRunO.lean`: `SWPO` = `SWP` ending in `LRO`; `swp_putc` (one `tohost` putchar
  store inside a symbolic run), `swpo_run`, `swpo_done`.

## In flight
- Step table for newlib's stdio code (generator shared with `gen_interp_steps.py`).

## Findings
- `_write_r` stores `errno = 0` (`0x8001ba08`), an allocator global (`VsaHeap.allocGlobal`),
  not in `stdioFoot`. Every stdout/stderr write path needs it owned; the hole statements
  (`outSpec`, H5's `fprintfSpec`/`fwriteSpec`/`exitHandlersSpec`) own only `stdioOwn`.

## Holes
- Unchanged so far: `out.fputs`, `out.fputc`, `out.fwrite`, `out.fprintf` (mine).

## Next
- The shared chain `__swrite → _write_r → _write` (n bytes), then `_fflush_r`/`__sflush_r`,
  `__swbuf_r`, `_putc_r`, `fputc`.
