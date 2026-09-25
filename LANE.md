# Lane N3: newlib stderr and exit holes (`newlib.fprintf`, `newlib.fwrite`, `newlib.exitHandlers`)

Branch `lane-n3` (from `hub/iris-main` `05874b5`). Status: in flight.

## Findings (machine-checked against `experiments/disasm.txt`; relevant to N1/N2)

1. **`fprintf(stderr, …)` does not reach `__sbprintf`.** `stderr`'s flags are `__SRW|__SNBF`
   (`0x12`, `ExitIdleFile`). `__swsetup_r` sets `__SWR` but keeps `__SRW`, so `_vfprintf_r`'s
   test `(flags & 0x1a) == 0x0a` (`0x8000abe8`) fails. The path is `_vfprintf_r` → `__sprint_r`
   → `__sfvwrite_r` → `__swrite` → `_write_r` → `_write` (one `_vfprintf_r` frame).
2. **`errno` (`0x8001ba08`) is written by every syscall wrapper** (`_write_r`, `_fstat_r`,
   `_close_r`, `_lseek_r`: `sw zero,1272(gp)`). It is an allocator global (`allocGlobal`,
   `_sbrk_r` writes it too), not in `stdioFoot`. No stdio spec that only owns `stdioOwn` is
   provable; the specs must own the `errno` word (N3 adds `errnoOwn`, split from `heapRes`).
3. **`StdioOK` does not pin what the stderr path reads**: `stderr->_bf._base` (+24), `_write`
   (+64), and `__global_locale`'s `mbtowc` slot (`0x8001b880`), `_localeconv_r`'s
   decimal-point string, `__locale_mb_cur_max`. These need a boundary field (standing rule:
   `BootHeapFacts` field with a control witness).
4. **`%s` calls word-at-a-time `strlen`** (`0x8000cfc8`), which reads up to 7 bytes past the NUL.
   `FmtArgsOK` covers only the string and its NUL.

## Plan

- `VsaIris/Vsa/SymOut.lean`: a local run that may print (`LocalRunO`, `wp_localRunOW`), its
  symbolic form `SWPO`, and `swpo_of_swp` (every silent `SWP` step lemma is reused inside a
  printing run), `swpo_putc` (`_write`'s `tohost` store), `swp_jalr` (indirect calls).
- `scripts/gen_interp_steps.py --target newlib`: the newlib step table (`nt_<pc>`).
- `exitHandlers` first, then `fwrite` (shared `__sfvwrite_r`/`_write` with N1), then `fprintf`.
