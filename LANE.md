# Lane N5: `out.fprintf` (`fprintf(stdout, fmt, arg)`)

Branch `lane-n5` (from `hub/iris-main` `286c2ad`; merged N1's `lane-n1` at `44f04ed`).
Brief: `~/lane-n5-aws.md`. Hole: `out.fprintf` (`VsaIris/HOLES.md`, `NewlibOut.OutHoles.fprintf`).

## The path (checked against `experiments/disasm.txt`)

`fprintf` → `_vfprintf_r(reent, stdout)`: `stdout`'s flags are `0x200a`
(`__SORD|__SWR|__SNBF`), so `(flags & 0x1a) == 0x0a` holds and it hands the format to
`__sbprintf` (`0x8000ac20`). `__sbprintf` builds a stack `FILE` at `sp+24` (flags
`0x2008`, fully buffered, 1024-byte buffer at `sp+208`, `_cookie`/`_write` copied from
`stdout`: `__swrite` on `stdout`), runs `_vfprintf_r` on it, then `_fflush_r` on it.
The inner `_vfprintf_r` prints through `__sprint_r` → `__sfvwrite_r` (fully buffered
branch: `memmove` into the buffer, `_fflush_r` when it fills, a direct `__swrite` of
`len - len % 1024` bytes when the buffer is empty and `len ≥ 1024`, via `__moddi3`).
`%lld` digits: `__hidden___udivdi3`/`__umoddi3`. `%s`: `strlen`.

## Done

- Step table: N1's `--table stdio` extended with `fprintf`, `_vfprintf_r`, `__sbprintf`,
  `__sprint_r`, `__sfvwrite_r`, `memmove`, the locale leaves, `strlen`, `memset`, the
  lock init/close stubs; `jr` with an offset (`memset`'s computed jump, N2's `jri`).
  Decode: N3's `Batch18` (unchanged copy) + `Batch19` (`__sbprintf`'s four `jal` words).
- `VsaIris/Vsa/SymBridge.lean`: `swpo_bridge`, a continuation-form run proved over
  another step table (E2's `udiv_iw`/`moddi3_iw` over the interpreter's) used inside a
  run over `stdioText` (`swp_text_mono`, `mem_dataOf`: the other table's code in the
  data view).

- `VsaIris/Vsa/Fprintf/`: `Move.lean` (`memmove_run`: every forward path), `Flush.lean`
  (`fflushF_run`/`fflushF_run0`: `_fflush_r` on `__sbprintf`'s stack FILE, fully buffered),
  `Arith.lean` (`moddi3_sw`, `udiv_sw`: E2's `ProofArith` runs bridged into stdio runs),
  `SbFile.lean` (`SbFile`, `Frame`, `nx_mem` through `fillR`), `Sfv.lean` (the passes),
  `SfvLoop.lean` (`sfv_loop`: `__sfvwrite_r`'s loop on the stack FILE, any iovs, any lengths;
  `pend0 ++ ALL = printed ++ pend'`).
- Tactics (`Fprintf/Tac.lean`): `nx_flat` (fresh register file + facts), `nf_run`, `nf_go`.
  Lesson: `try`/`first` do NOT catch heartbeat/recursion exceptions; a side goal that falls
  through to `sx_side`'s `decide` on a symbolic BitVec kills the run. Give every pointer bounds.

## For N1 / N3 (shared layer)

- I add functions to `STDIO_FUNCS` (list above) and nothing else in N1's files so far.
  N3 needs `_vfprintf_r`/`__sprint_r`/`__sfvwrite_r` too: they are in the table now.
- `sflush_run` pins `f = stdout` (`hfS`); `__sbprintf`'s stack `FILE` needs it for any
  `f` whose cookie is `stdout`. I will generalize it (N1: shout if you are on it).
- errno: I rely on `outS` (which owns `errno`) like N1; the `outSpec` statement change
  (add `errnoOwn`) is N1's to make for all four `out.*` holes.

## Holes

- `out.fprintf`: still ledgered.

## Next

- Inner `_vfprintf_r` runs for `"%lld"`, `"<fn %s>"`, `"<native fn %s>"`; `__sfvwrite_r`
  on the stack `FILE` (buffer invariant: printed ++ pending = consumed); `__sbprintf`;
  the outer call; the Iris wrapper.
