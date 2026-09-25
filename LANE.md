# Lane N5: newlib hole `out.fprintf` (`fprintf(stdout, fmt, arg)`)

Branch `lane-n5`. Formats: `"%lld"` (`0x800192c0`), `"<fn %s>"` (`0x800192c8`),
`"<native fn %s>"` (`0x800192d8`); stack need `fprintfNeed` = 4096. Merges `hub/lane-n3`
(one stdio step table for N1/N3/N5, scoped stdout `sx_side` rules, `vfpEntry_run`).
(LANE.md is per lane: after merging another lane's branch, keep this file.)

## The path (checked against `experiments/disasm.txt`)

`stdout` is `0x200a` (unbuffered), so the outer `_vfprintf_r(stdout)` hands off to
`__sbprintf` (`0x8000ac20`). `__sbprintf` builds a fully buffered `FILE` at `sp + 24`
(flags `0x2008`, 1024-byte buffer at `sp + 208`, `stdout`'s cookie and `_write`), runs
`_vfprintf_r` on it, and finishes with `_fflush_r`. The inner `_vfprintf_r`:
entry (N3's `vfpEntry_run`) → `0x8000a944` head → main loop `0x8000a9b0`: scan the
literal run through `mbtowc` → literal iov → `%` parse through the jump table
`0x8001a288` → conversion (`%lld`: sign, decimal loop over `__umoddi3`/`__udivdi3`;
`%s`: `strlen`) → iovs → `__sprint_r` → `__sfvwrite_r` (copy/flush/direct write) → loop.

## Done (all `lake build`-checked; axioms `propext, Classical.choice, Quot.sound`)

- `Fprintf/Move.lean`: `memmove_run` (forward paths, `ReadB`/`ReadWin` sources).
- `Fprintf/Flush.lean`: `sflushF_run(0)`, `fflushF_run(0)` on the stack `FILE`.
- `Fprintf/SbFile.lean`: `SbFile M f pend`, `Frame`, `PieceReads`, advance/flush lemmas.
- `Fprintf/Sfv.lean`, `Fprintf/SfvLoop.lean`: all of `__sfvwrite_r` on the stack `FILE`
  (`sfvwrite_chain`).
- `Fprintf/Sprint.lean`: `sprint_run` (`__sprint_r`).
- `Fprintf/Arith.lean`: `udiv_sw`, `umoddi3_sw`, `moddi3_sw` (E2's routines through
  `swpo_bridge`).
- `Fprintf/Strlen.lean`: `LocalRun.embed`, `strlen_sw` (H3's `strlen` in a stdout run).
- `Fprintf/Scan.lean`: `vfp_mb` (one `mbtowc` round trip), `vfp_lit`, `vfp_scan`
  (literal-run induction; `FmtAt`, `LocMb`, `MbReg`).
- `Fprintf/Digits.lean`: `vfp_digits` (decimal loop `0x8000ca80` → `0x8000cab8`; `digBytes n`
  = `natDigits (n+1) n` of `SnprintfSpec.lean`, whose `intToString_of_bv` gives the sign split).
- `Fprintf/Lld.lean`: `lld_head` (`%lld` parse, argument, sign byte, magnitude; `LldHead`),
  `lld_mag` (one digit or the decimal loop; `LldMag`).
- `Fprintf/Loop.lean`: the loop-head state `VfpLoop`, `VfpSpills`, `vfp_head`
  (`0x8000a944` → `0x8000a9b0`, FILE-independent; shared with N3).
- `Fprintf/ScanTo.lean`: `vfp_toTerm` (loop head → literal run → `%` at `0x8000a9fc` or NUL at
  `0x8000aca8`, the run's iov appended; `VfpPend`, `ScanPost`).
- `Fprintf/LldEmit.lean`, `LldConv.lean`: `lld_stage`, `vfp_lld` (`%lld` from `%` to the loop head).
- `Fprintf/Print.lean`: `vfp_printH` (print through a `__sprint_r` hook, any `FILE`), `sbSprint_hook`
  (the stack `FILE`'s hook, post `SbOut`), `vfp_print`.
- `Fprintf/SConv.lean`: `s_stage` (`%s`, `strlen` a hook).
- `Fprintf/End.lean`: `vfp_tail`, `vfp_end0`, `vfp_end1`, `vfp_end` (NUL → caller, final flush a hook).
- `Fprintf/Inner.lean`, `InnerLld.lean`, `InnerS.lean`: `vfp_fileSb`, `vfp_begin`, and the whole
  inner `_vfprintf_r` on the stack `FILE`: `vfpInnerLld` (`"%lld"`, prints `lldBytes v`),
  `vfpInnerS` (`"<lit>%s>"`, prints `lit ++ bs ++ ">"`).
- `Fprintf/Tac.lean`: `nf_run` passes its stops; `sx_side` rules check the branch fact's shape
  (`bv_side_contra`, `closed_decide`). Files that `open scoped VsaIris.Sym.Stdout` add
  `local macro_rules | \`(tactic| sx_side) => \`(tactic| closed_decide)` after it: N1's scoped
  `assumption` rule recurses on literal `Int.lt` branches.

- `Fprintf/Sbprintf.lean`, `Outer.lean`, `Top.lean`, `Run.lean`: `sbprintf_run` (`__sbprintf`),
  `vfp_outer` (outer `_vfprintf_r(stdout)`), `fprintf_wrap`, `fprintf_sb`, `fprintf_via`; stdout's
  flags (`lh 0x200a`) are a post through all four.
- `Fprintf/Fmts.lean`: `fprintf_lld`, `fprintf_s` (`strlen` through `strlen_sw`).
- `Fprintf/Out.lean`: **`out.fprintf` proved** (`fprintf_out`): data view `soDt` (impure,
  formats, `"."`, jump table, `interpText`, the name), `putcs (lldBytes v) = intToString v.toInt`,
  `OutEnd` through `outEnd_of`. Field and HOLES row removed; `ProofValuePrint` calls the theorem.
  Statement change (INTERP_DESIGN §10 N5): `interpText` live and `0x80100000 ≤ s - fprintfNeed`.

## Status

Done. `out.fprintf` is discharged; merged `hub/lane-n3` at `ecc8d0a`.

## Statement issues

- `_write_r` writes `errno` (`0x8001ba08`): `outSpec` lends it (N1's `ErrnoOwn`), as for
  every `out.*` hole.
- The C locale (`mbtowc` pointer, `mb_cur_max`, decimal point): N2's `LocaleData` /
  N3's `LocaleMt` in `StdioOK`.

## For N3 / N2

Reuse `vfp_scan`/`vfp_lit` for any format's literal runs and `vfp_digits` for `%d`/`%lld`
magnitudes; the conversion pieces will take `strlen` and the print as hook hypotheses and
the format/jump-table bytes as `Dt` facts (agreed with N3).
