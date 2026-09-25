# Lane N2: the `snprintf` family's newlib holes

Branch `lane-n2` (pushed to `hub`). Holes: `out.snprintfInt`, `out.snprintfFn`,
`newlib.snprintf` (`VsaIris/HOLES.md`). All three run `snprintf` →
`_svfprintf_r` on a string `FILE` (`__ssprint_r` → `__ssputs_r` → `memmove`).

## Done
- **Statement change: `StdioOK` pins the C locale** (`Vsa/Sim/LocaleData.lean`;
  `BootHeapFacts.locale`, control witness `Control.locale_mem`; INTERP_DESIGN.md
  §10 "STATEMENT CHANGES (N2)"). `_svfprintf_r` calls the locale's `mbtowc`
  hook through `jalr`; without the pin the holes were unprovable.
- **Step table for the family** (`scripts/gen_interp_steps.py --target snp` →
  `VsaIris/Vsa/SnpCode.lean`, `VsaIris/Vsa/SnpSteps/*`, over `NW`,
  `VsaIris/Vsa/SnpRunDef.lean`): the interpreter generator, renamed on output,
  plus the linking `jalr` (`ObsStep.lean`: `NStep`, `JalrObs`,
  `nstep_of_jalrObs`), `jr` with an offset (`memset`), and partly known loads
  (`SymHavoc.lean`: `swp_havocP`, `ntP_<pc>`) for `strlen`'s word loads past a
  `strAt` string's NUL. `decode_index.tsv` now also indexes `RetSupp.lean`.

- **Leaf runs over `NW`** (`VsaIris/Vsa/SnpMove.lean`, `SnpPuts.lean`):
  `memmove_nw` (all paths: byte loop, 32/8-byte word loops, tail; any length,
  disjoint ranges; bytes read through data or ownership, `ReadWin`),
  `ssputs_nw` (`__ssputs_r` on the string `FILE`: copies `min len _w`,
  advances `_p`, lowers `_w`; postcondition `PutsOut`). Tools: `nw_gen`
  (rebase the tracking memory), `snp_ld`/`snp_sd`, `bv_nat`, `Copied`.
- Lessons: `omega` recurses too deeply with two truncated subtractions of one
  variable (`x ≤ s - 1024 ⊢ x ≤ s - 264`): convert to additive form first.
  Grep filters on `linter` hide parse errors (the token list names
  `register_linter_set`); check with `grep error`. A doc comment cannot precede
  `#ix_chain`. A declaration holds ~20 driver steps before the 200k budget; split
  long runs into lemmas at call/branch boundaries and rebase memory with
  `nw_gen`; state memory facts at `BitVec.ofNat` addresses (`ofNat_add_ofNat`
  in `nx_run using`).

- **Output chain** (`SnpPrint.lean`): `ssprint_nw` (`__ssprint_r`: every iovec
  piece appended to the printed stream `BufAt`, cut at `n - 1`; uio emptied).
- **`strlen_nw`** (`SnpStrlen.lean`): any alignment, bytes readable through
  data or ownership (`StrRead`), word loads past the NUL as partly known loads;
  VSA's `detect_all_ones` decides the word test; tail arms by `#sl_tail`.
- **`_svfprintf_r` prologue** (`SnpSvf.lean`: `svf_entry`): entry →
  `strlen(".")` → `memset` → spills → loop-head invariant `SvfAt` (named
  fields; caller spills `SvfSaved`; frame outside `SvfW`). Piece chains rebase
  the state into named structures (`SvfPro`) to stay under budget.
- `SnpGeom` now puts the stack scratch and destination above newlib's static
  data (`0x8001c168`).

- **`_svfprintf_r` format loop, so far** (`SnpSvf.lean`): loop head
  `SvfAt`/`SvfCore`; the scan (`svf_scan`, one `__ascii_mbtowc` per byte);
  the literal run's piece (`svf_lit`); pending pieces `SvfSt` with
  memory-independent provenance `PieceSrc` (rebuilt into `PiecesOK` at the
  flush); the conversion start and jump-table dispatch (`svf_convStart`,
  `svf_disp`); `%s` (`svf_convS`, `strlen_nw`); PRINT with sign/body pieces,
  return count, flush through `ssprint_nw` and the back edge, composed as
  `svf_print` from `PrintIn`. `__umoddi3` (`umod_nw`).
- `nx_runF`: the driver variant whose facts also rewrite branch conditions.

- **Conversions and iterations** (`SnpSvfConv.lean`, `SnpSvfLoop.lean`): `%s`
  (`svf_convS`), `%d`/`%lld` (`svf_intD`/`svf_intQ`, `ll` via `svf_convLL`),
  digits (`svf_dig1`, `svf_digLoop` over `umod_nw`/`udiv_nw`, `svf_digExit`),
  rendered as `intToString` bytes (`intPieces`, over M3's
  `digits_eq_natToString`); whole iterations `svf_iterS`, `svf_iterLLD`,
  `svf_iterEnd` (loop head to loop head / to the return).
- **`snprintf_nw`** (`SnpSnprintf.lean`): `snprintf` end to end over `NW`
  (prologue `snp_pro`, `_svfprintf_r`, NUL, epilogue `snp_epi`), parametric in
  the format's loop `SvfLoopRun`; post `SnpOut` (stream cut at `n - 1`, NUL,
  frame).

## In flight
- `SvfLoopRun` for `"%lld"` and `"<fn %s>"`; `%d` iteration; the general
  `parseFmt` induction for `newlib.snprintf`.
- The Iris layer: `wp_localRunW`, readable bytes as the data view
  (`LocalRun.promote`), `binImg` → text and rodata, then the three holes.

## Plan
1. Leaf runs over `NW`: `__ascii_mbtowc` (one char), `strlen` of a data string
   with unknown slack, `memmove` (byte and word paths), `__udivdi3`/`__umoddi3`
   by 10, `memset(·, 0, 8)`, `_localeconv_r`, `__locale_mb_cur_max`.
2. `__ssputs_r` (copy `min(len, _w)`, truncation) and `__ssprint_r` (iov loop).
3. `_svfprintf_r`: prologue; the format loop (literal chunk, `%s`, `%d`,
   `%lld`, flush after each conversion, final flush); functional model
   `fmtRender` and the invariant "buffer = prefix of the rendering, cut at
   `n - 1`".
4. `snprintf` wrapper, then the Iris wrapper (`wp_localRunW`, as
   `HelperRun.helper_leaf`), then the three holes.

## Holes
- Unchanged: `newlib.snprintf`, `out.snprintfFn`, `out.snprintfInt` still ledgered.
- Expected statement changes (to be recorded when made): the destination
  buffer and the readable bytes need RAM geometry (`sb` needs `tohost + 16 ≤
  ea`, loads need RAM off HTIF); the holes state none.
