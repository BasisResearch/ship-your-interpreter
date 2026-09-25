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

## In flight
- Building the step table; then the `nx_run` driver (ITac's `ixRunCore` with
  the `nt*` prefixes).

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
