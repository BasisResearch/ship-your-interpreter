import Vsa.Sim.Regions

/-!
# Code byte pins for the `%lld` flush hop ranges (`FlushPinsLoaded`)

The executed `snprintf("%lld")` path (mechanical PC trace, `experiments/pctrace.md`)
crosses six small ranges outside `SvfprintfSliceLoaded`'s pinned windows: the
parse-loop tail, three dispatch hops, the `__ssprint_r`-call hop, and the no-pad
shortcut.  92 bytes total, generated from `c/while-riscv-htif.elf`.
-/

